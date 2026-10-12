/* Measurement-only TCP/filesystem floors. cc -O2 -pthread floor.c -o floor */
#define _POSIX_C_SOURCE 200809L
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#ifdef __APPLE__
#define fdatasync fsync
#endif

static void die(const char *what) { perror(what); exit(1); }
static void check(int rc, const char *what) { if (rc < 0) die(what); }
static double now(clockid_t clock) {
    struct timespec t;
    check(clock_gettime(clock, &t), "clock_gettime");
    return t.tv_sec + t.tv_nsec / 1e9;
}
static void full_write(int fd, const void *buf, size_t n) {
    const char *p = buf;
    while (n) {
        ssize_t k = write(fd, p, n);
        if (k < 0 && errno == EINTR) continue;
        if (k <= 0) die("write");
        p += k; n -= (size_t)k;
    }
}
static int full_read(int fd, void *buf, size_t n) {
    char *p = buf;
    while (n) {
        ssize_t k = read(fd, p, n);
        if (k < 0 && errno == EINTR) continue;
        if (k < 0) die("read");
        if (!k) return 0;
        p += k; n -= (size_t)k;
    }
    return 1;
}
static int cmp(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}
static void stats(double *ts, int n, double cpu) {
    double sum = 0;
    for (int i = 0; i < n; i++) sum += ts[i];
    qsort(ts, (size_t)n, sizeof(*ts), cmp);
    printf("{\"n\":%d,\"p50_ms\":%.6f,\"p99_ms\":%.6f,\"mean_ms\":%.6f,"
           "\"cpu_ms_per_request\":%.6f}", n, ts[(int)(.50*(n-1)+.5)]*1000,
           ts[(int)(.99*(n-1)+.5)]*1000, sum*1000/n, cpu*1000/n);
}
struct server { int listener; size_t size; char *template; double cpu; };
static void *serve(void *arg) {
    struct server *s = arg;
    int fd = accept(s->listener, NULL, NULL);
    check(fd, "accept");
    int one = 1;
    check(setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one)), "TCP_NODELAY");
    char *reply = malloc(s->size), request;
    if (!reply) die("malloc");
    double cpu0 = 0;
    while (full_read(fd, &request, 1)) {
        if (request == 'R') { cpu0 = now(CLOCK_THREAD_CPUTIME_ID); continue; }
        if (request == 'E') { s->cpu = now(CLOCK_THREAD_CPUTIME_ID) - cpu0; break; }
        memcpy(reply, s->template, s->size);
        full_write(fd, reply, s->size);
    }
    free(reply); check(close(fd), "close"); return NULL;
}
static void tcp_floor(size_t size, int lines, int n) {
    struct server s = {0};
    s.size = size;
    s.template = malloc(size);
    if (!s.template) die("malloc");
    memset(s.template, 'x', size);
    if (lines) for (int i = 1; i <= lines; i++) {
        s.template[i * (size / (size_t)lines) - 2] = '\r';
        s.template[i * (size / (size_t)lines) - 1] = '\n';
    }
    s.listener = socket(AF_INET, SOCK_STREAM, 0); check(s.listener, "socket");
    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    if (inet_pton(AF_INET, "127.0.0.1", &addr.sin_addr) != 1) die("inet_pton");
    check(bind(s.listener, (struct sockaddr *)&addr, sizeof(addr)), "bind");
    check(listen(s.listener, 1), "listen");
    socklen_t len = sizeof(addr);
    check(getsockname(s.listener, (struct sockaddr *)&addr, &len), "getsockname");
    pthread_t thread;
    int rc = pthread_create(&thread, NULL, serve, &s);
    if (rc) { errno = rc; die("pthread_create"); }
    int fd = socket(AF_INET, SOCK_STREAM, 0); check(fd, "socket");
    int one = 1;
    check(setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one)), "TCP_NODELAY");
    check(connect(fd, (struct sockaddr *)&addr, sizeof(addr)), "connect");
    char *reply = malloc(size);
    double *ts = malloc((size_t)n * sizeof(*ts));
    if (!reply || !ts) die("malloc");
    for (int i = 0; i < 50; i++) {
        full_write(fd, "Q", 1);
        if (!full_read(fd, reply, size)) die("unexpected EOF");
    }
    full_write(fd, "R", 1);
    double cpu0 = now(CLOCK_THREAD_CPUTIME_ID);
    for (int i = 0; i < n; i++) {
        double t = now(CLOCK_MONOTONIC);
        full_write(fd, "Q", 1);
        if (!full_read(fd, reply, size)) die("unexpected EOF");
        ts[i] = now(CLOCK_MONOTONIC) - t;
    }
    double client_cpu = now(CLOCK_THREAD_CPUTIME_ID) - cpu0;
    full_write(fd, "E", 1);
    rc = pthread_join(thread, NULL);
    if (rc) { errno = rc; die("pthread_join"); }
    printf("{\"reply_bytes\":%zu,\"reply_lines\":%d,\"latency\":", size, lines);
    stats(ts, n, client_cpu + s.cpu);
    printf(",\"server_cpu_ms_per_request\":%.6f,\"client_cpu_ms_per_request\":%.6f}",
           s.cpu*1000/n, client_cpu*1000/n);
    free(ts); free(reply); free(s.template);
    check(close(fd), "close"); check(close(s.listener), "close");
}
static void append_floor(const char *dir, int group, int n) {
    char path[4096], buf[2048]; memset(buf, 'a', sizeof(buf));
    if (snprintf(path, sizeof(path), "%s/append-%d.bin", dir, group) >= (int)sizeof(path)) {
        errno = ENAMETOOLONG; die("path");
    }
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL | O_APPEND, 0600); check(fd, "open");
    double *ts = malloc((size_t)n * sizeof(*ts)); if (!ts) die("malloc");
    double cpu0 = now(CLOCK_PROCESS_CPUTIME_ID);
    /* n is batches: include every sync, and amortize batch wall per POST.
       No partially unsynced tail or misleading pre-sync per-append percentile. */
    for (int i = 0; i < n; i++) {
        double t = now(CLOCK_MONOTONIC);
        for (int j = 0; j < group; j++) full_write(fd, buf, sizeof(buf));
        check(fdatasync(fd), "fdatasync");
        ts[i] = (now(CLOCK_MONOTONIC) - t) / group;
    }
    double cpu = (now(CLOCK_PROCESS_CPUTIME_ID) - cpu0) / group;
    printf("{\"batch_appends\":%d,\"appends\":%d,\"batch_amortized_per_post\":", group, n*group);
    stats(ts, n, cpu); printf("}");
    free(ts); check(close(fd), "close"); check(unlink(path), "unlink own append file");
}
static void publication(const char *dir) {
    char path[4096], renamed[4096];
    if (snprintf(path, sizeof(path), "%s/publication.bin", dir) >= (int)sizeof(path) ||
        snprintf(renamed, sizeof(renamed), "%s/published.bin", dir) >= (int)sizeof(renamed)) {
        errno = ENAMETOOLONG; die("path");
    }
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600); check(fd, "open");
    size_t chunk = 1024*1024, bytes = 100*chunk;
    char *buf = malloc(chunk); if (!buf) die("malloc"); memset(buf, 'b', chunk);
    double t = now(CLOCK_MONOTONIC), cpu0 = now(CLOCK_PROCESS_CPUTIME_ID);
    for (int i = 0; i < 100; i++) full_write(fd, buf, chunk);
    check(fsync(fd), "fsync");
    double wall = now(CLOCK_MONOTONIC)-t, cpu = now(CLOCK_PROCESS_CPUTIME_ID)-cpu0;
    check(close(fd), "close"); free(buf);
    int directory = open(dir, O_RDONLY); check(directory, "open directory");
    t = now(CLOCK_MONOTONIC);
    check(rename(path, renamed), "rename"); check(fsync(directory), "directory fsync");
    double rename_ms = (now(CLOCK_MONOTONIC)-t)*1000;
    printf("{\"bytes\":%zu,\"chunk_bytes\":%zu,\"write_fsync_ms\":%.6f,"
           "\"cpu_ms\":%.6f,\"mib_per_s\":%.6f,\"rename_dir_fsync_ms\":%.6f}",
           bytes, chunk, wall*1000, cpu*1000, 100/wall, rename_ms);
    check(close(directory), "close"); check(unlink(renamed), "unlink own publication file");
}
int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: floor WORKDIR REPS\n"); return 2; }
    char *end; long count = strtol(argv[2], &end, 10);
    if (*end || count < 1 || count > 1000000) { fprintf(stderr, "invalid reps\n"); return 2; }
    int n = (int)count;
    printf("{\"not_measured\":{},\"cpu_scope\":\"client plus server thread\","
           "\"sync_primitive\":\"");
#ifdef __APPLE__
    printf("fsync (macOS fallback)");
#else
    printf("fdatasync");
#endif
    printf("\",\"tcp\":{\"2k\":"); tcp_floor(2048, 0, n);
    printf(",\"128k\":"); tcp_floor(128*1024, 0, n);
    printf(",\"40_lines\":"); tcp_floor(40*150, 40, n);
    printf("},\"append\":{\"sync1\":"); append_floor(argv[1], 1, n);
    printf(",\"sync8\":"); append_floor(argv[1], 8, n);
    printf(",\"sync64\":"); append_floor(argv[1], 64, n);
    printf("},\"publication\":"); publication(argv[1]); printf("}\n"); return 0;
}
