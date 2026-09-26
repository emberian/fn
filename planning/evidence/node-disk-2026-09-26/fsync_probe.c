/* fsync_probe DIR SIZE N SYSCALL: in a fresh temporary directory under DIR,
   open one file O_WRONLY|O_CREAT|O_APPEND, then N times: write SIZE octets,
   call SYSCALL (fsync or fdatasync); time write+sync with CLOCK_MONOTONIC.
   One unmeasured warm-up append. Prints median, p95, min, max in ms.
   Removes the file and the directory before exiting. */
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
static int cmp(const void *a, const void *b) {
  double x = *(const double *)a, y = *(const double *)b;
  return (x > y) - (x < y);
}
static double now_ms(void) {
  struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e3 + t.tv_nsec / 1e6;
}
int main(int argc, char **argv) {
  if (argc != 5) { fprintf(stderr, "usage: DIR SIZE N fsync|fdatasync\n"); return 2; }
  size_t size = strtoul(argv[2], 0, 10); int n = atoi(argv[3]);
  int use_fdatasync = strcmp(argv[4], "fdatasync") == 0;
  char dir[4096]; snprintf(dir, sizeof dir, "%s/fsync-probe.XXXXXX", argv[1]);
  if (!mkdtemp(dir)) { perror("mkdtemp"); return 1; }
  char path[4200]; snprintf(path, sizeof path, "%s/log", dir);
  int fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0600);
  if (fd < 0) { perror("open"); rmdir(dir); return 1; }
  char *buf = malloc(size); memset(buf, 'x', size);
  double *s = malloc(sizeof(double) * n); int rc = 0;
  for (int i = -1; i < n; i++) {
    double t0 = now_ms();
    if (write(fd, buf, size) != (ssize_t)size) { perror("write"); rc = 1; break; }
    if ((use_fdatasync ? fdatasync(fd) : fsync(fd)) != 0) { perror("sync"); rc = 1; break; }
    if (i >= 0) s[i] = now_ms() - t0;
  }
  close(fd); unlink(path); rmdir(dir);
  if (rc) return rc;
  qsort(s, n, sizeof(double), cmp);
  double med = n % 2 ? s[n / 2] : (s[n / 2 - 1] + s[n / 2]) / 2;
  int p95 = (int)(0.95 * n + 0.999999) - 1; if (p95 < 0) p95 = 0;
  printf("dir=%s size=%zu n=%d syscall=%s median_ms=%.3f p95_ms=%.3f min_ms=%.3f max_ms=%.3f\n",
         argv[1], size, n, argv[4], med, s[p95], s[0], s[n - 1]);
  return 0;
}
