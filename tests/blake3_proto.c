/* Lane digest-native: the BLAKE3/Bao prototype's correctness witnesses and
 * measurements, over lib/libfn-blake3 (tools/build_blake3.sh).
 *
 *   blake3_proto hashes          one line per length: LEN HEX (input i % 251)
 *   blake3_proto verify          encode/verify witnesses; exit 1 on failure
 *   blake3_proto bench           GB/s, 16 KiB range verify, outboard per MiB
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

size_t fn_b3_outboard_size(uint64_t len, uint64_t group);
void fn_b3_hash(const uint8_t *in, size_t len, uint8_t out[32]);
int fn_b3_encode(const uint8_t *in, uint64_t len, uint64_t group,
                 uint8_t *outboard, uint8_t root[32]);
int fn_b3_verify_range(const uint8_t *data, uint64_t len, uint64_t group,
                       const uint8_t *outboard, const uint8_t root[32],
                       uint64_t a, uint64_t b);
const char *fn_b3_version(void);

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}

static uint8_t *pattern(size_t n) {
  uint8_t *b = malloc(n ? n : 1);
  for (size_t i = 0; i < n; i++) b[i] = (uint8_t)(i % 251);
  return b;
}

static const size_t LENS[] = {0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 2049,
  3072, 3073, 4096, 4097, 5120, 5121, 6144, 6145, 7168, 7169, 8192, 8193,
  16383, 16384, 16385, 31744, 102400, 1048575, 1048576, 1048577, 5000000};

static int fail(const char *what, size_t n, uint64_t g, uint64_t a, uint64_t b) {
  fprintf(stderr, "FAIL %s len=%zu group=%llu range=[%llu,%llu)\n", what, n,
          (unsigned long long)g, (unsigned long long)a, (unsigned long long)b);
  return 1;
}

static int verify_witnesses(void) {
  int bad = 0, checks = 0;
  uint64_t groups[] = {1024, 16384, 65536};
  for (size_t li = 0; li < sizeof LENS / sizeof LENS[0]; li++) {
    size_t n = LENS[li];
    uint8_t *d = pattern(n);
    uint8_t h[32];
    fn_b3_hash(d, n, h);
    for (int gi = 0; gi < 3; gi++) {
      uint64_t g = groups[gi];
      size_t obn = fn_b3_outboard_size(n, g);
      uint8_t *ob = malloc(obn ? obn : 1), root[32];
      fn_b3_encode(d, n, g, ob, root);
      checks++;
      if (memcmp(root, h, 32)) bad |= fail("root is not the hash", n, g, 0, 0);
      /* Ranges: whole, empty, first/last octet, a page in the middle. */
      uint64_t rs[][2] = {{0, n}, {0, 0}, {0, n ? 1 : 0}, {n ? n - 1 : 0, n},
                          {n / 2, n / 2 + (n / 2 + 16384 <= n ? 16384 : n - n / 2)}};
      for (int r = 0; r < 5; r++) {
        uint64_t a = rs[r][0], b = rs[r][1];
        checks++;
        if (fn_b3_verify_range(d, n, g, ob, root, a, b) != 0)
          bad |= fail("intact range refused", n, g, a, b);
        if (b > a) {
          /* A flipped octet inside the range is refused. */
          d[(a + b) / 2] ^= 1;
          checks++;
          if (fn_b3_verify_range(d, n, g, ob, root, a, b) != 1)
            bad |= fail("corrupt octet in range accepted", n, g, a, b);
          d[(a + b) / 2] ^= 1;
        }
        if (n > 2 * g && b - a <= g) {
          /* An octet in a leaf the range does not touch is never read. */
          uint64_t far = (a >= g) ? 0 : n - 1;
          if (far / g != a / g && far / g != (b ? (b - 1) / g : 0)) {
            d[far] ^= 1;
            checks++;
            if (fn_b3_verify_range(d, n, g, ob, root, a, b) != 0)
              bad |= fail("octet outside the range was read", n, g, a, b);
            d[far] ^= 1;
          }
        }
        if (obn) {
          /* The top pair is on every path: a flipped outboard octet there
           * is refused. */
          ob[0] ^= 1;
          checks++;
          if (fn_b3_verify_range(d, n, g, ob, root, a, b) != 1)
            bad |= fail("corrupt outboard accepted", n, g, a, b);
          ob[0] ^= 1;
        }
      }
      free(ob);
    }
    free(d);
  }
  printf("verify %s: %d checks, %s\n", fn_b3_version(), checks, bad ? "FAILED" : "all passed");
  return bad;
}

static void bench(void) {
  size_t n = (size_t)1 << 30; /* 1 GiB */
  uint8_t *d = pattern(n), h[32], root[32];
  double t = now();
  for (int r = 0; r < 3; r++) fn_b3_hash(d, n, h);
  double s = (now() - t) / 3;
  printf("hash 1 GiB: %.3f s, %.2f GB/s single-thread\n", s, n / s / 1e9);
  size_t small[] = {200, 4096, 16384};
  for (int k = 0; k < 3; k++) {
    int reps = 200000;
    t = now();
    for (int r = 0; r < reps; r++) fn_b3_hash(d, small[k], h);
    printf("hash %zu B: %.0f ns\n", small[k], (now() - t) / reps * 1e9);
  }
  uint64_t g = 16384;
  size_t obn = fn_b3_outboard_size(n, g);
  uint8_t *ob = malloc(obn);
  t = now();
  fn_b3_encode(d, n, g, ob, root);
  s = now() - t;
  printf("encode 1 GiB, 16 KiB leaves: %.3f s; outboard %zu octets = %.0f octets per MiB (%.3f%%)\n",
         s, obn, obn / 1024.0, 100.0 * obn / n);
  printf("outboard per MiB at 1 KiB leaves: %.0f octets\n",
         fn_b3_outboard_size(n, 1024) / 1024.0);
  int reps = 100000;
  uint64_t off = 0;
  t = now();
  for (int r = 0; r < reps; r++) {
    off = (off + 7919 * g) % (n - g);
    off -= off % g;
    if (fn_b3_verify_range(d, n, g, ob, root, off, off + g)) { printf("bench verify failed\n"); break; }
  }
  printf("verify one 16 KiB page of a 1 GiB extent: %.2f us\n", (now() - t) / reps * 1e6);
  t = now();
  for (int r = 0; r < reps; r++) {
    off = (off + 7919 * g) % (n - 4096);
    if (fn_b3_verify_range(d, n, g, ob, root, off, off + 1)) { printf("bench verify failed\n"); break; }
  }
  printf("verify one octet of a 1 GiB extent: %.2f us\n", (now() - t) / reps * 1e6);
  free(ob);
  free(d);
}

int main(int argc, char **argv) {
  if (argc == 2 && !strcmp(argv[1], "hashes")) {
    for (size_t li = 0; li < sizeof LENS / sizeof LENS[0]; li++) {
      uint8_t *d = pattern(LENS[li]), h[32];
      fn_b3_hash(d, LENS[li], h);
      printf("%zu ", LENS[li]);
      for (int i = 0; i < 32; i++) printf("%02x", h[i]);
      printf("\n");
      free(d);
    }
    return 0;
  }
  if (argc == 2 && !strcmp(argv[1], "verify")) return verify_witnesses();
  if (argc == 2 && !strcmp(argv[1], "bench")) { bench(); return 0; }
  fprintf(stderr, "usage: blake3_proto hashes|verify|bench\n");
  return 2;
}
