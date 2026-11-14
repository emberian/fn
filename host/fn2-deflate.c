/* Bounded raw RFC1951 carrier. Admission, extent and cumulative application
 * budgets belong to ACL2. Each call consumes only the supplied windows; the
 * caller retains unconsumed input and resumes after output backpressure.
 * Encode precondition: ACL2 selects a FULL output window of at least seven
 * bytes (zlib Z_SYNC_FLUSH contract); decode supports one-byte windows. */
#include <stdint.h>
#include <stdlib.h>
#include <zlib.h>

typedef struct { z_stream rx, tx; int rx_live, tx_live; } fn2_deflate;
void fn2_deflate_free(fn2_deflate *s) {
  if (!s) return;
  if (s->rx_live) inflateEnd(&s->rx);
  if (s->tx_live) deflateEnd(&s->tx);
  free(s);
}
fn2_deflate *fn2_deflate_new(void) {
  fn2_deflate *s = calloc(1, sizeof(*s));
  if (!s) return NULL;
  if (inflateInit2(&s->rx, -15) != Z_OK) { fn2_deflate_free(s); return NULL; }
  s->rx_live = 1;
  if (deflateInit2(&s->tx, Z_DEFAULT_COMPRESSION, Z_DEFLATED, -15, 8,
                   Z_DEFAULT_STRATEGY) != Z_OK) { fn2_deflate_free(s); return NULL; }
  s->tx_live = 1;
  return s;
}
/* 0 progress/would-block; 1 BFINAL (caller must close); -1 malformed/error.
 * BFINAL is never automatically restarted as another compressed stream. */
int fn2_deflate_step(fn2_deflate *s, int encode, const uint8_t *in,
                     uint32_t in_len, uint8_t *out, uint32_t out_len,
                     uint32_t *used, uint32_t *made) {
  *used = *made = 0;
  if (!s || !out_len || (!in && in_len) || !out) return -1;
  z_stream *z = encode ? &s->tx : &s->rx;
  z->next_in = (Bytef *)in; z->avail_in = in_len;
  z->next_out = out; z->avail_out = out_len;
  int rc = encode ? deflate(z, Z_SYNC_FLUSH) : inflate(z, Z_SYNC_FLUSH);
  *used = in_len - z->avail_in; *made = out_len - z->avail_out;
  /* Drop borrowed pointers before returning to the scheduler. */
  z->next_in = NULL; z->avail_in = 0; z->next_out = NULL; z->avail_out = 0;
  if (rc == Z_STREAM_END) return 1;
  return (rc == Z_OK || rc == Z_BUF_ERROR) ? 0 : -1;
}
