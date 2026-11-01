/* Stateless BLAKE3 primitives for fn2. Lifted from fn1's native adapter.
 * All continuation state remains in ACL2 columns; no C hasher survives a call.
 * The vendored 1.8.7 implementation supplies the algorithm and CPU dispatch.
 */
#include "blake3.c"
#include <stdint.h>
#include <string.h>
#define FN_B3_EXPORT __attribute__((visibility("default")))

/* The chaining value of the non-root subtree of LEN octets at chunk COUNTER. */
FN_B3_EXPORT void fn_b3_subtree_cv(const uint8_t *in, size_t len, uint64_t counter,
                             uint8_t cv[BLAKE3_OUT_LEN]) {
  if (len <= BLAKE3_CHUNK_LEN) {
    blake3_chunk_state cs;
    chunk_state_init(&cs, IV, 0);
    cs.chunk_counter = counter;
    chunk_state_update(&cs, in, len);
    output_t o = chunk_state_output(&cs);
    output_chaining_value(&o, cv);
  } else {
    uint8_t block[BLAKE3_BLOCK_LEN];
    compress_subtree_to_parent_node(in, len, IV, counter, 0, block, false);
    output_t o = parent_output(block, IV, 0);
    output_chaining_value(&o, cv);
  }
}

FN_B3_EXPORT void fn_b3_hash(const uint8_t *in, size_t len, uint8_t out[32]) {
  blake3_hasher h;
  blake3_hasher_init(&h);
  blake3_hasher_update(&h, in, len);
  blake3_hasher_finalize(&h, out, BLAKE3_OUT_LEN);
}

FN_B3_EXPORT void fn2_b3_subtree_words(const uint8_t *in, size_t len,
                                        uint64_t counter, uint32_t out[8]) {
  uint8_t bytes[32];
  fn_b3_subtree_cv(in, len, counter, bytes);
  for (size_t i = 0; i < 8; i++) out[i] = load32(bytes + 4*i);
}

/* Keep the rightmost Output: CV before its last block, plus the block itself.
 * ROOT is a later choice. A non-root CV alone would lose that information. */
FN_B3_EXPORT void fn2_b3_chunk_output(const uint8_t *in, uint64_t counter,
                                      uint32_t cv[8], uint32_t block[16]) {
  blake3_chunk_state cs;
  chunk_state_init(&cs, IV, 0);
  cs.chunk_counter = counter;
  chunk_state_update(&cs, in, BLAKE3_CHUNK_LEN);
  memcpy(cv, cs.cv, 32);
  for (size_t i = 0; i < 16; i++) block[i] = load32(cs.buf + 4*i);
}

FN_B3_EXPORT void fn2_b3_compress(const uint32_t cv[8],
                                  const uint32_t words[16], uint64_t counter,
                                  uint8_t len, uint8_t flags, uint32_t out[8]) {
  uint8_t block[64];
  for (size_t i = 0; i < 16; i++) store32(block + 4*i, words[i]);
  if (out != cv) memcpy(out, cv, 32);
  blake3_compress_in_place(out, block, len, counter, flags);
}

/* RFC 6962's complete 65-byte node message, not a BLAKE3 PARENT CV. */
FN_B3_EXPORT void fn2_b3_node(const uint32_t left[8], const uint32_t right[8],
                              uint32_t out[8]) {
  uint8_t message[65], digest[32];
  message[0] = 1;
  for (size_t i = 0; i < 8; i++) {
    store32(message + 1 + 4*i, left[i]);
    store32(message + 33 + 4*i, right[i]);
  }
  fn_b3_hash(message, sizeof(message), digest);
  for (size_t i = 0; i < 8; i++) out[i] = load32(digest + 4*i);
}
FN_B3_EXPORT const char *fn_b3_version(void) { return blake3_version(); }

/* Exact first-nonzero position; never inspect bytes beyond the admitted span. */
FN_B3_EXPORT size_t fn2_zero_prefix(const uint8_t *in, size_t len) {
  size_t i = 0;
  while (len - i >= sizeof(uint64_t)) {
    uint64_t word;
    memcpy(&word, in + i, sizeof(word));
    if (word != 0) break;
    i += sizeof(word);
  }
  while (i < len && in[i] == 0) i++;
  return i;
}

/* Append within one partial chunk. The buffered final block remains an Output.
 * Preserve unused message words exactly as fn2-b3-byte does. */
FN_B3_EXPORT void fn2_b3_fragment(const uint8_t *in, size_t len,
    uint64_t counter, uint32_t cv[8], uint32_t words[16], uint32_t state[2]) {
  unsigned pos = state[0], blocks = state[1];
  while (len--) {
    if (pos == 64) {
      fn2_b3_compress(cv, words, counter, 64, blocks == 0 ? 1 : 0, cv);
      blocks++;
      pos = 0;
    }
    unsigned i = pos / 4, shift = 8 * (pos % 4);
    words[i] = (shift ? words[i] : 0) + ((uint32_t)*in++ << shift);
    pos++;
  }
  state[0] = pos;
  state[1] = blocks;
}
