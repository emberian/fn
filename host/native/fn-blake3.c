/* fn-blake3: BLAKE3 and Bao-style verified streaming over the vendored
 * reference C (third_party/blake3, 1.8.7).  The served images load it as
 * lib/libfn-blake3 (host/native/digest.lisp: fn_b3_hash and the incremental
 * hasher replace ACL2's executable BLAKE3 after a start-up check, lane
 * blake3-digest); the outboard encoding and range verification below are
 * lane digest-native's prototype for verified partial reads of large
 * extents (b4, a follow-on lane).
 *
 * The tree.  BLAKE3 hashes 1 KiB chunks into a binary tree whose left
 * subtree always holds the largest power-of-two number of chunks that leaves
 * at least one byte on the right (left_subtree_len).  Every node covering a
 * power-of-two number of chunks at an aligned offset is a node of the whole
 * input's tree, so the tree cut at GROUP-octet leaves (GROUP a power of two
 * multiple of the chunk) is a prefix of BLAKE3's own tree: the root of the
 * cut tree IS the BLAKE3 hash of the input.
 *
 * The outboard (Bao's "outboard" encoding, with GROUP-octet leaves as in
 * Bao's chunk groups): for every node longer than GROUP, in pre-order, its
 * two children's chaining values (64 octets).  An input of n > GROUP octets
 * has ceil(n / GROUP) - 1 such nodes; an input of at most GROUP octets has
 * none and its root is hashed directly.
 *
 * Verifying a range [a, b) against the root: walk from the root; at each
 * internal node read its 64-octet pair from the outboard, check that the
 * pair compresses to the expected value (the root hash at the top, a
 * chaining value below), and descend only into the children the range
 * overlaps, skipping a subtree's outboard by its size; at each leaf the range
 * touches, hash the leaf's octets as a subtree of the whole tree (its chunk
 * counter is its offset / 1 KiB) and compare with the expected chaining
 * value.  Work: one leaf hash per GROUP the range touches and two parent
 * compressions per level, never the whole input.
 *
 * #include "blake3.c" gives this file the reference's static internals
 * (chunk_state_*, parent_output, left_subtree_len,
 * compress_subtree_to_parent_node); nothing in them is modified.
 */
#include "blake3.c"

#include <stdint.h>
#include <string.h>

#define FN_B3_EXPORT __attribute__((visibility("default")))

/* The chaining value of the non-root subtree of LEN octets at chunk COUNTER. */
static void fn_b3_subtree_cv(const uint8_t *in, size_t len, uint64_t counter,
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

static size_t fn_b3_leaves(size_t len, size_t group) {
  return len == 0 ? 1 : (len + group - 1) / group;
}

FN_B3_EXPORT size_t fn_b3_outboard_size(uint64_t len, uint64_t group) {
  return (fn_b3_leaves((size_t)len, (size_t)group) - 1) * BLAKE3_BLOCK_LEN;
}

FN_B3_EXPORT void fn_b3_hash(const uint8_t *in, size_t len, uint8_t out[32]) {
  blake3_hasher h;
  blake3_hasher_init(&h);
  blake3_hasher_update(&h, in, len);
  blake3_hasher_finalize(&h, out, BLAKE3_OUT_LEN);
}

/* The incremental hasher, for host/native/digest.lisp: a message that is a
 * list prefix and then an octet buffer is fed in pieces.  The caller owns
 * the hasher's storage (fn_b3_hasher_size octets, 8-aligned). */
FN_B3_EXPORT size_t fn_b3_hasher_size(void) { return sizeof(blake3_hasher); }

FN_B3_EXPORT void fn_b3_init(blake3_hasher *h) { blake3_hasher_init(h); }

FN_B3_EXPORT void fn_b3_update(blake3_hasher *h, const uint8_t *in, size_t len) {
  blake3_hasher_update(h, in, len);
}

FN_B3_EXPORT void fn_b3_final(const blake3_hasher *h, uint8_t out[32]) {
  blake3_hasher_finalize(h, out, BLAKE3_OUT_LEN);
}

/* Node of LEN > GROUP octets: write its pair at *pos, recurse, answer its
 * chaining value (or the root hash when ROOT). */
static void fn_b3_encode_node(const uint8_t *in, size_t len, uint64_t counter,
                              size_t group, int root, uint8_t *outboard,
                              size_t *pos, uint8_t out[BLAKE3_OUT_LEN]) {
  size_t mine = *pos;
  *pos += BLAKE3_BLOCK_LEN;
  size_t left = left_subtree_len(len);
  uint8_t *pair = outboard + mine;
  if (left <= group)
    fn_b3_subtree_cv(in, left, counter, pair);
  else
    fn_b3_encode_node(in, left, counter, group, 0, outboard, pos, pair);
  size_t right = len - left;
  uint64_t rc = counter + left / BLAKE3_CHUNK_LEN;
  if (right <= group)
    fn_b3_subtree_cv(in + left, right, rc, pair + BLAKE3_OUT_LEN);
  else
    fn_b3_encode_node(in + left, right, rc, group, 0, outboard, pos,
                      pair + BLAKE3_OUT_LEN);
  output_t o = parent_output(pair, IV, 0);
  if (root)
    output_root_bytes(&o, 0, out, BLAKE3_OUT_LEN);
  else
    output_chaining_value(&o, out);
}

/* The root hash of IN and its outboard (fn_b3_outboard_size octets).
 * GROUP is a power of two, at least 1 KiB. */
FN_B3_EXPORT int fn_b3_encode(const uint8_t *in, uint64_t len, uint64_t group,
                              uint8_t *outboard, uint8_t root[32]) {
  if (group < BLAKE3_CHUNK_LEN || (group & (group - 1)) != 0) return -1;
  if (len <= group) {
    fn_b3_hash(in, (size_t)len, root);
    return 0;
  }
  size_t pos = 0;
  fn_b3_encode_node(in, (size_t)len, 0, (size_t)group, 1, outboard, &pos, root);
  return 0;
}

/* Verify the node of LEN octets starting at OFFSET of the input against
 * EXPECT, restricted to [a, b).  DATA is the whole input's address space;
 * only the leaves overlapping [a, b) are read.  0 ok, 1 mismatch. */
static int fn_b3_verify_node(const uint8_t *data, size_t offset, size_t len,
                             size_t group, int root,
                             const uint8_t expect[BLAKE3_OUT_LEN],
                             const uint8_t *outboard, size_t *pos, size_t a,
                             size_t b) {
  const uint8_t *pair = outboard + *pos;
  *pos += BLAKE3_BLOCK_LEN;
  uint8_t got[BLAKE3_OUT_LEN];
  output_t o = parent_output(pair, IV, 0);
  if (root)
    output_root_bytes(&o, 0, got, BLAKE3_OUT_LEN);
  else
    output_chaining_value(&o, got);
  if (memcmp(got, expect, BLAKE3_OUT_LEN) != 0) return 1;
  size_t left = left_subtree_len(len);
  size_t spans[2][2] = {{offset, left}, {offset + left, len - left}};
  for (int side = 0; side < 2; side++) {
    size_t off = spans[side][0], n = spans[side][1];
    const uint8_t *cv = pair + side * BLAKE3_OUT_LEN;
    int overlaps = off < b && a < off + n;
    if (n <= group) {
      if (overlaps) {
        uint8_t leaf[BLAKE3_OUT_LEN];
        fn_b3_subtree_cv(data + off, n, off / BLAKE3_CHUNK_LEN, leaf);
        if (memcmp(leaf, cv, BLAKE3_OUT_LEN) != 0) return 1;
      }
    } else if (overlaps) {
      if (fn_b3_verify_node(data, off, n, group, 0, cv, outboard, pos, a, b))
        return 1;
    } else {
      *pos += (fn_b3_leaves(n, group) - 1) * BLAKE3_BLOCK_LEN;
    }
  }
  return 0;
}

/* Verify [a, b) of an input of LEN octets against ROOT and OUTBOARD, reading
 * DATA only in the GROUP-octet leaves the range overlaps.  0 verified,
 * 1 mismatch, -1 bad arguments. */
FN_B3_EXPORT int fn_b3_verify_range(const uint8_t *data, uint64_t len,
                                    uint64_t group, const uint8_t *outboard,
                                    const uint8_t root[32], uint64_t a,
                                    uint64_t b) {
  if (group < BLAKE3_CHUNK_LEN || (group & (group - 1)) != 0) return -1;
  if (a > b || b > len) return -1;
  if (len <= group) {
    uint8_t got[BLAKE3_OUT_LEN];
    fn_b3_hash(data, (size_t)len, got);
    return memcmp(got, root, BLAKE3_OUT_LEN) != 0;
  }
  size_t pos = 0;
  return fn_b3_verify_node(data, 0, (size_t)len, (size_t)group, 1, root,
                           outboard, &pos, (size_t)a, (size_t)b);
}

FN_B3_EXPORT const char *fn_b3_version(void) { return blake3_version(); }
