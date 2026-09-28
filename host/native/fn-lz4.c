/* fn native host: the LZ4 block ENCODER seam (lane compression-extents-2).
 *
 * The append asks this library for one thing: a CANDIDATE LZ4 block for a
 * record's payload span (LZ4-HC, against a dictionary of at most 65,536
 * octets; ID 0 is the empty one).  The candidate is untrusted: ACL2's proved
 * decoder (books/payload-lz.lisp fn-lz-decode, run by
 * books/payload-lz-append.lisp fn-lzr-append-decide) checks that it decodes to
 * exactly the span before the record is taken, and a candidate it refuses is a
 * named fault.  Nothing here decodes, and no reader calls this library.
 *
 * Vendored sources: third_party/lz4 (LZ4 1.10.0, BSD-2-Clause; UPSTREAM.txt
 * pins the tarball's SHA-256 and each file's).  Built by tools/build_lz4.sh
 * into lib/ beside the image's core; host/native/lz4.lisp loads it.
 */
#include <limits.h>
#include "lz4.h"
#include "lz4hc.h"

#define FN_EXPORT __attribute__((visibility("default")))
#define FN_LZ4_DICT_MAX 65536

/* One HC state per thread (about 256 KiB), reset before every block: a block
 * never depends on an earlier one.  Only the owner appends, but a developer
 * verb may encode from another thread. */
static _Thread_local LZ4_streamHC_t *fn_lz4_state;

/* The candidate block for SRC[0, SRC_LEN) against DICT[0, DICT_LEN) at LEVEL
 * into DST[0, DST_CAP): its length (> 0), 0 when it does not fit DST_CAP, or
 * a negative code: -1 an argument outside the library's domain (a source past
 * LZ4_MAX_INPUT_SIZE, a dictionary past the window), -2 no memory. */
FN_EXPORT int fn_lz4_compress_hc(const unsigned char *dict, int dict_len,
                                 const unsigned char *src, int src_len,
                                 unsigned char *dst, int dst_cap, int level)
{
    if (src_len < 0 || src_len > LZ4_MAX_INPUT_SIZE || dst_cap < 0 ||
        dict_len < 0 || dict_len > FN_LZ4_DICT_MAX ||
        (dict_len > 0 && dict == 0) || (src_len > 0 && src == 0) || dst == 0)
        return -1;
    if (fn_lz4_state == 0) {
        fn_lz4_state = LZ4_createStreamHC();
        if (fn_lz4_state == 0)
            return -2;
    }
    LZ4_resetStreamHC_fast(fn_lz4_state, level);
    if (dict_len > 0)
        LZ4_loadDictHC(fn_lz4_state, (const char *)dict, dict_len);
    return LZ4_compress_HC_continue(fn_lz4_state, (const char *)src, (char *)dst,
                                    src_len, dst_cap);
}

/* The worst-case block length for SRC_LEN octets (0 past the input limit). */
FN_EXPORT int fn_lz4_compress_bound(int src_len)
{
    return LZ4_compressBound(src_len);
}

/* The vendored library's version (10000 * major + 100 * minor + patch): the
 * image checks it at load against the pinned 1.10.0. */
FN_EXPORT int fn_lz4_version(void)
{
    return LZ4_versionNumber();
}
