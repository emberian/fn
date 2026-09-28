/* fn native host: the COMPRESS DEFLATE OUTBOUND compressor (lane compress;
 * RFC 8054 over RFC 1951).
 *
 * A served connection that issued COMPRESS DEFLATE (206) has one stream here
 * for what the server sends: each reply window ACL2 rendered is compressed
 * and followed by a sync flush (RFC 8054 section 2.2.2: "all data that was
 * submitted for compression MUST be included in the compressed output, and
 * appropriately flushed").  Nothing here decides an octet: the octets are
 * ACL2's, and a fault here can only garble what the server sends.  The
 * client's stream is decoded by ACL2 (books/deflate-inflate.lisp fn-zin-feed);
 * no inflater is compiled into this library.
 *
 * Vendored sources: third_party/zlib (zlib 1.3.2, the zlib licence;
 * UPSTREAM.txt pins the tarball's SHA-256 and each file's).  Built by
 * tools/build_deflate.sh into lib/ beside the image's core;
 * host/native/deflate.lisp loads it.  The parameters (level, window bits,
 * memory level) are ACL2's (books/nntp-compress.lisp fn-zc-deflate-params).
 */
#include <stdlib.h>
#include "zlib.h"

#define FN_EXPORT __attribute__((visibility("default")))

/* Built Z_SOLO (no gzip file layer), so the allocator is ours. */
static voidpf fn_deflate_alloc(voidpf opaque, uInt items, uInt size)
{
    (void)opaque;
    return calloc(items, size);
}

static void fn_deflate_release(voidpf opaque, voidpf address)
{
    (void)opaque;
    free(address);
}

/* A new raw-DEFLATE stream (no zlib header: negative window bits, RFC 8054
 * section 4), or 0 when the parameters are outside zlib's domain or memory
 * runs out. */
FN_EXPORT void *fn_deflate_new(int level, int window_bits, int mem_level)
{
    z_stream *s;
    if (level < 0 || level > 9 || window_bits < 9 || window_bits > 15 ||
        mem_level < 1 || mem_level > 9)
        return 0;
    s = calloc(1, sizeof *s);
    if (s == 0)
        return 0;
    s->zalloc = fn_deflate_alloc;
    s->zfree = fn_deflate_release;
    s->opaque = 0;
    if (deflateInit2(s, level, Z_DEFLATED, -window_bits, mem_level,
                     Z_DEFAULT_STRATEGY) != Z_OK) {
        free(s);
        return 0;
    }
    return s;
}

/* The worst case for SRC_LEN octets and a sync flush: deflateBound plus the
 * flush's empty stored block and its alignment. */
FN_EXPORT long fn_deflate_bound(void *h, long src_len)
{
    if (h == 0 || src_len < 0 || src_len > 0x3fffffffL)
        return -1;
    return (long)deflateBound((z_stream *)h, (uLong)src_len) + 16;
}

/* Compress SRC[0, SRC_LEN) into DST[0, DST_CAP) and sync-flush: the octets
 * written, or -1 (arguments), -2 (the output did not fit DST_CAP; the stream
 * is then unusable and the connection must close), -3 (a zlib error). */
FN_EXPORT long fn_deflate_sync(void *h, const unsigned char *src, long src_len,
                               unsigned char *dst, long dst_cap)
{
    z_stream *s = (z_stream *)h;
    int rc;
    if (s == 0 || src_len < 0 || dst_cap <= 0 || dst == 0 ||
        (src_len > 0 && src == 0) || src_len > 0x3fffffffL || dst_cap > 0x3fffffffL)
        return -1;
    s->next_in = (Bytef *)src;
    s->avail_in = (uInt)src_len;
    s->next_out = dst;
    s->avail_out = (uInt)dst_cap;
    rc = deflate(s, Z_SYNC_FLUSH);
    if (rc != Z_OK && rc != Z_BUF_ERROR)
        return -3;
    if (s->avail_in != 0 || s->avail_out == 0)
        return -2;
    return dst_cap - (long)s->avail_out;
}

FN_EXPORT void fn_deflate_free(void *h)
{
    if (h != 0) {
        deflateEnd((z_stream *)h);
        free(h);
    }
}

/* The vendored library's version (ZLIB_VERNUM, 0x1320 for 1.3.2): the image
 * checks it at load against the pinned one. */
FN_EXPORT int fn_deflate_version(void)
{
    return ZLIB_VERNUM;
}
