"""BLAKE3-256 (the default hash mode, no key, no derivation) in pure Python, for the FNCT trailer the
consumer socket client seals and checks (books/consumer-codec.lisp fn2-fnct-seal; the served side is B's
hasher, books/fnct-pool.lisp). The standard library has no BLAKE3; this follows the specification's
reference implementation and is checked against its published vectors by `python3 -m
tests.surface.blake3_pure`."""

IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)
PERM = (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)
CHUNK_START, CHUNK_END, PARENT, ROOT = 1, 2, 4, 8
M32 = 0xFFFFFFFF


def _g(s, a, b, c, d, x, y):
    s[a] = (s[a] + s[b] + x) & M32
    s[d] = ((s[d] ^ s[a]) >> 16 | (s[d] ^ s[a]) << 16) & M32
    s[c] = (s[c] + s[d]) & M32
    s[b] = ((s[b] ^ s[c]) >> 12 | (s[b] ^ s[c]) << 20) & M32
    s[a] = (s[a] + s[b] + y) & M32
    s[d] = ((s[d] ^ s[a]) >> 8 | (s[d] ^ s[a]) << 24) & M32
    s[c] = (s[c] + s[d]) & M32
    s[b] = ((s[b] ^ s[c]) >> 7 | (s[b] ^ s[c]) << 25) & M32


def _compress(cv, block, counter, blen, flags):
    m = [int.from_bytes(block[4 * i:4 * i + 4], 'little') for i in range(16)]
    s = list(cv) + list(IV[:4]) + [counter & M32, (counter >> 32) & M32, blen, flags]
    for r in range(7):
        _g(s, 0, 4, 8, 12, m[0], m[1]); _g(s, 1, 5, 9, 13, m[2], m[3])
        _g(s, 2, 6, 10, 14, m[4], m[5]); _g(s, 3, 7, 11, 15, m[6], m[7])
        _g(s, 0, 5, 10, 15, m[8], m[9]); _g(s, 1, 6, 11, 12, m[10], m[11])
        _g(s, 2, 7, 8, 13, m[12], m[13]); _g(s, 3, 4, 9, 14, m[14], m[15])
        if r < 6:
            m = [m[p] for p in PERM]
    return [s[i] ^ s[i + 8] for i in range(8)]


def _chunk_output(data, counter):
    """(cv, last block, its length, its flags) of one chunk (at most 1024 octets)."""
    cv = list(IV)
    blocks = [data[i:i + 64] for i in range(0, len(data), 64)] or [b'']
    for i, b in enumerate(blocks[:-1]):
        cv = _compress(cv, b.ljust(64, b'\0'), counter, 64, CHUNK_START if i == 0 else 0)
    last = blocks[-1]
    flags = (CHUNK_START if len(blocks) == 1 else 0) | CHUNK_END
    return cv, last.ljust(64, b'\0'), len(last), flags, counter


def blake3(data):
    data = bytes(data)
    chunks = [data[i:i + 1024] for i in range(0, len(data), 1024)] or [b'']
    outs = [_chunk_output(c, n) for n, c in enumerate(chunks)]
    # the tree: each node's output is (cv, block, len, flags, counter); a parent's block is its children's CVs
    while len(outs) > 1:
        cvs = [_compress(cv, blk, ctr, ln, fl) for cv, blk, ln, fl, ctr in outs]
        # the left subtree of every parent is the largest power of two of chunks: merge pairwise from the left
        nxt = []
        for i in range(0, len(cvs) - 1, 2):
            block = b''.join(w.to_bytes(4, 'little') for w in cvs[i] + cvs[i + 1])
            nxt.append((list(IV), block, 64, PARENT, 0))
        if len(cvs) % 2:
            nxt.append(outs[-1])
        outs = nxt
    cv, block, ln, fl, ctr = outs[0]
    words = _compress(cv, block, ctr, ln, fl | ROOT)
    return b''.join(w.to_bytes(4, 'little') for w in words)


if __name__ == '__main__':
    # The specification's vectors: input i is octet i mod 251, the first 32 octets of the hash.
    vectors = {0: 'af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262',
               1: '2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213',
               1023: '10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11',
               1024: '42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7',
               1025: 'd00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444',
               2048: 'e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a',
               3072: 'b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2',
               4096: '015094013f57a5277b59d8475c0501042c0b642e531b0a1c8f58d2163229e969'}
    bad = [n for n, h in vectors.items() if blake3(bytes(i % 251 for i in range(n))).hex() != h]
    print('blake3_pure:', 'ok' if not bad else f'FAIL at lengths {bad}')
    raise SystemExit(1 if bad else 0)
