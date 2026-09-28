#!/usr/bin/env python3
"""BLAKE3 for fn's Python tools: an independent reference and a fast path.

fn's digest is BLAKE3 (books/blake3.lisp is its definition; books/crypto-attach
.lisp attaches it to the digest seams; store format 10).  Python is a test and
tooling client, never a second decision engine (AGENTS.md): the tools that
build fixtures or check a store's digests off-line need the same function,
and the Python standard library has none.

Two implementations, one interface (`blake3(data, key=None, context=None)`,
32 octets):

* `blake3_py' is a direct transcription of the BLAKE3 paper's section 2 and
  the reference implementation (reference_impl.rs in the BLAKE3 repository):
  pure Python, a third implementation beside the ACL2 definition and the
  vendored C, used by the self-tests (`python3 tools/blake3_ref.py check'
  runs every official vector, third_party/blake3/test_vectors).  About 0.2
  MB/s: for vectors and small inputs.
* `blake3_c' calls lib/libfn-blake3 (tools/build_blake3.sh over the vendored
  C, third_party/blake3) through ctypes when that library is present
  (FN_BLAKE3_LIBRARY names it, else build/lib/ or lib/ beside the tree):
  gigabytes per second, for fixtures.

`blake3' is the C when it loads and the Python otherwise; `backend()' says
which.  Only the 32-octet default output is provided (fn uses no other).
"""
from __future__ import annotations

import ctypes
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent

IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
      0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)
PERM = (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)
CHUNK_START, CHUNK_END, PARENT, ROOT_FLAG = 1, 2, 4, 8
KEYED_HASH, DERIVE_KEY_CONTEXT, DERIVE_KEY_MATERIAL = 16, 32, 64
M32 = 0xFFFFFFFF


def _g(v, a, b, c, d, x, y):
    v[a] = (v[a] + v[b] + x) & M32
    t = v[d] ^ v[a]; v[d] = ((t >> 16) | (t << 16)) & M32
    v[c] = (v[c] + v[d]) & M32
    t = v[b] ^ v[c]; v[b] = ((t >> 12) | (t << 20)) & M32
    v[a] = (v[a] + v[b] + y) & M32
    t = v[d] ^ v[a]; v[d] = ((t >> 8) | (t << 24)) & M32
    v[c] = (v[c] + v[d]) & M32
    t = v[b] ^ v[c]; v[b] = ((t >> 7) | (t << 25)) & M32


def _compress(cv, block, counter, blen, flags):
    m = [int.from_bytes(block[4 * i:4 * i + 4], "little") for i in range(16)]
    v = list(cv) + list(IV[:4]) + [counter & M32, (counter >> 32) & M32, blen, flags]
    for r in range(7):
        _g(v, 0, 4, 8, 12, m[0], m[1]); _g(v, 1, 5, 9, 13, m[2], m[3])
        _g(v, 2, 6, 10, 14, m[4], m[5]); _g(v, 3, 7, 11, 15, m[6], m[7])
        _g(v, 0, 5, 10, 15, m[8], m[9]); _g(v, 1, 6, 11, 12, m[10], m[11])
        _g(v, 2, 7, 8, 13, m[12], m[13]); _g(v, 3, 4, 9, 14, m[14], m[15])
        if r < 6:
            m = [m[PERM[i]] for i in range(16)]
    return [v[i] ^ v[i + 8] for i in range(8)]


def _chunk_output(key, chunk, counter, flags):
    """The last block's compression inputs (a node's output, section 2.4)."""
    cv, pos, start = list(key), 0, CHUNK_START
    while len(chunk) - pos > 64:
        cv = _compress(cv, chunk[pos:pos + 64], counter, 64, flags | start)
        pos, start = pos + 64, 0
    last = chunk[pos:]
    return (cv, last.ljust(64, b"\0"), counter, len(last), flags | start | CHUNK_END)


def _node(key, data, counter, flags):
    if len(data) <= 1024:
        return _chunk_output(key, data, counter, flags)
    chunks = 1
    while 2048 * chunks < len(data):
        chunks *= 2
    left = _node(key, data[:1024 * chunks], counter, flags)
    right = _node(key, data[1024 * chunks:], counter + chunks, flags)
    block = b"".join(w.to_bytes(4, "little") for w in _compress(*left) + _compress(*right))
    return (list(key), block, 0, 64, flags | PARENT)


def _hash(key, flags, data):
    cv, block, _counter, blen, fl = _node(key, bytes(data), 0, flags)
    return b"".join(w.to_bytes(4, "little") for w in _compress(cv, block, 0, blen, fl | ROOT_FLAG))


def _key_words(key):
    return [int.from_bytes(key[4 * i:4 * i + 4], "little") for i in range(8)]


def blake3_py(data, key=None, context=None):
    """BLAKE3 in pure Python: hash, keyed_hash (32-octet KEY) or derive_key
    (CONTEXT a str or bytes, DATA the key material)."""
    if context is not None:
        ctx = context.encode() if isinstance(context, str) else bytes(context)
        return _hash(_key_words(_hash(IV, DERIVE_KEY_CONTEXT, ctx)), DERIVE_KEY_MATERIAL, data)
    if key is not None:
        if len(key) != 32:
            raise ValueError("a BLAKE3 key is 32 octets")
        return _hash(_key_words(key), KEYED_HASH, data)
    return _hash(IV, 0, data)


_LIB = None


def _library():
    global _LIB
    if _LIB is not None:
        return _LIB or None
    names = ["libfn-blake3.dylib", "libfn-blake3.so"]
    candidates = []
    if os.environ.get("FN_BLAKE3_LIBRARY"):
        candidates.append(Path(os.environ["FN_BLAKE3_LIBRARY"]))
    for base in (ROOT / "build" / "lib", ROOT / "lib"):
        candidates += [base / n for n in names]
    for path in candidates:
        if path.is_file():
            try:
                lib = ctypes.CDLL(str(path))
                lib.fn_b3_hash.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_char_p]
                lib.fn_b3_hash.restype = None
                _LIB = lib
                return lib
            except OSError:
                continue
    _LIB = False
    return None


def blake3_c(data):
    lib = _library()
    if lib is None:
        raise RuntimeError("lib/libfn-blake3 is not built (tools/build_blake3.sh)")
    out = ctypes.create_string_buffer(32)
    data = bytes(data)
    lib.fn_b3_hash(data, len(data), out)
    return out.raw


def blake3(data, key=None, context=None):
    if key is None and context is None and _library() is not None:
        return blake3_c(data)
    return blake3_py(data, key=key, context=context)


def backend():
    return "c" if _library() is not None else "python"


def blake3_hex(data, **kw):
    return blake3(data, **kw).hex()


def check(verbose=False):
    """Every official vector (the 32-octet default output) through the Python
    implementation, and through the C when it loads."""
    tv = json.loads((ROOT / "third_party/blake3/test_vectors/test_vectors.json").read_text())
    key = tv["key"].encode()
    failures = 0
    for case in tv["cases"]:
        n = case["input_len"]
        data = bytes(i % 251 for i in range(n))
        got = [("hash", blake3_py(data).hex(), case["hash"][:64]),
               ("keyed", blake3_py(data, key=key).hex(), case["keyed_hash"][:64]),
               ("derive", blake3_py(data, context=tv["context_string"]).hex(), case["derive_key"][:64])]
        if _library() is not None:
            got.append(("c-hash", blake3_c(data).hex(), case["hash"][:64]))
        for name, actual, expected in got:
            ok = actual == expected
            failures += not ok
            if verbose or not ok:
                print("{} len={} {}".format(name, n, "ok" if ok else "MISMATCH"))
    print("blake3_ref check: {} cases, {} failures, backend {}".format(len(tv["cases"]), failures, backend()))
    return 1 if failures else 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        sys.exit(check("-v" in sys.argv))
    for name in sys.argv[1:]:
        print("{}  {}".format(blake3_hex(Path(name).read_bytes()), name))
