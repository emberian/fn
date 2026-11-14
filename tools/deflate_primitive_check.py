#!/usr/bin/env python3
"""Narrow independent raw-DEFLATE controls; this is not served-path evidence."""
import ctypes as c
import pathlib
import subprocess
import tempfile
import zlib


def main():
    root = pathlib.Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory(prefix="fn2-deflate-") as tmp:
        lib = pathlib.Path(tmp) / "deflate.so"
        subprocess.run(["cc", "-shared", "-fPIC", "-Wall", "-Wextra", "-Werror",
                        str(root / "host/fn2-deflate.c"), "-lz", "-o", str(lib)], check=True)
        dll = c.CDLL(str(lib))
        dll.fn2_deflate_new.restype = c.c_void_p
        dll.fn2_deflate_free.argtypes = [c.c_void_p]
        dll.fn2_deflate_step.argtypes = [c.c_void_p, c.c_int, c.c_void_p, c.c_uint32,
                                       c.c_void_p, c.c_uint32, c.POINTER(c.c_uint32),
                                       c.POINTER(c.c_uint32)]
        def step(s, encode, data, cap):
            inp = c.create_string_buffer(data)
            out = c.create_string_buffer(cap)
            used, made = c.c_uint32(), c.c_uint32()
            status = dll.fn2_deflate_step(s, encode, inp, len(data), out, cap,
                                          c.byref(used), c.byref(made))
            assert used.value <= len(data) and made.value <= cap
            return status, used.value, out.raw[:made.value]
        payload = bytes(range(256)) * 40 + b"a" * 100000
        comp = zlib.compressobj(wbits=-15)
        wire = comp.compress(payload) + comp.flush(zlib.Z_SYNC_FLUSH)
        for chunk, cap in [(1, 1), (7, 13), (len(wire), 64)]:
            s = dll.fn2_deflate_new(); assert s
            result = bytearray()
            try:
                for pos in range(0, len(wire), chunk):
                    pending = wire[pos:pos+chunk]
                    while True:
                        status, used, out = step(s, 0, pending, cap)
                        assert status == 0
                        result.extend(out); pending = pending[used:]
                        if not pending and len(out) < cap: break
                        assert used or out
                assert result == payload
            finally: dll.fn2_deflate_free(s)
        s = dll.fn2_deflate_new(); assert s
        try:
            pending, wire_out = payload, bytearray()
            while True:
                status, used, out = step(s, 1, pending, 29)
                assert status == 0
                pending = pending[used:]; wire_out.extend(out)
                if not pending and len(out) < 29: break
                assert used or out
            assert zlib.decompressobj(-15).decompress(wire_out) == payload
        finally: dll.fn2_deflate_free(s)
        for wire_bad, expected in [(b"\x07", -1), (zlib.compress(payload, wbits=-15), 1)]:
            s = dll.fn2_deflate_new()
            try:
                status, _, _ = step(s, 0, wire_bad, len(payload) + 1)
                assert status == expected
            finally: dll.fn2_deflate_free(s)
        # A bomb can expose at most the caller's application window per turn.
        s = dll.fn2_deflate_new()
        try:
            status, used, out = step(s, 0, wire, 11)
            assert status == 0 and len(out) == 11 and used < len(wire)
        finally: dll.fn2_deflate_free(s)
    print("PASS raw DEFLATE: fragmentation, backpressure, roundtrip, malformed, BFINAL, output budget")


if __name__ == "__main__": main()
