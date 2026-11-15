#!/usr/bin/env python3
"""Narrow independent raw-DEFLATE controls; this is not served-path evidence."""
import ctypes as c
import argparse
import hashlib
import pathlib
import tempfile
import zlib


def selected_library(root, library, scratch):
    if library is not None:
        selected = pathlib.Path(library).resolve(strict=True)
        if not selected.is_file():
            raise ValueError("selected library is not a file")
        return selected
    from fn_admin import prepare_native_deflate
    selected = pathlib.Path(scratch) / "deflate.so"
    prepare_native_deflate(root, selected)
    return selected


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=pathlib.Path,
                        help="test this exact existing artifact without compiling another")
    args = parser.parse_args(argv)
    root = pathlib.Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory(prefix="fn2-deflate-") as tmp:
        lib = selected_library(root, args.library, tmp)
        before = hashlib.sha256(lib.read_bytes()).hexdigest()
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
        for encoder_capacity in (7, 29):
            s = dll.fn2_deflate_new(); assert s
            try:
                peer = zlib.decompressobj(-15)
                for message in (payload, b"second command after the first sync flush\r\n"):
                    pending, wire_out = message, bytearray()
                    while True:
                        status, used, out = step(s, 1, pending, encoder_capacity)
                        assert status == 0
                        pending = pending[used:]; wire_out.extend(out)
                        if not pending and len(out) < encoder_capacity: break
                        assert used or out
                    assert peer.decompress(wire_out) == message
                # The receive stream is independent of both completed send turns.
                status, used, out = step(s, 0, wire, len(payload) + 1)
                assert status == 0 and used == len(wire) and out == payload
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
        assert hashlib.sha256(lib.read_bytes()).hexdigest() == before, "selected library changed during controls"
        print(f"artifact {lib} sha256={before}")
    print("PASS raw DEFLATE: fragmentation, backpressure, persistent duplex roundtrip, malformed, BFINAL, output budget")


if __name__ == "__main__": main()
