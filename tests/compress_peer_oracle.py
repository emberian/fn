"""Independent persistent raw-DEFLATE peer oracle for the backend socket gate.

Each JSON row is [expected plaintext hex, compressed socket bytes hex].
The inflater survives every row; each row must decode exactly one reply.
"""
import json
import sys
import zlib


def check(rows):
    inflater = zlib.decompressobj(-15)
    for index, (plain_hex, wire_hex) in enumerate(rows):
        plain, wire = bytes.fromhex(plain_hex), bytes.fromhex(wire_hex)
        if not wire:
            raise AssertionError(f"reply {index}: no socket output")
        actual = inflater.decompress(wire)
        if actual != plain:
            raise AssertionError(f"reply {index}: {actual!r} != {plain!r}")
        if inflater.eof or inflater.unused_data or inflater.unconsumed_tail:
            raise AssertionError(f"reply {index}: stream ended or left undecoded bytes")
    if len(rows) < 2:
        raise AssertionError("persistent stream needs multiple replies")
    return True


if __name__ == "__main__":
    check(json.load(sys.stdin))
    print("backend persistent DEFLATE peer: PASS")
