"""specs/wire-grammar.json read by a second, independent interpreter.

The file is ACL2's (books/wire-export.lisp, written by
`tools/protocol_emit.py --wire --write`).  This test is the contract's other
side in miniature: an interpreter of the language written from its
description (planning/design/wire-grammar-2026-10-04.md section 2), not from
the ACL2 code, that must decode every accepted vector to its value, re-encode
the value to the identical octets, and refuse every refusal vector with the
reason the file names.  It is what Mini's generated decoder is checked
against; here it checks that the description and the file agree.  It decides
nothing about fn's bytes (AGENTS.md: Python is a client, never a second
decision engine).
"""
import base64
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import blake3_ref  # noqa: E402

WIRE = ROOT / "specs" / "wire-grammar.json"


class Refused(Exception):
    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


def class_ok(cls, octets):
    if cls == "any":
        return True
    if cls == "header":
        return all(o == 9 or 32 <= o <= 126 for o in octets)
    if cls == "utf8":
        try:
            octets.decode("utf-8", errors="strict")
        except UnicodeDecodeError:
            return False
        return True
    raise AssertionError("unknown class " + cls)


def be(octets):
    return int.from_bytes(octets, "big")


def lines(width, text):
    out = b""
    while text:
        out += text[:width] + b"\r\n"
        text = text[width:]
    return out


def unlines(width, xs):
    out = b""
    while xs:
        if len(xs) <= width + 2:
            return out + xs[:max(len(xs) - 2, 0)]
        out += xs[:width]
        xs = xs[width + 2:]
    return out


def decode(g, xs):
    """(value, rest) or raise Refused."""
    op = g[0]
    if op == "const":
        k = bytes.fromhex(g[1])
        if not xs.startswith(k):
            raise Refused("malformed")
        return None, xs[len(k):]
    if op == "uint":
        w, lo, hi = g[1:]
        if len(xs) < w or not lo <= be(xs[:w]) <= hi:
            raise Refused("malformed")
        return be(xs[:w]), xs[w:]
    if op == "bytes":
        w, lo, hi, cls = g[1:]
        if len(xs) < w:
            raise Refused("malformed")
        n, body = be(xs[:w]), xs[w:]
        if not (lo <= n <= hi and n <= len(body) and class_ok(cls, body[:n])):
            raise Refused("malformed")
        return body[:n].hex(), body[n:]
    if op == "rest":
        lo, hi, cls = g[1:]
        if not (lo <= len(xs) <= hi and class_ok(cls, xs)):
            raise Refused("malformed")
        return xs.hex(), b""
    if op == "line":
        lo, hi, cls = g[1:]
        i = xs.find(b"\r")
        v = xs if i < 0 else xs[:i]
        after = xs[len(v):]
        if not (after.startswith(b"\r\n") and class_ok(cls, v) and lo <= len(v) <= hi):
            raise Refused("malformed")
        return v.hex(), after[2:]
    if op == "base64-lines":
        w, lo, hi = g[1:]
        text = unlines(w, xs)
        if lines(w, text) != xs:
            raise Refused("malformed")
        try:
            v = base64.b64decode(text, validate=True)
        except Exception:
            raise Refused("malformed")
        if base64.b64encode(v) != text or not lo <= len(v) <= hi:
            raise Refused("malformed")
        return v.hex(), b""
    if op == "enum":
        w, base, names = g[1:]
        if len(xs) < w or not base <= be(xs[:w]) < base + len(names):
            raise Refused("malformed")
        return names[be(xs[:w]) - base], xs[w:]
    if op == "seq":
        out = []
        for e in g[1]:
            v, xs = decode(e, xs)
            out.append(v)
        return out, xs
    if op == "tag":
        w, arms = g[1:]
        if len(xs) < w:
            raise Refused("malformed")
        for code, name, sub in arms:
            if be(xs[:w]) == code:
                v, rest = decode(sub, xs[w:])
                return [name, v], rest
        raise Refused("malformed")
    if op == "maybe":
        if not xs:
            return [], b""
        v, rest = decode(g[1], xs)
        return [v], rest
    if op == "where":
        v, rest = decode(g[1], xs)
        for check in g[2]:
            name, *ix = check
            vals = [v[i] for i in ix]
            if not all(isinstance(x, int) for x in vals):
                raise Refused("malformed")
            ok = {"le": lambda a, b: a <= b,
                  "eq": lambda a, b: a == b,
                  "diff": lambda k, j, i: i <= j and k == j - i}[name](*vals)
            if not ok:
                raise Refused("malformed")
        return v, rest
    if op == "frame":
        magic, version, kind, mx, sub = g[1:]
        if len(xs) < 10 or xs[:4] != bytes.fromhex(magic) or xs[4] != version or xs[5] != kind:
            raise Refused("malformed")
        n = be(xs[6:10])
        if n > mx or len(xs) < 10 + n + 32:
            raise Refused("malformed")
        payload, trailer = xs[10:10 + n], xs[10 + n:10 + n + 32]
        if trailer != blake3_ref.blake3(xs[:10 + n]):
            raise Refused("trailer")
        v, rest = decode(sub, payload)
        if rest:
            raise Refused("malformed")
        return v, xs[10 + n + 32:]
    raise AssertionError("unknown node " + op)


def encode(g, v):
    op = g[0]
    if op == "const":
        return bytes.fromhex(g[1])
    if op == "uint":
        return v.to_bytes(g[1], "big")
    if op == "bytes":
        o = bytes.fromhex(v)
        return len(o).to_bytes(g[1], "big") + o
    if op == "rest":
        return bytes.fromhex(v)
    if op == "line":
        return bytes.fromhex(v) + b"\r\n"
    if op == "base64-lines":
        return lines(g[1], base64.b64encode(bytes.fromhex(v)))
    if op == "enum":
        return (g[2] + g[3].index(v)).to_bytes(g[1], "big")
    if op == "seq":
        return b"".join(encode(e, x) for e, x in zip(g[1], v))
    if op == "tag":
        for code, name, sub in g[2]:
            if name == v[0]:
                return code.to_bytes(g[1], "big") + encode(sub, v[1])
        raise AssertionError("no arm " + v[0])
    if op == "maybe":
        return encode(g[1], v[0]) if v else b""
    if op == "where":
        return encode(g[1], v)
    if op == "frame":
        magic, version, kind, mx, sub = g[1:]
        p = encode(sub, v)
        prot = bytes.fromhex(magic) + bytes([version, kind]) + len(p).to_bytes(4, "big") + p
        return prot + blake3_ref.blake3(prot)
    raise AssertionError("unknown node " + op)


class WireGrammarFile(unittest.TestCase):
    def setUp(self):
        self.doc = json.loads(WIRE.read_bytes())

    def test_header(self):
        self.assertEqual(self.doc["format"], "fn-wire-grammar")
        self.assertEqual(self.doc["version"], 1)
        self.assertEqual(self.doc["trailer"], "blake3-256")

    def test_every_vector(self):
        names = {f["name"] for f in self.doc["families"]}
        counted = 0
        for family in self.doc["families"]:
            g = family["grammar"]
            self.assertTrue(family["vectors"], family["name"])
            for vector in family["vectors"]:
                self.assertEqual(vector["family"], family["name"])
                self.assertEqual(vector["version"], self.doc["version"])
                octets = bytes.fromhex(vector["octets"])
                if "refused" in vector:
                    with self.assertRaises(Refused) as caught:
                        value, rest = decode(g, octets)
                        if rest:
                            raise Refused("malformed")
                    self.assertEqual(caught.exception.reason, vector["refused"])
                else:
                    value, rest = decode(g, octets)
                    self.assertEqual(rest, b"", family["name"])
                    self.assertEqual(value, vector["value"], family["name"])
                    self.assertEqual(encode(g, value), octets, family["name"])
                counted += 1
        self.assertGreater(counted, 0)
        for exchange in self.doc["exchanges"]:
            self.assertIn(exchange["request"], names)
            for reply in exchange["replies"]:
                self.assertIn(reply, names)


if __name__ == "__main__":
    unittest.main()
