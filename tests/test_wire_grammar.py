"""build/box/wire-grammar.json (the box step's artifact) read by a second, independent interpreter.

The file is ACL2's (books/wire-export.lisp, written by
`tools/protocol_emit.py --wire --write`).  This test is the contract's other
side in miniature: an interpreter of the language written from its
description (planning/design/wire-grammar-2026-10-04.md section 2), not from
the ACL2 code, that must find every grammar well formed (the static rules,
read independently: a reader that skips them accepts grammars the round
trips do not cover), decode every accepted vector to its value, re-encode
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

import box_artifacts  # noqa: E402


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


CLASSES = {"any", "utf8", "header"}
WIDTHS = {1, 2, 4, 8}


def nat(x):
    return isinstance(x, int) and not isinstance(x, bool) and x >= 0


def is_hex(x):
    return (isinstance(x, str) and len(x) % 2 == 0
            and all(c in "0123456789abcdef" for c in x))


def delimited(g):
    """Section 2, `Delimited`: decoding stops at the end of the encoding."""
    op = g[0]
    if op in ("const", "uint", "bytes", "line", "enum", "frame"):
        return True
    if op == "seq":
        return all(delimited(e) for e in g[1])
    if op == "tag":
        return all(delimited(arm[2]) for arm in g[2])
    if op == "where":
        return delimited(g[1])
    return False  # rest, maybe, base64-lines


def nonempty(g):
    """Section 2, `Non-empty`: no value encodes to no octets."""
    op = g[0]
    if op == "const":
        return len(g[1]) > 0
    if op in ("uint", "bytes", "line", "enum", "frame", "tag"):
        return True
    if op == "rest":
        return g[1] >= 1
    if op == "base64-lines":
        return g[2] >= 1
    if op == "seq":
        return any(nonempty(e) for e in g[1])
    if op == "where":
        return nonempty(g[1])
    return False  # maybe


def wellformed(g):
    """Section 2, `Well-formedness`, exactly; False for anything else."""
    if not isinstance(g, list) or not g or not isinstance(g[0], str):
        return False
    op, args = g[0], g[1:]

    def bounded(lo, hi, limit=None):
        return nat(lo) and nat(hi) and lo <= hi and (limit is None or hi < limit)

    if op == "const":
        return len(args) == 1 and is_hex(args[0])
    if op == "uint":
        return len(args) == 3 and args[0] in WIDTHS and nat(args[0]) and \
            bounded(args[1], args[2], 256 ** args[0])
    if op == "bytes":
        return len(args) == 4 and args[0] in WIDTHS and nat(args[0]) and \
            bounded(args[1], args[2], 256 ** args[0]) and args[3] in CLASSES
    if op == "rest":
        return len(args) == 3 and bounded(args[0], args[1]) and args[2] in CLASSES
    if op == "line":
        return len(args) == 3 and bounded(args[0], args[1]) and args[2] == "header"
    if op == "base64-lines":
        return len(args) == 3 and nat(args[0]) and args[0] >= 1 and \
            bounded(args[1], args[2])
    if op == "enum":
        if len(args) != 3 or args[0] not in WIDTHS or not nat(args[0]) or not nat(args[1]):
            return False
        names = args[2]
        return (isinstance(names, list) and len(names) > 0
                and all(isinstance(n, str) for n in names)
                and len(set(names)) == len(names)
                and args[1] + len(names) <= 256 ** args[0])
    if op == "seq":
        if len(args) != 1 or not isinstance(args[0], list):
            return False
        elems = args[0]
        return all(wellformed(e) for e in elems) and \
            all(delimited(e) for e in elems[:-1])
    if op == "tag":
        if len(args) != 2 or args[0] not in WIDTHS or not nat(args[0]) \
                or not isinstance(args[1], list):
            return False
        arms = args[1]
        for arm in arms:
            if not (isinstance(arm, list) and len(arm) == 3 and nat(arm[0])
                    and arm[0] < 256 ** args[0] and isinstance(arm[1], str)
                    and wellformed(arm[2])):
                return False
        return (len({a[0] for a in arms}) == len(arms)
                and len({a[1] for a in arms}) == len(arms))
    if op == "maybe":
        return len(args) == 1 and wellformed(args[0]) and nonempty(args[0])
    if op == "where":
        if len(args) != 2 or not wellformed(args[0]) or args[0][0] != "seq" \
                or not isinstance(args[1], list):
            return False
        for check in args[1]:
            if not (isinstance(check, list) and check
                    and ((check[0] in ("le", "eq") and len(check) == 3)
                         or (check[0] == "diff" and len(check) == 4))
                    and all(nat(i) for i in check[1:])):
                return False
        return True
    if op == "frame":
        return (len(args) == 5 and is_hex(args[0]) and len(args[0]) == 8
                and nat(args[1]) and args[1] < 256 and nat(args[2]) and args[2] < 256
                and nat(args[3]) and args[3] < 2 ** 32 and wellformed(args[4]))
    return False


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
        # The fields first (a refusal there is theirs); then each check on the
        # decoded value: an index past the end or a non-number fails it.
        v, rest = decode(g[1], xs)
        for check in g[2]:
            name, *ix = check
            vals = [v[i] if i < len(v) else None for i in ix]
            ok = all(nat(x) for x in vals) and {
                "le": lambda a, b: a <= b,
                "eq": lambda a, b: a == b,
                "diff": lambda k, j, i: i <= j and k == j - i}[name](*vals)
            if not ok:
                raise Refused("where")
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


KINDS = {"accept", "concat", "prefix", "mutation", "length", "refuse"}
REFUSALS = ["trailer", "where", "malformed"]
NODES = {"const", "uint", "bytes", "rest", "line", "base64-lines", "enum",
         "seq", "tag", "maybe", "where", "frame"}


def nodes(g):
    """Every node kind G uses."""
    out = {g[0]}
    if g[0] == "seq":
        for e in g[1]:
            out |= nodes(e)
    elif g[0] == "tag":
        for arm in g[2]:
            out |= nodes(arm[2])
    elif g[0] in ("maybe", "where"):
        out |= nodes(g[1])
    elif g[0] == "frame":
        out |= nodes(g[5])
    return out


class WellFormedness(unittest.TestCase):
    """The checker's own teeth: each static rule refuses a grammar that breaks
    only it, and the same grammar with the rule met is accepted."""

    CASES = [
        # (rule, a grammar that breaks it, the nearest grammar that meets it)
        ("uint width", ["uint", 3, 0, 1], ["uint", 4, 0, 1]),
        ("uint bound", ["uint", 1, 0, 256], ["uint", 1, 0, 255]),
        ("uint order", ["uint", 1, 2, 1], ["uint", 1, 1, 1]),
        ("bytes class", ["bytes", 1, 0, 1, "latin1"], ["bytes", 1, 0, 1, "any"]),
        ("line class", ["line", 0, 9, "any"], ["line", 0, 9, "header"]),
        ("line class utf8", ["line", 0, 9, "utf8"], ["line", 0, 9, "header"]),
        ("base64 width", ["base64-lines", 0, 0, 9], ["base64-lines", 1, 0, 9]),
        ("enum empty", ["enum", 1, 0, []], ["enum", 1, 0, ["a"]]),
        ("enum distinct", ["enum", 1, 0, ["a", "a"]], ["enum", 1, 0, ["a", "b"]]),
        ("enum room", ["enum", 1, 255, ["a", "b"]], ["enum", 1, 254, ["a", "b"]]),
        ("seq tail-only", ["seq", [["rest", 0, 1, "any"], ["uint", 1, 0, 1]]],
         ["seq", [["uint", 1, 0, 1], ["rest", 0, 1, "any"]]]),
        ("seq maybe last", ["seq", [["maybe", ["uint", 1, 0, 1]], ["uint", 1, 0, 1]]],
         ["seq", [["uint", 1, 0, 1], ["maybe", ["uint", 1, 0, 1]]]]),
        ("tag codes", ["tag", 1, [[0, "a", ["seq", []]], [0, "b", ["seq", []]]]],
         ["tag", 1, [[0, "a", ["seq", []]], [1, "b", ["seq", []]]]]),
        ("tag names", ["tag", 1, [[0, "a", ["seq", []]], [1, "a", ["seq", []]]]],
         ["tag", 1, [[0, "a", ["seq", []]], [1, "b", ["seq", []]]]]),
        ("tag code width", ["tag", 1, [[256, "a", ["seq", []]]]],
         ["tag", 2, [[256, "a", ["seq", []]]]]),
        ("maybe non-empty", ["maybe", ["rest", 0, 4, "any"]], ["maybe", ["rest", 1, 4, "any"]]),
        ("maybe of maybe", ["maybe", ["maybe", ["uint", 1, 0, 1]]],
         ["maybe", ["uint", 1, 0, 1]]),
        ("maybe empty seq", ["maybe", ["seq", []]], ["maybe", ["seq", [["uint", 1, 0, 1]]]]),
        ("where over seq", ["where", ["uint", 1, 0, 1], []],
         ["where", ["seq", [["uint", 1, 0, 1]]], []]),
        ("where check arity", ["where", ["seq", [["uint", 1, 0, 1]]], [["le", 0]]],
         ["where", ["seq", [["uint", 1, 0, 1]]], [["le", 0, 0]]]),
        ("where check name", ["where", ["seq", [["uint", 1, 0, 1]]], [["lt", 0, 0]]],
         ["where", ["seq", [["uint", 1, 0, 1]]], [["eq", 0, 0]]]),
        ("frame magic", ["frame", "666e63", 1, 1, 0, ["seq", []]],
         ["frame", "666e6374", 1, 1, 0, ["seq", []]]),
        ("frame max", ["frame", "666e6374", 1, 1, 2 ** 32, ["seq", []]],
         ["frame", "666e6374", 1, 1, 2 ** 32 - 1, ["seq", []]]),
        ("frame kind", ["frame", "666e6374", 1, 256, 0, ["seq", []]],
         ["frame", "666e6374", 1, 255, 0, ["seq", []]]),
        ("unknown node", ["cbor-uint"], ["seq", []]),
    ]

    def test_each_rule_has_teeth(self):
        for rule, bad, good in self.CASES:
            self.assertFalse(wellformed(bad), rule)
            self.assertTrue(wellformed(good), rule)

    def test_frame_payload_need_not_be_delimited(self):
        self.assertTrue(wellformed(["frame", "666e6374", 1, 1, 9, ["rest", 0, 9, "any"]]))


class WireGrammarFile(unittest.TestCase):
    def setUp(self):
        self.doc = box_artifacts.load("wire-grammar.json", ROOT)

    def test_header(self):
        self.assertEqual(self.doc["format"], "fn-wire-grammar")
        self.assertEqual(self.doc["version"], 1)
        self.assertEqual(self.doc["trailer"], "blake3-256")

    def test_words(self):
        """The decoder's refusal words, in the file; nothing else is answered."""
        self.assertEqual(self.doc["words"]["refusals"], REFUSALS)

    def test_every_grammar_is_well_formed(self):
        for family in self.doc["families"]:
            self.assertTrue(wellformed(family["grammar"]), family["name"])

    def test_the_vectors_cover_the_language(self):
        """Every node is in some family, and every refusal word and the where
        refusal case are pinned by a vector."""
        used, refused, cases = set(), set(), set()
        for family in self.doc["families"]:
            used |= nodes(family["grammar"])
            for vector in family["vectors"]:
                refused.add(vector.get("refused"))
                cases.add(vector.get("case"))
        self.assertEqual(used, NODES)
        self.assertLessEqual(set(REFUSALS), refused)
        self.assertIn("where-le", cases)
        self.assertIn("empty-history", cases)

    def test_identity_fields_are_never_empty(self):
        """Mini's note 1: the store-identity reply's history and incarnation
        are 1..64 octets; their absence is the `unbootstrapped' arm."""
        family = {f["name"]: f for f in self.doc["families"]}["fnct.store-identity.reply"]
        accepted = family["grammar"][5][2][0][2][1]
        consumer = accepted[4]
        self.assertEqual(consumer[0], "tag")
        arms = {arm[1]: arm[2] for arm in consumer[2]}
        self.assertEqual(arms["unbootstrapped"], ["seq", []])
        self.assertEqual(arms["bootstrapped"],
                         ["seq", [["bytes", 1, 1, 64, "any"], ["bytes", 1, 1, 64, "any"]]])
        for field in accepted:
            if field[0] == "bytes":
                self.assertGreaterEqual(field[2], 1, field)

    def test_every_vector(self):
        """Each vector's octets decode here to exactly the answer the file
        prints: the value, the octets consumed and the rest, or the refusal
        (which consumes nothing); an accepted value re-encodes to exactly the
        octets consumed."""
        names = {f["name"] for f in self.doc["families"]}
        counted = {}
        for family in self.doc["families"]:
            g = family["grammar"]
            kinds = set()
            for vector in family["vectors"]:
                where = "%s %s %s" % (family["name"], vector["kind"], vector["octets"][:80])
                self.assertEqual(vector["family"], family["name"])
                self.assertEqual(vector["version"], self.doc["version"])
                self.assertIn(vector["kind"], KINDS)
                self.assertEqual("case" in vector, vector["kind"] == "refuse", where)
                kinds.add(vector["kind"])
                octets = bytes.fromhex(vector["octets"])
                try:
                    value, rest = decode(g, octets)
                except Refused as refusal:
                    self.assertIn("refused", vector, where)
                    self.assertIn(vector["refused"], REFUSALS, where)
                    self.assertEqual(refusal.reason, vector["refused"], where)
                    continue
                self.assertNotEqual(vector["kind"], "refuse", where)
                self.assertNotIn("refused", vector, where)
                self.assertEqual(value, vector["value"], where)
                self.assertEqual(len(octets) - len(rest), vector["consumed"], where)
                self.assertEqual(rest.hex(), vector["rest"], where)
                self.assertEqual(encode(g, value), octets[:vector["consumed"]], where)
                counted[vector["kind"]] = counted.get(vector["kind"], 0) + 1
            self.assertIn("accept", kinds, family["name"])
            self.assertIn("prefix", kinds, family["name"])
            self.assertIn("mutation", kinds, family["name"])
            if g[0] == "frame":
                self.assertIn("length", kinds, family["name"])
                refused = {v.get("refused") for v in family["vectors"]}
                self.assertIn("trailer", refused, family["name"])
                self.assertIn("malformed", refused, family["name"])
        self.assertTrue(counted)
        for exchange in self.doc["exchanges"]:
            self.assertIn(exchange["request"], names)
            for reply in exchange["replies"]:
                self.assertIn(reply, names)


if __name__ == "__main__":
    unittest.main()
