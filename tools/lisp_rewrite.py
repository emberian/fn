#!/usr/bin/env python3
"""Shared structural rewriter for Lisp source (the one reader of tools/).

Public interface: exactly four entry points.  Spans are half-open [start, end)
offsets into `Parsed.text`, a str decoded from UTF-8 with surrogateescape and
no newline translation, so write() round-trips any file byte for byte (for
ASCII text a span IS a byte span; `Parsed.byte_span` gives the true one).

  parse(src) -> Parsed            src: a Path / an existing file name / the text
      .text .forms .comments      forms: top-level nodes Atom | Str | Pre | Lst,
      each with .start .end; comments: [(start, text)] for ; and nested #| |#.
      Reads ; #|..|# (nested) "strings" #\\c ' ` , ,@ #' #(..) |pipes| pkg::sym
      numbers #x #b #o #NNr #:sym.  Refuses #. (read-eval), #+ #- and every
      other dispatch macro with Unsupported (a ReadError) naming it.
  match(pattern, forms, *, deep=True, head=None, name=None, arity=None,
        where=None) -> [Match]        Match(node, start, end, captures)
      pattern is Lisp text/node: `?x` captures one form (repeats must be equal),
      `?*xs` captures a run of list items, `_` is any; symbols compare
      case-insensitively.  head=/name=/arity= (int or predicate on the arg
      count) and where=(Match -> bool) are shape predicates.  deep=False tests
      only the given top-level forms.
  emit(form, *, indent=0, width=84, layout="house", drop_comments=False) -> str
      House layout (see EMIT below); layout="aligned" is the original
      def_loop_drain printer.  Refuses (CommentLoss) a parsed list that holds
      comments, since the tree does not carry them; splice source text instead.
  write(text, edits) -> str          edits: (start, end, replacement) spans;
      "" deletes, start == end inserts.  Overlaps and out-of-range raise
      EditError; every byte outside the edited spans is identical.
"""
from __future__ import annotations

import os
import re
from dataclasses import dataclass, field
from pathlib import Path

# --------------------------------------------------------------------------
# nodes


@dataclass
class Atom:
    text: str
    start: int = 0
    end: int = 0

    @property
    def low(self):
        return self.text.lower()

    @property
    def kind(self):
        t = self.text
        if isinstance(self, Str):
            return "string"
        if t.startswith("#\\"):
            return "char"
        if NUMBER.match(t):
            return "number"
        return "symbol"


@dataclass
class Str(Atom):
    pass


@dataclass
class Pre:
    prefix: str
    node: object
    start: int = 0
    end: int = 0


@dataclass
class Lst:
    items: list
    start: int = 0
    end: int = 0
    comments: list = field(default_factory=list)  # `;` comment text inside, in order
    has_comment: bool = False  # any comment (; or #| |#) anywhere inside


NUMBER = re.compile(r"^[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$|^[+-]?\d+/\d+$|^#[xXbBoO][+-]?[0-9a-fA-F/]+$|^#\d+[rR]\w+$")


class ReadError(Exception):
    pass


class Unsupported(ReadError):
    """A reader form this reader refuses by name (never guessed at)."""

    def __init__(self, reason, pos, detail=""):
        super().__init__(f"{reason} at {pos}: {detail}")
        self.reason = reason
        self.pos = pos


class CommentLoss(Exception):
    pass


class EditError(Exception):
    pass


# --------------------------------------------------------------------------
# reader

WS = " \t\n\r\f\v"
TERMINATORS = set(WS) | set("()\";'`,")
REFUSED_DISPATCH = {
    ".": "read-eval (#.)",
    "+": "feature-expression (#+)",
    "-": "feature-expression (#-)",
}


@dataclass
class Parsed:
    text: str
    forms: list
    comments: list
    path: str | None = None

    def byte_span(self, node):
        enc = lambda s: len(s.encode("utf-8", "surrogateescape"))  # noqa: E731
        return enc(self.text[:node.start]), enc(self.text[:node.end])


def _load(src):
    if isinstance(src, bytes):
        return src.decode("utf-8", "surrogateescape"), None
    if isinstance(src, os.PathLike) or (
            isinstance(src, str) and "\n" not in src and len(src) < 4096
            and not src.lstrip().startswith(("(", ";", "#", '"', "'", "`"))
            and os.path.isfile(src)):
        p = Path(src)
        return p.read_bytes().decode("utf-8", "surrogateescape"), str(p)
    return src, None


class _Reader:
    def __init__(self, text):
        self.t = text
        self.i = 0
        self.n = len(text)
        self.comments = []
        self.stack = []  # open Lst frames, for comment attribution

    def note_comment(self, a, b, semi):
        s = self.t[a:b]
        self.comments.append((a, s))
        for f in self.stack:
            f.has_comment = True
        if semi and self.stack:
            self.stack[-1].comments.append(s)

    def skip(self):
        t, n = self.t, self.n
        while self.i < n:
            c = t[self.i]
            if c in WS:
                self.i += 1
            elif c == ";":
                j = t.find("\n", self.i)
                j = n if j < 0 else j
                self.note_comment(self.i, j, True)
                self.i = j
            elif c == "#" and t.startswith("#|", self.i):
                self.block_comment()
            else:
                return

    def block_comment(self):
        t = self.t
        a = self.i
        depth = 0
        i = a
        while i < self.n:
            if t.startswith("#|", i):
                depth += 1
                i += 2
            elif t.startswith("|#", i):
                depth -= 1
                i += 2
                if depth == 0:
                    self.note_comment(a, i, False)
                    self.i = i
                    return
            else:
                i += 1
        raise ReadError(f"unterminated #| at {a}")

    def token_end(self, i):
        t, n = self.t, self.n
        while i < n:
            c = t[i]
            if c == "\\":
                i += 2
            elif c == "|":
                j = t.find("|", i + 1)
                if j < 0:
                    raise ReadError(f"unterminated | at {i}")
                i = j + 1
            elif c in TERMINATORS:
                break
            else:
                i += 1
        return min(i, n)

    def datum(self):
        self.skip()
        t, a = self.t, self.i
        if a >= self.n:
            raise ReadError("unexpected end of input")
        c = t[a]
        if c == ")":
            raise ReadError(f"unbalanced ) at {a}")
        if c == "(":
            return self.lst(a, 1)
        if c == '"':
            i = a + 1
            while i < self.n and t[i] != '"':
                i += 2 if t[i] == "\\" else 1
            if i >= self.n:
                raise ReadError(f"unterminated string at {a}")
            self.i = i + 1
            return Str(t[a:i + 1], a, i + 1)
        if c in "'`":
            return self.pre(c, a, a + 1)
        if c == ",":
            p = ",@" if t.startswith(",@", a) else ","
            return self.pre(p, a, a + len(p))
        if c == "#":
            return self.dispatch(a)
        e = self.token_end(a)
        if e == a:  # a lone escape at the end
            raise ReadError(f"unreadable text at {a}")
        self.i = e
        return Atom(t[a:e], a, e)

    def pre(self, prefix, a, after):
        self.i = after
        node = self.datum()
        return Pre(prefix, node, a, node.end)

    def lst(self, a, skip):
        node = Lst([], a, 0)
        self.stack.append(node)
        self.i = a + skip
        while True:
            self.skip()
            if self.i >= self.n:
                raise ReadError(f"unbalanced ( at {a}")
            if self.t[self.i] == ")":
                self.i += 1
                break
            node.items.append(self.datum())
        self.stack.pop()
        node.end = self.i
        return node

    def dispatch(self, a):
        t = self.t
        d = t[a + 1] if a + 1 < self.n else ""
        if d == "'":
            return self.pre("#'", a, a + 2)
        if d == "(":
            i = a + 1
            node = self.lst(i, 1)
            return Pre("#", node, a, node.end)
        if d == "\\":
            e = self.token_end(a + 3) if a + 2 < self.n else a + 2
            if a + 2 >= self.n:
                raise ReadError(f"unterminated #\\ at {a}")
            e = max(e, a + 3)
            self.i = e
            return Atom(t[a:e], a, e)
        if d in REFUSED_DISPATCH:
            raise Unsupported(REFUSED_DISPATCH[d], a, t[a:a + 12])
        m = re.compile(r"#(?:[xXbBoO]|\d+[rR]|:)").match(t, a)
        if m:
            e = self.token_end(m.end())
            if e == m.end() and not t.startswith("#:", a):
                raise Unsupported("malformed radix number", a, t[a:a + 12])
            self.i = e
            return Atom(t[a:e], a, e)
        raise Unsupported(f"dispatch macro #{d}", a, t[a:a + 12])


def parse(src) -> Parsed:
    """Read SRC (a Path, an existing file name, bytes, or Lisp text) to a Parsed."""
    text, path = _load(src)
    r = _Reader(text)
    forms = []
    while True:
        r.skip()
        if r.i >= r.n:
            break
        forms.append(r.datum())
    return Parsed(text, forms, r.comments, path)


# --------------------------------------------------------------------------
# structural match


@dataclass
class Match:
    node: object
    start: int
    end: int
    captures: dict


def _sym(n):
    return isinstance(n, Atom) and not isinstance(n, Str) and n.kind != "char"


def flat(n) -> str:
    if isinstance(n, Pre):
        return n.prefix + flat(n.node)
    if isinstance(n, Lst):
        return "(" + " ".join(flat(i) for i in n.items) + ")"
    return n.text


def _same(a, b):
    """Structural equality ignoring spans and symbol case."""
    if isinstance(a, Pre):
        return isinstance(b, Pre) and a.prefix == b.prefix and _same(a.node, b.node)
    if isinstance(a, Lst):
        return (isinstance(b, Lst) and len(a.items) == len(b.items)
                and all(_same(x, y) for x, y in zip(a.items, b.items)))
    if not isinstance(b, Atom) or isinstance(a, Str) != isinstance(b, Str):
        return False
    return a.text == b.text if (isinstance(a, Str) or a.kind == "char") else a.low == b.low


def _items_match(pats, i, items, j, caps):
    if i == len(pats):
        return j == len(items)
    p = pats[i]
    if _sym(p) and p.text.startswith("?*"):
        name = p.text[2:]
        for k in range(len(items), j - 1, -1):
            c2 = dict(caps)
            run = items[j:k]
            if name != "_":
                if name in c2 and not (len(c2[name]) == len(run)
                                       and all(_same(x, y) for x, y in zip(c2[name], run))):
                    continue
                c2[name] = list(run)
            if _items_match(pats, i + 1, items, k, c2):
                caps.clear()
                caps.update(c2)
                return True
        return False
    if j >= len(items):
        return False
    c2 = dict(caps)
    if _node_match(p, items[j], c2) and _items_match(pats, i + 1, items, j + 1, c2):
        caps.clear()
        caps.update(c2)
        return True
    return False


def _node_match(p, n, caps):
    if _sym(p):
        if p.text == "_":
            return True
        if p.text.startswith("?") and len(p.text) > 1 and not p.text.startswith("?*"):
            name = p.text[1:]
            if name in caps:
                return _same(caps[name], n)
            caps[name] = n
            return True
    if isinstance(p, Lst):
        return isinstance(n, Lst) and _items_match(p.items, 0, n.items, 0, caps)
    if isinstance(p, Pre):
        return isinstance(n, Pre) and p.prefix == n.prefix and _node_match(p.node, n.node, caps)
    return _same(p, n)


def _walk(n):
    yield n
    if isinstance(n, Pre):
        yield from _walk(n.node)
    elif isinstance(n, Lst):
        for i in n.items:
            yield from _walk(i)


def match(pattern, forms, *, deep=True, head=None, name=None, arity=None, where=None):
    """Matches of PATTERN (None: any form) among FORMS, in source order."""
    if isinstance(pattern, str):
        ps = parse(pattern).forms
        if len(ps) != 1:
            raise ReadError("a pattern is exactly one form")
        pattern = ps[0]
    if isinstance(forms, Parsed):
        forms = forms.forms
    elif isinstance(forms, (Atom, Pre, Lst)):
        forms = [forms]
    out = []
    for top in forms:
        for n in (_walk(top) if deep else [top]):
            if head is not None or name is not None or arity is not None:
                if not (isinstance(n, Lst) and n.items and _sym(n.items[0])):
                    continue
                if head is not None and n.items[0].low != head.lower():
                    continue
                if name is not None and not (len(n.items) > 1 and _sym(n.items[1])
                                             and n.items[1].low == name.lower()):
                    continue
                if arity is not None:
                    k = len(n.items) - 1
                    if not (arity(k) if callable(arity) else arity == k):
                        continue
            caps = {}
            if pattern is not None and not _node_match(pattern, n, caps):
                continue
            m = Match(n, n.start, n.end, caps)
            if where is None or where(m):
                out.append(m)
    return out


# --------------------------------------------------------------------------
# emit

DEFUN_LIKE = {"defun", "defund", "defun-nx", "defun-inline", "defmacro", "defun-sk",
              "defund-nx", "defabbrev"}
DEFTHM_LIKE = {"defthm", "defthmd", "defthm-inline"}
LET_LIKE = {"let", "let*", "mv-let", "flet", "labels", "mv?-let", "b*"}


def _kw(n):
    return isinstance(n, Atom) and not isinstance(n, Str) and n.text.startswith(":")


def _units(items):
    """Items with each :keyword grouped with the datum that follows it."""
    out, i = [], 0
    while i < len(items):
        if _kw(items[i]) and i + 1 < len(items):
            out.append((items[i], items[i + 1]))
            i += 2
        else:
            out.append((items[i],))
            i += 1
    return out


def _unit(u, indent, width, layout, drop):
    if len(u) == 1:
        return _emit(u[0], indent, width, layout, drop)
    return u[0].text + " " + _emit(u[1], indent + len(u[0].text) + 1, width, layout, drop)


def _check_comments(n, drop):
    if isinstance(n, Lst) and n.has_comment and not drop:
        raise CommentLoss(f"list at {n.start} holds comments; emit would drop them")


def _emit(n, indent, width, layout, drop):
    _check_comments(n, drop)
    one = flat(n)
    head = n.items[0] if isinstance(n, Lst) and n.items else None
    hl = head.low if _sym(head) else None
    house = layout == "house"
    must_break = house and hl in (DEFUN_LIKE | DEFTHM_LIKE) and len(n.items) > 3
    if not must_break and (indent + len(one) <= width or not isinstance(n, (Lst, Pre))):
        return one
    if isinstance(n, Pre):
        return n.prefix + _emit(n.node, indent + len(n.prefix), width, layout, drop)
    items = n.items
    if not items:
        return "()"
    em = lambda x, ind: _emit(x, ind, width, layout, drop)  # noqa: E731
    if house and hl is not None and len(items) > 1:
        body = indent + 2
        if hl in DEFUN_LIKE and len(items) > 2:
            hdr = [items[1], items[2]]
            first = f"({head.text} {em(items[1], indent + len(head.text) + 2)} " \
                    f"{em(items[2], indent + len(head.text) + 3 + len(flat(items[1])))}"
            rest = [" " * body + _unit(u, body, width, layout, drop) for u in _units(items[3:])]
            return "\n".join([first] + rest) + ")"
        if hl in DEFTHM_LIKE:
            first = f"({head.text} {em(items[1], indent + len(head.text) + 2)}"
            rest = [" " * body + _unit(u, body, width, layout, drop) for u in _units(items[2:])]
            return "\n".join([first] + rest) + ")"
        if hl in LET_LIKE and len(items) > 2:
            if hl in ("mv-let",) and len(items) > 3:
                hdr_items, rest_items = items[1:3], items[3:]
            else:
                hdr_items, rest_items = items[1:2], items[2:]
            pad = indent + len(head.text) + 2
            hdr = em(hdr_items[0], pad)
            if len(hdr_items) == 2:
                hdr += " " + em(hdr_items[1], indent + len(head.text) + 3 + len(flat(hdr_items[0])))
            return "\n".join([f"({head.text} {hdr}"] +
                             [" " * body + em(x, body) for x in rest_items]) + ")"
        if hl == "if" and len(items) == 4:
            pad = indent + 4
            return (f"(if {em(items[1], indent + 4)}\n" + " " * pad + em(items[2], pad) + "\n"
                    + " " * body + em(items[3], body) + ")")
    if isinstance(head, Atom) and len(items) > 1 and not isinstance(head, Str):
        pad = indent + 2 + len(head.text)
        us = _units(items[1:]) if house else [(i,) for i in items[1:]]
        first = _unit(us[0], pad, width, layout, drop)
        rest = [" " * pad + _unit(u, pad, width, layout, drop) for u in us[1:]]
        return "(" + head.text + " " + "\n".join([first] + rest) + ")"
    pad = indent + 1
    return "(" + ("\n" + " " * pad).join(_emit(i, pad, width, layout, drop) for i in items) + ")"


def emit(form, *, indent=0, width=84, layout="house", drop_comments=False) -> str:
    """FORM as text laid out at column INDENT.  Forms that fit within WIDTH stay
    on one line, except defun/defthm families, which always break after their
    header.  EMIT (house): defun/defmacro NAME ARGS on the head line, body at +2;
    defthm NAME on the head line, the rest at +2 with each :key and its value on
    one line; let/mv-let bindings on the head line, body at +2; (if T A B) with
    A at +4 and B at +2; any other call aligns its arguments under the first,
    with :key value pairs kept together.  layout="aligned" is the plain
    align-under-first-argument printer."""
    return _emit(form, indent, width, layout, drop_comments)


# --------------------------------------------------------------------------
# byte-preserving write


def write(text: str, edits) -> str:
    """TEXT with each (start, end, replacement) edit applied; all else identical."""
    es = sorted(((int(s), int(e), r) for s, e, r in edits), key=lambda t: (t[0], t[1]))
    out = []
    pos = 0
    for s, e, r in es:
        if not (0 <= s <= e <= len(text)):
            raise EditError(f"span [{s},{e}) outside the text (length {len(text)})")
        if s < pos:
            raise EditError(f"span [{s},{e}) overlaps an earlier edit ending at {pos}")
        out.append(text[pos:s])
        out.append(r)
        pos = e
    out.append(text[pos:])
    return "".join(out)
