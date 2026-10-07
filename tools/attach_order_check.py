#!/usr/bin/env python3
"""Fail a certified host file whose include-book closure reaches an attachable stobj generic before its attach book.

Why: a host file that is include-book'd (D61) is compiled in the world its own
include-books build.  Reaching `fn-arena` (books/payload-arena.lisp) without
`books/payload-arena-attach` first compiles it against the generic arena, while
the image runs the attached one.  The owner then read arena count 0 where the
host's arena held 1, and every second POST stopped with "owner prepare returned
NOT-SEALED" (CONVERGE-1, red 1).

What it checks, in the default image's source tree, no ACL2 needed:
  pairs   an attach book is a books/*.lisp with a literal `(attach-stobj GEN IMPL)`
          that host/native/build.lisp includes; the generic is the book with
          `(defabsstobj GEN ... :attachable t`.  Today: fn-arena
          (payload-arena-attach) and fn-hist (history-paged-attach).
  scope   the host/*.lisp files reachable by include-book from the four
          books/image-world* umbrellas.
  rule    walking a file's include-books depth first, each book at its first
          inclusion (the order ACL2 certifies it), the generic must be met
          inside the attach book or after it.  Otherwise: one finding naming the
          file and the include-book line to add first.

What it does not check: `defattach` seams (codec-attach, records-attach,
crypto-attach), because the stub resolves its attachment at call time and order
does not matter; books/* above a generic, which stay certified over it by design
(books/catalog.lisp header); catalog-paged-attach, which the image does not
include.  It reads source order, not the .cert files, which are binary; a
certificate records the same inclusion order.

Enforced by: tools/native_preflight.py gate `attach-order` (hbox_native.sh static
gates), `make check`, and tests/test_attach_order_check.py (red and green
fixtures).  Exit 1 on any finding.
"""
from __future__ import annotations

import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
UMBRELLAS = ("books/image-world", "books/image-world-dtn", "books/image-world-paged",
             "books/image-world-store-test")
BUILD = "host/native/build.lisp"
_INCLUDE = re.compile(r'^\s*\(include-book\s+"([^"]+)"', re.M)
_ATTACH = re.compile(r'\(attach-stobj\s+([A-Za-z0-9$*+-]+)\s+[A-Za-z0-9$*+-]+\s*\)', re.I)


def _read(path: Path) -> str:
    return re.sub(r";[^\n]*", "", path.read_text(errors="replace"))


class World:
    def __init__(self, root: Path):
        self.root = root
        self._incs: dict[str, list[str]] = {}

    def includes(self, rel: str) -> list[str]:
        if rel not in self._incs:
            out = []
            base = os.path.dirname(rel)
            for m in _INCLUDE.finditer(_read(self.root / (rel + ".lisp"))):
                target = os.path.normpath(os.path.join(base, m.group(1)))
                if (self.root / (target + ".lisp")).exists():
                    out.append(target)
            self._incs[rel] = out
        return self._incs[rel]

    def closure(self, rel: str) -> list[str]:
        seen: list[str] = []
        stack = [rel]
        while stack:
            book = stack.pop()
            if book not in seen:
                seen.append(book)
                stack.extend(self.includes(book))
        return seen

    def generic_state(self, rel: str, generic: str, attach: str) -> str:
        """How the closure of REL first meets GENERIC: "absent" (not reached),
        "attached" (inside the attach book, which attaches before it includes the
        generic, or after it finished) or "bare" (reached with no attachment)."""
        done: set[str] = set()
        result = ["absent"]

        def go(book: str, stack: tuple[str, ...]) -> None:
            if book in done or result[0] != "absent":
                return
            done.add(book)
            if book == generic:
                result[0] = "attached" if attach in stack or attach in finished else "bare"
                return
            for child in self.includes(book):
                go(child, stack + (book,))
            finished.add(book)

        finished: set[str] = set()
        go(rel, ())
        return result[0]


def pairs(root: Path) -> list[tuple[str, str, str]]:
    """(generic name, generic book, attach book), the image's attach books only."""
    image = {os.path.normpath(m.group(1)) for m in _INCLUDE.finditer(_read(root / BUILD))}
    found = []
    for path in sorted((root / "books").glob("*.lisp")):
        rel = "books/" + path.stem
        if rel not in image:
            continue
        for m in _ATTACH.finditer(_read(path)):
            gen = m.group(1).lower()
            generic = [p for p in sorted((root / "books").glob("*.lisp"))
                       if re.search(r"\(defabsstobj\s+%s\b" % re.escape(gen), _read(p), re.I)
                       and ":attachable t" in _read(p).lower()]
            if len(generic) == 1:
                found.append((gen, "books/" + generic[0].stem, rel))
    return found


def scope(root: Path, world: World) -> list[str]:
    hosts: set[str] = set()
    for umbrella in UMBRELLAS:
        if (root / (umbrella + ".lisp")).exists():
            hosts.update(b for b in world.closure(umbrella) if b.startswith("host/"))
    return sorted(hosts)


def check(root: Path = ROOT) -> list[str]:
    world = World(root)
    findings = []
    for gen, generic, attach in pairs(root):
        for host in scope(root, world):
            if world.generic_state(host, generic, attach) == "bare":
                findings.append(
                    "%s.lisp: its closure reaches %s (%s) before %s attaches it; "
                    "include-book \"../%s\" first" % (host, generic, gen, attach, attach))
    return findings


def main() -> int:
    findings = check()
    for line in findings:
        print("attach_order_check: " + line)
    ps = pairs(ROOT)
    print("attach_order_check: %d attach pair(s) (%s), %d host file(s) in scope, %d finding(s)"
          % (len(ps), ", ".join(p[0] for p in ps), len(scope(ROOT, World(ROOT))), len(findings)))
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
