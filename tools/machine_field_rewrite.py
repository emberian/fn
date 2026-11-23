#!/usr/bin/env python3
"""Structural rewrite of private fn2-machine-<F> / fn2-machine-write-<F> sites.

Built on tools/lisp_rewrite.py (parse, match, emit, write).
Coalesces consecutive same-row fn2-machine-write-<F> bindings in let*/b* into
chunked (<= 6 columns per call) <kind>-put-core forms so neither stobj-let
branching (2^K) nor ACL2 preprocess remove-lambdas (3^C) blows up.
"""
from __future__ import annotations

import argparse
import difflib
import glob
import sys
import unittest
from collections import defaultdict
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS_DIR))

import lisp_rewrite as lr  # noqa: E402

MAX_PUT_COLS = 6

UNIVERSAL_OR_SHARED_KEEP = {
    "phase",
    "stopped",
    "pending",
    "next-free",
    "pool-slot",
    "pool-gen",
    "outcome",
    "borrows",
    "cap-index",
    "cap-nonce",
    "cursor",
    "event-ready",
    "mode",
}


def discover_machine_fields(books_dir: Path) -> dict[str, list[str]]:
    field_kinds: dict[str, list[str]] = defaultdict(list)
    for path in sorted(glob.glob(str(books_dir / "*.lisp"))):
        p = lr.parse(path)
        for m in lr.match("(defmachine ?kind ?*rest)", p, head="defmachine"):
            if not lr._sym(m.captures["kind"]):
                continue
            kind = m.captures["kind"].low
            rest = m.captures["rest"]
            for i in range(len(rest) - 1):
                if (isinstance(rest[i], lr.Atom) and rest[i].low == ":fields"
                        and isinstance(rest[i + 1], lr.Lst)):
                    for col in rest[i + 1].items:
                        if isinstance(col, lr.Lst) and col.items and lr._sym(col.items[0]):
                            field_kinds[col.items[0].low].append(kind)
    return dict(field_kinds)


def discover_cda_hint_commit_fns(books_dir: Path) -> set[str]:
    cda = books_dir / "commit-durable-all.lisp"
    commit = books_dir / "commit.lisp"
    if not cda.exists() or not commit.exists():
        return set()
    p_commit = lr.parse(commit)
    commit_fns = {
        m.captures["fn"].low
        for m in lr.match("(defun ?fn ?*rest)", p_commit, head="defun")
        if lr._sym(m.captures["fn"])
    }
    p_cda = lr.parse(cda)
    opened: set[str] = set()
    for top in p_cda.forms:
        for n in lr._walk(top):
            if isinstance(n, lr.Lst):
                for i in range(len(n.items) - 1):
                    if lr._sym(n.items[i]) and n.items[i].low == ":hints":
                        for sub in lr._walk(n.items[i + 1]):
                            if lr._sym(sub) and sub.low in commit_fns:
                                opened.add(sub.low)
    return opened


def resolve_write_kind(field: str, row_node: object, rel_path: str,
                       field_kinds: dict[str, list[str]]) -> str | None:
    if field in UNIVERSAL_OR_SHARED_KEEP:
        return None
    ks = field_kinds.get(field, [])
    if len(ks) == 1:
        return ks[0]
    row_txt = lr.flat(row_node).lower()
    if field == "tx-off" and row_txt == "ctl":
        return "fn2-ctl"
    if field == "seen" and "upload" in rel_path:
        return "fn2-upload"
    if field == "word" and "upload" in rel_path:
        if row_txt == "conn":
            return "fn2-conn"
        if row_txt == "id":
            return "fn2-upload"
    if field == "feed-discard" and row_txt == "owner" and "upload" in rel_path:
        return "*conn-or-cns*"
    return None


def _is_core_write_call(node: object) -> tuple[str, object, object] | None:
    """If NODE is (fn2-machine-write-<F> ROW VAL fn2-core), return (F, ROW, VAL)."""
    if not (isinstance(node, lr.Lst) and len(node.items) == 4 and lr._sym(node.items[0])):
        return None
    h = node.items[0].low
    if not h.startswith("fn2-machine-write-"):
        return None
    if not (lr._sym(node.items[3]) and node.items[3].low == "fn2-core"):
        return None
    return h[len("fn2-machine-write-"):], node.items[1], node.items[2]


def _is_core_binding(b: object) -> tuple[str, object, object] | None:
    """If B is (fn2-core (fn2-machine-write-<F> ROW VAL fn2-core)), return (F, ROW, VAL)."""
    if not (isinstance(b, lr.Lst) and len(b.items) == 2
            and lr._sym(b.items[0]) and b.items[0].low == "fn2-core"):
        return None
    return _is_core_write_call(b.items[1])


def _format_put_core(kind: str, row_src: str, pairs: list[tuple[str, str]]) -> str:
    args = " ".join(f"({f} {v})" for f, v in pairs)
    return f"({kind}-put-core {row_src} {args})"


def _indent_of(text: str, pos: int) -> int:
    nl = text.rfind("\n", 0, pos)
    return pos if nl < 0 else (pos - nl - 1)


def rewrite_parsed(p: lr.Parsed, rel_path: str,
                   field_kinds: dict[str, list[str]],
                   skip_defuns: set[str] | None = None,
                   rewrite_commit_reads: bool = False) -> list[tuple[int, int, str]]:
    skip_defuns = skip_defuns or set()
    edits: list[tuple[int, int, str]] = []
    covered: list[tuple[int, int]] = []

    def is_covered(s: int, e: int) -> bool:
        return any(cs <= s and e <= ce for cs, ce in covered)

    def walk_form(node: object, in_skipped_defun: bool = False):
        if isinstance(node, lr.Lst):
            if node.items and lr._sym(node.items[0]):
                head = node.items[0].low
                if head == "defun" and len(node.items) > 1 and lr._sym(node.items[1]):
                    if node.items[1].low in skip_defuns:
                        in_skipped_defun = True

                # Check sequential binding lists in let* and b*
                if head in ("let*", "b*") and len(node.items) >= 3 and isinstance(node.items[1], lr.Lst):
                    blist = node.items[1].items
                    idx = 0
                    while idx < len(blist):
                        cw = _is_core_binding(blist[idx])
                        if cw is not None:
                            f0, r0, v0 = cw
                            k0 = resolve_write_kind(f0, r0, rel_path, field_kinds)
                            if k0 == "*conn-or-cns*":
                                row_s = p.text[r0.start:r0.end]
                                val_s = p.text[v0.start:v0.end]
                                rep = (f"(fn2-core (if (eq (fn2-conn-snapshot-read-code {row_s} fn2-core) :ok) "
                                       f"(fn2-conn-put-core {row_s} ({f0} {val_s})) "
                                       f"(fn2-cns-put-core {row_s} ({f0} {val_s}))))")
                                bnode = blist[idx]
                                edits.append((bnode.start, bnode.end, rep))
                                covered.append((bnode.start, bnode.end))
                                idx += 1
                                continue
                            if k0 is not None:
                                run = [(f0, r0, v0, blist[idx])]
                                j = idx + 1
                                while j < len(blist):
                                    cwj = _is_core_binding(blist[j])
                                    if cwj is None:
                                        break
                                    fj, rj, vj = cwj
                                    if not lr._same(r0, rj):
                                        break
                                    if fj == "phase":
                                        run.append((fj, rj, vj, blist[j]))
                                        j += 1
                                        break
                                    kj = resolve_write_kind(fj, rj, rel_path, field_kinds)
                                    if kj != k0:
                                        break
                                    run.append((fj, rj, vj, blist[j]))
                                    j += 1
                                start_pos = run[0][3].start
                                end_pos = run[-1][3].end
                                indent = _indent_of(p.text, start_pos)
                                row_s = p.text[r0.start:r0.end]
                                pairs = [(f, p.text[v.start:v.end]) for f, _, v, _ in run]
                                chunks = [
                                    pairs[c:c + MAX_PUT_COLS]
                                    for c in range(0, len(pairs), MAX_PUT_COLS)
                                ]
                                rendered = [
                                    f"(fn2-core {_format_put_core(k0, row_s, ch)})"
                                    for ch in chunks
                                ]
                                sep = "\n" + (" " * indent)
                                edits.append((start_pos, end_pos, sep.join(rendered)))
                                covered.append((start_pos, end_pos))
                                idx = j
                                continue
                        idx += 1

                # Standalone (fn2-machine-write-<F> row val fn2-core)
                if not is_covered(node.start, node.end):
                    cw = _is_core_write_call(node)
                    if cw is not None:
                        f0, r0, v0 = cw
                        k0 = resolve_write_kind(f0, r0, rel_path, field_kinds)
                        if k0 and k0 != "*conn-or-cns*":
                            row_s = p.text[r0.start:r0.end]
                            val_s = p.text[v0.start:v0.end]
                            edits.append((node.start, node.end, _format_put_core(k0, row_s, [(f0, val_s)])))
                            covered.append((node.start, node.end))
                            return

                # Private commit row read: (fn2-machine-<F> id core) -> (fn2-commit-row-<F> id core)
                if (rewrite_commit_reads and not in_skipped_defun
                        and not is_covered(node.start, node.end)
                        and len(node.items) == 3
                        and node.items[0].low.startswith("fn2-machine-")):
                    fname = node.items[0].low[len("fn2-machine-"):]
                    ks = field_kinds.get(fname, [])
                    if len(ks) == 1 and ks[0] == "fn2-commit":
                        hnode = node.items[0]
                        edits.append((hnode.start, hnode.end, f"fn2-commit-row-{fname}"))
                        covered.append((hnode.start, hnode.end))

            for item in node.items:
                walk_form(item, in_skipped_defun)
        elif isinstance(node, lr.Pre):
            walk_form(node.node, in_skipped_defun)

    for top in p.forms:
        walk_form(top, False)
    return edits


class RewriteTests(unittest.TestCase):
    def setUp(self):
        self.fields = {
            "ototal": ["fn2-ctl"],
            "oleft": ["fn2-ctl"],
            "ochecked": ["fn2-ctl"],
            "ophase": ["fn2-ctl"],
            "tx-off": ["fn2-ctl", "fn2-conn"],
            "tx-len": ["fn2-ctl"],
            "word": ["fn2-conn", "fn2-txn", "fn2-upload"],
            "inj": ["fn2-upload"],
            "feed-discard": ["fn2-cns", "fn2-conn"],
            "batch-no": ["fn2-commit"],
            "member-count": ["fn2-commit"],
        }
        for i in range(13):
            self.fields[f"ucol{i}"] = ["fn2-upload"]

    def test_coalesce_with_trailing_phase(self):
        src = (
            "(let* ((fn2-core (fn2-machine-write-ototal ctl len fn2-core))\n"
            "       (fn2-core (fn2-machine-write-oleft ctl len fn2-core))\n"
            "       (fn2-core (fn2-machine-write-phase ctl *s* fn2-core))\n"
            "       (fn2-core (fn2-core-scheduler-wake ctl fn2-core)))\n"
            "  fn2-core)\n"
        )
        p = lr.parse(src)
        edits = rewrite_parsed(p, "books/ctl-output-events.lisp", self.fields)
        out = lr.write(p.text, edits)
        self.assertIn("(fn2-ctl-put-core ctl (ototal len) (oleft len) (phase *s*))", out)
        self.assertIn("(fn2-core-scheduler-wake ctl fn2-core)", out)

    def test_chunk_13_writes_into_at_most_6(self):
        lines = ["(b* ((fn2-core (fn2-machine-write-ucol0 id v0 fn2-core))"]
        for i in range(1, 13):
            lines.append(f"     (fn2-core (fn2-machine-write-ucol{i} id v{i} fn2-core))")
        lines[-1] += ")\n  fn2-core)\n"
        src = "\n".join(lines)
        p = lr.parse(src)
        edits = rewrite_parsed(p, "books/upload.lisp", self.fields)
        out = lr.write(p.text, edits)
        p2 = lr.parse(out)
        puts = lr.match("(fn2-upload-put-core id ?*cols)", p2)
        self.assertEqual(len(puts), 3)
        self.assertEqual([len(m.captures["cols"]) for m in puts], [6, 6, 1])

    def test_owner_feed_discard_split(self):
        src = "(b* ((fn2-core (fn2-machine-write-feed-discard owner 4 fn2-core))) (mv :ok fn2-core))\n"
        p = lr.parse(src)
        edits = rewrite_parsed(p, "books/upload.lisp", self.fields)
        out = lr.write(p.text, edits)
        self.assertIn("fn2-conn-snapshot-read-code owner fn2-core", out)
        self.assertIn("(fn2-conn-put-core owner (feed-discard 4))", out)
        self.assertIn("(fn2-cns-put-core owner (feed-discard 4))", out)

    def test_nested_bstar_unless_and_if_writes(self):
        src = (
            "(b* (((unless ok)\n"
            "      (let* ((fn2-core (fn2-machine-write-word id w fn2-core))\n"
            "             (fn2-core (fn2-machine-write-inj id j fn2-core)))\n"
            "        fn2-core))\n"
            "     (fn2-core (if flag (fn2-machine-write-inj id 1 fn2-core) fn2-core)))\n"
            "  fn2-core)\n"
        )
        p = lr.parse(src)
        edits = rewrite_parsed(p, "books/upload.lisp", self.fields)
        out = lr.write(p.text, edits)
        self.assertIn("(fn2-upload-put-core id (word w) (inj j))", out)
        self.assertIn("(if flag (fn2-upload-put-core id (inj 1)) fn2-core)", out)

    def test_commit_read_respects_skipped_defuns(self):
        src = (
            "(defun keep-me (id fn2-core) (fn2-machine-batch-no id fn2-core))\n"
            "(defun port-me (id fn2-core) (fn2-machine-batch-no id fn2-core))\n"
        )
        p = lr.parse(src)
        edits = rewrite_parsed(p, "books/commit.lisp", self.fields,
                               skip_defuns={"keep-me"}, rewrite_commit_reads=True)
        out = lr.write(p.text, edits)
        self.assertIn("(defun keep-me (id fn2-core) (fn2-machine-batch-no id fn2-core))", out)
        self.assertIn("(defun port-me (id fn2-core) (fn2-commit-row-batch-no id fn2-core))", out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(Path(__file__).resolve().parents[1]))
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--diff", action="store_true")
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(RewriteTests)
        res = unittest.TextTestRunner(verbosity=2).run(suite)
        sys.exit(0 if res.wasSuccessful() else 1)

    root = Path(args.root)
    books_dir = root / "books"
    field_kinds = discover_machine_fields(books_dir)
    cda_fns = discover_cda_hint_commit_fns(books_dir)

    write_targets = [
        "books/assembly-callbacks-d.lisp",
        "books/authority.lisp",
        "books/cns.lisp",
        "books/ctl-output-events.lisp",
        "books/ctl-stream-events.lisp",
        "books/txn.lisp",
        "books/upload-stream-reset.lisp",
        "books/upload-stream-settle.lisp",
        "books/upload-stream-stage.lisp",
        "books/upload-stream.lisp",
        "books/upload.lisp",
        "books/commit.lisp",
        "books/commit-arms.lisp",
        "books/retirement-coordinator.lisp",
    ]
    commit_read_targets = {
        "books/txn.lisp",
        "books/commit.lisp",
        "books/commit-arms.lisp",
        "books/retirement-coordinator.lisp",
    }

    total_edits = 0
    for rel in write_targets:
        path = root / rel
        p = lr.parse(path)
        edits = rewrite_parsed(
            p,
            rel,
            field_kinds,
            skip_defuns=(cda_fns if rel == "books/commit.lisp" else set()),
            rewrite_commit_reads=(rel in commit_read_targets),
        )
        if not edits:
            continue
        total_edits += len(edits)
        new_text = lr.write(p.text, edits)
        lr.parse(new_text)
        if args.diff:
            diff = difflib.unified_diff(
                p.text.splitlines(True),
                new_text.splitlines(True),
                fromfile=f"a/{rel}",
                tofile=f"b/{rel}",
                n=2,
            )
            sys.stdout.writelines(diff)
        if args.apply:
            path.write_bytes(new_text.encode("utf-8", "surrogateescape"))
            print(f"Applied {len(edits)} structural edits to {rel}")
    print(f"Total structural edits: {total_edits}")


if __name__ == "__main__":
    main()
