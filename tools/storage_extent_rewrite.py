#!/usr/bin/env python3
"""One source rewrite: separate physical extent stride from three-way packing.

Match Lisp expressions within named owners; never replace arbitrary threes.
The fixture keeps journal row arithmetic and block packing beside physical
addresses so a broader rewrite fails visibly. Re-running is a no-op.
"""
from pathlib import Path
import argparse
import lisp_rewrite as lr

STRIDE = "*fn2-storage-extent-units*"
PACK = "*fn2-upload-payload-units*"

# path, named function (None means exact expressions throughout this file),
# old expression, replacement template; captures preserve source spelling.
RULES = [
 ("books/commit-format.lisp", "fn2-commit-pack", "(* 3 extent)", f"(* {STRIDE} extent)"),
 ("books/commit.lisp", "fn2-commit-context", "(* 3 e)", f"(* {STRIDE} e)"),
 ("books/recovery.lisp", "fn2-rec-context", "(* 3 p)", f"(* {STRIDE} p)"),
 ("books/machines-b.lisp", "fn2-pinned-block-io-children", "(floor pu *fn2-commit-write-resources*)", f"(floor pu {STRIDE})"),
 ("books/recovery-payload.lisp", "fn2-recovery-claim-article", "*fn2-commit-write-resources*", STRIDE),
 ("books/recovery-payload.lisp", "fn2-rp-entries", "*fn2-commit-write-resources*", STRIDE),
 ("books/upload.lisp", "fn2-upload-manifest-extents", "*fn2-commit-write-resources*", STRIDE),
 ("books/txn.lisp", "fn2-txn-put-post-for", "(* *fn2-commit-write-resources* (nfix pext))", f"(* {STRIDE} (nfix pext))"),
 ("books/assembly-callbacks-d-upload.lisp", None, "(* *fn2-commit-write-resources* row-cext)", f"(* {STRIDE} row-cext)"),
 ("books/assembly-callbacks-d-upload.lisp", None, "(mod blk *fn2-commit-write-resources*)", f"(mod blk {PACK})"),
 ("books/article-manifest.lisp", "fn2-am-fits", "*fn2-commit-write-resources*", PACK),
 ("books/article-manifest.lisp", "fn2-am-manifestp", "*fn2-commit-extent-bytes*", "*fn2-upload-payload-bytes*"),
 ("books/upload-kind.lisp", None, "(* *fn2-am-block-bytes* *fn2-am-entries-per-unit* *fn2-commit-write-resources*)", f"(* *fn2-am-block-bytes* *fn2-am-entries-per-unit* {PACK})"),
 ("tests/read-pins-unit.lisp", "fn2-read-pin-test-body", "(* extent *fn2-commit-write-resources*)", f"(* extent {STRIDE})"),
 ("tests/storage-write-pins-unit.lisp", "fn2-write-pin-test-body", "(* extent *fn2-commit-write-resources*)", f"(* extent {STRIDE})"),
 ("tests/recovery-article-unit.lisp", None, "(* 3 (nth 0 ?x))", f"(* {STRIDE} (nth 0 {{x}}))"),
 ("sim/commit-history.lisp", "fn2-b-test-profile", "(floor (nfix sectors) 3)", f"(floor (nfix sectors) {STRIDE})"),
 ("books/owed-cursor.lisp", "fn2-cs-submit", "(<= hashed *fn2-commit-extent-bytes*)", "(<= hashed *fn2-upload-payload-bytes*)"),
 ("books/owed-cursor.lisp", "fn2-csp-seedsp", "(<= (len (fn2-cs-source (nth 3 s))) *fn2-commit-extent-bytes*)", "(<= (len (fn2-cs-source (nth 3 s))) *fn2-upload-payload-bytes*)"),
 ("tests/txn-unit.lisp", None, "(< *fn2-commit-extent-bytes* ?length)", "(< *fn2-upload-payload-bytes* {length})"),
 ("tests/recovery-article-unit.lisp", None, "(< *fn2-commit-extent-bytes* ?length)", "(< *fn2-upload-payload-bytes* {length})"),
 ("tests/recovery-article-unit.lisp", None, "(< ?length *fn2-commit-extent-bytes*)", "(< {length} *fn2-upload-payload-bytes*)"),
 ("tests/commit-turn-frame-unit.lisp", None, "(put-assoc-equal :sim-sectors 16 p)", f"(put-assoc-equal :sim-sectors (* 5 {STRIDE}) p)"),
 ("tests/commit-durable-all-unit.lisp", None, "(put-assoc-equal :sim-sectors 16 p)", f"(put-assoc-equal :sim-sectors (* 5 {STRIDE}) p)"),
 ("tests/stop-boundary-unit.lisp", None, "(put-assoc-equal :sim-sectors 16 p)", f"(put-assoc-equal :sim-sectors (* 5 {STRIDE}) p)"),
 ("tests/sim-layer-b.lisp", "fn2-b-case", "(if post (nth 2 post) 8)", f"(if post (nth 2 post) (* 2 {STRIDE}))"),
 ("tests/q1-contracts-b.lisp", "fn2-q1r-post", "(list (fn2-cm-profile :broad t t frontier 0 budget) faults 16)", f"(list (fn2-cm-profile :broad t t frontier 0 budget) faults (* 5 {STRIDE}))"),
]

def rewrite(text, owner, old, new):
    parsed = lr.parse(text)
    roots = parsed.forms if owner is None else [
        m.node for m in lr.match(None, parsed, head="defun", name=owner)
    ]
    edits = []
    for m in lr.match(old, roots):
        captures = {k: text[v.start:v.end] for k, v in m.captures.items()}
        edits.append((m.start, m.end, new.format(**captures)))
    return lr.write(text, edits), len(edits)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    pending = {}
    for path, owner, old, new in RULES:
        text = pending.get(path, (root / path).read_text())
        text, count = rewrite(text, owner, old, new)
        pending[path] = text
        print(f"{path}: {owner or 'exact forms'}: {count} expression(s)")
    if args.write:
        for path, text in pending.items():
            (root / path).write_text(text)

if __name__ == "__main__":
    main()
