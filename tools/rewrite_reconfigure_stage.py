#!/usr/bin/env python3
"""Move a live reconfiguration's staging entry out of its (fnn-rc-begin ...) call.

Ruling 19 (host/native/admin.lisp fnn-owner-live-reconfigure): the macro takes
the staging entry as its :stage clause, a form the raw-host dispatch reader
sees as a literal dispatch.  This rewrites each

    (fnn-owner-live-reconfigure (...) (W R) ... :before ...
        (fnn-rc-begin RUN RESERVE 'ENTRY ARG...) ...)

to (fnn-rc-begin RUN RESERVE) and inserts, before :before,

    :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'ENTRY pcid ARG...))

A form already written with a :stage clause is left alone (idempotent).

    python3 tools/rewrite_reconfigure_stage.py FILE...      # rewrite in place
    python3 tools/rewrite_reconfigure_stage.py --check FILE...
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lisp_rewrite as lr


def _is(node, name):
    return isinstance(node, lr.Atom) and node.low == name


def rewrite(text):
    parsed = lr.parse(text)
    edits = []
    for m in lr.match("(fnn-owner-live-reconfigure ?*xs)", parsed):
        items = m.node.items
        if any(_is(x, ":stage") for x in items):
            continue
        begins = lr.match("(fnn-rc-begin ?*ys)", [m.node])
        if len(begins) != 1:
            raise SystemExit(f"{len(begins)} fnn-rc-begin calls in the form at offset {m.start}")
        b = begins[0].node.items
        if len(b) < 4 or not (isinstance(b[3], lr.Pre) and text[b[3].start:b[3].start + 1] == "'"):
            raise SystemExit(f"fnn-rc-begin at offset {begins[0].start} does not name a quoted entry")
        entry = text[b[3].start:b[3].end]
        args = " ".join(text[a.start:a.end] for a in b[4:])
        before = [x for x in items if _is(x, ":before")]
        if len(before) != 1:
            raise SystemExit(f"form at offset {m.start} has no single :before")
        new_begin = "(fnn-rc-begin " + text[b[1].start:b[1].end] + " " + text[b[2].start:b[2].end] + ")"
        lam = ("(lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p " + entry + " pcid"
               + (" " + args if args else "") + "))")
        edits.append((begins[0].start, begins[0].end, new_begin))
        col = text.rfind("\n", 0, before[0].start)
        indent = " " * (before[0].start - col - 1)
        edits.append((before[0].start, before[0].start, ":stage " + lam + "\n" + indent))
    return lr.write(text, edits)


def main(argv):
    check = "--check" in argv
    status = 0
    for name in [a for a in argv if not a.startswith("--")]:
        p = Path(name)
        old = p.read_text(encoding="utf-8", errors="surrogateescape")
        new = rewrite(old)
        if new != old:
            status = 1
            if not check:
                p.write_text(new, encoding="utf-8", errors="surrogateescape")
            print(f"{name}: {'would rewrite' if check else 'rewrote'}")
    return status if check else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
