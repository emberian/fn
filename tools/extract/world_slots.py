#!/usr/bin/env python3
"""Measure and file the TLS slot cost of each umbrella include (lane n-tls-chain).

tools/extract/world.py splits an umbrella into a chain of links so that no
certify process nears --tls-limit 65536; it needs a cost for each include
line without running ACL2.  That cost is a measured table,
tools/extract/world_slots.json, filed by this tool, not an estimate from the
sources: the raw stubs that take the slots are made by macros the sources do
not show (tools/tls_check.py counts 101 where 2215 live stubs exist).

  world_slots.py script UMBRELLA TSV   print an ACL2 session script (stdin of
                                       a LOAD-ONLY launcher, tls256k, over the
                                       certified tree) that includes UMBRELLA's
                                       include lines at top level, in order,
                                       and writes one row per include to TSV:
                                       depth<TAB>book<TAB>slots
  world_slots.py ingest TSV...         merge the depth-0 rows into the table
                                       (the larger value per book wins)

A slot is 8 units of sb-vm::*free-tls-index* (SBCL 2.6.8, 16-byte entries);
--tls-limit 65536 is 524288 units.  A top-level include-book reloads the
compiled file of its whole closure, so a book's cost is its closure's stubs,
paid again at each include: it is the number the include costs wherever it
stands once everything before it is loaded, which is the position it has in a
link (the link includes the previous link first).
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TABLE = ROOT / "tools" / "extract" / "world_slots.json"

HEAD = r""":q
(in-package "ACL2")
(defvar cl-user::*lg* (open "%(tsv)s" :direction :output :if-exists :supersede))
(defvar cl-user::*depth* 0)
(defun cl-user::slots () (/ sb-vm::*free-tls-index* 8))
(sb-int:encapsulate 'acl2::include-book-fn 'tlsmeter
  (lambda (f book &rest args)
    (let ((b (cl-user::slots)) (d cl-user::*depth*))
      (multiple-value-prog1
        (let ((cl-user::*depth* (1+ d))) (apply f book args))
        (format cl-user::*lg* "~a~a~a~a~a~%%" d #\Tab book #\Tab (float (- (cl-user::slots) b)))
        (finish-output cl-user::*lg*)))))
(format t "~&TLSBASE ~a~%%" (float (cl-user::slots)))
(lp)
(set-cbd "%(books)s/")
"""
TAIL = (':q\n(format t "~&TLSEND ~a~%%" (float (cl-user::slots)))\n(quit)\n')


def script(umbrella, tsv):
    books = ROOT / "books"
    lines = [l for l in (books / (umbrella + ".lisp")).read_text().splitlines()
             if l.startswith("(include-book ")]
    return HEAD % {"tsv": tsv, "books": books} + "\n".join(lines) + "\n" + TAIL % {}


def ingest(paths):
    table = json.loads(TABLE.read_text()) if TABLE.exists() else {}
    for path in paths:
        for line in Path(path).read_text().splitlines():
            depth, book, cost = line.split("\t")
            if depth != "0":
                continue
            value = int(float(re.sub(r"f0$", "", cost)))
            table[book] = max(table.get(book, 0), value)
    TABLE.write_text(json.dumps(dict(sorted(table.items())), indent=0, sort_keys=True) + "\n")
    return len(table)


if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) == 3 and args[0] == "script":
        sys.stdout.write(script(args[1], args[2]))
    elif len(args) >= 2 and args[0] == "ingest":
        print("world_slots.json: %d books" % ingest(args[1:]))
    else:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
