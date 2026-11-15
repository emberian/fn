"""Extract the actual pre-crash RELEASE fixture without cloning its producer.

The fixture is the frozen f98412d19 source. Preserve all prefix bindings and
all four recovery assertions exactly; replace only their common call boundary.
"""
import argparse
import json
from pathlib import Path
from lisp_rewrite import parse, Lst, Atom, write

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tools/fixtures/release_producer_fixture.json"
SUPPORT = ROOT / "tests/recovery-release-producer-support.lisp"
UNIT = ROOT / "tests/recovery-release-connected-unit.lisp"


def extract(source):
    forms = parse(source).forms
    functions = [f for f in forms if isinstance(f, Lst) and len(f.items) > 1
                 and isinstance(f.items[0], Atom) and f.items[0].low == "defun"
                 and f.items[1].low == "fn2-rrc-body"]
    if len(functions) != 1:
        raise ValueError("require one actual fn2-rrc-body")
    fn = functions[0]
    body = fn.items[4]
    if not isinstance(body, Lst) or body.items[0].low != "b*":
        raise ValueError("require actual B* body")
    bindings = body.items[1]
    markers = [b for b in bindings.items if isinstance(b, Lst)
               and isinstance(b.items[0], Lst) and len(b.items[0].items) > 1
               and b.items[0].items[0].low == "mv"
               and b.items[0].items[1].low == "restarted"]
    if len(markers) != 1:
        raise ValueError("require exact physical restart boundary")
    first, last = bindings.start + 1, markers[0].start
    prefix = source[first:last]
    before = source[:fn.start]
    image_include = '(include-book "recovery-release-image-support")\n'
    if before.count(image_include) != 1:
        raise ValueError("require exact recovery-only image include")
    # The old recovery-only image include supplied the actual attachments
    # transitively. Preserve that runtime dependency explicitly for LIVE.
    support = before.replace(image_include, '(include-book "../books/assembly-attach")\n') + """; SAME producer prefix, ending before process death. No assertion is imported.
(defun fn2-rrc-producer (fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (""" + prefix + """)
  (mv (list :persisted target ep allocation prefix suffix batch event)
      fn2-core fn2-sim fn2-own)))
"""
    replacement = """((mv producer fn2-core fn2-sim fn2-own)
       (fn2-rrc-producer fn2-core fn2-sim fn2-own))
      ((unless (and (eq (car producer) :persisted) (= (len producer) 8)))
       (mv producer fn2-core fn2-sim fn2-own))
      (target (nth 1 producer)) (ep (nth 2 producer)) (allocation (nth 3 producer))
      (prefix (nth 4 producer)) (suffix (nth 5 producer))
      (batch (nth 6 producer)) (event (nth 7 producer))
      """
    rewritten = write(source, [(first, last, replacement)])
    unit = """; Full selected-recovery assertions retained from f98412d19.
; The actual pre-crash producer is shared with the narrower LIVE gate.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "recovery-release-producer-support")
(include-book "recovery-release-image-support")

""" + rewritten[fn.start:]
    return support, unit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    support, unit = extract(json.loads(FIXTURE.read_text())["source"])
    if args.check:
        if SUPPORT.read_text() != support or UNIT.read_text() != unit:
            raise SystemExit("producer extraction differs from frozen source recipe")
        print("Exact producer-prefix extraction and unchanged recovery suffix: PASS")
    else:
        SUPPORT.write_text(support)
        UNIT.write_text(unit)


if __name__ == "__main__":
    main()
