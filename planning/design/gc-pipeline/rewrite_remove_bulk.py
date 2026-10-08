"""Retire the draft bulk algorithm; generate explicit ground-test events."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as rw


def remove_forms(text, names):
    edits = []
    for form in rw.parse(text).forms:
        node = form
        if isinstance(node, rw.Lst) and node.items[0].low == 'local':
            node = node.items[1]
        if not isinstance(node, rw.Lst) or len(node.items) < 2:
            continue
        if getattr(node.items[1], 'low', '') in names:
            edits.append((form.start, form.end, ''))
    return rw.write(text, edits)


def remove_atoms(text, names):
    edits = []
    def walk(node):
        if isinstance(node, rw.Lst):
            for item in node.items:
                walk(item)
        elif isinstance(node, rw.Atom) and node.low in names:
            edits.append((node.start, node.end, ''))
    for node in rw.parse(text).forms:
        walk(node)
    return rw.write(text, edits)


fixture = '; old remains in comment\n(local (defthm old t))\n(defun kept (x) x)\n'
assert remove_forms(fixture, {'old'}) == '; old remains in comment\n\n(defun kept (x) x)\n'
assert remove_atoms('(disable old kept)', {'old'}) == '(disable  kept)'


def expand_tests(text):
    parsed = rw.parse(text)
    edits = []
    for tag, which in ((':start', ':current'), (':next', ':next')):
        for hit in rw.match('_', parsed.forms, head=tag, arity=2):
            records, outcomes = hit.node.items[1:]
            if not isinstance(records, rw.Lst) or not isinstance(outcomes, rw.Lst):
                raise ValueError('ground bulk event expected')
            events = [f'({tag})']
            for record in records.items:
                # Fixture identities: A/B/C are transactions 1/2/3; the
                # probes deliberately use later identities, not a host allocator.
                txid = int(record.items[0].text) - 64
                raw = text[record.start:record.end]
                events += [f'(:reserve {which} {txid})', f'(:take {which} {raw} {txid})']
            events += [f'(:member {which} {text[o.start:o.end]})' for o in outcomes.items]
            events.append(f'(:seal {which})')
            edits.append((hit.start, hit.end, ' '.join(events)))
    return rw.write(text, edits)


assert expand_tests("'((:start ((65)) ((:accepted t))))") == (
    "'((:start) (:reserve :current 1) (:take :current (65) 1) "
    "(:member :current (:accepted t)) (:seal :current))")


if __name__ == '__main__':
    names = {'fn-ocp-gc-start', 'fn-ocp-gc-start-preserves-linkedp', 'fn-ocp-gc-start-project'}
    for name in ('books/owner-commit-durability.lisp', 'books/owner-commit-durability-concrete.lisp'):
        p = ROOT / name
        p.write_text(remove_atoms(remove_forms(p.read_text(), names), names))
    for name in ('tests/acl2/gc-pipeline-tests.lisp', 'tests/acl2/gc-pipeline-drain-tests.lisp'):
        p = ROOT / name
        p.write_text(expand_tests(p.read_text()))
