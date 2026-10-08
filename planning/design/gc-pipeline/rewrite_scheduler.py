"""Lift the pipeline's scheduler component to the existing OTM value."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as rw


def lift(text):
    parsed = rw.parse(text)
    edits = []
    for hit in rw.match('(fn-ocs-phase (fn-ocp-ocs ?s))', parsed.forms):
        node = hit.node.items[1].items[1]
        edits.append((hit.start, hit.end, f'(fn-otm-phase-of {text[node.start:node.end]})'))
    text = rw.write(text, edits)
    parsed = rw.parse(text)
    edits = []
    for old, new in {'fn-ocp-open-next': 'fn-otm-next-of',
                     'fn-ocp-init': 'fn-otm-init',
                     'fn-ocp-commit-event': 'fn-otm-commit-event',
                     'fn-ocp-next': 'fn-otm-next'}.items():
        for hit in rw.match('_', parsed.forms, head=old):
            node = hit.node.items[0]
            edits.append((node.start, node.end, new))
    return rw.write(text, edits)


fixture = '; fn-ocp-init\n(and (fn-ocs-phase (fn-ocp-ocs (nth 1 x))) (fn-ocp-open-next s))'
assert lift(fixture) == '; fn-ocp-init\n(and (fn-otm-phase-of (nth 1 x)) (fn-otm-next-of s))'
assert lift(lift(fixture)) == lift(fixture)

if __name__ == '__main__':
    p = ROOT / 'books/owner-commit-durability.lisp'
    p.write_text(lift(p.read_text()))
