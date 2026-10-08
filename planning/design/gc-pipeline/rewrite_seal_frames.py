"""Add the pending-frames operand to the existing seal, not a second seal."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as rw


def extend(text):
    edits = []
    for name, arity in [('fn-ocp-gc-seal', 2), ('fn-ocp-gc-seal-held', 1),
                        ('fn-ocp-gc-entry-seal-held', 1)]:
        for hit in rw.match('_', rw.parse(text).forms, head=name, arity=arity):
            edits.append((hit.end - 1, hit.end - 1, ' frames'))
    return rw.write(text, edits)

assert extend('(fn-ocp-gc-seal x nextp)') == '(fn-ocp-gc-seal x nextp frames)'
assert extend('; (fn-ocp-gc-seal x nextp)\n(fn-ocp-gc-seal x nextp frames)') == '; (fn-ocp-gc-seal x nextp)\n(fn-ocp-gc-seal x nextp frames)'
if __name__ == '__main__':
    for file in ('owner-commit-durability', 'owner-commit-durability-concrete',
                 'owner-commit-held-durability'):
        p = ROOT / 'books' / (file + '.lisp')
        p.write_text(extend(p.read_text()))
