#!/usr/bin/env python3
"""Replace seven owner-kind positivity mistakes with bound-generation checks."""
from pathlib import Path
import lisp_rewrite as lr
TARGETS = {'commit.lisp': 1, 'checkpoint-allocation-coordinator.lisp': 2,
           'checkpoint-maintenance-staging.lisp': 1,
           'checkpoint-installation-coordinator.lisp': 1, 'retirement-coordinator.lisp': 2}
def rewrite(text, expected):
    parsed = lr.parse(text)
    hits = lr.match('(posp okind)', parsed.forms)
    if len(hits) != expected:
        raise ValueError(f'expected {expected} owner-kind checks, found {len(hits)}')
    return lr.write(text, [(h.start, h.end, '(posp ogen)') for h in hits])
if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    for name, expected in TARGETS.items():
        path = root / 'books' / name
        path.write_text(rewrite(path.read_text(), expected))
