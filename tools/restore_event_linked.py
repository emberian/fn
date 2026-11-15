"""Replace only linked-reader metadata selection with its shared role schema.

The real role2/5 branches retain their exact metadata; role3 adds the actual
retained-event format. Bodies, codecs and unrelated selectors stay untouched.
"""
from pathlib import Path
import argparse
import lisp_rewrite as lr

PATTERNS = (
    ('(if (equal role 2) *fn2-checkpoint-map-slots* *fn2-checkpoint-arena-slots*)', 'slots'),
    ('(if (equal role 2) *fn2-checkpoint-map-entry-width* *fn2-checkpoint-arena-entry-width*)', 'width'),
    ('(if (equal role 2) *page-kind-allocation-map* *page-kind-recovery-arena*)', 'pagekind'),
    ('(if (equal role 2) *checkpoint-map-body-kind-allocation-map* *checkpoint-map-body-kind-recovery-arena*)', 'bodykind'),
    ('(if (equal role 2) *fn2-format-allocation-map-entry-num-fields* *fn2-format-recovery-arena-entry-num-fields*)', 'nfields'),
)
OWNERS = {'fn2-checkpoint-restore-header', 'fn2-checkpoint-restore-entry',
          'fn2-checkpoint-restore-reader-begin', 'fn2-checkpoint-restore-reader-page-step'}


def rewrite(text):
    edits = []
    for found in lr.match('(defun ?name ?args ?*body)', lr.parse(text).forms, deep=False):
        if getattr(found.captures['name'], 'low', '') not in OWNERS:
            continue
        for pattern, value in PATTERNS:
            for match in lr.match(pattern, found.captures['body'], deep=True):
                # Match source offsets come from the parsed concrete node.
                node = match.node
                edits.append((node.start, node.end, value))
    return lr.write(text, edits), len(edits)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    for name in ('checkpoint-restore-read', 'checkpoint-restore-reader'):
        path = root / f'books/{name}.lisp'
        result, count = rewrite(path.read_text())
        print(f'{name}: {count} linked metadata selectors')
        if args.write:
            path.write_text(result)
