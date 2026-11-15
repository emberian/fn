"""Exact reversible three-site PAYLOAD group change; journal grouping is separate."""
import argparse
from pathlib import Path
import lisp_rewrite as lr


def transform(source, reverse=False):
    old = '*fn2-storage-extent-units*' if reverse else '*fn2-commit-write-resources*'
    new = '*fn2-commit-write-resources*' if reverse else '*fn2-storage-extent-units*'
    matches = lr.match(f'(mod blk {old})', lr.parse(source).forms)
    if len(matches) != 3:
        raise ValueError(f'expected three exact payload sites, got {len(matches)}')
    return lr.write(source, [(m.start, m.end, source[m.start:m.end].replace(old, new)) for m in matches])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', type=Path)
    parser.add_argument('--reverse', action='store_true')
    args = parser.parse_args()
    args.path.write_text(transform(args.path.read_text(), args.reverse))
