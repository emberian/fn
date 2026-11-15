#!/usr/bin/env python3
"""Project the actual shared bound-reader cursor fields onto an existing ROOT book.

Preserve every ROOT definition/API except appending the required columns and
clearing those new columns in its existing resident start. Copy the exact
hash accessor from the frozen real implementation; do not copy installed or
query paths. This is a source transformation, not an ACL2 admission tool.
"""
from pathlib import Path
import argparse
import lisp_rewrite as lr

REQUIRED = ('physical', 'source-row', 'catalog-tag', 'epoch', 'run', 'resume-child') + tuple(f'hash-{i}' for i in range(8))
HASH = 'fn2-run-cursor-hash-word'


def one(text, pattern):
    nodes = lr.match(pattern, lr.parse(text).forms, deep=False)
    if len(nodes) != 1:
        raise ValueError(f'expected one {pattern}: found {len(nodes)}')
    return nodes[0].node


def field_name(node):
    return node.items[0].low


def project(root, frozen):
    old = one(root, '(defcolumns fn2-run-cursors ?*args)')
    source = one(frozen, '(defcolumns fn2-run-cursors ?*args)')
    present = {field_name(n) for n in old.items[2].items}
    if present.intersection(REQUIRED):
        raise ValueError('ROOT already contains projected fields; do not duplicate or replace it')
    real = {field_name(n): n for n in source.items[2].items}
    if any(name not in real for name in REQUIRED):
        raise ValueError('frozen implementation lacks required actual cursor field')
    added = '\n  ' + ' '.join(frozen[real[name].start:real[name].end] for name in REQUIRED)
    edits = [(old.items[2].end - 1, old.items[2].end - 1, added)]
    start = one(root, '(defun fn2-run-cursor-start ?*args)')
    puts = lr.match('(fn2-run-cursors-put c ?*fields)', [start])
    if len(puts) != 1:
        raise ValueError('ROOT resident start does not have one actual cursor write')
    reset = ' '.join(f'({name} {"*fn2-none*" if name == "source-row" else "0"})' for name in REQUIRED)
    edits.append((puts[0].end - 1, puts[0].end - 1, '\n                               ' + reset))
    if lr.match(f'(defun {HASH} ?*args)', lr.parse(root).forms, deep=False):
        raise ValueError('ROOT already defines the actual hash accessor')
    accessor = one(frozen, f'(defun {HASH} ?*args)')
    anchor = one(root, '(fn2-run-cursors-preserves fn2-run-cursor-save ?*args)')
    edits.append((anchor.end, anchor.end, '\n\n; Exact shared bound-reader digest accessor; no installed/query path is added.\n'
                  + frozen[accessor.start:accessor.end]))
    return lr.write(root, edits)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('frozen', type=Path)
    args = parser.parse_args()
    args.root.write_text(project(args.root.read_text(), args.frozen.read_text()))


if __name__ == '__main__':
    main()
