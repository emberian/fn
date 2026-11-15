#!/usr/bin/env python3
"""Move the actual descriptor target/hash loaders to one narrow provider.

The physical family owner applies remove_from_restore to its staged restore
book at composition. Runtime bodies/guards are spliced verbatim, never cloned.
"""
from pathlib import Path
import sys
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
NAMES = ('fn2-checkpoint-restore-read-target', 'fn2-checkpoint-restore-load-hash')


def unique(text, name):
    matches = lr.match('(defun '+name+' ?*body)', lr.parse(text).forms)
    assert len(matches) == 1, (name, len(matches))
    return matches[0].node


def provider(text):
    definitions = [text[(n := unique(text, name)).start:n.end] for name in NAMES]
    return '''; One canonical descriptor target and immutable digest loader.
; Extracted unchanged from checkpoint-restore; no allocator or serving authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint")
(include-book "columns-carrier-contracts")
(fn2-book-layer :b)

'''+ '\n\n'.join(definitions)+'''

(defcolumns-guarded-contracts fn2-checkpoint-restore-load-hash
 :carriers ((fn2-digests nil :prefix "-DIGESTS")) :rows t
 :hints ((fn2-columns-guard-hint
          '(fn2-checkpoint-bytes fn2-digests)
          '(fn2-digest-set-word) '(fn2-checkpoint-restore-load-hash) world)))
'''


def remove_from_restore(text):
    if '(include-book "checkpoint-descriptor-input")' in text:
        assert not any(lr.match('(defun '+n+' ?*body)', lr.parse(text).forms) for n in NAMES)
        return text
    nodes = [unique(text, name) for name in NAMES]
    anchor = text.index('(include-book "checkpoint")')+len('(include-book "checkpoint")')
    return lr.write(text, [(n.start, n.end, '') for n in nodes]+
                    [(anchor, anchor, '\n(include-book "checkpoint-descriptor-input")')])


if __name__ == '__main__':
    assert len(sys.argv) == 2, 'pass the actual staged checkpoint-restore source'
    source = Path(sys.argv[1]).read_text()
    (ROOT/'books/checkpoint-descriptor-input.lisp').write_text(provider(source))
