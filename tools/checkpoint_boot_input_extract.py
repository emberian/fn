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
ANCHOR_NAMES = ('fn2-checkpoint-restore-capture-ref', 'fn2-checkpoint-restore-anchor-step')


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


def anchor_provider(text):
    definitions = [text[(n := unique(text, name)).start:n.end] for name in ANCHOR_NAMES]
    return '''; The existing authenticated anchor intake, with no second parser.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-descriptor-input")
(fn2-book-layer :b)

'''+ '\n\n'.join(definitions)+'\n'


def remove_anchor_from_restore(text):
    if '(include-book "checkpoint-anchor-input")' in text:
        assert not any(lr.match('(defun '+n+' ?*body)', lr.parse(text).forms) for n in ANCHOR_NAMES)
        return text
    nodes = [unique(text, name) for name in ANCHOR_NAMES]
    anchor = text.index('(include-book "checkpoint")')+len('(include-book "checkpoint")')
    return lr.write(text, [(n.start, n.end, '') for n in nodes]+
                    [(anchor, anchor, '\n(include-book "checkpoint-anchor-input")')])


def remove_zero_from_restore_read(text):
    if '(include-book "checkpoint-zero-range")' in text:
        assert not lr.match('(defun fn2-checkpoint-restore-zero-range ?*body)', lr.parse(text).forms)
        return text
    node = unique(text, 'fn2-checkpoint-restore-zero-range')
    anchor = text.index('(include-book "event-proof-format")')+len('(include-book "event-proof-format")')
    return lr.write(text, [(node.start, node.end, ''),
                          (anchor, anchor, '\n(include-book "checkpoint-zero-range")')])


if __name__ == '__main__':
    assert len(sys.argv) == 2, 'pass the actual staged checkpoint-restore source'
    source = Path(sys.argv[1]).read_text()
    (ROOT/'books/checkpoint-descriptor-input.lisp').write_text(provider(source))
