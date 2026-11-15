#!/usr/bin/env python3
"""Split the real sealer INSTALL once from retryable owner cleanup.

Six fixed original forms are required. All edits use Lisp AST spans; the
script refuses a changed starting body rather than rebasing its fixture.
"""

import json
from pathlib import Path
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT / 'books/sealer.lisp'
BEFORE = json.loads((ROOT / 'tools/fixtures/seal-cleanup-phase-before.json').read_text())

OVERLAY = '''
; INSTALL publishes the run once. Cleanup has its own phase, so a held arena
; leaves the published run and its exact owner handles available for retry.
(defun fn2-seal-overlay-return (fn2-seals fn2-overlays fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-overlays fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-overlays-wfp fn2-overlays)
              (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-seal-retire fn2-seals-rows
                                            fn2-overlays-rows)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals)))
       (mv :bounds fn2-seals fn2-overlays fn2-pool))
      ((unless (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-overlay-return*))
       (mv :state fn2-seals fn2-overlays fn2-pool))
      (o (fn2-seals-o 0 fn2-seals))
      (rows (fn2-overlays-rows fn2-overlays))
      ((unless (and (natp o) (<= o rows)))
       (mv :bounds fn2-seals fn2-overlays fn2-pool))
      ((mv code fn2-overlays fn2-pool)
       (if (< o rows) (fn2-seal-retire o fn2-overlays fn2-pool)
         (mv :ok fn2-overlays fn2-pool)))
      ((unless (or (eq code :ok) (eq code :retired)))
       (mv code fn2-seals fn2-overlays fn2-pool))
      (fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-hash-return* fn2-seals)))
  (mv :more fn2-seals fn2-overlays fn2-pool)))
(fn2-seal-shape fn2-seal-overlay-return (fn2-seals fn2-overlays fn2-pool)
 (fn2-seals fn2-overlays fn2-pool) (fn2-seals fn2-overlays fn2-pool) t
 (fn2-seal-retire fn2-seals-set-phase fn2-seals-phase fn2-seals-o
  fn2-seals-rows fn2-overlays-rows))

(defun fn2-seal-hash-return (fn2-seals fn2-pool)
 (declare (xargs :stobjs (fn2-seals fn2-pool)
  :guard (and (fn2-seals-wfp fn2-seals) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-pool-release
                    fn2-pool-release-countp fn2-seals-rows fn2-seals-hslot
                    fn2-seals-hgen fn2-seals-okind fn2-seals-oslot fn2-seals-ogen)))))
 (b* (((unless (< 0 (fn2-seals-rows fn2-seals)))
       (mv :bounds fn2-seals fn2-pool))
      ((unless (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-hash-return*))
       (mv :state fn2-seals fn2-pool))
      (hslot (fn2-seals-hslot 0 fn2-seals))
      ((unless (fn2-pool-release-countp hslot fn2-pool))
       (mv :bounds fn2-seals fn2-pool))
      ((mv code fn2-pool)
       (fn2-pool-release hslot (fn2-seals-hgen 0 fn2-seals)
        (fn2-seals-okind 0 fn2-seals) (fn2-seals-oslot 0 fn2-seals)
        (fn2-seals-ogen 0 fn2-seals) fn2-pool))
      ((unless (or (eq code :ok) (eq code :retired)))
       (mv code fn2-seals fn2-pool))
      (k (fn2-seals-k 0 fn2-seals))
      (fn2-seals (fn2-seals-put 0
       (phase (if (zp k) *fn2-seal-phase-idle* *fn2-seal-phase-release*))
       (sub *fn2-seal-sub-open*) (filter 0) (k 0) (held 0))))
  (mv :done fn2-seals fn2-pool)))
(fn2-seal-shape fn2-seal-hash-return (fn2-seals fn2-pool)
 (fn2-seals fn2-pool) (fn2-seals fn2-pool) t
 (fn2-pool-release fn2-pool-release-countp fn2-seals-phase fn2-seals-hslot
  fn2-seals-hgen fn2-seals-okind fn2-seals-oslot fn2-seals-ogen fn2-seals-k))
'''

DISPATCH = '''((equal phase *fn2-seal-phase-overlay-return*)
    (mv-let (code fn2-seals fn2-overlays fn2-pool)
      (fn2-seal-overlay-return fn2-seals fn2-overlays fn2-pool)
     (fn2-seal-mv code)))
   ((equal phase *fn2-seal-phase-hash-return*)
    (mv-let (code fn2-seals fn2-pool)
      (fn2-seal-hash-return fn2-seals fn2-pool)
     (fn2-seal-mv code)))
   '''


def one(pattern, source):
    found = lr.match(pattern, lr.parse(source).forms, deep=False)
    if len(found) != 1:
        raise ValueError(f'expected one {pattern}')
    return found[0].node


def target(pattern, original):
    node = one(pattern, original)
    edits = []
    if pattern.startswith('(defcolumns'):
        enum = lr.match('(:enum fn2-seal-phase ?*values)', [node])
        if len(enum) != 1:
            raise ValueError('seal phase enum changed')
        edits.append((enum[0].start, enum[0].end,
                      '(:enum fn2-seal-phase (:idle :build :filter :install '
                      ':overlay-return :hash-return :failed :release))'))
    elif 'pending-p' in pattern:
        install = lr.match('(equal phase *fn2-seal-phase-install*)', [node])
        if len(install) != 1:
            raise ValueError('pending install case changed')
        edits.append((install[0].end, install[0].end,
                      '\n           (equal phase *fn2-seal-phase-overlay-return*)'
                      '\n           (equal phase *fn2-seal-phase-hash-return*)'))
    elif pattern.startswith('(defun fn2-seal-install '):
        body = node.items[-1]
        bindings = body.items[1].items
        if len(bindings) != 22 or not lr.match(
                '(fn2-seal-install-run fn2-seals fn2-run-installed)', [bindings[14]]):
            raise ValueError('install-once boundary changed')
        if not lr.match('(fn2-seal-retire o fn2-overlays fn2-pool)', [bindings[16]]):
            raise ValueError('overlay cleanup boundary changed')
        guard = '''((unless (equal (fn2-seals-phase 0 fn2-seals) *fn2-seal-phase-install*))
       (mv :state fn2-seals fn2-overlays fn2-run-installed fn2-pool))'''
        edits.append((bindings[0].end, bindings[0].end, '\n      ' + guard))
        edits.append((bindings[16].start, bindings[-1].end,
                      '(fn2-seals (fn2-seals-set-phase 0 '
                      '*fn2-seal-phase-overlay-return* fn2-seals))'))
        result = body.items[2]
        code = lr.match(':done', [result])
        if len(code) != 1:
            raise ValueError('install result changed')
        edits.append((code[0].start, code[0].end, ':more'))
    elif pattern.startswith('(fn2-seal-shape fn2-seal-install '):
        reads = node.items[-1]
        names = [x.low for x in reads.items]
        for old in ('fn2-seal-retire', 'fn2-pool-release'):
            if names.count(old) != 1:
                raise ValueError('install shape cleanup call changed')
        names = [x for x in names if x not in ('fn2-seal-retire', 'fn2-pool-release')]
        names += ['fn2-seals-set-phase', 'fn2-seals-phase']
        edits.append((reads.start, reads.end, '(' + ' '.join(names) + ')'))
    elif pattern.startswith('(defun fn2-seal-step '):
        cond = node.items[-1].items[-1]
        release = lr.match('((equal phase *fn2-seal-phase-release*) ?*body)', [cond])
        if len(release) != 1:
            raise ValueError('seal step release dispatch changed')
        edits.append((release[0].start, release[0].start, DISPATCH))
    elif pattern.startswith('(fn2-seal-shape fn2-seal-step '):
        reads = node.items[-1]
        install = lr.match('fn2-seal-install', [reads])
        if len(install) != 1:
            raise ValueError('seal step shape install changed')
        edits.append((install[0].end, install[0].end,
                      ' fn2-seal-overlay-return fn2-seal-hash-return'))
    else:
        raise ValueError(pattern)
    return lr.write(original, edits)


def transform(source):
    edits = []
    for pattern, old in BEFORE.items():
        node = one(pattern, source)
        current = source[node.start:node.end]
        desired = target(pattern, old)
        if current == desired:
            continue
        if current != old:
            raise ValueError(f'fixed original {pattern} changed')
        replacement = desired + (OVERLAY if pattern.startswith('(fn2-seal-shape fn2-seal-install ') else '')
        if pattern.startswith('(fn2-seal-shape fn2-seal-install ') and lr.match(
                '(defun fn2-seal-overlay-return ?*body)', lr.parse(source).forms, deep=False):
            raise ValueError('cleanup helpers already exist')
        edits.append((node.start, node.end, replacement))
    result = lr.write(source, edits)
    old_comment = '; Install, then retire the overlay and release the hash workspace: one step\n; (no reader sees the run beside its published overlay, nor neither).'
    new_comment = '; Publish the run exactly once, then enter bounded owner-return phases.\n; Readers may see the frozen overlay beside its run until cleanup accepts.'
    if old_comment in result:
        result = result.replace(old_comment, new_comment, 1)
    elif new_comment not in result:
        raise ValueError('install comment changed')
    old_header = ('; view of runs (fn2-run-installed), and the overlay is retired with its arena\n'
                  '; released, in one step. The engine half names runs and pages itself (a run')
    new_header = ('; view of runs (fn2-run-installed), then the overlay arena and seal hash\n'
                  '; workspace return in bounded cleanup steps. The engine half names runs and pages itself (a run')
    if old_header in result:
        result = result.replace(old_header, new_header, 1)
    elif new_header not in result:
        raise ValueError('sealer header changed')
    return result, len(edits)


if __name__ == '__main__':
    changed, count = transform(PATH.read_text())
    if count:
        PATH.write_text(changed)
    print(f'{count} fixed original phase/dispatch forms transformed')
