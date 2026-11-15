#!/usr/bin/env python3
"""Conserve a retired run's cache handle until its pool release accepts.

The fixed original forms in seal-release-held-before.json are the only input
accepted for rewriting. This is a source transformation, not an ACL2 run.
"""

import json
from pathlib import Path
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
BEFORE = json.loads((ROOT / 'tools/fixtures/seal-release-held-before.json').read_text())

PEEK = '''; Read the exact resident handle without consuming it. A held pool release
; must leave this cache entry available for the next bounded retry.
(defun fn2-run-cache-peek (unit fn2-run-cache)
 (declare (xargs :stobjs fn2-run-cache :guard (fn2-run-cache-wfp fn2-run-cache)))
 (b* (((unless (and (natp unit) (< 0 (fn2-run-cache-rows fn2-run-cache)))) (mv :bounds 0 0))
      (i (nfix (fn2-run-cache-row unit fn2-run-cache)))
      ((unless (< i (fn2-run-cache-rows fn2-run-cache))) (mv :bounds 0 0))
      ((unless (and (equal (fn2-run-cache-state i fn2-run-cache) *fn2-run-cache-state-ready*)
                    (equal (fn2-run-cache-unit i fn2-run-cache) unit)))
       (mv :absent 0 0)))
  (mv :ok (nfix (fn2-run-cache-slot i fn2-run-cache))
          (nfix (fn2-run-cache-gen i fn2-run-cache)))))
(defthm fn2-run-cache-peek-types
 (and (natp (mv-nth 1 (fn2-run-cache-peek unit fn2-run-cache)))
      (natp (mv-nth 2 (fn2-run-cache-peek unit fn2-run-cache))))
 :hints (("Goal" :in-theory (enable fn2-run-cache-peek))))

'''

DROP = '''(defun fn2-run-cache-drop (unit fn2-run-cache)
 (declare (xargs :stobjs fn2-run-cache :guard (fn2-run-cache-wfp fn2-run-cache)))
 (b* (((mv code slot gen) (fn2-run-cache-peek unit fn2-run-cache))
      ((unless (eq code :ok)) (mv code 0 0 fn2-run-cache))
      (i (nfix (fn2-run-cache-row unit fn2-run-cache)))
      ((unless (< i (fn2-run-cache-rows fn2-run-cache))) (mv :bounds 0 0 fn2-run-cache))
      (fn2-run-cache (fn2-run-cache-put i (state *fn2-run-cache-state-empty*))))
  (mv :ok slot gen fn2-run-cache)))'''

ROW = '''(defun fn2-seal-release-row (r fn2-run-installed fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-installed fn2-run-cache fn2-pool)
  :guard (and (fn2-run-installed-wfp fn2-run-installed)
              (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-run-cache-drop fn2-run-retired-next
                                            fn2-pool-release fn2-pool-release-countp
                                            fn2-run-installed-rows)))))
 (b* (((unless (and (natp r) (< r (fn2-run-installed-rows fn2-run-installed))))
       (mv :bounds fn2-run-installed fn2-run-cache fn2-pool))
      ((unless (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*))
       (mv :state fn2-run-installed fn2-run-cache fn2-pool))
      ; Physical roots have no resident-cache interval; their catalog promise
      ; and query leases drain through checkpoint-summary retirement.
      ((when (= (fn2-run-installed-physical r fn2-run-installed) 1))
       (mv :cache fn2-run-installed fn2-run-cache fn2-pool))
      (u (fn2-run-installed-ufirst r fn2-run-installed))
      ((mv code fn2-run-cache fn2-pool)
       (if (<= (nfix u) (nfix (fn2-run-installed-ulast r fn2-run-installed)))
           (b* (((mv peek slot gen) (fn2-run-cache-peek (nfix u) fn2-run-cache))
                ((when (eq peek :absent)) (mv :ok fn2-run-cache fn2-pool))
                ((unless (eq peek :ok)) (mv peek fn2-run-cache fn2-pool))
                ((unless (fn2-pool-release-countp slot fn2-pool))
                 (mv :bounds fn2-run-cache fn2-pool))
                ((mv released fn2-pool)
                 (fn2-pool-release slot gen
                  (fn2-run-installed-okind r fn2-run-installed)
                  (fn2-run-installed-oslot r fn2-run-installed)
                  (fn2-run-installed-ogen r fn2-run-installed) fn2-pool))
                ((unless (or (eq released :ok) (eq released :retired)))
                 (mv released fn2-run-cache fn2-pool))
                ((mv dropped drop-slot drop-gen fn2-run-cache)
                 (fn2-run-cache-drop (nfix u) fn2-run-cache))
                ((unless (and (eq dropped :ok) (equal drop-slot slot)
                              (equal drop-gen gen)))
                 (mv :invariant fn2-run-cache fn2-pool)))
             (mv :ok fn2-run-cache fn2-pool))
         (mv :ok fn2-run-cache fn2-pool)))
      ((unless (eq code :ok)) (mv code fn2-run-installed fn2-run-cache fn2-pool))
      ((mv code fn2-run-installed) (fn2-run-retired-next r fn2-run-installed)))
  (mv (if (eq code :ok) :more code) fn2-run-installed fn2-run-cache fn2-pool)))'''

SHAPE = '''(fn2-seal-shape fn2-seal-release-row (r fn2-run-installed fn2-run-cache fn2-pool)
 (fn2-run-installed fn2-run-cache fn2-pool) (fn2-run-installed fn2-run-cache fn2-pool) t
 (fn2-run-cache-peek fn2-run-cache-drop fn2-run-retired-next fn2-pool-release fn2-pool-release-countp
  fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen
  fn2-run-installed-state fn2-run-installed-physical fn2-run-installed-ufirst
  fn2-run-installed-ulast))'''

OVERLAY = '''(defun fn2-seal-retire (o fn2-overlays fn2-pool)
 (declare (xargs :stobjs (fn2-overlays fn2-pool) :guard (and (fn2-overlays-wfp fn2-overlays) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-ov-retire fn2-ov-advance fn2-pool-release fn2-pool-release-countp)))))
 (b* (((unless (and (natp o) (< o (fn2-overlays-rows fn2-overlays))))
       (mv :bounds fn2-overlays fn2-pool))
      ((unless (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*))
       (mv :state fn2-overlays fn2-pool))
      (slot (fn2-overlays-slot o fn2-overlays))
      (gen (fn2-overlays-gen o fn2-overlays))
      (okind (fn2-overlays-okind o fn2-overlays))
      (oslot (fn2-overlays-oslot o fn2-overlays))
      (ogen (fn2-overlays-ogen o fn2-overlays))
      ((unless (fn2-pool-release-countp slot fn2-pool))
       (mv :bounds fn2-overlays fn2-pool))
      ((mv released fn2-pool) (fn2-pool-release slot gen okind oslot ogen fn2-pool))
      ((unless (or (eq released :ok) (eq released :retired)))
       (mv released fn2-overlays fn2-pool))
      ((mv code fn2-overlays)
       (fn2-ov-advance o *fn2-overlay-phase-frozen* *fn2-overlay-phase-free* fn2-overlays)))
  (mv (if (eq code :ok) released code) fn2-overlays fn2-pool)))'''

OVERLAY_SHAPE = '''(fn2-seal-shape fn2-seal-retire (o fn2-overlays fn2-pool)
 (fn2-overlays fn2-pool) (fn2-overlays fn2-pool) t
 (fn2-ov-advance fn2-pool-release fn2-pool-release-countp fn2-overlays-phase
  fn2-overlays-slot fn2-overlays-gen fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))'''

REPLACEMENTS = {
    'books/runs.lisp': {
        '(defun fn2-run-cache-drop ?*body)': PEEK + DROP,
    },
    'books/sealer.lisp': {
        '(defun fn2-seal-retire ?*body)': OVERLAY,
        '(fn2-seal-shape fn2-seal-retire ?*body)': OVERLAY_SHAPE,
        '(defun fn2-seal-release-row ?*body)': ROW,
        '(fn2-seal-shape fn2-seal-release-row ?*body)': SHAPE,
    },
}

CALLERS = ('(defun fn2-seal-start ?*body)', '(defun fn2-seal-install ?*body)')


def caller_target(pattern, original):
    node = lr.match(pattern, lr.parse(original).forms, deep=False)[0].node
    if 'fn2-seal-start' in pattern:
        found = lr.match('(if (eq code :ok) :retired code)', [node])
        if len(found) != 1:
            raise ValueError('empty-overlay return mapping changed')
        return lr.write(original, [(found[0].start, found[0].end,
                                    '(if (or (eq code :ok) (eq code :retired)) :retired code)')])
    overlay = lr.match('(fn2-seal-retire o fn2-overlays fn2-pool)', [node])
    hash_release = lr.match('(fn2-pool-release hslot ?*args)', [node])
    checks = lr.match('((unless (eq code :ok)) ?*rest)', [node])
    if len(overlay) != 1 or len(hash_release) != 1:
        raise ValueError('seal install release calls changed')
    if not overlay[0].start < hash_release[0].start:
        raise ValueError('seal install release order changed')
    selected = []
    for call in (overlay[0], hash_release[0]):
        later = [m for m in checks if m.start > call.start]
        if not later:
            raise ValueError('seal install release acceptance missing')
        selected.append(later[0].node.items[0].items[1])
    if len({n.start for n in selected}) != 2:
        raise ValueError('seal install release checks overlap')
    return lr.write(original, [(n.start, n.end,
                                '(or (eq code :ok) (eq code :retired))')
                               for n in selected])


def transform(file, source):
    edits = []
    for pattern, replacement in REPLACEMENTS[file].items():
        found = lr.match(pattern, lr.parse(source).forms, deep=False)
        if len(found) != 1:
            raise ValueError(f'{file}: expected one {pattern}')
        node = found[0].node
        current = source[node.start:node.end]
        old = BEFORE[file][pattern]
        target = DROP if pattern == '(defun fn2-run-cache-drop ?*body)' else replacement
        if current == target:
            continue
        if current != old:
            raise ValueError(f'{file}: fixed original {pattern} changed')
        if pattern == '(defun fn2-run-cache-drop ?*body)' and lr.match(
                '(defun fn2-run-cache-peek ?*body)', lr.parse(source).forms, deep=False):
            raise ValueError(f'{file}: cache peek already exists')
        edits.append((node.start, node.end, replacement))
    if file == 'books/sealer.lisp':
        for pattern in CALLERS:
            found = lr.match(pattern, lr.parse(source).forms, deep=False)
            if len(found) != 1:
                raise ValueError(f'{file}: expected one {pattern}')
            node = found[0].node
            current = source[node.start:node.end]
            old = BEFORE[file][pattern]
            target = caller_target(pattern, old)
            if current == target:
                continue
            if current != old:
                raise ValueError(f'{file}: fixed original caller {pattern} changed')
            edits.append((node.start, node.end, target))
    return lr.write(source, edits), len(edits)


if __name__ == '__main__':
    total = 0
    for file in REPLACEMENTS:
        path = ROOT / file
        result, count = transform(file, path.read_text())
        if count:
            path.write_text(result)
        total += count
    print(f'{total} fixed-source forms transformed')
