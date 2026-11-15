#!/usr/bin/env python3
"""Extract one resident retired-row release from the actual sealer body."""
from pathlib import Path
import lisp_rewrite as lr


def one(pattern, forms):
    matches = lr.match(pattern, forms)
    if len(matches) != 1:
        raise ValueError(f'expected one {pattern}; found {len(matches)}')
    return matches[0].node


def release_parts(source):
    forms = lr.parse(source).forms
    fn = one('(defun fn2-seal-release ?*body)', forms)
    body = fn.items[-1]
    if body.items[0].low != 'b*':
        raise ValueError('actual release lost b* body')
    bindings = body.items[1].items
    if len(bindings) != 9:
        raise ValueError('retired release binding sequence changed')
    if not lr.match('(fn2-seal-retired-row rows 0 fn2-run-installed)', [bindings[2]]):
        raise ValueError('actual sealer selector changed')
    if not lr.match('(= (fn2-run-installed-physical r fn2-run-installed) 1)', [bindings[4]]):
        raise ValueError('physical fence is not the resident-body boundary')
    if not lr.match('(fn2-run-retired-next r fn2-run-installed)', [bindings[8]]):
        raise ValueError('actual retired advance changed')
    return fn, body, bindings


def row_body(source, body, bindings):
    tail = source[bindings[4].start:body.items[1].end - 1]
    result = source[body.items[2].start:body.items[2].end]
    fragment = '(b* (' + tail + ') ' + result + ')'
    forms = lr.parse(fragment).forms
    edits = []
    for field in ('okind', 'oslot', 'ogen'):
        matches = lr.match(f'(fn2-seals-{field} 0 fn2-seals)', forms)
        if len(matches) != 1:
            raise ValueError(f'expected one sealer owner {field}')
        edits.append((matches[0].start, matches[0].end,
                      f'(fn2-run-installed-{field} r fn2-run-installed)'))
    outputs = lr.match('(mv ?code fn2-seals fn2-run-installed fn2-run-cache fn2-pool)', forms)
    if len(outputs) != 3:
        raise ValueError('resident body output sites changed')
    for output in outputs:
        node = output.node
        code = fragment[node.items[1].start:node.items[1].end]
        edits.append((node.start, node.end,
                      f'(mv {code} fn2-run-installed fn2-run-cache fn2-pool)'))
    fragment = lr.write(fragment, edits)
    check = '''((unless (and (natp r) (< r (fn2-run-installed-rows fn2-run-installed))))
       (mv :bounds fn2-run-installed fn2-run-cache fn2-pool))
      ((unless (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*))
       (mv :state fn2-run-installed fn2-run-cache fn2-pool))
      ; Physical roots have no resident-cache interval; their catalog promise
      ; and query leases drain through checkpoint-summary retirement.
      '''
    parsed = lr.parse(fragment).forms[0]
    binding_list = parsed.items[1]
    return lr.write(fragment, [(binding_list.start + 1, binding_list.start + 1, check)])


def helper(source, body, bindings):
    return '''; One bounded release for the exact resident installed row. The row
; retains the pool owner from installation; the active sealer may have moved
; to another owner before this older run retires.
(defun fn2-seal-release-row (r fn2-run-installed fn2-run-cache fn2-pool)
 (declare (xargs :stobjs (fn2-run-installed fn2-run-cache fn2-pool)
  :guard (and (fn2-run-installed-wfp fn2-run-installed)
              (fn2-run-cache-wfp fn2-run-cache) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-run-cache-drop fn2-run-retired-next
                                            fn2-pool-release fn2-pool-release-countp
                                            fn2-run-installed-rows)))))
 ''' + row_body(source, body, bindings) + ''')
(fn2-seal-shape fn2-seal-release-row (r fn2-run-installed fn2-run-cache fn2-pool)
 (fn2-run-installed fn2-run-cache fn2-pool) (fn2-run-installed fn2-run-cache fn2-pool) t
 (fn2-run-cache-drop fn2-run-retired-next fn2-pool-release fn2-pool-release-countp
  fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen
  fn2-run-installed-state fn2-run-installed-physical fn2-run-installed-ufirst
  fn2-run-installed-ulast))
'''


def wrapper_body(source, bindings):
    early = source[bindings[0].start:bindings[3].end]
    return '''(b* (''' + early + ''')
  (mv-let (code fn2-run-installed fn2-run-cache fn2-pool)
   (fn2-seal-release-row r fn2-run-installed fn2-run-cache fn2-pool)
   (mv code fn2-seals fn2-run-installed fn2-run-cache fn2-pool)))'''


def transform(source):
    fn, body, bindings = release_parts(source)
    shape = one('(fn2-seal-shape fn2-seal-release ?*body)', lr.parse(source).forms)
    old_shape = source[shape.start:shape.end]
    shape_form = lr.parse(old_shape).forms[0]
    reads = shape_form.items[6]
    new_reads = '(fn2-seal-retired-row fn2-seal-release-row fn2-seals-rows fn2-run-installed-rows)'
    shape_text = lr.write(old_shape, [(reads.start, reads.end, new_reads)])
    hint = one('(disable fn2-seal-retired-row ?*rest)', [fn])
    hint_text = '(disable fn2-seal-retired-row fn2-seal-release-row fn2-seals-rows fn2-run-installed-rows)'
    return lr.write(source, [
        (fn.start, fn.start, helper(source, body, bindings) + '\n'),
        (hint.start, hint.end, hint_text),
        (body.start, body.end, wrapper_body(source, bindings)),
        (shape.start, shape.end, shape_text),
    ])


if __name__ == '__main__':
    path = Path(__file__).resolve().parents[1] / 'books/sealer.lisp'
    path.write_text(transform(path.read_text()))
