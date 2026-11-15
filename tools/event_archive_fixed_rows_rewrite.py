"""Use the canonical guarded fixed-pair predicate at actual archive boundaries."""
import lisp_rewrite as lr


def rewrite(source):
    matches=lr.match('(< 1 (fn2-run-loads-rows fn2-run-loads))',lr.parse(source).forms)
    return lr.write(source,[(m.start,m.end,
        '(fn2-b-fixed-cursor-rows-p (fn2-run-loads-rows fn2-run-loads))') for m in matches])
