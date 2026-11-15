"""Source-only preservation check for the existing ordinary release decision."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_source import forms, read_sexp

def test_existing_ordinary_formula_preserved():
    source = Path(__file__).resolve().parents[1] / 'books' / 'alloc.lisp'
    functions = {x[1]: x for raw in forms(source.read_text()) if (x := read_sexp(raw)) and x[0] == 'defun'}
    def subst(x):
        if x == 'cut': return ['fn2-alloc-cut','fn2-extents']
        if not isinstance(x,list): return x
        if x and x[0] == 'fn2-alloc-releasable-under-cut-p':
            return ['fn2-alloc-releasablep', x[1], x[3]]
        return [subst(v) for v in x]
    expected = read_sexp('''(let ((code (fn2-alloc-handle-code i epoch counter fn2-extents)))
      (cond ((not (eq code :ok)) code)
       ((not (= (fn2-extents-state i fn2-extents) *fn2-extent-state-retire-pending*)) :state)
       ((fn2-alloc-protector i nil fn2-extents) (fn2-alloc-protector i nil fn2-extents))
       ((not (fn2-alloc-releasablep i fn2-extents)) :checkpoint-blocked)
       ((not (fn2-alloc-free-linksp i fn2-extents)) :links) (t :ok)))''')
    assert subst(functions['fn2-alloc-release-under-cut-code'][-1]) == expected
    assert functions['fn2-alloc-release-code'][-1] == read_sexp('''(if (fn2-alloc-frozenp fn2-extents) :frozen
      (fn2-alloc-release-under-cut-code i epoch counter (fn2-alloc-cut fn2-extents) fn2-extents))''')
    assert subst(functions['fn2-alloc-releasable-under-cut-p'][-1]) == read_sexp('''(and
      (= (fn2-extents-state i fn2-extents) *fn2-extent-state-retire-pending*)
      (not (fn2-alloc-protector i nil fn2-extents))
      (<= (fn2-extents-retirement i fn2-extents) (fn2-alloc-cut fn2-extents)))''')

if __name__ == '__main__':
    test_existing_ordinary_formula_preserved()
    print('ordinary release formula source check passed')
