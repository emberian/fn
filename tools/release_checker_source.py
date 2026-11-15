"""Exact concrete format-checker continuation fields retained by RELEASE."""
from lisp_rewrite import parse, emit, match
FIELDS = ('phase', 'pos', 'zero', 'pad', 'pad-end', 'geom', 'previous-seal-offset')
def columns():
    return '\n'.join(emit(n) for n in parse(' '.join(f'(checker-{f} :u8)' if f == 'phase' else f'(checker-{f} :u32)' for f in FIELDS)).forms)
def capture():
    return '\n'.join(emit(n) for n in parse(' '.join(f'(checker-{f} (fn2-fc-{f} row fn2-fc))' for f in FIELDS)).forms)
def matches():
    return '\n'.join(emit(n) for n in parse(' '.join(f'(equal (fn2-fc-{f} row fn2-fc) (fn2-allocation-release-checker-{f} 0 fn2-allocation-release))' for f in FIELDS)).forms)

def context_matches(source):
    found = match('(defun fn2-rec-context ?*body)', parse(source).forms, deep=False)
    if len(found) != 1:
        raise ValueError('expected actual recovery context constructor')
    tests = []
    for m in match('(?head ?*args)', [found[0].node]):
        n = m.node
        head = getattr(n.items[0], 'low', '')
        prefix = 'fn2-fc-context-set-'
        if head.startswith(prefix):
            if len(n.items) != 4:
                raise ValueError('context setter signature changed')
            field = head[len(prefix):]
            tests.append(f'(equal (fn2-fc-context-{field} row fn2-fc-context) {emit(n.items[2])})')
    if len(tests) != 14:
        raise ValueError('actual context fields changed')
    return '\n'.join(tests)
