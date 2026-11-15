"""Share the actual installation field conjunction, leaving hash/coverage at caller."""
import lisp_rewrite as lr
EXPECTED = ('checkpoint', 'domain', 'unit', 'epoch', 'allocation', 'kind-ref', 'length')
READERS = ('checkpoint', 'storage-domain', 'physical-unit', 'writer-epoch', 'allocation', 'page-kind', 'encoded-length')

def field_tests():
    f = '*fn2-format-checkpoint-installation-field-descriptor-storage-domain*'
    tests = ['(equal kind *record-kind-checkpoint-installation*)',
             '(equal (fn2-fields-value (+ base *fn2-format-checkpoint-installation-field-checkpoint*) fn2-fields) checkpoint)']
    for i, name in enumerate(EXPECTED[1:]):
        tests.append(f'(equal (fn2-fields-value (+ base {f} {i}) fn2-fields) {name})')
    tests.append(f'(equal (fn2-fields-value (+ base {f} 6) fn2-fields) 1)')
    return '\n'.join(lr.emit(x) for x in lr.parse('\n'.join(tests)).forms)

def call():
    args = ['kind', '(fn2-checkpoints-checkpoint c fn2-checkpoints)']
    args += [f'(fn2-checkpoint-refs-{name} r fn2-checkpoint-refs)' for name in READERS[1:]]
    return '(fn2-checkpoint-installation-ref-fields-p ' + ' '.join(args) + ' base fn2-fields)'

def transform(source):
    parsed = lr.parse(source)
    found = lr.match('(match (and ?*tests))', parsed.forms)
    if len(found) != 1:
        raise ValueError('expected one actual installation conjunction')
    n = found[0].node
    conjunction = n.items[1]
    if len(conjunction.items) != 11:
        raise ValueError('installation matcher changed')
    tail = conjunction.items[-1]
    if getattr(tail.items[0], 'low', '') != 'fn2-checkpoint-pool-hash-matchesp':
        raise ValueError('expected original concrete hash comparison')
    replacement = '(match (and ' + call() + '\n' + source[tail.start:tail.end] + '))'
    return lr.write(source, [(n.start, n.end, replacement)])
