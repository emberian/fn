"""Source recipes for the six scalar fields of the existing generated Ref."""
from lisp_rewrite import emit, parse
REF_COLUMNS = (
 ('storage-domain', 'storage-domain'), ('physical-unit', 'physical-unit'),
 ('descriptor-epoch', 'writer-epoch'), ('descriptor-allocation', 'allocation'),
 ('page-kind', 'page-kind'), ('encoded-length', 'encoded-length'),
)
def stage_bindings():
    source = '\n'.join(f'({target} (fn2-checkpoint-refs-{reader} r fn2-checkpoint-refs))'
                       for target, reader in REF_COLUMNS)
    return '\n'.join(emit(form) for form in parse(source).forms)
def field_bindings():
    source = '\n'.join(f'(fn2-fields (fn2-fields-set-value (+ f {i}) (fn2-allocation-release-{target} 0 fn2-allocation-release) fn2-fields))'
                       for i, (target, _) in enumerate(REF_COLUMNS))
    return '\n'.join(emit(form) for form in parse(source).forms)

def decoded_matches():
    source = '\n'.join(f'(= (fn2-fields-value (+ f {i}) fn2-fields) (fn2-allocation-release-{target} 0 fn2-allocation-release))'
                       for i, (target, _) in enumerate(REF_COLUMNS))
    return '\n'.join(emit(form) for form in parse(source).forms)
