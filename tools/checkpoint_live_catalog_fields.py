"""Source fragments for the eight-word retained producer root commitment.

No Lisp is evaluated; the emitter stores the same words used by the actual
manifest hash writer. This generator only spells the repetitive source fields.
"""
def declarations():
    return ' '.join(f'(catalog-hash-{i} :u32)' for i in range(8))

def captures():
    return '\n'.join(f'        (catalog-hash-{i} (fn2-checkpoint-page-verified-word extent {i} fn2-checkpoint-page-verified))' for i in range(8))
