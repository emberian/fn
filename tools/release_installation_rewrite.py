"""Thread actual readonly directory through release claim and its frame class."""
import lisp_rewrite as lr

def thread(source, expected):
    lr.parse(source)
    old = 'fn2-ops fn2-allocation-release fn2-release-evidence'
    if source.count(old) != expected:
        raise ValueError(f'expected {expected} actual release child boundaries')
    result = source.replace(old, 'fn2-ops fn2-commit-root fn2-allocation-release fn2-release-evidence')
    lr.parse(result)
    return result

def frame_hyps(source, expected):
    old = '(fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (fn2-allocation-releasep'
    if source.count(old) != expected:
        raise ValueError(f'expected {expected} actual release readonly frame domains')
    result = source.replace(old, '(fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (fn2-commit-rootp fn2-commit-root) (fn2-commit-root-wfp fn2-commit-root) (fn2-allocation-releasep')
    lr.parse(result)
    return result
