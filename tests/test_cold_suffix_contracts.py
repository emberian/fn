import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from cold_suffix_contracts import extend

def test_real_guard_domain_and_args():
    source = '(fn2-extents-preserves fn2-checkpoint-suffix-allocation-begin (commit base fields extents) :hyps ((actual-source-wfp source)) :specs (("-ROWS" rows 2 :frame extents)))\n'
    output = extend(source)
    assert '(commit base extent epoch allocation owner-kind owner fields extents)' in output
    assert output.count(':hyps ((actual-source-wfp source))') == 2
    assert output.count(':frame extents') == 2
    assert extend(output) == output

def test_walk_and_existing_consumers():
    source = '(fn2-job-preserves fn2-checkpoint-suffix-allocation-step (source job extents) :hyps (source-ok))\n(fn2-edges-preserves fn2-checkpoint-suffix-allocation-existing (commit source fields extents edges) :hyps (actual-guard))'
    output = extend(source)
    assert 'fn2-checkpoint-suffix-allocation-walk (source job extents)' in output
    assert 'fn2-checkpoint-suffix-allocation-existing-record (commit e epoch allocation owner-kind owner source fields extents edges)' in output
    assert extend(output) == output

if __name__ == '__main__':
    test_real_guard_domain_and_args()
    test_walk_and_existing_consumers()
    print('2 shared contract rewrite fixtures passed')
