import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_rewrite import parse
from release_ref_source import REF_COLUMNS, stage_bindings, field_bindings, decoded_matches, decoded_capture_bindings, digest_columns, digest_put

def test_exact_existing_ref_scalar_order():
    assert tuple(reader for _, reader in REF_COLUMNS) == ('storage-domain','physical-unit','writer-epoch','allocation','page-kind','encoded-length')
    assert len(parse(stage_bindings()).forms) == 6
    fields = field_bindings()
    assert len(parse(fields).forms) == 6
    for i, (target, _) in enumerate(REF_COLUMNS):
        assert f'(+ f {i})' in fields
        assert f'fn2-allocation-release-{target}' in fields
    assert len(parse(decoded_matches()).forms) == 6
    captures = decoded_capture_bindings()
    assert len(parse(captures).forms) == 6
    for i, (target, _) in enumerate(REF_COLUMNS):
        assert f'(+ f {i})' in captures
        assert target in captures
    assert len(parse(digest_columns()).forms) == 8
    assert len(parse(digest_put("fn2-release-descriptor-word")).forms) == 8
    assert 'expected-hash' not in fields  # actual digest remains an owned byte Ref

if __name__ == '__main__':
    test_exact_existing_ref_scalar_order()
    print('release Ref source recipe fixture passed')
