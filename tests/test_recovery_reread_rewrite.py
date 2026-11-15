import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from recovery_reread_rewrite import rewrite, install_digest_fields

def test_shared_class_symbols_only():
    source = '; fn2-rp-replay-row-p\n(defun fn2-rp-replay-row-p (x) (fn2-rp-replay-auth-p x))\n"fn2-recovery-replay-open"\n'
    expected = '; fn2-rp-replay-row-p\n(defun fn2-rp-current-unit-row-p (x) (fn2-rp-current-unit-auth-p x))\n"fn2-recovery-replay-open"\n'
    assert rewrite(source) == expected

def test_theory_reference_and_idempotence():
    source = "'(fn2-recovery-replay-open fn2-unrelated)"
    expected = "'(fn2-recovery-current-unit-open fn2-unrelated)"
    assert rewrite(source) == expected
    assert rewrite(expected) == expected

def test_fixed_digest_fields():
    source = '((rc-auth-roff :u32) (unrelated :u60))'
    output = install_digest_fields(source)
    for i in range(8):
        assert output.count(f'(rc-auth-h{i} :u32)') == 1
    assert '(unrelated :u60)' in output
    assert install_digest_fields(output) == output

if __name__ == "__main__":
    test_shared_class_symbols_only()
    test_theory_reference_and_idempotence()
    test_fixed_digest_fields()
    print("3 scoped rewrite fixtures passed")
