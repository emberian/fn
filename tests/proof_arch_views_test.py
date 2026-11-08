"""Fixtures for the relation migration; no ACL2 proof is inferred from these."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from proof_arch_views import migrate, SELECT


def test_all_seven_and_comments():
    source = '; keep this comment\n' + '\n'.join(
        f'(defun-nx fn2-env-{key} (b a) (equal b a))' for key in SELECT)
    output = migrate(source)
    assert output.startswith('; keep this comment\n')
    for key in SELECT:
        assert f'(fn2-defview fn2-env-{key} ' in output
        assert f'(defthm fn2-env-{key}-view-equivalence' in output
        assert f'(equal (fn2-env-{key} b a) (equal b a))' in output
    assert migrate(output) == output


def test_hints_and_unrelated_forms():
    source = '''(defthm unchanged (equal x x)
  :hints (("Goal" :in-theory '(fn2-env-tk))))
(defthm also-unchanged (equal y y) :hints (("Goal" :in-theory nil)))'''
    output = migrate(source)
    assert "(union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) '(fn2-env-tk))" in output
    assert source[source.index('(defthm also-unchanged'):] in output
    assert migrate(output) == output
