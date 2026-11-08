"""Fixtures for the relation migration; no ACL2 proof is inferred from these."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from proof_arch_views import migrate, lift_transports, SELECT


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


def test_lifts_keep_the_statement_parameters_and_comments():
    forms = []
    for family in ('log', 'child', 'view'):
        for invariant in ('j', 'j3'):
            step = ('fn2-env-' + family + '-step' if family != 'view'
                    else f'fn2-env-{invariant}-view-step')
            all_fn = f'fn2-env-{invariant}-rows'
            forms.append(f'(defthm fn2-env-{invariant}-{family}-transport '
                         f'(implies (and ({all_fn} keys g a) ({step} delta g a h b)) '
                         f'({all_fn} keys h b)) :rule-classes nil :hints nil)')
    output = lift_transports('; preserve\n' + '\n'.join(forms))
    assert output.startswith('; preserve\n')
    assert output.count('(fn2-pw-lift-locality ') == 6
    assert output.count(':open (fn2-env-j3-point)') == 3
    assert ':step fn2-env-log-step' in output
    assert ':step fn2-env-j3-view-step' in output
    assert lift_transports(output) == output


def test_lift_refuses_a_changed_statement():
    source = '(defthm fn2-env-j-log-transport (equal x x) :rule-classes nil)'
    try:
        lift_transports(source)
    except ValueError as error:
        assert 'unexpected statement' in str(error)
    else:
        raise AssertionError('migration accepted an unrecognized statement')
