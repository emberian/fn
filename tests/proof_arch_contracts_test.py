from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import lisp_rewrite as lr
from proof_arch_contracts import migrate
from proof_arch_views import walk


def statements(s):
    return [s[n.items[2].start:n.items[2].end] for top in lr.parse(s).forms for n in walk(top)
            if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom)
            and n.items[0].low == 'defthm']


def test_removes_traversal_without_changing_other_functions():
    src = "(defun fn2-env-rel-forms (x) x)\n(defun untouched (x) x)\n(make-event (value (fn2-env-rel-forms xs)))"
    out = migrate(src)
    assert 'fn2-env-rel-forms' not in out
    assert '(defun untouched (x) x)' in out


def test_static_runes_and_instances_become_projections():
    src = '''(defthm consumer (implies p q)
 :hints (("Goal" :in-theory '(f fn2-step-fn2-env-ek fn2-step-keeps-commit-root)
 :use ((:instance fn2-step-fn2-env-ek (x y)) (:instance retained (x y))))))'''
    out = migrate(src)
    assert statements(src) == statements(out)
    assert 'fn2-step-fn2-env-ek' not in out
    assert 'fn2-step-keeps-commit-root' not in out
    assert '(:instance retained (x y))' in out
    assert "'(fn2-env-ek fn2-env-root-table-view) clause world" in out
    assert migrate(out) == out


def test_dynamic_runes_inside_a_generator():
    src = '''(defun events (fn)
 `((make-event (value (fn2-env-rel-forms fns)))
   (defthm name (implies p q)
    :hints (("Goal" :in-theory '(,fn ,(fn2-env-rel-name fn 'fn2-env-rk)
      ,@(fn2-env-rel-callee-runes fns 'fn2-env-rk world)))))))'''
    out = migrate(src)
    assert statements(src) == statements(out)
    assert 'fn2-env-rel-forms' not in out
    assert 'fn2-env-rel-name' not in out
    assert 'fn2-env-rel-callee-runes' not in out
    assert "'(fn2-env-rk) clause world" in out
    assert migrate(out) == out


def test_root_statements_keep_names_and_replace_induction():
    src = '''(defthm fn2-reserve-fn2-env-tk (implies (fn2-env-tk x r) (fn2-env-tk (step x) r))
 :hints (("Goal" :induct (loop x) :in-theory '(loop fn2-reserve-fn2-env-tk))))'''
    out = migrate(src)
    assert statements(src) == statements(out)
    assert '(defthm fn2-reserve-fn2-env-tk' in out
    assert ':induct' not in out
    assert migrate(out) == out


def test_public_keeps_theorem_is_not_a_private_callee_rule():
    src = '''(defthm consumer (equal x y)
 :hints (("Goal" :in-theory '(fn2-env-commit-run-publish-keeps-commit-io))))'''
    assert migrate(src) == src


def test_layout_cleanup_preserves_string_contents_and_single_use():
    src = '(defconst text "line  \nnext")\n(defthm p (equal x x)\n :hints (("Goal" :use fn2-step-fn2-env-ek)))  \n'
    out = migrate(src)
    assert '"line  \nnext"' in out
    assert ':use nil' in out
    assert not out.endswith('  \n')
    assert statements(src) == statements(out)


def test_views_stay_closed_and_dead_callee_binding_disappears():
    src = """(defun events (x)
 (let ((glue '(f g)) (arm (arm-name x)))
  `(defthm use (fn2-env-tk (f x) x)
    :hints (("Goal" :in-theory '(,@(fn2-env-rel-callee-runes glue 'fn2-env-tk world)))))))"""
    out = migrate(src)
    assert 'glue' not in out
    assert '(arm (arm-name x))' not in out
    assert "(union-theories '(fn2-env-tk)" not in out
    assert "(theory 'fn2-column-projection-base)" in out
    assert statements(src) == statements(out)


if __name__ == '__main__':
    tests = [fn for name, fn in list(globals().items()) if name.startswith('test_')]
    for test in tests:
        test()
    print(f'{len(tests)} structural fixtures passed')
