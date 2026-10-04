"""tools/native_overlay.py plan: what a form swap carries and what it refuses."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import native_overlay  # noqa: E402

BUILD = '''(include-book "books/w")
(ld "host/a-host.lisp" :ld-error-action :error)
(progn! (set-raw-mode t)
        (load "host/native/x.lisp")
        (fnn-boot-check)
        (defun fn-native-entry (st) (declare (ignore st)) (fnn-g 1)))
(save-exec "x" "y" :return-from-lp '(fn-native-entry state))
'''
RAW = '''(in-package "ACL2")
(declaim (inline fnn-fast))
(defun fnn-fast (x) (+ x 1))
(defun fnn-g (x) (fnn-h x))
(defun fnn-h (x) (list x))
(defun fnn-tabled () (make-hash-table))
(defparameter *fnn-table* (fnn-tabled))
(defparameter +fnn-limit+ 4)
(defparameter *fnn-read-pairs* '((fnn-h . formals) (fn-native-entry . guard)))
(fnn-register "late" (lambda () (fnn-h 2)))
(defmacro fnn-with (x) x)
(defstruct (fnn-state) a b)
(pushnew 'fnn-g *fnn-hooks*)
(fnn-register "verb" #'fnn-verb)
(defun fnn-verb () (fnn-h 1))
(defun fnn-boot-check () t)
(defun fnn-unused () 1)
(defun fnn-used () 2)
(defun fnn-caller () (fnn-used))
'''
HOST = '''(in-package "ACL2")
(defun fn-a (x) (declare (xargs :guard t)) (cons x x))
(defthm fn-a-consp (consp (fn-a x)))
(defthm fn-unrelated (equal 1 1))
'''
BOOK_W = '''(in-package "ACL2")
(include-book "s")
(defun fn-w (x) x)
'''
BOOK_S = '''(in-package "ACL2")
(defstobj st fld)
'''


class FakeSource:
    def __init__(self, files):
        self.files = files

    def text(self, path):
        return self.files.get(path)


def plan(changes, files=None):
    base = {"host/native/build.lisp": BUILD, "host/native/build-dtn.lisp": "",
            "host/native/x.lisp": RAW, "host/a-host.lisp": HOST,
            "books/w.lisp": BOOK_W, "books/s.lisp": BOOK_S, "books/outside.lisp": "(defun z () 1)\n"}
    new = dict(base)
    for path, (old, replacement) in changes.items():
        assert old in new[path], (path, old)
        new[path] = new[path].replace(old, replacement)
    return native_overlay.Plan("base", "rev", FakeSource(base), FakeSource(new),
                               files=files or sorted(changes)).make()


class OverlayPlanTests(unittest.TestCase):
    def assertRefused(self, p, *fragments):
        text = "\n".join(p.refusals)
        self.assertTrue(p.refusals, "expected a refusal")
        for fragment in fragments:
            self.assertIn(fragment, text)

    def test_changed_raw_defun_applies(self):
        p = plan({"host/native/x.lisp": ("(defun fnn-h (x) (list x))", "(defun fnn-h (x) (list x x))")})
        self.assertEqual(p.refusals, [])
        self.assertEqual([(a, f.name) for a, f in p.forms["host/native/x.lisp"]], [("changed", "fnn-h")])
        self.assertEqual(p.images["developer"]["raw"], ["host/native/x.lisp"])
        self.assertNotIn("refused", p.images["production"])  # raw-only: stripped images too

    def test_comment_only_change_applies_nothing(self):
        p = plan({"host/native/x.lisp": ("(defun fnn-h (x) (list x))", "(defun fnn-h (x) ; why\n (list x))")})
        self.assertEqual((p.refusals, p.forms), ([], {}))

    def test_values_and_layouts_refused(self):
        for old, new, why in [
                ("(defparameter +fnn-limit+ 4)", "(defparameter +fnn-limit+ 5)", "old expansion or value"),
                ("(defmacro fnn-with (x) x)", "(defmacro fnn-with (x) (list x))", "old expansion or value"),
                ("(defstruct (fnn-state) a b)", "(defstruct (fnn-state) a b c)", "layout change"),
                ("(pushnew 'fnn-g *fnn-hooks*)", "(pushnew 'fnn-h *fnn-hooks*)", "load-time effect"),
                ("(defun fnn-fast (x) (+ x 1))", "(defun fnn-fast (x) (+ x 2))", "declared inline")]:
            with self.subTest(old=old):
                self.assertRefused(plan({"host/native/x.lisp": (old, new)}), why)

    def test_build_time_call_refused_symbol_reference_not(self):
        # *fnn-table*'s initializer ran fnn-tabled at image build
        self.assertRefused(plan({"host/native/x.lisp": ("(make-hash-table)", "(make-hash-table :test 'equal)")}),
                           "defparameter *fnn-table* runs at image build and calls fnn-tabled")
        # the build script's raw block called fnn-boot-check
        self.assertRefused(plan({"host/native/x.lisp": ("(defun fnn-boot-check () t)", "(defun fnn-boot-check () nil)")}),
                           "host/native/build.lisp", "fnn-boot-check")
        # what evaluation does not run is not a build-time call: a quoted
        # list, a lambda handed to a registration, a defun in the build's
        # raw block, the save-exec's quoted return form
        # a hook stored by symbol reaches the new body; fnn-g is reached from fnn-h
        self.assertEqual(plan({"host/native/x.lisp": ("(defun fnn-h (x) (list x))", "(defun fnn-h (x) x)")}).refusals, [])
        # #'fnn-verb captured the old function object
        self.assertRefused(plan({"host/native/x.lisp": ("(defun fnn-verb () (fnn-h 1))", "(defun fnn-verb () 2)")}),
                           "captures the function object of fnn-verb")

    def test_deleted_definitions(self):
        p = plan({"host/native/x.lisp": ("(defun fnn-unused () 1)\n", "")})
        self.assertEqual(p.refusals, [])
        self.assertTrue(any("fnn-unused deleted" in n for n in p.notes))
        self.assertRefused(plan({"host/native/x.lisp": ("(defun fnn-used () 2)\n", "")}),
                           "fnn-used deleted but still named")

    def test_acl2_change_rechecks_theorems_and_refuses_stripped(self):
        p = plan({"host/a-host.lisp": ("(cons x x))", "(list* x x nil))")})
        self.assertEqual(p.refusals, [])
        self.assertEqual([f.name for f in p.rechecks["host/a-host.lisp"]], ["fn-a-consp"])
        self.assertIn("refused", p.images["production"])
        self.assertNotIn("refused", p.images["developer"])
        with tempfile.TemporaryDirectory() as d:
            record = p.write(Path(d))
            text = (Path(d) / record["images"]["developer"]["acl2"][0]).read_text()
            self.assertIn("(defthm fn-overlay-recheck-fn-a-consp (consp (fn-a x)))", text)
            self.assertNotIn("fn-unrelated", text)
            self.assertEqual(json.loads((Path(d) / "plan.json").read_text())["changed_names"], ["fn-a"])

    def test_world_book_stobj_refused_outside_book_ignored(self):
        self.assertRefused(plan({"books/s.lisp": ("(defstobj st fld)", "(defstobj st fld fld2)")}),
                           "never mix obsolete stobj")
        p = plan({"books/outside.lisp": ("1)", "2)")})
        self.assertEqual((p.refusals, p.forms), ([], {}))
        self.assertTrue(any("no image loads" in n for n in p.notes))

    def test_image_inputs_refused(self):
        self.assertRefused(plan({"host/native/build.lisp": ("(fnn-boot-check)", "(fnn-boot-check) (fnn-more)")}),
                           "an image input")
        self.assertRefused(plan({}, files=["host/native/fn-blake3.c"]), "an image input")


if __name__ == "__main__":
    unittest.main()
