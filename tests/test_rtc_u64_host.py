"""Replay the owner's real begin caller for terminal and temporary exhaustion."""
import shutil
import subprocess
import unittest
from pathlib import Path

from tools import lisp_rewrite

ROOT = Path(__file__).resolve().parents[1]
SBCL = shutil.which("sbcl")


@unittest.skipUnless(SBCL, "SBCL required for native begin control-flow replay")
class RtcU64HostTests(unittest.TestCase):
    def test_begin_terminal_is_refused_and_temporary_wait_is_kept(self):
        source = (ROOT / "host/native/owner.lisp").read_text()
        start = source.index("(defun fnn-owner-lease-article-step ")
        end = source.index("\n(defun ", start + 1)
        parsed = lisp_rewrite.parse(source[start:end])
        node = lisp_rewrite.match(
            None, parsed.forms, head="defun", name="fnn-owner-lease-article-step"
        )[0].node
        actual = parsed.text[node.start:node.end]
        script = """
(defstruct fnn-lease id inc op (n 0))
(defvar *begin-inc* nil)
(defun fnn-live-rtc-st () :state)
(defun fnn-owner-lease-sent-locked (lease outcome) (declare (ignore lease outcome)))
(defun fnn-call (subject &rest args)
  (declare (ignore args))
  (assert (eq subject 'fn-hld-begin))
  (list :state nil *begin-inc* nil))
(defun fnn-fault (&rest args) (error "unexpected fault: ~s" args))
""" + actual + """
(let ((*begin-inc* :rtc-slots-exhausted))
  (assert (equal (fnn-owner-lease-article-step 7 (make-fnn-lease) :plan)
                 '(:refused :rtc-slots-exhausted))))
(let ((*begin-inc* nil))
  (assert (equal (fnn-owner-lease-article-step 7 (make-fnn-lease) :plan)
                 '(:wait))))
(format t "RTC-U64 terminal/wait PASS~%")
"""
        result = subprocess.run(
            [SBCL, "--noinform", "--dynamic-space-size", "256", "--script", "/dev/stdin"],
            cwd=ROOT, input=script, text=True, capture_output=True, timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("RTC-U64 terminal/wait PASS", result.stdout)

    def test_render_terminal_branch_calls_named_refusal(self):
        source = (ROOT / "host/native/owner.lisp").read_text()
        start = source.index("(defun fnn-owner-render-next-quantum ")
        end = source.index("\n(defun ", start + 1)
        parsed = lisp_rewrite.parse(source[start:end])
        cases = [hit.node for hit in lisp_rewrite.match(None, parsed.forms, head="case")
                 if parsed.text[hit.node.items[1].start:hit.node.items[1].end] == "(car article)"]
        self.assertTrue(cases)
        case = parsed.text[cases[0].start:cases[0].end]
        filters = [hit.node for hit in lisp_rewrite.match(None, parsed.forms, head="if")
                   if "(car attempt)" in parsed.text[hit.node.items[1].start:hit.node.items[1].end]]
        self.assertTrue(filters)
        admission = parsed.text[filters[0].start:filters[0].end]
        io = (ROOT / "host/native/io.lisp").read_text()
        definitions = []
        for head, name in (("define-condition", "fnn-store-error"), ("defun", "fnn-refuse")):
            first = io.index(f"({head} {name} ")
            last = io.index("\n(", first + 1)
            definitions.append(io[first:last])
        script = "\n".join(definitions) + """
(defvar *yield-count* 0)
(defun fnn-make-octets (n) (incf *yield-count*) (make-array n))
(handler-case
    (block fnn-owner-render-next-quantum
      (let ((article (let ((attempt '(:refused :rtc-slots-exhausted))
                            (service :service) (cid 7))
""" + admission + """)) (plan :plan))
""" + case + """
        (error "terminal returned instead of refusing")))
  (fnn-store-error (c)
    (assert (search "rtc-slots-exhausted:" (fnn-message c)))))
(assert (zerop *yield-count*))
(let ((result (multiple-value-list
                (block fnn-owner-render-next-quantum
                  (let ((article '(:wait)) (plan :plan))
""" + case + """)))))
  (assert (eq (fourth result) t)))
(assert (= *yield-count* 1))
(format t "RTC-U64 refusal/no-yield PASS~%")
"""
        result = subprocess.run(
            [SBCL, "--noinform", "--dynamic-space-size", "256", "--script", "/dev/stdin"],
            cwd=ROOT, input=script, text=True, capture_output=True, timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("RTC-U64 refusal/no-yield PASS", result.stdout)
