"""Current allocator source evaluated on a published developer image.

The saved image supplies existing core/host machinery. Current new definitions
and exact native allocator forms are loaded for this test only. This exercises
the changed adapter; it is not a qualification of a rebuilt current image.
"""
import re
import unittest
from pathlib import Path

from tools.proof_repl import forms
from tests.native_harness import Acl2Session, native_image, requires

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
ROOT = Path(__file__).resolve().parent.parent


def definition(path, name):
    for form in forms((ROOT / path).read_text()):
        if re.match(r"\(defun\s+" + re.escape(name) + r"\s", form, re.I):
            return form
    raise AssertionError((path, name))


@requires(IMAGE)
class NativeIdentityReserveTests(unittest.TestCase):
    def test_current_gate_and_actual_native_allocator(self):
        with Acl2Session(IMAGE) as session:
            for path in ("books/store-identity-reserve.lisp",
                         "tests/acl2/store-identity-reserve-tests.lisp"):
                for form in forms((ROOT / path).read_text()):
                    if not re.match(r"\((defun|defconst|assert-event)\s", form, re.I):
                        continue
                    result = session.call(form)
                    self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
                    self.assertNotIn(b"******** FAILED ********", result, result.decode(errors="replace"))
            result = session.call(definition("host/store-node-host.lisp",
                                             "fn-store-sn-identity-reservation"))
            self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))

            for form in ("(assign fn-store-sn *idr-near*)",
                         "(assign fn-store-sn-record-debt nil)"):
                result = session.call(form)
                self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
            native = "\n".join(definition("host/native/io.lisp", name) for name in
                               ("fnn-bridge-identity-reservation", "fnn-log-reserve"))
            # The trust tag is restricted to evaluating the actual CL adapter
            # forms in a test process; no production proof uses it.
            result = session.call("""(defttag :identity-reserve-adapter-test)""")
            self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
            result = session.call("""(progn!
 (set-raw-mode t)
""" + native + """
 (defvar *fnn-identity-reservation-callback* #'fnn-bridge-identity-reservation)
 (let* ((log (%make-fnn-log :kernel (fn-lgc-make 0 nil 0 0 nil nil 0 :idle)))
        ;; Reservation performs no filesystem syscall. The live-writer
        ;; premise is supplied; disk durability is outside this test.
        (store (%make-fnn-store :writable t :lock-fd 1
                    :frontier *idr-frontier* :log log)))
   (unless (= (fnn-log-reserve store *idr-frontier*) (+ 1 *idr-frontier*))
     (error "ordinary reservation did not issue exactly one identity"))
   (unless (eq (fnn-bridge-refuse-reservation) :refused)
     (error "actual core did not consume post-reservation refusal"))
   (let ((before (fnn-store-frontier store))
         (kernel (fnn-log-kernel log)) (refused nil))
     (handler-case (fnn-log-reserve store before)
       (fnn-store-error (e)
         (unless (search "reserved for promised releases" (fnn-message e))
           (error e))
         (setf refused t)))
     (unless (and refused (= before (fnn-store-frontier store))
                  (equal kernel (fnn-log-kernel log))
                  (not (fnn-store-fenced store)))
       (error "quota refusal mutated or fenced the allocator")))
   (format t "~&IDR-NATIVE-RESULT PASS~%"))
 (set-raw-mode nil))""")
            self.assertIn(b"IDR-NATIVE-RESULT PASS", result, result.decode(errors="replace"))
            self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))

    def test_actual_owner_prepare_consumes_exact_grant(self):
        with Acl2Session(IMAGE) as session:
            for path in ("books/store-identity-reserve.lisp",
                         "tests/acl2/store-identity-reserve-tests.lisp"):
                for form in forms((ROOT / path).read_text()):
                    if not re.match(r"\((defun|defconst)\s", form, re.I):
                        continue
                    result = session.call(form)
                    self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
            result = session.call("(set-ld-redefinition-action '(:doit . :overwrite) state)")
            self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
            result = session.call(definition("host/owner-host.lisp", "fn-owner-prepare-retention"))
            self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
            for form in (
                """(assign fn-owner
                  (fn-ocfg-make
                    (fn-own-make *idr-reserved* nil nil 0 1 nil nil nil nil
                                 nil nil nil nil nil nil)
                    (fn-cfg-initial) nil nil))""",
                "(assign fn-owner-identity-grant nil)",
                """(mv-let (erp word state)
                   (fn-owner-prepare-retention :release
                      (fn-record-string-octets "work-1")
                      (fn-record-string-octets "subject-1")
                      (fn-record-string-octets "receipt-1") 0 fn-arena state)
                   (declare (ignore erp))
                   (mv nil (and (eq word :refused)
                                (null (f-get-global 'fn-owner-identity-grant state))
                                (eq (fn-sf-phase (fn-sn-files (fn-owner-store state))) :reserved))
                       state))""",
            ):
                result = session.call(form)
                self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
            self.assertRegex(result, rb"\sT\s+ACL2")
            session.call("(assign fn-owner-identity-grant *idr-grant*)")
            result = session.call("""(mv-let (erp word state)
                (fn-owner-prepare-retention :release
                   (fn-record-string-octets "work-1")
                   (fn-record-string-octets "subject-1")
                   (fn-record-string-octets "receipt-1") 0 fn-arena state)
                (declare (ignore erp))
                (mv nil (and (eq word :prepared)
                             (null (f-get-global 'fn-owner-identity-grant state))
                             (eq (fn-sf-phase (fn-sn-files (fn-owner-store state))) :record-staged))
                    state))""")
            self.assertNotIn(b"ACL2 Error", result, result.decode(errors="replace"))
            self.assertRegex(result, rb"\sT\s+ACL2")
