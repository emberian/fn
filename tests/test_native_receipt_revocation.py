"""Current receipt authority after actual Store revocation in a saved image.

The image evaluates all semantic fixtures. Primitive observations are abstract;
this is not a network signature, owner serialization, or qualification claim.
"""
import unittest
from pathlib import Path

from tools.proof_repl import forms

from tests.native_harness import Acl2Session, acl2_boolean, native_image, requires

IMAGE = native_image("FN_NATIVE_DTN_DEVELOPER_HOST")


@requires(IMAGE)
class NativeReceiptRevocationTests(unittest.TestCase):
    def test_durable_revocation_refuses_old_signature_observations(self):
        with Acl2Session(IMAGE) as session:
            session.call("""(defun rr-native-reserve (s)
              (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                      :frontier-file :ok) :frontier-replace :ok)
                        :frontier-directory :ok))""")
            session.call("""(defun rr-native-publish (s)
              (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                     :record-link :ok) :record-directory :ok))""")
            session.call("""(defun rr-native-commit (s e)
              (fn-sn-finish (rr-native-publish
                (fn-sn-prepare-identity (rr-native-reserve s) e))))""")
            result = session.call("""
(let* ((principal (make-list 32 :initial-element 7))
       (ed (make-list 32 :initial-element 1))
       (ml (make-list 1952 :initial-element 2))
       (keys (list (cons :ed25519 ed) (cons :ml-dsa-65 ml)))
       (e (fn-hsig-keyring-event 0 0 0 1 principal keys))
       (enrolled (rr-native-commit (fn-sn-initial '("fn.test") 16) e))
       (wire (fn-record-make 1 1 1 "<receipt-revoke@example>" '(65 66)
               '("fn.test") "archive-pin" "subject-1" "release-1" 2 841000000))
       (before (fn-sn-finish (rr-native-publish
                  (fn-sn-prepare (rr-native-reserve enrolled) (fn-held-plain wire 0)))))
       (tomb (fn-hl-revoke-event 2 2 2 2 principal
                                (fn-sn-keyring-snapshots before)))
       (completing (rr-native-publish
                    (fn-sn-prepare-identity (rr-native-reserve before) tomb)))
       (after (fn-sn-finish completing))
       (adu (fn-bpa-encode (fn-bpa-make-receipt
              "receipt-1" "work-1" "subject-1" "dtn://issuer/" "dtn://issuer/"
              "policy-1" "incarnation-1" "authorization-1" "terms-1")))
       (signed (fn-bpsr-encode (fn-bpsr-make adu principal
                   (make-list 64 :initial-element 3)
                   (make-list 3309 :initial-element 4))))
       (view (list :delivery '("k" "b") :receipt signed
              (list :cl (cons 3 1) 1
                    (cons :dtn (fn-record-string-octets "//issuer/"))
                    (fn-record-string-octets "issuer") 7)
              nil "dtn://issuer/" "dtn://home/"))
       (rows (list
              (fn-cfg-row-make "issuer" "path-identity" "issuer.example" 0)
              (fn-cfg-row-make "issuer" "auth-principal" "bp-only" 0)
              (fn-cfg-row-make "issuer" "transport-bp" "dtn://issuer/" 0)
              (fn-cfg-row-make "issuer" "bp-trust" "network" 0)
              (fn-cfg-row-make "issuer" "bp-boundary-listener" "127.0.0.1" 4601)
              (fn-cfg-row-make "issuer" "bp-boundary-source" "127.0.0.1" 0)
              (fn-cfg-row-make "issuer" "bp-boundary-translation" "none" 0)
              (fn-cfg-row-make "issuer" "bp-boundary-originators" "all-co-resident" 0)
              (fn-cfg-row-make "issuer" "bp-boundary-receipt-signer"
                (fn-record-octets-string (fn-stx-hex-octets principal)) 0)))
       (cfg (fn-cfg-make 7 (fn-cfg-value-make nil 0 nil nil nil rows nil nil nil nil)))
       (obs (list ml :verified :verified)))
 (and e tomb (fn-cfgp cfg) (fn-sn-completion-enabledp completing)
      (equal (fn-sn-completion-record completing) tomb)
      (fn-bpah-receipt-gatep view cfg (fn-sn-keyring-snapshots before) obs)
      (not (fn-bpah-receipt-gatep view cfg (fn-sn-keyring-snapshots after) obs))
      (equal (fn-sn-keyring-snapshots after) (list tomb e))
      (equal (fn-sn-verdicts after) (fn-sn-verdicts before))
      (consp (fn-retain-pins (fn-node-retention (fn-sn-node before))))
      (equal (fn-node-retention (fn-sn-node after))
             (fn-node-retention (fn-sn-node before)))))
""")
            self.assertTrue(acl2_boolean(result), result.decode(errors="replace"))

    def test_literal_logical_witnesses_on_published_baseline(self):
        # These are test definitions and literal assertions, not a source load
        # or theorem admission. The image supplies all production functions.
        root = Path(__file__).resolve().parent / "acl2"
        with Acl2Session(IMAGE) as session:
            for name in ("held-rows-tests", "bp-release-authority-tests",
                         "store-identity-traces-tests", "receipt-revocation-tests"):
                for index, form in enumerate(forms((root / (name + ".lisp")).read_text())):
                    head = form.split(None, 1)[0].lower()
                    fixture = head in ("(defun", "(defconst", "(make-event")
                    witness = name == "receipt-revocation-tests" and head == "(assert-event"
                    if not fixture and not witness:
                        continue
                    output = session.call(form)
                    self.assertNotIn(b"ACL2 Error", output, (name, index, output.decode(errors="replace")))
                    self.assertNotIn(b"FAILED", output, (name, index, output.decode(errors="replace")))
