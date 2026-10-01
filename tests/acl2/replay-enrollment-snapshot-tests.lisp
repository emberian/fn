; Literal actual public boundary witnesses; no native/grant qualification.
(in-package "ACL2")
(include-book "../../books/replay-enrollment-snapshot-refinement")
(include-book "../../books/statement-attach")
(defun fn-rses-test-repeat (n byte)
 (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons byte (fn-rses-test-repeat (1- n) byte))))
(defun fn-rses-test-result (snapshot)
 (declare (xargs :guard t :verify-guards nil))
 (let ((begin (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))))
  (fn-sic-result (fn-sic-run (fn-sic-completion-cost begin) begin))))
(defconst *fn-rses-test-principal* (fn-rses-test-repeat 32 11))
(defconst *fn-rses-test-ed* (fn-rses-test-repeat 32 21))
(defconst *fn-rses-test-ml* (fn-rses-test-repeat 1952 31))
(defconst *fn-rses-test-payload*
 (append '(88 32) *fn-rses-test-principal* '(1 88 32)
         *fn-rses-test-ed* '(2 89 7 160) *fn-rses-test-ml*))
(defconst *fn-rses-test-snapshot*
 (fn-stxk-make 0 0 0 7 *fn-hsig-profile-tag* *fn-rses-test-payload*))
; All retained hypotheses and complete actual public value, with actual tail
; custody and exact actual field contents, not only boolean acceptance.
(assert-event
 (let* ((snapshot *fn-rses-test-snapshot*)
        (spans (fn-rse-result-spans (fn-rses-test-result snapshot))))
  (and (fn-stxk-p snapshot) spans
       (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
       (equal (fn-hsig-keyring-snapshot-value snapshot)
              (fn-rse-enrollment-model spans))
       (equal (fn-hsig-keyring-snapshot-value snapshot)
              (list *fn-rses-test-principal*
               (list (cons :ed25519 *fn-rses-test-ed*)
                     (cons :ml-dsa-65 *fn-rses-test-ml*))))
       (equal (fn-rse-span-tail (fn-rsc-at 0 spans))
              (nthcdr 2 *fn-rses-test-payload*))
       (equal (fn-rse-span-tail (fn-rsc-at 1 spans))
              (nthcdr 37 *fn-rses-test-payload*))
       (equal (fn-rse-span-tail (fn-rsc-at 2 spans))
              (nthcdr 73 *fn-rses-test-payload*)))))
; Corrupted-state removal of typed snapshot: all other hypotheses true.
(assert-event
 (let* ((snapshot (fn-stxk-make :bad 0 0 7 *fn-hsig-profile-tag*
                               *fn-rses-test-payload*))
        (spans (fn-rse-result-spans (fn-rses-test-result snapshot))))
  (and (not (fn-stxk-p snapshot)) spans
       (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
       (not (equal (fn-hsig-keyring-snapshot-value snapshot)
                   (fn-rse-enrollment-model spans))))))
; Removal of profile selection, with actual valid snapshot and spans.
(assert-event
 (let* ((snapshot (fn-stxk-make 0 0 0 7 '(0) *fn-rses-test-payload*))
        (spans (fn-rse-result-spans (fn-rses-test-result snapshot))))
  (and (fn-stxk-p snapshot) spans
       (not (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*))
       (not (equal (fn-hsig-keyring-snapshot-value snapshot)
                   (fn-rse-enrollment-model spans))))))
; Removal of selected spans: the one-item actual payload has no enrollment.
(assert-event
 (let* ((snapshot (fn-stxk-make 0 0 0 7 *fn-hsig-profile-tag* '(0)))
        (spans (fn-rse-result-spans (fn-rses-test-result snapshot))))
  (and (fn-stxk-p snapshot) (not spans)
       (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
       (not (equal (fn-hsig-keyring-snapshot-value snapshot)
                   (fn-rse-enrollment-model spans))))))
; Exhausted scheduling work preserves the original borrowed payload and does
; not manufacture a parsed result or enrollment.
(assert-event
 (let ((begin (fn-sic-begin-legacy 5 *fn-rses-test-payload*)))
  (and (equal (fn-sic-run 0 begin) begin)
       (eq (fn-sic-result begin) :pending)
       (not (fn-rse-result-spans (fn-sic-result begin))))))

; Arbitrary scheduled terminal transport uses the actual step run, not a
; producer call to the ghost completion-cost reference.
(assert-event
 (let* ((snapshot *fn-rses-test-snapshot*)
        (parser (fn-sic-run 5000 (fn-sic-begin-legacy 5 (fn-stxk-snapshot snapshot))))
        (spans (fn-rse-result-spans (fn-sic-result parser))))
  (and (natp 5000) (fn-stxk-p snapshot)
       (equal (fn-sic-at 0 parser) :done) spans
       (equal (fn-stxk-profile snapshot) *fn-hsig-profile-tag*)
       (equal (fn-hsig-keyring-snapshot-value snapshot)
              (fn-rse-enrollment-model spans)))))
(assert-event
 (let* ((begin (fn-sic-begin-legacy 5 *fn-rses-test-payload*))
        (parser (fn-sic-run 1 begin)))
  (and (eq (fn-sic-result parser) :pending)
       (equal (fn-sic-at 1 parser) *fn-rses-test-payload*)
       (equal (fn-sic-run 4999 parser) (fn-sic-run 5000 begin)))))
