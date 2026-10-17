; Literal actual public boundary witnesses; no native/grant qualification.
(in-package "ACL2")
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

(assert-event
 (let* ((begin (fn-sic-begin-legacy 5 *fn-rses-test-payload*))
        (parser (fn-sic-run 1 begin)))
  (and (eq (fn-sic-result parser) :pending)
       (equal (fn-sic-at 1 parser) *fn-rses-test-payload*)
       (equal (fn-sic-run 4999 parser) (fn-sic-run 5000 begin)))))
