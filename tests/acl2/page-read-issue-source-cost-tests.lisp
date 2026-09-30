(in-package "ACL2")
(include-book "../../books/page-read-issue-source-cost")

; This helper calls the actual issuer, checking its complete three-value
; output against the observer as well as the explicit source roster.
(defun fn-prsc-test (budget used rescue charged next limit demand word cells adds)
 (declare (xargs :guard t))
 (let ((observation (fn-prsc-issue budget used rescue charged next limit demand)))
  (mv-let (actual issued total)
   (fn-prs-issue budget used rescue charged next limit demand)
   (and (equal actual word)
        (equal (fn-prsc-value observation) (list actual issued total))
        (equal (fn-prsc-cells observation) cells)
        (equal (len (fn-prsc-trace observation)) adds)))))

(assert-event
 (fn-prsc-test '(100 100 10 10 10) '(1 0 0 0 0) '(0 0 0 0 0)
               '(2 0 0 0 1) 1 10 '(3 0 0 0 1) :admitted 30 31))
(assert-event
 (fn-prsc-test '(100 100 10 10 10) '(1 0 0 0 0) '(0 0 0 0 0)
               '(2 0 0 0 1) 10 10 '(3 0 0 0 1) :read-identities-exhausted 10 10))
(assert-event
 (fn-prsc-test '(5 100 10 10 10) '(1 0 0 0 0) '(0 0 0 0 0)
               '(2 0 0 0 1) 1 10 '(3 0 0 0 1) :read-resources-unavailable 25 25))
; Explicit malformed input, not a reachable maintained-pool counterexample.
(assert-event
 (fn-prsc-test nil '(1 0 0 0 0) '(0 0 0 0 0)
               '(2 0 0 0 1) 1 10 '(3 0 0 0 1) :invalid-resource-state 0 0))
(assert-event
 (fn-prsc-test '(100 100 10 10 10) '(1 0 0 0 0) '(0 0 0 0 0)
               '(2 0 0 0 1) 1 10 '(3) :invalid-resource-state 10 10))
; Literal removal of the admitted-result premise: every other input remains
; well formed, but resources are refused and the asserted 30/31 fails.
(assert-event
 (let* ((b '(5 100 10 10 10)) (u '(1 0 0 0 0)) (r '(0 0 0 0 0))
        (c '(2 0 0 0 1)) (d '(3 0 0 0 1))
        (o (fn-prsc-issue b u r c 1 10 d)))
  (mv-let (word issued total) (fn-prs-issue b u r c 1 10 d)
   (and (fn-prs-fundedp b u r c) (fn-prs-vectorp d)
        (not (equal word :admitted)) (equal issued 1) (equal total c)
        (not (and (equal (fn-prsc-cells o) 30)
                  (equal (len (fn-prsc-trace o)) 31)))))))
; Full logical natural domain retained: no selected-machine cutoff is added.
(assert-event
 (fn-prsc-test (list (expt 2 102) 100 10 10 (expt 2 102))
               '(1 0 0 0 0) '(0 0 0 0 0)
               (list (expt 2 100) 0 0 0 1)
               (expt 2 100) (expt 2 101) '(3 0 0 0 1) :admitted 30 31))
