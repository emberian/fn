(in-package "ACL2")
(include-book "../../books/byte-store-fault-keystones")
(include-book "../../books/byte-store-frame")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-bsfk-groups* '("fn.letters" "fn.test"))
(defconst *fn-bsfk-capacity* 10)
(defconst *fn-bsfk-record*
  (fn-record-make 0 0 0 "<k7@example.invalid>" '(90)
                  *fn-bsfk-groups* "archive" "subject" "evidence" 2))
(defconst *fn-bsfk-frontier-run*
  (fn-bs-run *fn-bs-initialized-store* (fn-sf-initial-state)
             *fn-bs-p-frontier* nil *fn-bsfk-groups* *fn-bsfk-capacity*))
(defconst *fn-bsfk-reserved* (cdr (car (last *fn-bsfk-frontier-run*))))
(defconst *fn-bsfk-staged*
  (fn-sf-prepare-record *fn-bsfk-reserved* *fn-bsfk-record*
                        *fn-bsfk-groups* *fn-bsfk-capacity*))
(defconst *fn-bsfk-record-run*
  (fn-bs-run (car (car (last *fn-bsfk-frontier-run*))) *fn-bsfk-staged*
             *fn-bs-p-record* nil *fn-bsfk-groups* *fn-bsfk-capacity*))

; Reachable non-degenerate witness at record-linked: one pending final-name
; operation, an uncertain kernel phase, and recovery's directory fence drains
; the exact operation.
(assert-event
 (let* ((pair (nth 8 *fn-bsfk-record-run*))
        (bs (car pair))
        (ks (cdr pair)))
   (and (equal (fn-sf-phase ks) :record-data-durable)
        (not (fn-bs-dir-quietp bs :transactions))
        (fn-sf-fencedp (fn-sf-record-link-result ks :error))
        (fn-bs-dir-quietp (fn-bs-fence-dir bs :transactions) :transactions))))

; Without an issued operation there is nothing for recovery to drain.
(must-fail
 (assert-event
  (mv-let (result bs)
    (fn-bs-link (car (nth 6 *fn-bsfk-record-run*)) :staging ".stage-1"
                :transactions "00000000000000000000.txn"
                (cons :eio :not-issued))
    (declare (ignore result))
    (not (fn-bs-dir-quietp bs :transactions)))))
