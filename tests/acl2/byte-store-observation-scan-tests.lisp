(in-package "ACL2")
(include-book "../../books/byte-store-observation-scan")
(include-book "../../books/byte-store-frame")
(include-book "../../books/byte-store-txn-name")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bso-event-0*
  (fn-record-make 0 0 0 "<bso-0@example.invalid>" '(65)
                  '("fn.letters") "archive" "subject" "evidence" 1 :legacy))
(defconst *bso-event-1*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "obligation-1" "article-0" "local" 1))

; These are functions because ACL2 does not evaluate codec attachments while
; admitting a defconst.  The two records give the scanner real frame work.
(defun bso-frame-0 ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind* (fn-store-event-encode *bso-event-0*)))
(defun bso-frame-1 ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind* (fn-store-event-encode *bso-event-1*)))

(defun bso-model ()
  (fn-bs-make 4
              (list (cons 10 (fn-bs-initial-config-octets))
                    (cons 11 (fn-bs-frontier-encode 2))
                    (cons 12 (bso-frame-0))
                    (cons 13 (bso-frame-1)))
              (list (cons :root
                          (list (cons *fn-bs-scan-config-name* 10)
                                (cons *fn-bs-scan-frontier-name* 11)))
                    (cons :transactions
                          (list (cons (fn-bs-txn-name 0) 12)
                                (cons (fn-bs-txn-name 1) 13)))
                    (cons :staging nil)) nil 14))

(defun bso-physical ()
  (fn-bs-make 4
              (list (cons 110 (fn-bs-initial-config-octets))
                    (cons 111 (fn-bs-frontier-encode 2))
                    (cons 112 (bso-frame-0))
                    (cons 113 (bso-frame-1)))
              (list (cons :root
                          (list (cons *fn-bs-scan-config-name* 110)
                                (cons *fn-bs-scan-frontier-name* 111)))
                    (cons :transactions
                          (list (cons (fn-bs-txn-name 0) 112)
                                (cons (fn-bs-txn-name 1) 113)))
                    (cons :staging nil)) nil 114))

(defun bso-corrupt ()
  (fn-bs-make 4
              (cons (cons 113 '(1 2)) (remove-assoc-equal 113 (fn-bs-inodes (bso-physical))))
              (fn-bs-dirs (bso-physical)) nil 114))

(defun bso-reordered ()
  (fn-bs-make 4 (fn-bs-inodes (bso-physical))
              (list (car (fn-bs-dirs (bso-physical)))
                    (cons :transactions
                          (reverse (cdr (assoc-equal :transactions
                                                     (fn-bs-dirs (bso-physical))))))
                    (cons :staging nil)) nil 114))

; Non-degenerate theorem witness: two decoded transactions, physical inode
; renaming, and the exact same successful scan.
(assert-event
 (and (fn-bso-served-image-agree (bso-model) (bso-physical))
      (equal (fn-bs-names (bso-model) :transactions)
             (fn-bs-names (bso-physical) :transactions))
      (fn-bs-scan-okp (fn-bs-scan-store (bso-model)))
      (equal (len (fn-bs-scan-records (fn-bs-scan-store (bso-model)))) 2)
      (equal (fn-bs-scan-store (bso-model))
             (fn-bs-scan-store (bso-physical)))))

; Without the visible relation, exact ordered names and a good source scan
; do not stop a damaged transaction frame from changing the scan.
(must-fail
 (assert-event
  (implies (and (equal (fn-bs-names (bso-model) :transactions)
                       (fn-bs-names (bso-corrupt) :transactions))
                (fn-bs-scan-okp (fn-bs-scan-store (bso-model))))
           (equal (fn-bs-scan-store (bso-model))
                  (fn-bs-scan-store (bso-corrupt))))))

; Without ordered transaction names, the same exact octets and alias pattern
; may fail the scanner's canonical namespace check.
(must-fail
 (assert-event
  (implies (and (fn-bso-served-image-agree (bso-model) (bso-reordered))
                (fn-bs-scan-okp (fn-bs-scan-store (bso-model))))
           (equal (fn-bs-scan-store (bso-model))
                  (fn-bs-scan-store (bso-reordered))))))

(defun bso-duplicate-root-model ()
  (fn-bs-make 4 '((1 . (65)))
              '((:root . (("x" . 1) ("x" . 1)))
                (:transactions) (:staging)) nil 2))
(defun bso-duplicate-root-physical ()
  (fn-bs-make 4 (list (cons 73 '(65))
                      (cons 74 (fn-bs-initial-config-octets)))
              '((:root . (("x" . 73) ("config.json" . 74)))
                (:transactions) (:staging)) nil 75))

; The scan-ok premise excludes malformed duplicate-name roots: a set/count
; observation alone cannot detect the extra physical key in this input.
(must-fail
 (assert-event
  (implies (and (fn-bso-served-image-agree
                 (bso-duplicate-root-model) (bso-duplicate-root-physical))
                (equal (fn-bs-names (bso-duplicate-root-model) :transactions)
                       (fn-bs-names (bso-duplicate-root-physical) :transactions)))
           (equal (fn-bs-scan-store (bso-duplicate-root-model))
                  (fn-bs-scan-store (bso-duplicate-root-physical))))))
