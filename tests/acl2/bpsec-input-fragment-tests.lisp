(in-package "ACL2")
(include-book "../../books/bpsec-input-fragment")
(defconst *fn-bpsif-op*
 (fn-bps-op-make :verify-bib '(:bps-ref 1 1) '(:bps-ref 2 1) '(:bps-ref 3 1)
  '(:bps-ref 4 1) 2 1 1 '(:bps-bib-params 7 0 nil) '(:bps-ref 5 1)
  '(:bytes-span 9 0 64)))
(assert-event
 (and (fn-bps-opp *fn-bpsif-op*)
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0 88 35)) 0 1)
       (list :bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0)) 1 1))
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0 88 35)) 1 64)
       (list :bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (88 35)) 2 3))))
(assert-event
 (and (fn-bps-input-spanp '(:bps-span (:bps-ref 9 1) 4294967296 1099511627776))
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac
               '(:bps-span (:bps-ref 9 1) 4294967296 1099511627776) 1099511627712 64)
       (list :bps-input-fragment *fn-bpsif-op* :hmac
        '(:bps-span (:bps-ref 9 1) 1103806595008 64) 64 1099511627776))))
(assert-event
 (and (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0)) 0 0)
             (list :yield *fn-bpsif-op* :hmac))
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0)) 1 0)
             (list :input-complete *fn-bpsif-op* :hmac))))
(assert-event
 (and (equal (fn-bps-input-fragment *fn-bpsif-op* :ciphertext '(:bps-literal (0)) 0 1)
             '(:refused :input-role))
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0)) 2 1)
             '(:refused :input-offset))
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0)) 0 65)
             '(:refused :input-quantum))))
; Corrupted command/profile witnesses, not genuine issued input records.
(assert-event
 (and (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (256)) 0 1)
             '(:refused :input-command))
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac
               (list :bps-literal (make-list 28 :initial-element 0)) 0 1)
             '(:refused :input-command))
      (equal (fn-bps-input-fragment *fn-bpsif-op* :hmac '(:bps-literal (0 . 1)) 0 1)
             '(:refused :input-command))
      (equal (fn-bps-input-fragment nil :hmac '(:bps-literal (0)) 0 1)
             '(:refused :invalid-descriptor))))
(assert-event
 (and (eq (symbol-class 'fn-bps-input-literal-length (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-command-length (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-literal-window (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-input-fragment (w state)) :common-lisp-compliant)))
(assert-event
 (let ((op (fn-bps-op-make :decrypt-bcb '(:bps-ref 11 1) '(:bps-ref 2 1) '(:bps-ref 3 1)
             '(:bps-ref 4 1) 2 1 2
             '(:bps-bcb-params 1 0 (:bytes-span 9 0 12) nil :separate-tag)
             '(:bps-ref 15 1) '(:bytes-span 9 0 16))))
  (and (fn-bps-opp op)
       (equal (fn-bps-input-fragment op :aad '(:bps-literal (0)) 0 64)
        (list :bps-input-fragment op :aad '(:bps-literal (0)) 1 1))
       (equal (fn-bps-input-fragment op :ciphertext '(:bps-span (:bps-ref 9 1) 129 35) 34 64)
        (list :bps-input-fragment op :ciphertext '(:bps-span (:bps-ref 9 1) 163 1) 1 35))
       (equal (fn-bps-input-fragment op :ciphertext '(:bps-literal (0)) 0 64)
              '(:refused :input-command)))))
; Complete antecedent/conclusion for the literal count-bound theorem.
(assert-event
 (let ((result (fn-bps-input-fragment *fn-bpsif-op* :hmac
                '(:bps-span (:bps-ref 9 1) 129 35) 7 7)))
  (and (fn-bps-opp *fn-bpsif-op*)
       (eq (fn-bps-field 0 result) :bps-input-fragment)
       (natp (fn-bps-field 4 result)) (< 0 (fn-bps-field 4 result))
       (<= (fn-bps-field 4 result) (nfix 7)) (<= (fn-bps-field 4 result) 64)
       (equal (fn-bps-field 5 result) (+ (nfix 7) (fn-bps-field 4 result))))))
; Sole-hypothesis removal: actual refused role has no positive fragment count.
; No retained theorem hypotheses; valid descriptor/command affirm reachability.
(assert-event
 (let ((result (fn-bps-input-fragment *fn-bpsif-op* :ciphertext
                '(:bps-span (:bps-ref 9 1) 129 35) 7 7)))
  (and (fn-bps-opp *fn-bpsif-op*)
       (fn-bps-input-spanp '(:bps-span (:bps-ref 9 1) 129 35))
       (not (eq (fn-bps-field 0 result) :bps-input-fragment))
       (not (natp (fn-bps-field 4 result))))))
