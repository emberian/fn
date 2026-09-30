; Literal constructor/domain witnesses. These do not issue a request or RX
; custody receipt and are not a serialized producer reachability claim.
(in-package "ACL2")
(include-book "../../books/index-reader-step")
(assert-event
 (let ((result (fn-own-tls-make-result 6 nil nil nil)))
  (and (true-listp (fn-own-tls-result-effects result))
       (true-listp nil)
       (or (null nil) (fn-cbor-octet-listp nil))
       (fn-splan-step-p (fn-irr-step-from-read-result result nil nil nil nil nil))
       (equal (fn-splan-step-consumed
               (fn-irr-step-from-read-result result nil nil nil nil nil))
              (nfix (fn-own-tls-result-consumed result))))))
; Literal hypothesis removals: every retained premise and failed conclusion.
(assert-event
 (let ((result (fn-own-tls-make-result 6 'bad-effects nil nil)))
  (and (not (true-listp (fn-own-tls-result-effects result)))
       (true-listp nil)
       (or (null nil) (fn-cbor-octet-listp nil))
       (not (fn-splan-step-p (fn-irr-step-from-read-result result nil nil nil nil nil))))))
(assert-event
 (let ((result (fn-own-tls-make-result 6 nil nil nil)))
  (and (true-listp (fn-own-tls-result-effects result))
       (not (true-listp 'bad-lines))
       (or (null nil) (fn-cbor-octet-listp nil))
       (not (fn-splan-step-p
             (fn-irr-step-from-read-result result nil nil nil 'bad-lines nil))))))
(assert-event
 (let ((result (fn-own-tls-make-result 6 nil nil nil)))
  (and (true-listp (fn-own-tls-result-effects result))
       (true-listp nil)
       (not (or (null '(300)) (fn-cbor-octet-listp '(300))))
       (not (fn-splan-step-p
             (fn-irr-step-from-read-result result nil nil nil nil '(300)))))))
(assert-event
 (let ((result (fn-own-tls-make-result -1 nil nil nil)))
  (equal (fn-splan-step-consumed (fn-irr-step-from-read-result result nil nil nil nil nil))
         (nfix (fn-own-tls-result-consumed result)))))
