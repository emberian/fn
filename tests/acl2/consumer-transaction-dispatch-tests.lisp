(in-package "ACL2")
(include-book "../../books/consumer-transaction-dispatch")

(defconst *cnet-local*
 (fn-cpe-make 0 1 0 (list :bootstrap (make-list 32 :initial-element 1)
                                    (make-list 32 :initial-element 2))))
(defconst *cnet-authority*
 '(:consumer-authority 1 2 0 (:authority-begin (65) 0 1 7)))
(defconst *cnet-binding*
 (list :consumer-authority 2 3 0
       (fn-cab-operation '(65) 0 '(98) 0 2 (make-list 32 :initial-element 9))))
;@mutation-witness existing-v1-is-not-routed-to-authority-v2
(assert-event
 (and (fn-cpe-eventp *cnet-local*)
      (not (eq (fn-cp-nth 0 (fn-cac-decode-exact (fn-cpe-encode *cnet-local*))) :ok))
      (equal (fn-cne-decode-exact (fn-cpe-encode *cnet-local*)) (list :ok *cnet-local*))))
;@positive-witness fn-cae-event-shape
(assert-event
 (and (fn-cae-eventp *cnet-binding*) (true-listp *cnet-binding*)
      (equal (len *cnet-binding*) 5) (consp *cnet-binding*)
      (equal (car *cnet-binding*) :consumer-authority)
      (natp (fn-cp-nth 1 *cnet-binding*)) (natp (fn-cp-nth 2 *cnet-binding*))
      (natp (fn-cp-nth 3 *cnet-binding*))))
;@hyp-removal-witness fn-cae-event-shape omitted=authority-event
(assert-event
 (let ((bad '(:consumer-authority bad-count 3 0 nil)))
  (and (not (fn-cae-eventp bad))
       (not (and (true-listp bad) (equal (len bad) 5) (consp bad)
                 (equal (car bad) :consumer-authority)
                 (natp (fn-cp-nth 1 bad)) (natp (fn-cp-nth 2 bad))
                 (natp (fn-cp-nth 3 bad)))))))
;@mutation-witness account-v2-and-binding-v3-remain-exactly-distinct
(assert-event
 (and (equal (fn-cne-decode-exact (fn-cae-encode *cnet-authority*))
             (list :ok *cnet-authority*))
      (fn-cac-eventp *cnet-authority*) (fn-cab-eventp *cnet-binding*)
      (equal (fn-cne-decode-exact (fn-cae-encode *cnet-binding*))
             (list :ok *cnet-binding*))
      (not (fn-cac-eventp *cnet-binding*)) (not (fn-cab-eventp *cnet-authority*))))
;@mutation-witness reserved-version-and-malformed-binding-refuse
(assert-event
 (and (equal (fn-cne-decode-exact '(102 110 99 101 4 6))
             '(:error :remote-consumer-decoder-unavailable))
      (equal (fn-cne-decode-exact '(102 110 99 101 9 6))
             '(:error :consumer-envelope-version))
      (not (eq (fn-cp-nth 0 (fn-cne-decode-exact '(102 110 99 101 3 7))) :ok))))
