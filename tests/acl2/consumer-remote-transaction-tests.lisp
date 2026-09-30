(in-package "ACL2")
(include-book "../../books/consumer-transaction-dispatch")
(assert-event
 (let* ((local (fn-cpe-make 1 2 3 '(:bootstrap (104) (105))))
        (authority '(:consumer-authority 1 2 3 (:authority-begin (99) 0 1 0)))
        (binding (list :consumer-authority 1 2 3
                  (fn-cab-operation '(99) 0 '(97) 0 1 *fn-cab-zero-principal*)))
        (remote '(:consumer 1 2 3 (:remote-register (99) (112) (99) 1 2 1 ((97) (98)) (65)))))
  (and (equal (fn-cne-decode-exact (fn-cpe-encode local)) (list :ok local))
       (equal (fn-cne-decode-exact (fn-cac-encode authority)) (list :ok authority))
       (equal (fn-cne-decode-exact (fn-cab-encode binding)) (list :ok binding))
       (equal (fn-cne-decode-exact (fn-crev-encode-reference remote)) (list :ok remote))
       (equal (fn-cne-decode-exact '(102 110 99 101 5 6)) '(:error :consumer-envelope-version))
       (not (eq (car (fn-cne-decode-exact '(70 78 67 84 4 6))) :ok)))))

; Complete logical recovery recognition includes the ordered query; fixed
; head alone cannot admit malformed/duplicate/unordered/empty groups.
(assert-event
 (let* ((op '(:remote-register (99) (112) (99) 1 2 1 ((97) (98)) (65)))
        (remote (list :consumer 1 2 3 op))
        (duplicate (list :consumer 1 2 3
                    '(:remote-register (99) (112) (99) 1 2 1 ((97) (97)) (65))))
        (unordered (list :consumer 1 2 3
                    '(:remote-rebase (99) (112) (99) 1 2 1 ((98) (97)) (65))))
        (empty (list :consumer 1 2 3
                    '(:remote-register (99) (112) (99) 1 2 1 nil (65))))
        (bad (list :consumer 1 2 3
                    '(:remote-register (99) (112) (99) 1 2 1 ((0)) (65)))))
  (and (fn-crev-eventp remote)
       (fn-crev-result-okp (fn-crev-decode-exact (fn-crev-encode-reference remote)))
       (fn-crev-headp duplicate) (not (fn-crev-eventp duplicate))
       (not (fn-crev-eventp unordered)) (not (fn-crev-eventp empty))
       (not (fn-crev-eventp bad))
       (null (fn-crev-encode-reference duplicate))
       (null (fn-crev-encode-reference unordered))
       (null (fn-crev-encode-reference empty))
       (null (fn-crev-encode-reference bad)))))
