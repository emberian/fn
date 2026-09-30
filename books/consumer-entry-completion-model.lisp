; Exact model boundaries for the actual selected completion. These relations
; are proof-only; no whole CP/entry-table recognizer is called at publication.
(in-package "ACL2")
(include-book "consumer-entry-completion")
(include-book "consumer-progress-metadata")
(include-book "consumer-store-projection")

(local
 (defthm fn-cecm-scope-gate-is-original
  (equal (fn-cec-scope-matchp cp cursor old)
         (fn-cp-scope-matchp cp (fn-cp-nth 4 cursor) (fn-cp-nth 6 cursor)
                               (fn-cp-nth 7 cursor) cursor old))
  :hints (("Goal" :in-theory
   (e/d (fn-cec-scope-matchp fn-cp-scope-matchp fn-cp-cursorp)
        (fn-cp-nth fn-cp-idp fn-cp-uintp fn-cec-length-is))))))

; OLD/REMOVED must be the one prepared result from this CP. Fixed ACK-entry
; shape is maintained by the actual publication invariant, not revalidated.
(defthm fn-cecm-selected-local-is-actual-apply
 (implies
  (and (not (member-eq (fn-cp-nth 0 op) '(:remote-register :remote-rebase)))
       (equal old (fn-cp-find (fn-cep-operation-key op) (fn-cp-nth 5 cp)))
       (equal removed (fn-cp-remove (fn-cep-operation-key op) (fn-cp-nth 5 cp)))
       (implies (eq (fn-cp-nth 0 op) :ack)
                (or (equal (len old) 8) (equal (len old) 10))))
  (equal (fn-cp-nth 1 (fn-cec-selected-local cp op old removed))
         (fn-cp-apply cp op)))
 :hints (("Goal" :in-theory
  (e/d (fn-cec-selected-local fn-cp-apply fn-cep-operation-key member-equal fn-cp-nth)
       (fn-cp-find fn-cp-remove fn-cp-state-carry fn-cp-event-entry
        fn-cp-entry-with-ack fn-cp-scope-matchp fn-cp-cursorp
        fn-cp-idp fn-cp-uintp fn-cec-length-is fn-cec-scope-matchp)))))

(defthm fn-cecm-local-entry-constructor-carry
 (implies (and (fn-scc-octet-listp consumer) (fn-scc-octet-listp principal)
               (fn-scc-octet-listp query)
               (integerp qver) (integerp view) (integerp epoch) (integerp ack))
  (equal (fn-cec-local-entry-carry (fn-cp-entry consumer principal query qver view epoch ack))
         (fn-scs-summary (fn-cp-entry consumer principal query qver view epoch ack))))
 :hints (("Goal"
  :use ((:instance fn-caac-spine-keeps-canonical-size
    (cs (list (fn-caac-atom :entry)
              (fn-scs-octets (len consumer)) (fn-scs-octets (len principal))
              (fn-scs-octets (len query)) (fn-caac-atom qver)
              (fn-caac-atom view) (fn-caac-atom epoch) (fn-caac-atom ack)))
    (xs (list :entry consumer principal query qver view epoch ack))))
  :in-theory
  (e/d (fn-cec-local-entry-carry fn-cp-entry fn-cp-nth fn-scs-correspondsp
        fn-caac-atom)
       (fn-caac-spine fn-scs-summary fn-scs-octets fn-scs-atom)))))

(local
 (defthm fn-cecm-summary-generic-cons
  (implies (not (fn-scc-octet-listp (cons x y)))
   (equal (fn-scs-summary (cons x y))
          (list (+ 1 (car (fn-scs-summary x)) (car (fn-scs-summary y))) nil nil)))
  :hints (("Goal"
   :use ((:instance fn-scs-cons-preserves-canonical-size
           (a (fn-scs-summary x)) (d (fn-scs-summary y))))
   :in-theory (e/d (fn-scs-cons fn-scs-summary fn-scc-octet-listp)
                   (fn-scc-encode fn-scc-program))))))

(local
 (defthm fn-cecm-summary-octets-natural
  (natp (car (fn-scs-summary x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-scs-summary)))))

; Shared groups are not inspected or copied. The generic remote10 spine is
; what makes scalar delta sound; the local8 numeric suffix is excluded.
(defthm fn-cecm-remote-ack-retains-exact-carry
 (implies
  (and (not (fn-scc-octet-listp (list groups account)))
       (integerp ack) (integerp next-ack)
       (equal oldcarry
        (fn-scs-summary (append (fn-cp-entry consumer principal query qver view epoch ack)
                                (list groups account)))))
  (equal
   (fn-cec-remote-ack-carry
     (append (fn-cp-entry consumer principal query qver view epoch ack) (list groups account))
     oldcarry next-ack)
   (fn-scs-summary
    (append (fn-cp-entry consumer principal query qver view epoch next-ack) (list groups account)))))
 :hints (("Goal" :in-theory
  (e/d (fn-cec-remote-ack-carry fn-cp-entry fn-cp-nth append fn-caac-atom
        fn-scc-octet-listp fn-scc-octetp)
       (fn-scs-summary fn-scs-atom fn-scs-atom-size fn-scc-encode fn-scc-program)))))


(defthm fn-cecm-selected-proposal-is-actual-projection-decision
 (implies (equal old (fn-cp-find (fn-cep-operation-key op) (fn-cp-nth 5 cp)))
  (equal (fn-cec-proposal-local cp op old) (fn-cpe-projection-decision cp op)))
 :hints (("Goal" :in-theory
  (e/d (fn-cec-proposal-local fn-cec-register-selected fn-cec-ack-selected
        fn-cec-rebase-selected fn-cec-unregister-selected
        fn-cpe-projection-decision fn-cp-register fn-cp-ack fn-cp-rebase
        fn-cp-unregister fn-cep-operation-key fn-cp-nth fn-cp-cursorp
        fn-cp-scope-matchp)
       (fn-cp-find fn-cp-idp fn-cp-uintp
        fn-cp-scope-cursor fn-cec-length-is)))))
