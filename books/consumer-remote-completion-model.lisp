; Logical observation only; none of these scans is a served decision.
(in-package "ACL2")
(include-book "consumer-remote-completion")

(defun fn-crdm-domainp (s)
 (declare (xargs :guard t))
 (and (true-listp (fn-cp-nth 6 s)) (true-listp (fn-cp-nth 7 s))
      (or (not (eq (fn-cp-nth 8 s) :compare)) (fn-cp-nth 9 (fn-cp-nth 4 s)))))

(defun fn-crdm-observe (s)
 (declare (xargs :guard t))
 (case (fn-cp-nth 8 s)
  (:compare (list :comparison (and (fn-cp-nth 9 s) (equal (fn-cp-nth 6 s) (fn-cp-nth 7 s)) t)))
  (:capacity (if (< (+ (nfix (fn-cp-nth 10 s)) (len (fn-cp-nth 7 s)))
                     (nfix (fn-cp-nth 11 s))) '(:capacity-admissible) '(:refused :max-consumers)))
  (:ready (if (fn-cp-nth 9 (fn-cp-nth 4 s))
               (list :comparison (and (fn-cp-nth 9 s) t)) '(:capacity-admissible)))
  (otherwise '(:refused :consumer-decision-phase))))

(defun fn-crdm-answer (answer)
 (declare (xargs :guard t))
 (if (member-eq (fn-cp-nth 0 answer) '(:yield :ready))
     (fn-crdm-observe (fn-cp-nth 1 answer)) answer))

(defthm fn-crd-tick-preserves-exact-definition-comparison-and-capacity
 (implies (and (fn-crdm-domainp s) (equal current-key (fn-cp-nth 1 s))
               (or (not (eq (fn-cp-nth 8 s) :capacity))
                   (not (fn-cp-nth 9 (fn-cp-nth 4 s)))))
  (equal (fn-crdm-answer (fn-crd-tick s current-key)) (fn-crdm-observe s)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-crdm-domainp fn-crdm-answer fn-crdm-observe
                          fn-crd-tick fn-crd-state fn-cp-nth len)
                          ()))))

(defthm fn-crd-remote-entry-constructor-has-exact-canonical-carry
 (implies (and (fn-scc-octet-listp consumer) (fn-scc-octet-listp principal)
               (fn-scc-octet-listp query) (fn-scc-octet-listp account)
               (integerp qver) (integerp view) (integerp epoch)
               (equal (fn-caac-list-carry groupmeta) (fn-scs-summary groups)))
  (equal (fn-crd-entry-carry
           (fn-cp-event-entry (list :remote-register consumer principal query qver view epoch groups account))
           groupmeta)
         (fn-scs-summary
           (fn-cp-event-entry (list :remote-register consumer principal query qver view epoch groups account)))))
 :hints (("Goal"
  :use ((:instance fn-caac-spine-keeps-canonical-size
    (cs (list (fn-caac-atom :entry) (fn-scs-octets (len consumer))
              (fn-scs-octets (len principal)) (fn-scs-octets (len query))
              (fn-caac-atom qver) (fn-caac-atom view) (fn-caac-atom epoch) (fn-caac-atom 0)
              (fn-caac-list-carry groupmeta) (fn-scs-octets (len account))))
    (xs (list :entry consumer principal query qver view epoch 0 groups account))))
  :in-theory (e/d (fn-crd-entry-carry fn-cp-event-entry fn-cp-entry fn-cp-nth
                   fn-scs-correspondsp fn-caac-atom append)
                  (fn-caac-spine fn-scs-summary fn-scs-octets fn-scs-atom fn-caac-list-carry)))))

(in-theory (disable fn-crdm-domainp fn-crdm-observe fn-crdm-answer))
