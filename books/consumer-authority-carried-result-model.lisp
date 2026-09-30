; Named full-result bridge for the once-called account/config producer.
; Structural bridges are not new authority/lifecycle keystones.
(in-package "ACL2")
(include-book "consumer-authority-carried-result")
(include-book "consumer-progress-metadata")

(defthm fn-carfc-authority-step-keeps-produced-values-by-definition
 (implies (and (fn-cp-uintp expected) (< expected *fn-cbor-max-uint*)
               (equal (fn-cp-nth 1 event) expected))
  (let* ((one (mv-nth 0 (fn-cpm-authority-step cp event metadata)))
         (nm (mv-nth 1 (fn-cpm-authority-step cp event metadata)))
         (rc (mv-nth 2 (fn-cpm-authority-step cp event metadata))))
   (equal (fn-carfc-authority-step cp event expected metadata)
    (if (eq (fn-cp-nth 0 one) :ok)
        (fn-carfc-result (fn-cp-nth 1 one) (fn-cp-nth 2 one)
                         (if (fn-cp-nth 2 one) (1+ expected) nil) nm rc)
      one))))
 :hints (("Goal" :in-theory
  (e/d (fn-carfc-authority-step fn-cp-uintp)
       (fn-cpm-authority-step fn-carfc-result fn-cp-nth)))))

(defthm fn-carfc-config-step-keeps-approved-values-by-definition
 (let ((one (fn-cpm-config-preflight cp metadata)))
  (equal (fn-carfc-config-step cp metadata)
         (if (eq (fn-cp-nth 0 one) :ok)
             (fn-carfc-result (fn-cp-nth 1 one) nil nil (fn-cp-nth 2 one) nil)
           one)))
 :hints (("Goal" :in-theory
          (e/d (fn-carfc-config-step) (fn-cpm-config-preflight fn-carfc-result fn-cp-nth)))))

; Reuses the existing exact whole-source boundary rather than promoting this
; result packing into a second semantic claim. Actual Store publication and
; recovery must establish the same full preconditions on their reachable state.
(defthm fn-carfc-authority-produced-metadata-corollary
 (let* ((cp (fn-cp-state-carry h i frontier next entries a))
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (kind (fn-cp-nth 0 (fn-cp-nth 4 event)))
        (result (fn-carfc-authority-step cp event expected metadata)))
  (implies
   (and (fn-caam-authority-sizep a)
        (equal metadata (fn-cpmm-annotation cp))
        (implies (member-eq kind '(:authority-row :authority-tombstone))
                 (and (fn-caps-merge-relp p installed)
                      (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))))
        (implies (equal kind :authority-prepare) (fn-caar-preparation-relp prep))
        (equal (fn-cp-nth 0 result) :ok))
   (equal (fn-cp-nth 4 result) (fn-cpmm-annotation (fn-cp-nth 1 result)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-cpmm-actual-authority-step-maintains-fixed-five-metadata))
  :in-theory
   (e/d (fn-carfc-authority-step fn-carfc-result fn-cp-nth)
        (fn-cpm-authority-step fn-cpmm-annotation fn-caam-authority-sizep
         fn-caps-merge-relp fn-cais-triep fn-caar-preparation-relp fn-cp-state-carry)))))
