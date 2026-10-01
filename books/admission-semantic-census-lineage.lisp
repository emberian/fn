; Ghost association for the exact registered admission census caller.
; No runtime census, supplied candidate, or allocation authority is added.
(in-package "ACL2")
(include-book "snapshot-source-resident-lineage")

(defthm fn-rccap-target-field-retains-exact-candidate-unfolds
 (equal (fn-sfr-list (fn-sfr-snoc committed candidate))
        (append (fn-sfr-list committed) (list candidate)))
 :hints (("Goal" :use ((:instance fn-sfr-list-of-fn-sfr-snoc
                       (f committed) (r candidate)))
          :in-theory (disable fn-sfr-list fn-sfr-snoc))))

(defthm fn-rccap-target-count-is-one-actual-candidate-by-definition
 (equal (fn-sfr-count (fn-sfr-snoc committed candidate))
        (1+ (fn-sfr-count committed)))
 :hints (("Goal" :use ((:instance fn-sfr-count-is-len
                        (f (fn-sfr-snoc committed candidate)))
                       (:instance fn-sfr-count-is-len (f committed)))
          :in-theory (e/d (len)
                          (fn-sfr-count fn-sfr-list fn-sfr-snoc)))))

; Committed CanonP is supplied by the actual captured Store relation.
; Candidate identity/produced-decision binding is a distinct builder-current
; obligation, never derived from sequence or transaction-id coincidence.
(defthm fn-rccap-actual-appended-candidate-begins-resident-lineage
 (implies (fn-sfr-canonp committed)
  (fn-rccos-cursor-invariantp
   (fn-osrc-begin (fn-sfr-snoc committed candidate)
                 (1+ (fn-sfr-count committed)) frontier
                 (list nonce (1+ (fn-sfr-count committed))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sfr-canonp-of-fn-sfr-snoc
                    (f committed) (r candidate))
        (:instance fn-rccos-actual-field-count-begins-carried-resident-lineage
                    (field (fn-sfr-snoc committed candidate))
                    (epoch frontier)
                    (lease (list nonce (1+ (fn-sfr-count committed))))))
  :in-theory (e/d (fn-rccap-target-count-is-one-actual-candidate-by-definition)
                  (fn-sfr-canonp fn-sfr-snoc fn-sfr-count
                   fn-osrc-begin fn-rccos-cursor-invariantp)))))
