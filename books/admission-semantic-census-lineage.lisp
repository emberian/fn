; Ghost association for the exact registered admission census caller.
; No runtime census, supplied candidate, or allocation authority is added.
(in-package "ACL2")
(include-book "snapshot-source-order-lineage")

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

(local (defthm fn-rccap-nth-after-exact-prefix
 (equal (nth (len prefix) (append prefix (list candidate))) candidate)
 :hints (("Goal" :induct (len prefix)
          :in-theory (enable nth len binary-append)))))

; At the new ordinal, the actual source cursor emits the literal candidate
; selected by the registered builder. No host row projection is involved.
(defthm fn-rccap-actual-resident-new-ordinal-is-exact-candidate
 (implies
  (and (fn-sfr-canonp committed)
       (equal (fn-osrc-at 1 cursor) (fn-sfr-snoc committed candidate))
       (fn-rccos-cursor-invariantp cursor)
       (equal (fn-osrc-at 2 cursor) (fn-sfr-count committed))
       (eq (car (fn-osrc-tick cursor observation)) :row)
       (eq (fn-osrc-at 0 (fn-osrc-at 2 (fn-osrc-tick cursor observation)))
           :resident))
  (equal (fn-osrc-at 1 (fn-osrc-at 2 (fn-osrc-tick cursor observation)))
         candidate))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sfr-canonp-of-fn-sfr-snoc
                     (f committed) (r candidate))
        (:instance fn-rcco-actual-resident-row-is-the-captured-logical-record-ordinal
                     (c cursor))
        (:instance fn-sfr-count-is-len (f committed))
        (:instance fn-rccap-nth-after-exact-prefix
                     (prefix (fn-sfr-list committed))))
  :in-theory (e/d (fn-rccap-target-field-retains-exact-candidate-unfolds)
                  (fn-sfr-canonp fn-sfr-snoc fn-sfr-list fn-sfr-count
                   fn-osrc-at fn-osrc-tick fn-rccos-cursor-invariantp nth len)))))
