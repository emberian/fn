; The actual admission caller's resident mapped row establishes the SAME
; tagged census invariant already used by decoded rows. Proof-only: domain
; and encoded width are carried producer obligations, never served scans.
(in-package "ACL2")
(include-book "snapshot-row-source-tagged-refinement")

(local (defthm fn-rccap-resident-census-is-not-cold
 (implies (fn-hrcur-census-invariantp c)
          (not (fn-hsrcb-coldp (fn-hrcur-field 1 c))))
 :hints (("Goal" :in-theory
  (e/d (fn-hrcur-census-invariantp fn-hrcur-byte-invariantp
        fn-hsrcb-coldp fn-hrcur-widthp fn-hrcur-field)
       (fn-hrcur-census-total fn-hrcur-byte-rest))))))

(defthm fn-rccap-resident-tagged-census-begin-has-exact-row-length
 (implies (and (fn-hrcur-tree-domainp row)
               (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*))
  (let ((child (fn-hsrcc-begin (list :resident row) capture lease)))
   (and (fn-hsrcc-invariantp child pool)
        (equal (fn-hsrcc-total child pool) (len (fn-scc-encode row))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hrcur-census-begin-refines-length
        (:instance fn-rccap-resident-census-is-not-cold
         (c (fn-hrcur-census-begin (list :resident row) capture lease))))
  :in-theory
   (e/d (fn-hsrcc-resident-begin-by-definition fn-hsrcc-invariantp
         fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
         fn-hrcur-census-invariantp fn-hrcur-census-total)
        (fn-hsrcc-begin fn-hrcur-census-begin fn-hsrcb-coldp
         fn-hrcur-byte-invariantp fn-hrcur-byte-rest fn-scc-encode)))))

(defthm fn-rccap-actual-resident-offer-establishes-same-mapped-row
 (implies
  (and (fn-hrcur-tree-domainp row)
       (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*)
       (fn-hct-shapep c) (eq (fn-hrcur-field 0 c) :need-row)
       (equal ordinal (fn-hrcur-field 2 c))
       (equal (fn-hrcur-field 2 c) (len history))
       (equal (fn-hrcur-field 3 c) (fn-hp-pes-len history)))
  (let ((next (mv-nth 1 (fn-hct-offer c ordinal (list :resident row)))))
   (and (eq (mv-nth 0 (fn-hct-offer c ordinal (list :resident row))) :started)
        (fn-rcct-current-row-invariantp next history row pool))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-resident-tagged-census-begin-has-exact-row-length
         (capture (list (fn-hrcur-field 5 c) ordinal))
         (lease (fn-hrcur-field 6 c)))
        (:instance fn-hct-offer-keeps-shape (source (list :resident row))))
  :in-theory (e/d (fn-hct-offer fn-rcct-current-row-invariantp fn-hrcur-field)
   (fn-hsrcc-begin fn-hsrcc-invariantp fn-hsrcc-total fn-hct-shapep
    fn-scc-encode fn-hp-pes-len len)))))
