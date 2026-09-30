; Actual same-row census completion -> remapper ACK.
; Ghost relation only; runtime never checks this or traverses histories.
(in-package "ACL2")
(include-book "snapshot-row-source-tagged-refinement")
(defun-nx fn-rcca-waiting-rowp (remapper census history row pool)
 (let* ((source (fn-omk-at 1 remapper))
        (pair (fn-omk-at 1 source)) (pending (fn-omk-at 3 remapper)))
  (and (fn-omk-widthp remapper 4)
       (eq (fn-omk-at 0 remapper) :waiting)
       (fn-omk-tokenp source) (fn-omk-widthp pending 4)
       (natp (fn-omk-at 2 remapper)) (natp (fn-omk-at 2 pending))
       (equal (fn-omk-at 3 pending) source)
       (equal (fn-omk-at 1 pending)
        (mv-nth 0 (fn-osm-row-source (fn-omk-at 0 pending) (fn-omk-at 2 remapper))))
       (equal (fn-omk-at 2 pending)
        (mv-nth 1 (fn-osm-row-source (fn-omk-at 0 pending) (fn-omk-at 2 remapper))))
       (fn-omk-widthp (fn-omk-at 1 pending) 2)
       (cond ((eq (fn-omk-at 0 (fn-omk-at 1 pending)) :resident)
              (equal row (fn-omk-at 1 (fn-omk-at 1 pending))))
             ((eq (fn-omk-at 0 (fn-omk-at 1 pending)) :decoded)
              (equal row (fn-hdc-abstract (fn-omk-at 1 (fn-omk-at 1 pending)) pool)))
             (t nil))
       (equal (fn-omk-at 3 source) (len history))
       (equal (fn-omk-at 1 census) (fn-omk-at 1 pair))
       (equal (fn-omk-at 5 census)
              (list (fn-omk-at 0 pair) (fn-omk-at 1 pair)))
       (fn-rcct-current-row-invariantp census history row pool))))
(local (defthm fn-rcca-width-lenses-agree
 (equal (fn-omk-widthp x n) (fn-hrcur-widthp x n))
 :hints (("Goal" :induct (fn-omk-widthp x n)
  :in-theory (enable fn-omk-widthp fn-hrcur-widthp)))))
(local (defthm fn-rcca-field-lenses-agree
 (implies (natp n) (equal (fn-omk-at n x) (fn-hrcur-field n x)))
 :hints (("Goal" :induct (fn-omk-at n x)
  :in-theory (enable fn-omk-at fn-hrcur-field)))))
(local (defthm fn-rcca-row-done-has-actual-ack-phase
 (implies (eq (mv-nth 0 (fn-hct-tick c)) :row-done)
  (and (fn-hrcur-widthp (mv-nth 2 (fn-hct-tick c)) 7)
       (member-eq (fn-hrcur-field 0 (mv-nth 2 (fn-hct-tick c))) '(:need-row :prepared))
       (equal (fn-hrcur-field 1 (mv-nth 2 (fn-hct-tick c))) (fn-hrcur-field 1 c))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hct-tick fn-hrcur-field fn-hrcur-widthp)
                 (fn-hsrcc-tick fn-hcc-row fn-hct-shapep fn-hsrcb-demandp))))))
; The row parameter is the SAME mapped pending row's logical abstraction.
; Establishment from actual Offer/PrepareRow is required before using this
; relational precondition, not inferred from scalar coincidence.
(defthm fn-rcca-actual-row-done-ack-advances-exactly-the-same-prefix
 (implies (and (fn-rcca-waiting-rowp remapper census history row pool)
               (eq (mv-nth 0 (fn-hct-tick census)) :row-done))
  (let* ((completed (mv-nth 2 (fn-hct-tick census)))
         (next (mv-nth 1 (fn-osm-census-ack remapper completed)))
         (source (fn-omk-at 1 remapper)))
   (and (eq (mv-nth 0 (fn-osm-census-ack remapper completed)) :acknowledged)
        (eq (fn-omk-at 0 next) :idle)
        (equal (fn-omk-at 3 next) nil)
        (equal (fn-omk-at 2 next) (fn-omk-at 2 (fn-omk-at 3 remapper)))
        (equal (fn-omk-at 1 next)
         (list (fn-omk-at 0 source) (fn-omk-at 1 source)
               (fn-omk-at 2 source) (len (append history (list row)))))
        (equal (fn-omk-at 2 completed) (len (append history (list row))))
        (equal (fn-omk-at 3 completed) (fn-hp-pes-len (append history (list row)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rcct-actual-census-completes-exactly-the-same-row (c census))
        (:instance fn-rcca-row-done-has-actual-ack-phase (c census)))
  :in-theory (e/d (fn-rcca-waiting-rowp fn-osm-census-ack fn-osm-advance
                   fn-rcct-current-row-invariantp fn-omk-tokenp fn-omk-widthp fn-hrcur-widthp)
                 (fn-hct-tick fn-osm-row-source fn-hdc-abstract fn-hsrcb-demandp
                  fn-hsrcc-tick fn-hsrcc-invariantp fn-hsrcc-total
                  fn-hp-pes-len fn-scc-encode fn-hcc-row fn-hct-shapep)))))
