; Composed actual mapped source -> SAME tagged census child.
; Proof-only: no alternate source walk, served invariant check or issuer.
(in-package "ACL2")
(include-book "snapshot-row-source-cold-refinement")
(include-book "history-source-byte-refinement")

(local (defthm fn-rcct-widths-agree
 (equal (fn-omk-widthp x n) (fn-hrcur-widthp x n))
 :hints (("Goal" :induct (fn-omk-widthp x n)
  :in-theory (enable fn-omk-widthp fn-hrcur-widthp)))))
(local (defthm fn-rcct-first-field-is-car
 (equal (fn-omk-at 0 x) (car x))
 :hints (("Goal" :expand ((fn-omk-at 0 x)) :in-theory (enable fn-omk-at)))))
(defthm fn-rccs-mapped-source-initializes-actual-tagged-byte-child
 (implies (and (fn-rccs-decoded-row-lineagep source handle pool)
               (fn-scc-octet-listp pool))
  (let* ((mapped (mv-nth 0 (fn-osm-row-source source handle)))
         (child (fn-hsrcb-begin mapped capture lease)))
   (and (fn-hsrcb-invariantp child pool)
        (equal (fn-hsrcb-rest child pool)
               (fn-scc-encode (fn-hdc-abstract (fn-omk-at 1 mapped) pool))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccs-mapped-source-initializes-the-actual-cold-codec
        fn-rccs-actual-row-source-preserves-decoded-domain)
  :in-theory (e/d (fn-hsrcb-begin fn-hsrcb-coldp fn-hsrcb-invariantp
                   fn-hsrcb-rest fn-hrcur-widthp fn-hrcur-field fn-omk-widthp fn-omk-at)
                 (fn-rccs-decoded-row-lineagep fn-osm-row-source fn-hrcur-cold-begin fn-hrcur-cold-invariantp
                  fn-hrcur-cold-rest fn-hdc-abstract fn-scc-encode)))))

; The selected profile/producer must establish this total encoded-width
; condition from a maintained carry. No served SCCEncode/length scan.
(defthm fn-rccs-mapped-source-initializes-actual-tagged-census-child
 (implies (and (fn-rccs-decoded-row-lineagep source handle pool)
               (fn-scc-octet-listp pool)
               (< (len (fn-scc-encode
                         (fn-hdc-abstract
                           (fn-omk-at 1 (mv-nth 0 (fn-osm-row-source source handle))) pool)))
                  *fn-hrcur-u64-bound*))
  (let* ((mapped (mv-nth 0 (fn-osm-row-source source handle)))
         (child (fn-hsrcc-begin mapped capture lease)))
   (and (fn-hsrcc-invariantp child pool)
        (equal (fn-hsrcc-total child pool)
               (len (fn-scc-encode (fn-hdc-abstract (fn-omk-at 1 mapped) pool)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use fn-rccs-mapped-source-initializes-actual-tagged-byte-child
  :in-theory (e/d (fn-hsrcc-begin fn-hsrcc-invariantp fn-hsrcc-total
                   fn-hrcur-widthp fn-hrcur-field)
                 (fn-hsrcb-begin fn-hsrcb-invariantp fn-hsrcb-rest fn-hdc-abstract
                  fn-scc-encode fn-osm-row-source)))))

(defthm fn-rccs-actual-census-offer-installs-mapped-row-lineage
 (implies
  (and (fn-rccs-decoded-row-lineagep source handle pool)
       (fn-scc-octet-listp pool)
       (< (len (fn-scc-encode
                (fn-hdc-abstract (fn-omk-at 1 (mv-nth 0 (fn-osm-row-source source handle))) pool)))
          *fn-hrcur-u64-bound*)
       (fn-hct-shapep c) (eq (fn-hrcur-field 0 c) :need-row)
       (equal ordinal (fn-hrcur-field 2 c)))
  (let* ((mapped (mv-nth 0 (fn-osm-row-source source handle)))
         (next (mv-nth 1 (fn-hct-offer c ordinal mapped))))
   (and (eq (mv-nth 0 (fn-hct-offer c ordinal mapped)) :started)
        (fn-hsrcc-invariantp (fn-hrcur-field 4 next) pool)
        (equal (fn-hsrcc-total (fn-hrcur-field 4 next) pool)
               (len (fn-scc-encode (fn-hdc-abstract (fn-omk-at 1 mapped) pool))))
        (equal (fn-hrcur-field 2 next) (fn-hrcur-field 2 c))
        (equal (fn-hrcur-field 3 next) (fn-hrcur-field 3 c))
        (equal (fn-hrcur-field 5 next) (fn-hrcur-field 5 c))
        (equal (fn-hrcur-field 6 next) (fn-hrcur-field 6 c)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccs-mapped-source-initializes-actual-tagged-census-child
         (capture (list (fn-hrcur-field 5 c) ordinal)) (lease (fn-hrcur-field 6 c))))
  :in-theory (e/d (fn-hct-offer fn-hrcur-field)
                 (fn-hsrcc-begin fn-hsrcc-invariantp fn-hsrcc-total fn-hct-shapep
                  fn-osm-row-source fn-rccs-decoded-row-lineagep fn-scc-encode
                  fn-scc-encode-is-program fn-hdc-abstract)))))

(defun-nx fn-rcct-current-row-invariantp (c history row pool)
 (and (fn-hct-shapep c) (eq (fn-hrcur-field 0 c) :codec)
      (equal (fn-hrcur-field 2 c) (len history))
      (equal (fn-hrcur-field 3 c) (fn-hp-pes-len history))
      (fn-hsrcc-invariantp (fn-hrcur-field 4 c) pool)
      (equal (fn-hsrcc-total (fn-hrcur-field 4 c) pool)
             (len (fn-scc-encode row)))))

(defthm fn-rcct-actual-census-continue-retains-the-same-row
 (implies (and (fn-rcct-current-row-invariantp c history row pool)
               (eq (mv-nth 0 (fn-hct-tick c)) :continue))
  (fn-rcct-current-row-invariantp (mv-nth 2 (fn-hct-tick c)) history row pool))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hsrcc-tick-preserves-canonical-length (c (fn-hrcur-field 4 c)))
        fn-hct-tick-keeps-shape fn-hct-continuation-keeps-census)
  :in-theory (e/d (fn-rcct-current-row-invariantp fn-hct-tick fn-hrcur-field)
                 (fn-hsrcc-tick fn-hsrcc-invariantp fn-hsrcc-total fn-hct-shapep
                  fn-hcc-row fn-hp-pes-len fn-scc-encode fn-scc-encode-is-program)))))

(defthm fn-rcct-actual-census-completes-exactly-the-same-row
 (implies (and (fn-rcct-current-row-invariantp c history row pool)
               (eq (mv-nth 0 (fn-hct-tick c)) :row-done))
  (let ((next (mv-nth 2 (fn-hct-tick c))))
   (and (equal (mv-nth 1 (fn-hct-tick c)) (len (fn-scc-encode row)))
        (equal (fn-hrcur-field 2 next) (len (append history (list row))))
        (equal (fn-hrcur-field 3 next) (fn-hp-pes-len (append history (list row))))
        (equal (fn-hrcur-field 4 next) nil)
        (equal (fn-hrcur-field 5 next) (fn-hrcur-field 5 c))
        (equal (fn-hrcur-field 6 next) (fn-hrcur-field 6 c)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hsrcc-tick-preserves-canonical-length (c (fn-hrcur-field 4 c)))
        (:instance fn-hct-tagged-completed-row-refines-history-census
         (h history) (ev row)) fn-hct-tick-keeps-capture-and-lease)
  :in-theory (e/d (fn-rcct-current-row-invariantp fn-hct-tick fn-hrcur-field)
                 (fn-hsrcc-tick fn-hsrcc-invariantp fn-hsrcc-total fn-hct-shapep
                  fn-hcc-row fn-hp-pes-len fn-scc-encode fn-scc-encode-is-program len)))))

(defthm fn-rcct-actual-census-supply-retains-the-same-row
 (implies
  (and (fn-rcct-current-row-invariantp c history row pool)
       (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :active)
       (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 (fn-hrcur-field 4 c)))))
       (equal position (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 (fn-hrcur-field 4 c))))))
       (equal byte (nth position pool)))
  (and (eq (mv-nth 0 (fn-hct-supply c position byte)) :continue)
       (fn-rcct-current-row-invariantp (mv-nth 1 (fn-hct-supply c position byte)) history row pool)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hsrcc-supply-preserves-canonical-length (c (fn-hrcur-field 4 c)))
        fn-hct-supply-keeps-shape fn-hct-supply-keeps-source-and-census)
  :in-theory (e/d (fn-rcct-current-row-invariantp fn-hct-supply fn-hrcur-field fn-hsrcc-invariantp)
                 (fn-hsrcc-supply fn-hsrcc-total fn-hct-shapep fn-hsrcb-tick
                  fn-hsrcb-demandp fn-hsrcb-invariantp fn-hsrcb-rest
                  fn-hp-pes-len fn-scc-encode fn-scc-encode-is-program)))))

(defthm fn-rcct-actual-mapped-row-offer-establishes-current-row-invariant
 (implies
  (and (fn-rccs-decoded-row-lineagep source handle pool)
       (fn-scc-octet-listp pool)
       (< (len (fn-scc-encode
                (fn-hdc-abstract (fn-omk-at 1 (mv-nth 0 (fn-osm-row-source source handle))) pool)))
          *fn-hrcur-u64-bound*)
       (fn-hct-shapep c) (eq (fn-hrcur-field 0 c) :need-row)
       (equal ordinal (fn-hrcur-field 2 c))
       (equal (fn-hrcur-field 2 c) (len history))
       (equal (fn-hrcur-field 3 c) (fn-hp-pes-len history)))
  (let ((mapped (mv-nth 0 (fn-osm-row-source source handle))))
   (fn-rcct-current-row-invariantp
     (mv-nth 1 (fn-hct-offer c ordinal mapped)) history
     (fn-hdc-abstract (fn-omk-at 1 mapped) pool) pool)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccs-actual-census-offer-installs-mapped-row-lineage
        (:instance fn-hct-offer-keeps-shape
         (source (mv-nth 0 (fn-osm-row-source source handle)))))
  :in-theory (e/d (fn-rcct-current-row-invariantp fn-hct-offer fn-hrcur-field)
                 (fn-hsrcc-begin fn-hsrcc-invariantp fn-hsrcc-total fn-hct-shapep
                  fn-osm-row-source fn-rccs-decoded-row-lineagep fn-scc-encode
                  fn-scc-encode-is-program fn-hdc-abstract len fn-hp-pes-len)))))
