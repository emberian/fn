; Proof-only target-prefix association for the actual source/remap/census
; pipeline. No served traversal or independent remapping implementation.
(in-package "ACL2")
(include-book "snapshot-row-source-ack-refinement")
(include-book "admission-semantic-census-lineage")

; This model invokes the ACTUAL row transformer at each ordinal. It is never
; host-called. The handle output is essential: a count is not a handle count.
(defun-nx fn-rccap-remapped-prefix (rows handle)
 (declare (xargs :measure (acl2-count rows)))
 (if (atom rows) (mv nil handle)
  (mv-let (source next-handle) (fn-osm-row-source (list :resident (car rows)) handle)
   (mv-let (tail final-handle) (fn-rccap-remapped-prefix (cdr rows) next-handle)
    (mv (cons (fn-omk-at 1 source) tail) final-handle)))))

(defthm fn-rccap-actual-remap-appends-one-produced-row
 (let* ((old (mv-nth 0 (fn-rccap-remapped-prefix prefix handle)))
        (old-handle (mv-nth 1 (fn-rccap-remapped-prefix prefix handle)))
        (row-source (mv-nth 0 (fn-osm-row-source (list :resident row) old-handle)))
        (next-handle (mv-nth 1 (fn-osm-row-source (list :resident row) old-handle))))
  (and (equal (mv-nth 0 (fn-rccap-remapped-prefix (append prefix (list row)) handle))
              (append old (list (fn-omk-at 1 row-source))))
       (equal (mv-nth 1 (fn-rccap-remapped-prefix (append prefix (list row)) handle))
              next-handle)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-rccap-remapped-prefix prefix handle)
  :in-theory (e/d (fn-rccap-remapped-prefix binary-append)
                  (fn-osm-row-source fn-omk-at)))))

(defun-nx fn-rccap-idle-original-prefixp (remapper census originals)
 (and (fn-rcca-idle-prefixp remapper census
                           (mv-nth 0 (fn-rccap-remapped-prefix originals 0)))
      (equal (fn-omk-at 2 remapper)
             (mv-nth 1 (fn-rccap-remapped-prefix originals 0)))))

; This phase relation retains ORIGINAL prefix separately from its transformed
; prefix. A scalar count or newly supplied row cannot establish it.
(defun-nx fn-rccap-waiting-original-prefixp (remapper census originals original row pool)
 (and (fn-rcca-waiting-rowp remapper census
                           (mv-nth 0 (fn-rccap-remapped-prefix originals 0)) row pool)
      (equal (fn-omk-at 2 remapper)
             (mv-nth 1 (fn-rccap-remapped-prefix originals 0)))
      (equal (fn-omk-at 0 (fn-omk-at 3 remapper)) (list :resident original))))

(local (defthm fn-rccap-resident-transform-is-resident
 (equal (fn-omk-at 0 (mv-nth 0 (fn-osm-row-source (list :resident row) handle)))
        :resident)
 :hints (("Goal" :in-theory
  (e/d (fn-osm-row-source fn-omk-at fn-omk-widthp)
       (fn-orm-held fn-hstxa-make fn-hstxa-stxa fn-hstxa-held
        fn-osm-resident-held-headp fn-osm-node-held-headp))))))

(local (defthm fn-rccap-waiting-row-is-produced-from-same-original
 (implies (fn-rccap-waiting-original-prefixp remapper census originals original row pool)
  (equal row
   (fn-omk-at 1
    (mv-nth 0 (fn-osm-row-source (list :resident original)
                 (mv-nth 1 (fn-rccap-remapped-prefix originals 0)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
   (e/d (fn-rccap-waiting-original-prefixp fn-rcca-waiting-rowp
         fn-osm-row-source fn-omk-at fn-omk-widthp)
        (fn-rccap-remapped-prefix fn-orm-held fn-hstxa-make fn-hstxa-stxa
         fn-hstxa-held fn-osm-resident-held-headp fn-osm-node-held-headp
         fn-hdc-abstract fn-rcct-current-row-invariantp))))))

(local (defthm fn-rccap-waiting-handle-is-produced-from-same-original
 (implies (fn-rccap-waiting-original-prefixp remapper census originals original row pool)
  (equal (fn-omk-at 2 (fn-omk-at 3 remapper))
   (mv-nth 1 (fn-osm-row-source (list :resident original)
                 (mv-nth 1 (fn-rccap-remapped-prefix originals 0))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
   (e/d (fn-rccap-waiting-original-prefixp fn-rcca-waiting-rowp)
        (fn-rccap-remapped-prefix fn-osm-row-source fn-omk-at
         fn-rcct-current-row-invariantp fn-hdc-abstract))))))

(defthm fn-rccap-actual-ack-preserves-the-original-to-remapped-prefix
 (implies
  (and (fn-rccap-waiting-original-prefixp remapper census originals original row pool)
       (eq (mv-nth 0 (fn-hct-tick census)) :row-done))
  (let* ((completed (mv-nth 2 (fn-hct-tick census)))
         (next (mv-nth 1 (fn-osm-census-ack remapper completed))))
   (fn-rccap-idle-original-prefixp next completed (append originals (list original)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-waiting-handle-is-produced-from-same-original)
        (:instance fn-rccap-waiting-row-is-produced-from-same-original)
        (:instance fn-rccap-resident-transform-is-resident
         (row original) (handle (fn-omk-at 2 remapper)))
        (:instance fn-rcca-actual-ack-preserves-the-idle-mapped-prefix
         (history (mv-nth 0 (fn-rccap-remapped-prefix originals 0))))
        (:instance fn-rcca-actual-row-done-ack-advances-exactly-the-same-prefix
         (history (mv-nth 0 (fn-rccap-remapped-prefix originals 0))))
        (:instance fn-rccap-actual-remap-appends-one-produced-row
         (prefix originals) (handle 0) (row original)))
  :in-theory (e/d (fn-rccap-waiting-original-prefixp fn-rccap-idle-original-prefixp
                   )
                  (fn-rcca-waiting-rowp fn-osm-row-source fn-omk-at fn-rccap-remapped-prefix
                   fn-rcca-idle-prefixp fn-rcct-current-row-invariantp fn-hct-tick
                   fn-osm-census-ack fn-hdc-abstract)))))

(local (defthm fn-rccap-field-lenses-agree
 (implies (natp n) (equal (fn-omk-at n x) (fn-hrcur-field n x)))
 :hints (("Goal" :induct (fn-omk-at n x)
  :in-theory (enable fn-omk-at fn-hrcur-field)))))

(defthm fn-rccap-actual-begin-establishes-empty-original-prefix
 (implies (and (fn-omk-tokenp source) (equal (fn-omk-at 3 source) 0)
               (unsigned-byte-p 61 (fn-omk-at 1 (fn-omk-at 1 source))))
  (fn-rccap-idle-original-prefixp (fn-osm-begin source)
   (fn-hct-begin (fn-omk-at 1 (fn-omk-at 1 source)) (fn-omk-at 1 source) resource)
   nil))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use fn-rcca-actual-begin-establishes-the-empty-mapped-prefix
  :in-theory (e/d (fn-rccap-idle-original-prefixp fn-rccap-remapped-prefix
                   fn-osm-begin fn-omk-at)
                  (fn-rcca-idle-prefixp fn-hct-begin fn-omk-tokenp
                   fn-rccap-field-lenses-agree)))))

; Establish the waiting relation using the SAME actual remapper output and
; actual census Offer. Domain/width are producer obligations, not scans.
(local (defthm fn-rccap-fixed-resident-pair-reconstructs
 (implies (and (fn-omk-widthp x 2) (eq (fn-omk-at 0 x) :resident))
          (equal (list :resident (fn-omk-at 1 x)) x))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :expand ((fn-omk-widthp x 2) (fn-omk-widthp (cdr x) 1)
           (fn-omk-widthp (cddr x) 0))
  :in-theory
  (e/d (fn-omk-widthp fn-omk-at) (fn-rccap-field-lenses-agree))))))

(defthm fn-rccap-actual-resident-offers-establish-original-prefix
 (let* ((history (mv-nth 0 (fn-rccap-remapped-prefix originals 0)))
        (source (fn-omk-at 1 remapper))
        (mapped (mv-nth 0 (fn-osm-row-source (list :resident original)
                                           (fn-omk-at 2 remapper))))
        (row (fn-omk-at 1 mapped))
        (next-census (mv-nth 1 (fn-hct-offer census (len history) mapped)))
        (next-remapper (mv-nth 1 (fn-osm-offer remapper source (list :resident original)))))
  (implies
   (and (fn-rccap-idle-original-prefixp remapper census originals)
        (eq (fn-omk-at 0 census) :need-row)
        (fn-omk-widthp mapped 2)
        (natp (mv-nth 1 (fn-osm-row-source (list :resident original)
                                         (fn-omk-at 2 remapper))))
        (fn-hrcur-tree-domainp row)
        (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*)
        (eq (car (mv-nth 0 (fn-osm-offer remapper source (list :resident original)))) :mapped))
   (fn-rccap-waiting-original-prefixp next-remapper next-census originals original row pool)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-fixed-resident-pair-reconstructs
         (x (mv-nth 0 (fn-osm-row-source (list :resident original)
                                        (fn-omk-at 2 remapper)))))
        (:instance fn-rccap-resident-transform-is-resident
         (row original) (handle (fn-omk-at 2 remapper)))
        (:instance fn-rccap-actual-resident-offer-establishes-same-mapped-row
         (c census) (ordinal (len (mv-nth 0 (fn-rccap-remapped-prefix originals 0))))
         (history (mv-nth 0 (fn-rccap-remapped-prefix originals 0)))
         (row (fn-omk-at 1 (mv-nth 0 (fn-osm-row-source (list :resident original)
                                                     (fn-omk-at 2 remapper))))))
        (:instance fn-rcca-actual-offer-retains-the-produced-row-and-child
         (token (fn-omk-at 1 remapper)) (original (list :resident original))
         (history (mv-nth 0 (fn-rccap-remapped-prefix originals 0)))
         (row (fn-omk-at 1 (mv-nth 0 (fn-osm-row-source (list :resident original)
                                                     (fn-omk-at 2 remapper)))))
         (census (mv-nth 1 (fn-hct-offer census
                   (len (mv-nth 0 (fn-rccap-remapped-prefix originals 0)))
                   (mv-nth 0 (fn-osm-row-source (list :resident original)
                                                (fn-omk-at 2 remapper))))))))
  :in-theory (e/d (fn-rccap-idle-original-prefixp fn-rcca-idle-prefixp
                   fn-rccap-waiting-original-prefixp fn-osm-offer fn-omk-widthp fn-hct-offer)
                  (fn-osm-row-source fn-rccap-remapped-prefix fn-omk-at
                   fn-omk-token-matchp fn-omk-tokenp fn-rcca-waiting-rowp
                   fn-hsrcc-begin fn-rcct-current-row-invariantp fn-hct-shapep
                   fn-hp-pes-len fn-scc-encode)))))

(defun-nx fn-rccap-idle-target-prefixp (cursor remapper census mapped-prefix)
 (let* ((ordinal (fn-osrc-at 2 cursor))
        (target (fn-sfr-list (fn-osrc-at 1 cursor))))
  (and (fn-rccos-cursor-invariantp cursor)
       (fn-sfr-canonp (fn-osrc-at 1 cursor))
       (fn-rcca-idle-prefixp remapper census mapped-prefix)
       (equal (fn-omk-at 1 remapper) (fn-osrc-token cursor))
       (equal mapped-prefix
              (mv-nth 0 (fn-rccap-remapped-prefix (take ordinal target) 0)))
       (equal (fn-omk-at 2 remapper)
              (mv-nth 1 (fn-rccap-remapped-prefix (take ordinal target) 0))))))

; The terminal result is authorized by the SAME completed source/OSM/HCT
; lineage, not by a scalar :prepared tag. Establishment/preservation of this
; joint invariant through resident Offer/ACK is a separate proof obligation.
(defthm fn-rccap-terminal-target-pool-unfolds
 (implies
  (and (fn-rccap-idle-target-prefixp cursor remapper census mapped-prefix)
       (equal (fn-osrc-at 2 cursor) (fn-sfr-count (fn-osrc-at 1 cursor)))
       (eq (fn-omk-at 0 census) :prepared))
  (and (equal (fn-omk-at 2 census)
              (len (fn-sfr-list (fn-osrc-at 1 cursor))))
       (equal (fn-omk-at 3 census)
              (fn-hp-pes-len
               (mv-nth 0 (fn-rccap-remapped-prefix
                           (fn-sfr-list (fn-osrc-at 1 cursor)) 0))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sfr-count-is-len (f (fn-osrc-at 1 cursor))))
  :in-theory (e/d (fn-rccap-idle-target-prefixp fn-rcca-idle-prefixp)
                  (fn-rccap-remapped-prefix fn-sfr-count fn-sfr-list
                   fn-hp-pes-len fn-osrc-at fn-osrc-token fn-rccos-cursor-invariantp
                   fn-sfr-canonp fn-omk-at fn-omk-widthp fn-hct-shapep)))))
