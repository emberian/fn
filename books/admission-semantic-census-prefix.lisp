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
