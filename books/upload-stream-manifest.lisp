; One provisional entry -> canonical final entry, through the SAME codecs.
; Controller-owned positions/padding are not guessed here. The complete
; remaining input span is protected from the destination's maximum write.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "upload")
(fn2-book-layer :d)

(defun fn2-upload-repack-entry-children
 (base ss sg so se ds dg do kind owner ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
  :guard (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
              (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-am-get-entry
    fn2-format-source-manifest-entry-encode fn2-format-source-manifest-entry-size)))))
 (b* (((unless (and (natp base) (<= (+ base *fn2-am-entry-fields*) (fn2-fields-rows fn2-fields))
    (unsigned-byte-p 32 ss) (unsigned-byte-p 60 sg)
    (unsigned-byte-p 32 ds) (unsigned-byte-p 60 dg)
    (< ss (fn2-pool-rows fn2-pool)) (< ds (fn2-pool-rows fn2-pool))
    (unsigned-byte-p 32 so) (unsigned-byte-p 32 se) (< so se)
    (unsigned-byte-p 32 do) (unsigned-byte-p 32 (+ do *fn2-am-entry-max*))
    (posp kind) (unsigned-byte-p 8 kind) (unsigned-byte-p 32 owner)
    (posp ogen) (unsigned-byte-p 60 ogen)))
   (mv :bounds 0 0 fn2-fields fn2-pool))
  ((unless (and (eq (fn2-pool-readable-code ss sg kind owner ogen fn2-pool) :ok)
                (eq (fn2-pool-workspace-code ds dg kind owner ogen fn2-pool) :ok)))
   (mv :owner 0 0 fn2-fields fn2-pool))
  ((unless (and (eq (fn2-layout-range-code ss sg so se nil kind owner ogen fn2-pool) :ok)
                (eq (fn2-layout-range-code ds dg do (+ do *fn2-am-entry-max*) t kind owner ogen fn2-pool) :ok)))
   (mv :bounds 0 0 fn2-fields fn2-pool))
  ; Compare actual physical spans, even if distinct slot metadata aliases.
  (source-low (+ (fn2-pool-slot-base ss fn2-pool) so))
  (source-high (+ (fn2-pool-slot-base ss fn2-pool) se))
  (dest-low (+ (fn2-pool-slot-base ds fn2-pool) do))
  ((unless (or (<= (+ dest-low *fn2-am-entry-max*) source-low) (<= source-high dest-low)))
   (mv :overlap 0 0 fn2-fields fn2-pool))
  ; Bound malformed input too: one actual entry cannot exceed its codec max.
  (limit (min se (+ so *fn2-am-entry-max*)))
  ((mv decoded next & & & & & fn2-fields)
   (fn2-am-get-entry base ss sg so limit kind owner ogen fn2-fields fn2-pool))
  ((unless (and (eq decoded :ok) (unsigned-byte-p 32 next) (< so next) (<= next limit)
                (<= (+ base *fn2-am-entry-fields*) (fn2-fields-rows fn2-fields))))
   (mv :decode 0 0 fn2-fields fn2-pool))
  (size (fn2-format-source-manifest-entry-size base fn2-fields))
  ((unless (and (posp size) (<= size *fn2-am-entry-max*)))
   (mv :decode 0 0 fn2-fields fn2-pool))
  ; In particular digest/CV references still point into SS/SG's actual bytes.
  ((mv encoded end fn2-pool)
   (fn2-format-source-manifest-entry-encode base ds dg do kind owner ogen fn2-fields fn2-pool)))
  (if (and (eq encoded :ok) (unsigned-byte-p 32 end) (= end (+ do size)))
      (mv :ok next end fn2-fields fn2-pool)
    (mv :encode 0 0 fn2-fields fn2-pool))))

(fn2-fc-shape fn2-upload-repack-entry-children-shape
 (fn2-upload-repack-entry-children base ss sg so se ds dg do kind owner ogen fn2-fields fn2-pool)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
      (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 ((fn2-fields 3) (fn2-pool 4)))
(defthm fn2-upload-repack-entry-children-naturals
 (and (natp (mv-nth 1 (fn2-upload-repack-entry-children base ss sg so se ds dg do kind owner ogen fn2-fields fn2-pool)))
      (natp (mv-nth 2 (fn2-upload-repack-entry-children base ss sg so se ds dg do kind owner ogen fn2-fields fn2-pool))))
 :hints (("Goal" :in-theory (disable fn2-am-get-entry fn2-format-source-manifest-entry-encode
                                    fn2-format-source-manifest-entry-size))))
(in-theory (disable fn2-upload-repack-entry-children))

; Materialize after the existing concrete core. This is only its projection
; face: all parsing, ownership and copying decisions are in CHILDREN above.
(defmacro fn2-upload-stream-manifest-op-events ()
 '(progn
   (defun fn2-upload-repack-entry (base ss sg so se ds dg do kind owner ogen fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
     (code next end fn2-fields fn2-pool)
     (fn2-upload-repack-entry-children base ss sg so se ds dg do kind owner ogen fn2-fields fn2-pool)
     (mv code next end fn2-core)))
   (fn2-core-preserves fn2-upload-repack-entry
    (base ss sg so se ds dg do kind owner ogen fn2-core) :position 3 :rows nil)
   (defcost fn2-upload-repack-entry :child fn2-upload-repack-entry-children
    :answers (:ok :bounds :owner :overlap :decode :encode)
    :bytes *fn2-upload-entry-bytes* :tables (fn2-core-fields fn2-core-pool)
    :doc "Repack one actual decoded entry, retaining source digest/CV refs; no allocator or publication authority.")))
