; Active and sole pending archive header/source ownership. The old active
; descriptor remains immutable while the next tail and manifest are built.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-event-archive
 ((phase (:enum fn2-event-archive-phase (:idle :members :member-complete :manifest :header :header-zero :header-pack :header-seal :page :bound :complete :cold-header :cold-manifest :cold-members :uncertain)))
  (origin (:enum fn2-event-archive-origin (:none :fresh :append :cold)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (candidate :u32) (checkpoint :u60) (history :u60) (incarnation :u60)
  (cut-commit :u60) (cut-event :u60) (previous-cut :u60) (previous-event :u60)
  (first-event :u60) (last-event :u60) (member-runs :u60) (manifest-entries :u60)
  (member-pages :u60) (manifest-pages :u60) (source-pages :u60)
  (member-unit :u60) (member-epoch :u60) (member-allocation :u60) (member-height :u8) (member-entries :u60)
  (member-first-event :u60) (member-last-event :u60) (member-seen :u60)
  (manifest-unit :u60) (manifest-epoch :u60) (manifest-allocation :u60) (manifest-height :u8)
  (header-ordinal :u60) (header-slot :u32) (header-gen :u60) (header-zero :u32) (header-payload :u32)
  (header-unit :u60) (header-epoch :u60) (header-allocation :u60)
  (source-tag :u60) (source-generation :u60) (scan :u60) (next-event :u60) (entry-pending :bool) (leaf-pending :bool)
  (read-armed :bool) (read-offset :u60) (read-sector :u8)
  (read-unit :u60) (read-epoch :u60) (read-allocation :u60) (read-schema :u60) (read-run :u60) (read-level :u8)
  (read-page :u32) (read-page-gen :u60) (read-scratch :u32) (read-scratch-gen :u60)
  (read-candidate :u32) (read-checkpoint :u60) (read-history :u60) (read-incarnation :u60)
  (read-owner-kind :u8) (read-owner-slot :u32) (read-owner-gen :u60))
  :extra-fields
 ((fn2-event-archive-read-hash :type (array (unsigned-byte 32) (8)) :initially 0
   :why "Exact single armed candidate-read hash; not recomputed from a mutable cursor at completion.")
  (fn2-event-archive-read-descriptor :type (array (unsigned-byte 8) (32)) :initially 0
   :why "Single armed read's descriptor binding survives candidate/row interleavings.")
  (fn2-event-archive-words :type (array (unsigned-byte 32) (48)) :initially 0
   :why "Per active/pending row: actual completed member root, manifest root and cut-C seal, eight words each.")
  (fn2-event-archive-descriptor :type (array (unsigned-byte 8) (64)) :initially 0
   :why "Exact active/pending descriptor bindings; neither aliases investigation scratch.")))

(defun fn2-event-archive-word (r kind i fn2-event-archive)
 (declare (xargs :stobjs fn2-event-archive
  :guard (and (fn2-event-archive-wfp fn2-event-archive) (natp r) (< r 2)
              (member-eq kind '(:member :manifest :cut-seal)) (natp i) (< i 8))))
 (fn2-event-archive-wordsi (+ (* r 24) (case kind (:member 0) (:manifest 8) (otherwise 16)) i) fn2-event-archive))

; Construction and cold discovery both retain their exact candidate even
; before a serving tag/generation exists. Uncertain rows retain ownership.
(defun fn2-event-archive-candidate-held-p (c checkpoint fn2-event-archive)
 (declare (xargs :stobjs fn2-event-archive :guard (fn2-event-archive-wfp fn2-event-archive)))
 (and (natp c) (unsigned-byte-p 60 checkpoint)
  (or (and (< 0 (fn2-event-archive-rows fn2-event-archive))
           (not (equal (fn2-event-archive-phase 0 fn2-event-archive) *fn2-event-archive-phase-idle*))
           (equal (fn2-event-archive-candidate 0 fn2-event-archive) c)
           (equal (fn2-event-archive-checkpoint 0 fn2-event-archive) checkpoint))
      (and (< 1 (fn2-event-archive-rows fn2-event-archive))
           (not (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-idle*))
           (equal (fn2-event-archive-candidate 1 fn2-event-archive) c)
           (equal (fn2-event-archive-checkpoint 1 fn2-event-archive) checkpoint)))))
