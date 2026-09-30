; One actual placement-slot action on an unpublished registered chunk.
; Provider-selected directory/stamp and current writer carry authorize the
; call; this internal lower kernel never accepts a native page object.
(in-package "ACL2")
(logic)
(include-book "index-backing-row-retain")
(local (include-book "arithmetic-5/top" :dir :system))
(defun fn-ibp-node-table-place-one
 (tag ordinal cursor pages physical depth id incarnation fuel fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (posp tag) (unsigned-byte-p 64 tag)
                             (natp ordinal) (unsigned-byte-p 64 (+ 1 ordinal))
                             (fn-mpr-cursorp cursor pages)
                             (natp physical) (natp depth) (posp id)
                             (natp incarnation) (natp fuel))))
 (cond
  ((<= fuel depth) (mv :yield cursor fuel fn-ibp-node))
  ((zp depth)
   (if (not (and (zp physical)
                 (fn-ibp-node-children-boundp 'fn-ibp-table-page fn-ibp-node)))
       (mv :unavailable cursor fuel fn-ibp-node)
     (stobj-let ((fn-ibp-table-page
                  (fn-ibp-node-children-get 'fn-ibp-table-page fn-ibp-node
                                            (create-fn-ibp-table-page))))
      (word next left fn-ibp-table-page)
      (if (not (and (equal (fn-ibp-table-id fn-ibp-table-page) id)
                    (equal (fn-ibp-table-incarnation fn-ibp-table-page) incarnation)
                    (equal (fn-ibp-table-sealed fn-ibp-table-page) 0)))
          (mv :recovery-required cursor 1 fn-ibp-table-page)
        (fn-miw-chunk-place tag ordinal cursor 1 pages (nth 0 cursor) fn-ibp-table-page))
      (if (and (natp left) (<= left 1))
          (mv word next (+ (- fuel 1) left) fn-ibp-node)
        (mv :recovery-required cursor 0 fn-ibp-node)))))
  ((equal (mod physical 2) 0)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
       (mv :unavailable cursor fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-left
                  (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                            (create-fn-ibp-node-left))))
      (word next left fn-ibp-node-left)
      (fn-ibp-node-table-place-one tag ordinal cursor pages (floor physical 2)
                                   (- depth 1) id incarnation (- fuel 1) fn-ibp-node-left)
      (mv word next left fn-ibp-node))))
  (t
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
       (mv :unavailable cursor fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-right
                  (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                            (create-fn-ibp-node-right))))
      (word next left fn-ibp-node-right)
      (fn-ibp-node-table-place-one tag ordinal cursor pages (floor physical 2)
                                   (- depth 1) id incarnation (- fuel 1) fn-ibp-node-right)
      (mv word next left fn-ibp-node))))))
(verify-guards fn-ibp-node-table-place-one
 :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))
