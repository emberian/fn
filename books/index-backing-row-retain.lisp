; Persistent row-root sharing also owns the actual physical chunks. Retain
; each old full page through its CURRENT owner row before publication. The
; copied partial page is excluded; the builder already owns its new chunk.
(in-package "ACL2")
(logic)
(include-book "index-backing-table-pages")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-ipa-row-share-begin (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (publication (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 builder))))
        (count (fn-omk-at 6 builder)) (depth (fn-ipub-row-depth publication)))
  (cond
   ((zp fuel) (mv :yield fuel fn-index-backing))
   ((not (and (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :table-layout)
              (null (fn-omk-at 17 builder)) (null (fn-ibp-page-pending fn-index-backing))
              (natp count) (natp depth) (equal count (fn-ipub-count publication))))
    (mv :recovery-required fuel fn-index-backing))
   (t
    (let* ((done (zp (floor count 256)))
           (next (if done (update-nth 17 :rows-shared builder)
                   (update-nth 1 :row-share
                    (update-nth 18
                     (list :row-share 0 (fn-ibp-directory-start (fn-ipub-row-root publication) 0 depth) nil)
                     builder))))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv (if done :table-layout :row-share) (- fuel 1) fn-index-backing))))))

(defun fn-ipa-row-share-ready-p (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((builder (fn-ibp-builder fn-index-backing)) (carry (fn-omk-at 18 builder)))
  (and (eq (fn-omk-at 1 builder) :row-share)
       (fn-ibp-directory-cursorp (fn-omk-at 2 carry)))))

(defun fn-ipa-row-share-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (and (natp fuel) (fn-ipa-row-share-ready-p fn-index-backing)) :verify-guards nil))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (publication (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 builder))))
        (continuation (fn-omk-at 18 builder))
        (index (fn-omk-at 1 continuation)) (cursor (fn-omk-at 2 continuation))
        (descriptor (fn-omk-at 3 continuation))
        (count (fn-omk-at 6 builder)) (row-depth (fn-ipub-row-depth publication))
        (depth (fn-ibp-slot-depth fn-index-backing)))
  (cond
   ((zp fuel) (mv :yield fuel fn-index-backing))
   ((not (and (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :row-share)
              (eq (fn-omk-at 0 continuation) :row-share)
              (natp count) (natp row-depth) (natp index) (< index (floor count 256))
              (equal count (fn-ipub-count publication))))
    (mv :recovery-required fuel fn-index-backing))
   ((null descriptor)
    (mv-let (word next-cursor borrowed left) (fn-ibp-directory-step cursor 1)
     (let* ((failed (not (member-eq word '(:yield :borrow-ready))))
            (next (if failed (update-nth 1 :recovery-required builder)
                    (update-nth 18 (list :row-share index next-cursor borrowed) builder)))
            (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
      (mv (if failed :recovery-required :row-share)
          (+ (- fuel 1) left) fn-index-backing))))
   ((< fuel (* 2 (+ 1 depth))) (mv :yield fuel fn-index-backing))
   (t
    (let* ((physical (fn-omk-at 1 descriptor)) (id (fn-omk-at 2 descriptor))
           (incarnation (fn-omk-at 3 descriptor)))
     (if (not (and (eq (fn-omk-at 0 descriptor) :chunk)
                   (natp physical) (posp id) (equal id incarnation)))
         (mv :recovery-required fuel fn-index-backing)
       (let ((token (list :index-page id (+ 1 (floor physical 64)) (mod physical 64))))
        (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
         (word row delta left fn-ibp-node)
         (mv-let (read held ignored remaining fn-ibp-node)
          (fn-ibp-node-page-owner-action token :read nil nil nil nil fuel
                                        (floor physical 64) depth fn-ibp-node)
          (declare (ignore ignored))
          (if (not (and (eq read :present) (natp remaining)
                        (eq (fn-omk-at 2 held) :rows) (eq (fn-omk-at 9 held) :sealed)
                        (equal (fn-omk-at 4 held) id) (equal (fn-omk-at 5 held) incarnation)))
              (mv :recovery-required held 0 (if (natp remaining) remaining 0) fn-ibp-node)
            (fn-ibp-node-page-owner-action token :retain :generation nil nil nil remaining
                                          (floor physical 64) depth fn-ibp-node)))
         (if (not (and (eq word :updated) (equal delta 0)
                       (eq (fn-omk-at 2 row) :rows) (eq (fn-omk-at 9 row) :sealed)))
             (mv :recovery-required left fn-index-backing)
           (let* ((next-index (+ 1 index)) (done (>= next-index (floor count 256)))
                  (next (if done
                            (update-nth 1 :table-layout
                             (update-nth 17 :rows-shared (update-nth 18 nil builder)))
                          (update-nth 18
                           (list :row-share next-index
                            (fn-ibp-directory-start (fn-ipub-row-root publication) next-index row-depth) nil)
                           builder)))
                  (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
            (mv (if done :table-layout :row-share) left fn-index-backing)))))))))))
(verify-guards fn-ipa-row-share-one
 :hints (("Goal" :in-theory (e/d (fn-ipa-row-share-ready-p fn-ibp-directory-cursorp) (fn-ibp-node-page-owner-action)))))
