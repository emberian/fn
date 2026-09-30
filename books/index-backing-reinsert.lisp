; Reinsert oldest-first captured row ordinals into the unpublished table.
; The current builder owns roots/key/held references; no host row or tag is an
; argument. Its carried O invariant supplies bounded valid Message-IDs and
; the 32-octet key. Constructor/runtime admission is not established here.
(in-package "ACL2")
(logic)
(include-book "index-backing-table-place")
(local (include-book "arithmetic-5/top" :dir :system))

; Control8: tag,ordinal,phase,directory cursor,heldref,tag,probe,descriptor.
(defun fn-ipa-reinsert-ready-p (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (control (fn-omk-at 18 builder)) (phase (fn-omk-at 2 control))
        (ordinal (fn-omk-at 1 control)) (pages (fn-omk-at 5 builder)))
  (and (fn-omk-widthp builder 20) (true-listp builder)
       (fn-omk-widthp control 8) (true-listp control)
       (eq (fn-omk-at 1 builder) :table-reinsert)
       (eq (fn-omk-at 0 control) :table-reinsert)
       (natp ordinal) (unsigned-byte-p 64 (+ 1 ordinal))
       (natp (fn-omk-at 6 builder)) (<= ordinal (fn-omk-at 6 builder))
       (posp pages) (natp (fn-omk-at 10 builder)) (natp (fn-omk-at 13 builder))
       (cond
        ((member-eq phase '(:row-directory :table-directory))
         (fn-ibp-directory-cursorp (fn-omk-at 3 control)))
        ((eq phase :row-read) (fn-ibp-chunk-descriptorp (fn-omk-at 7 control)))
        ((eq phase :tag)
         (and (fn-record-msgidp (fn-record-msgid (fn-omk-at 4 control)))
              (true-listp (fn-omk-at 4 builder)) (equal (len (fn-omk-at 4 builder)) 32)))
        ((eq phase :place)
         (and (fn-ibp-chunk-descriptorp (fn-omk-at 7 control))
              (posp (fn-omk-at 5 control)) (unsigned-byte-p 64 (fn-omk-at 5 control))
              (fn-mpr-cursorp (fn-omk-at 6 control) pages)))
        (t nil)))))

(defun fn-ipa-reinsert-begin (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (count (fn-omk-at 6 builder)) (row-depth (fn-omk-at 13 builder)))
  (cond
   ((zp fuel) (mv :yield fuel fn-index-backing))
   ((not (and (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :table-reinsert)
              (equal (fn-omk-at 18 builder) '(:table-reinsert 0 nil))
              (natp count) (unsigned-byte-p 64 (+ 1 count)) (natp row-depth)
              (posp (fn-omk-at 5 builder)) (natp (fn-omk-at 10 builder))
              (eq (fn-omk-at 17 builder) :rows-shared)
              (null (fn-ibp-page-pending fn-index-backing))))
    (mv :recovery-required fuel fn-index-backing))
   (t
    (let* ((control (list :table-reinsert 0 :row-directory
                    (fn-ibp-directory-start (fn-omk-at 12 builder) 0 row-depth) nil nil nil nil))
           (fn-index-backing (update-fn-ibp-builder (update-nth 18 control builder) fn-index-backing)))
     (mv :table-reinsert (- fuel 1) fn-index-backing))))))

(defun fn-ipa-reinsert-directory-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil
                 :guard (and (natp fuel) (fn-ipa-reinsert-ready-p fn-index-backing)
                             (member-eq (fn-omk-at 2 (fn-omk-at 18 (fn-ibp-builder fn-index-backing)))
                                        '(:row-directory :table-directory)))))
 (if (zp fuel) (mv :yield fuel fn-index-backing)
  (let* ((builder (fn-ibp-builder fn-index-backing))
         (control (fn-omk-at 18 builder)) (phase (fn-omk-at 2 control)))
   (mv-let (word cursor descriptor left) (fn-ibp-directory-step (fn-omk-at 3 control) 1)
    (let* ((failed (not (member-eq word '(:yield :borrow-ready))))
           (next-control
            (if (eq word :borrow-ready)
                (update-nth 2 (if (eq phase :row-directory) :row-read :place)
                 (update-nth 7 descriptor (update-nth 3 cursor control)))
              (update-nth 3 cursor control)))
           (next (if failed (update-nth 1 :recovery-required builder)
                   (update-nth 18 next-control builder)))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv (if failed :recovery-required :table-reinsert) (+ (- fuel 1) left) fn-index-backing))))))
(verify-guards fn-ipa-reinsert-directory-one
 :hints (("Goal" :in-theory (enable fn-ipa-reinsert-ready-p fn-ibp-directory-cursorp))))

(defun fn-ipa-reinsert-row-read (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil
                 :guard (and (natp fuel) (fn-ipa-reinsert-ready-p fn-index-backing)
                             (eq (fn-omk-at 2 (fn-omk-at 18 (fn-ibp-builder fn-index-backing))) :row-read))))
 (let* ((builder (fn-ibp-builder fn-index-backing)) (control (fn-omk-at 18 builder))
        (descriptor (fn-omk-at 7 control)) (ordinal (fn-omk-at 1 control))
        (depth (fn-ibp-slot-depth fn-index-backing))
        (allowance (min fuel *fn-mpr-slot-quantum*)))
  (if (<= allowance depth) (mv :yield fuel fn-index-backing)
   (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
    (word held left)
    (fn-ibp-node-row-read ordinal allowance (nth 1 descriptor) depth
                          (nth 2 descriptor) (nth 3 descriptor) fn-ibp-node)
    (let* ((ok (and (eq word :row) (natp left) (<= left allowance)))
           (next (if ok
                     (update-nth 18 (update-nth 2 :tag (update-nth 4 held control)) builder)
                   (update-nth 1 :recovery-required builder)))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv (if ok :table-reinsert :recovery-required)
         (if ok (+ (- fuel allowance) left) 0) fn-index-backing))))))
(verify-guards fn-ipa-reinsert-row-read
 :hints (("Goal" :in-theory
  (e/d (fn-ipa-reinsert-ready-p fn-ibp-chunk-descriptorp) (fn-ibp-node-row-read)))))

(defun fn-ipa-reinsert-tag (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (and (natp fuel)
  (fn-ipa-reinsert-ready-p fn-index-backing)
  (eq (fn-omk-at 2 (fn-omk-at 18 (fn-ibp-builder fn-index-backing))) :tag))))
 (if (zp fuel) (mv :yield fuel fn-index-backing)
  (let* ((builder (fn-ibp-builder fn-index-backing)) (control (fn-omk-at 18 builder))
         (pages (fn-omk-at 5 builder))
         (tag (fn-mpxt-tag (fn-record-msgid (fn-omk-at 4 control)) (fn-omk-at 4 builder)))
         (home (fn-mpx-home tag pages)) (probe (list home pages 0))
         (directory (fn-ibp-directory-start (fn-omk-at 9 builder) home (fn-omk-at 10 builder)))
         (next (update-nth 2 :table-directory
                (update-nth 3 directory (update-nth 5 tag (update-nth 6 probe control)))))
         (fn-index-backing (update-fn-ibp-builder (update-nth 18 next builder) fn-index-backing)))
   (mv :table-reinsert (- fuel 1) fn-index-backing))))

(defun fn-ipa-reinsert-place-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil
                 :guard (and (natp fuel) (fn-ipa-reinsert-ready-p fn-index-backing)
                             (eq (fn-omk-at 2 (fn-omk-at 18 (fn-ibp-builder fn-index-backing))) :place))))
 (let* ((builder (fn-ibp-builder fn-index-backing)) (control (fn-omk-at 18 builder))
        (descriptor (fn-omk-at 7 control)) (ordinal (fn-omk-at 1 control))
        (pages (fn-omk-at 5 builder)) (depth (fn-ibp-slot-depth fn-index-backing)))
  (if (<= fuel depth) (mv :yield fuel fn-index-backing)
   (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
    (word probe left fn-ibp-node)
    (fn-ibp-node-table-place-one (fn-omk-at 5 control) ordinal (fn-omk-at 6 control) pages
                                 (nth 1 descriptor) depth (nth 2 descriptor) (nth 3 descriptor)
                                 fuel fn-ibp-node)
    (let* ((ok (and (member-eq word '(:placed :yield)) (natp left) (<= left fuel)
                    (fn-mpr-cursorp probe pages)))
           (next-ordinal (+ 1 ordinal))
           (done (and (eq word :placed) (> next-ordinal (fn-omk-at 6 builder))))
           (next-control
            (if (not ok) control
             (cond
             (done
              (list :table-seal 0 (fn-ibp-directory-start (fn-omk-at 9 builder) 0
                                                        (fn-omk-at 10 builder)) nil))
             ((eq word :placed)
              (list :table-reinsert next-ordinal :row-directory
               (fn-ibp-directory-start (fn-omk-at 12 builder) (floor next-ordinal 256)
                                       (fn-omk-at 13 builder)) nil nil nil nil))
             (t
              (update-nth 2 :table-directory
               (update-nth 3
                (fn-ibp-directory-start (fn-omk-at 9 builder) (nth 0 probe)
                                        (fn-omk-at 10 builder))
                (update-nth 6 probe control)))))))
           (next (if ok
                     (update-nth 1 (if done :table-seal :table-reinsert)
                      (update-nth 17 (if (eq word :placed) next-ordinal (fn-omk-at 17 builder))
                       (update-nth 18 next-control builder)))
                   (update-nth 1 :recovery-required builder)))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv (cond ((not ok) :recovery-required) (done :table-seal) (t :table-reinsert))
         (if ok left 0) fn-index-backing))))))
(verify-guards fn-ipa-reinsert-place-one
 :hints (("Goal" :in-theory
  (e/d (fn-ipa-reinsert-ready-p fn-ibp-chunk-descriptorp fn-mpr-cursorp)
       (fn-ibp-node-table-place-one)))))
