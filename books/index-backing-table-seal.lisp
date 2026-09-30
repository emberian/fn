; Seal every newly built table page only after all captured row ordinals
; landed. Readiness is produced by this continuation, not a host setter.
(in-package "ACL2")
(logic)
(include-book "index-backing-reinsert")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-ipa-table-seal-ready-p (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((builder (fn-ibp-builder fn-index-backing)) (control (fn-omk-at 18 builder))
        (index (fn-omk-at 1 control)) (pages (fn-omk-at 5 builder)))
  (and (fn-omk-widthp builder 20) (true-listp builder)
       (eq (fn-omk-at 1 builder) :table-seal)
       (eq (fn-omk-at 0 control) :table-seal)
       (natp (fn-omk-at 6 builder))
       (equal (fn-omk-at 17 builder) (+ 1 (fn-omk-at 6 builder)))
       (posp pages) (natp index) (< index pages) (natp (fn-omk-at 10 builder))
       (fn-ibp-directory-cursorp (fn-omk-at 2 control))
       (or (null (fn-omk-at 3 control))
           (fn-ibp-chunk-descriptorp (fn-omk-at 3 control))))))

(defun fn-ipa-table-seal-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil
                 :guard (and (natp fuel) (fn-ipa-table-seal-ready-p fn-index-backing))))
 (let* ((builder (fn-ibp-builder fn-index-backing)) (control (fn-omk-at 18 builder))
        (index (fn-omk-at 1 control)) (descriptor (fn-omk-at 3 control))
        (depth (fn-ibp-slot-depth fn-index-backing)))
  (cond
   ((zp fuel) (mv :yield fuel fn-index-backing))
   ((null descriptor)
    (mv-let (word cursor borrowed left) (fn-ibp-directory-step (fn-omk-at 2 control) 1)
     (let* ((ok (member-eq word '(:yield :borrow-ready)))
            (next (if ok
                      (update-nth 18 (list :table-seal index cursor borrowed) builder)
                    (update-nth 1 :recovery-required builder)))
            (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
      (mv (if ok :table-seal :recovery-required) (+ (- fuel 1) left) fn-index-backing))))
   ((< fuel (* 3 (+ 1 depth))) (mv :yield fuel fn-index-backing))
   (t
    (let* ((physical (nth 1 descriptor)) (id (nth 2 descriptor)) (incarnation (nth 3 descriptor))
           (token (list :index-page id (+ 1 (floor physical 64)) (mod physical 64))))
     (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (word left fn-ibp-node)
      (mv-let (read row ignored remaining fn-ibp-node)
       (fn-ibp-node-page-owner-action token :read nil nil nil nil fuel
                                     (floor physical 64) depth fn-ibp-node)
       (declare (ignore ignored))
       (if (not (and (eq read :present) (natp remaining)
                     (>= remaining (* 2 (+ 1 depth)))
                     (eq (fn-omk-at 2 row) :table) (eq (fn-omk-at 9 row) :building)
                     (equal (fn-omk-at 4 row) id) (equal (fn-omk-at 5 row) incarnation)
                     (equal (fn-omk-at 6 row) 1) (equal (fn-omk-at 7 row) 0)
                     (equal (fn-omk-at 8 row) 0)
                     (equal (fn-omk-at 12 row) (fn-omk-at 2 builder))))
           (mv :recovery-required 0 fn-ibp-node)
         (mv-let (sealed ignored remaining fn-ibp-node)
          (fn-ibp-node-word-action :seal 0 0 physical depth id incarnation remaining fn-ibp-node)
          (declare (ignore ignored))
          (if (not (and (eq sealed :sealed) (natp remaining) (> remaining depth)))
              (mv :recovery-required 0 fn-ibp-node)
            (mv-let (word row ignored remaining fn-ibp-node)
             (fn-ibp-node-page-owner-action token :sealed nil nil nil nil remaining
                                           (floor physical 64) depth fn-ibp-node)
             (declare (ignore row ignored))
             (mv word remaining fn-ibp-node))))))
      (let* ((ok (and (eq word :sealed) (natp left) (<= left fuel)))
             (next-index (+ 1 index)) (done (>= next-index (fn-omk-at 5 builder)))
             (next (if ok
                       (if done (update-nth 1 :ready (update-nth 18 nil builder))
                         (update-nth 18
                          (list :table-seal next-index
                           (fn-ibp-directory-start (fn-omk-at 9 builder) next-index
                                                   (fn-omk-at 10 builder)) nil) builder))
                     (update-nth 1 :recovery-required builder)))
             (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
       (mv (cond ((not ok) :recovery-required) (done :ready) (t :table-seal))
           (if ok left 0) fn-index-backing))))))))
(verify-guards fn-ipa-table-seal-one
 :hints (("Goal" :in-theory
  (e/d (fn-ipa-table-seal-ready-p fn-ibp-directory-cursorp fn-ibp-chunk-descriptorp)
       (fn-ibp-node-page-owner-action fn-ibp-node-word-action)))))
