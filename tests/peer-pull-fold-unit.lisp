; Execute the generated concrete cursor fold on every immutable pull
; coordinate. Refusals must frame the full materialized row.
(in-package "ACL2")
(include-book "../books/folds")

(defconst *fn2-pfu-next*
 '(7 11 13 17 19 23 29 31 37 41 43 1 5 9 0
   72057594037927935 72057594037927934 281474976710655 281474976710654 281474976710653
   101 102 103 104 105))

(defconst *fn2-pfu-row*
 '(7 11 5 0 0 0 0 1 13 17 19 23 29 31 37 41 43 1
   72057594037927935 72057594037927934 281474976710655 281474976710654 281474976710653))

(defun fn2-pfu-fill (at values fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil))
 (if (atom values) fn2-fields
   (let ((fn2-fields (fn2-fields-set-value at (car values) fn2-fields)))
    (fn2-pfu-fill (+ 1 (nfix at)) (cdr values) fn2-fields))))

(defun fn2-pfu-row-equalp (at values fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil :measure (acl2-count values)))
 (or (atom values)
     (and (equal (car values) (fn2-fields-value at fn2-fields))
          (fn2-pfu-row-equalp (+ 1 (nfix at)) (cdr values) fn2-fields))))

(defun fn2-pfu-apply (event fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil))
 (let ((fn2-fields (fn2-pfu-fill 64 event fn2-fields)))
  (fn2-consumer-cursor-fold-apply :pull-advance 0 64 fn2-fields)))

(defun fn2-pfu-refuse-all (cases fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil :measure (acl2-count cases)))
 (if (atom cases) (mv t fn2-fields)
   (mv-let (code fn2-fields) (fn2-pfu-apply (car cases) fn2-fields)
    (if (and (eq code :refused) (fn2-pfu-row-equalp 0 *fn2-pfu-row* fn2-fields))
        (fn2-pfu-refuse-all (cdr cases) fn2-fields)
      (mv nil fn2-fields)))))

(defun fn2-pfu-run (fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil))
 (b* ((fn2-fields (fn2-fields-init 128 fn2-fields))
      (fn2-fields (fn2-pfu-fill 0 '(7 11) fn2-fields))
      (first (append '(7 11 13 17 19 23 29 31 37 41 43 1 0 5 1 0 0 0 0 0)
                     (nthcdr 18 *fn2-pfu-row*)))
      ((mv created fn2-fields) (fn2-pfu-apply first fn2-fields))
      (first-ok (and (eq created :ok) (fn2-pfu-row-equalp 0 *fn2-pfu-row* fn2-fields)))
      ((mv refusals fn2-fields)
       (fn2-pfu-refuse-all
        (list first
              (update-nth 12 4 *fn2-pfu-next*)
              (update-nth 13 5 *fn2-pfu-next*)
              (update-nth 8 38 *fn2-pfu-next*)
              (update-nth 9 42 *fn2-pfu-next*)
              (update-nth 15 1 *fn2-pfu-next*)
              (update-nth 16 2 *fn2-pfu-next*)
              (update-nth 17 3 *fn2-pfu-next*)
              (update-nth 18 4 *fn2-pfu-next*)
              (update-nth 19 5 *fn2-pfu-next*)) fn2-fields))
      ((mv advanced fn2-fields) (fn2-pfu-apply *fn2-pfu-next* fn2-fields))
      (next (append (take 18 (update-nth 2 9 *fn2-pfu-row*)) '(101 102 103 104 105)))
      (advanced-ok (and (eq advanced :ok) (fn2-pfu-row-equalp 0 next fn2-fields)))
      ((mv duplicate fn2-fields) (fn2-pfu-apply *fn2-pfu-next* fn2-fields)))
  (mv (and first-ok refusals advanced-ok
           (eq duplicate :refused) (fn2-pfu-row-equalp 0 next fn2-fields)) fn2-fields)))

(defun fn2-pfu-check ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (ok fn2-fields) (fn2-pfu-run fn2-fields)
   ok)))

(assert-event (fn2-pfu-check))
