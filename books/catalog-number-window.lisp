; catalog-number-window.lisp -- the catalog's number range over windows
; (lane join-f2-2, 2026-09-29; PKT-733 (4)).
;
; fn-cnx-range-aux (books/catalog-number-index.lisp) probes once per number
; of a clamped range, so an OVER of a wide range is work proportional to the
; range.  A served arm that must bound its work per step (D27: bound work,
; never data) answers the range as a sequence of bounded windows and resumes;
; that is the range exactly when the range is the concatenation of its
; windows.  The split fn-cnxw-range-is-windows: [K, TOP] is [K, B-1] followed
; by [B, TOP] at every split point B with K <= B <= TOP+1; and so for any
; window width, fn-cnxw-windows (the range cut into windows of W numbers) is
; the range.

(in-package "ACL2")

(include-book "catalog-number-index")

(local (in-theory (disable (tau-system))))

(defthm fn-cnxw-range-is-windows
  (implies (and (natp k) (natp b) (natp top) (<= k b) (<= b (+ 1 top)))
           (equal (fn-cnx-range-aux group k top v fn-cat)
                  (append (fn-cnx-range-aux group k (+ -1 b) v fn-cat)
                          (fn-cnx-range-aux group b top v fn-cat))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cnx-range-aux group k top v fn-cat)
           :in-theory (e/d (fn-cnx-range-aux) (fn-cnx-view-seq)))))

(defthm fn-cnxw-range-empty-above
  (implies (and (natp k) (natp top) (< top k))
           (equal (fn-cnx-range-aux group k top v fn-cat) nil))
  :hints (("Goal" :in-theory (enable fn-cnx-range-aux))))


;; The range answered window by window: W numbers per window (W >= 1).
(defun fn-cnxw-windows (group k top w v fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (natp top) (posp w) (<= k top))
      (append (fn-cnx-range-aux group k (min top (+ k w -1)) v fn-cat)
              (fn-cnxw-windows group (+ k w) top w v fn-cat))
    nil))

; The windows are the range, for every width.
(defthm fn-cnxw-windows-is-range
  (implies (and (natp k) (natp top) (posp w))
           (equal (fn-cnxw-windows group k top w v fn-cat)
                  (fn-cnx-range-aux group k top v fn-cat)))
  :hints (("Goal" :induct (fn-cnxw-windows group k top w v fn-cat)
           :in-theory (e/d (fn-cnxw-windows) (fn-cnx-range-aux)))
          ("Subgoal *1/1" :cases ((<= (+ k w) (+ 1 top)))
                          :use ((:instance fn-cnxw-range-is-windows (b (+ k w)))
                                (:instance fn-cnxw-range-empty-above (k (+ k w)))))
          ("Subgoal *1/2" :use ((:instance fn-cnxw-range-empty-above)))))
