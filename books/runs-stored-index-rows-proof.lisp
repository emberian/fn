; The stored parent body and the writer restart table describe the same
; sequence of child references, including across restart intervals.
(in-package "ACL2")
(include-book "runs-builder-page-contents-proof")

(defun-nx fn2-run-stored-index-rows-p (rows w dst dg rs p)
  (let* ((body (fn2-run-entries-octets *fn2-overview-index* rows))
         (offsets (fn2-run-restart-offsets-spec *fn2-overview-index* rows 0 *fn2-run-entries-base*)))
    (and (equal (fn2-run-read-bytes (len body) dst dg *fn2-run-entries-base* 9 0 1 p) body)
         (equal (fn2-run-saved-offsets (len offsets) (* w *fn2-run-restart-capacity*) rs) offsets))))

(local (defthm fn2-run-index-list-length (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-run-append-admitted-reference
   (equal (fn2-run-entries-layoutp layout (append rows (list row)))
          (and (fn2-run-entries-layoutp layout (true-list-fix rows)) (fn2-run-values-layoutp layout row)))
   :hints (("Goal" :induct (len rows) :in-theory (e/d (true-list-fix) (fn2-run-values-layoutp))))))

(defthmd fn2-run-index-append-extents
  (let* ((body (fn2-run-entries-octets *fn2-overview-index* rows)) (bytes (fn2-layout-octets *fn2-overview-index* row))
         (offsets (fn2-run-restart-offsets-spec *fn2-overview-index* rows 0 *fn2-run-entries-base*))
         (restartp (equal (mod (len rows) *fn2-run-restart-interval*) 0)) (joined (append rows (list row))))
    (and (equal (fn2-run-entries-octets *fn2-overview-index* joined) (append body bytes))
         (equal (fn2-run-restart-offsets-spec *fn2-overview-index* joined 0 *fn2-run-entries-base*)
                (append offsets (if restartp (list (+ *fn2-run-entries-base* (len body))) nil)))
         (equal (len joined) (1+ (len rows)))
         (equal (fn2-run-entries-layoutp *fn2-overview-index* joined)
                (and (fn2-run-entries-layoutp *fn2-overview-index* (true-list-fix rows))
                     (fn2-run-values-layoutp *fn2-overview-index* row)))))
  :hints (("Goal" :use ((:instance fn2-run-spliced-restart-offsets (layout *fn2-overview-index*) (i 0)
                                      (off *fn2-run-entries-base*) (tail (list row)))
                         (:instance fn2-run-spliced-entry-bytes (layout *fn2-overview-index*) (tail (list row))))
           :expand ((fn2-run-entries-octets *fn2-overview-index* nil)
                    (fn2-run-entries-octets *fn2-overview-index* (list row))
                    (:free (i at) (fn2-run-restart-offsets-spec *fn2-overview-index* nil i at))
                    (:free (i at) (fn2-run-restart-offsets-spec *fn2-overview-index* (list row) i at)))
           :in-theory (disable fn2-run-spliced-entry-bytes fn2-run-entries-octets fn2-run-restart-offsets-spec
                               fn2-run-values-layoutp fn2-layout-octets mod))))

(defthmd fn2-run-index-extends-stored-sequence
  (let* ((body (fn2-run-entries-octets *fn2-overview-index* rows)) (bytes (fn2-layout-octets *fn2-overview-index* row))
         (off (+ *fn2-run-entries-base* (len body)))
         (nr (len (fn2-run-restart-offsets-spec *fn2-overview-index* rows 0 *fn2-run-entries-base*)))
         (at (* w *fn2-run-restart-capacity*)) (restartp (equal (mod (len rows) *fn2-run-restart-interval*) 0)))
    (implies (and (fn2-run-stored-index-rows-p rows w dst dg rs p)
                  (equal (fn2-run-read-bytes (len body) dst dg *fn2-run-entries-base* 9 0 1 after)
                         (fn2-run-read-bytes (len body) dst dg *fn2-run-entries-base* 9 0 1 p))
                  (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 after) bytes)
                  (equal (fn2-run-saved-offsets (if restartp (1+ nr) nr) at newrs)
                         (append (fn2-run-saved-offsets nr at rs) (if restartp (list off) nil))))
             (fn2-run-stored-index-rows-p (append rows (list row)) w dst dg newrs after)))
  :hints (("Goal" :do-not '(preprocess) :use (fn2-run-index-append-extents
                  (:instance fn2-run-read-prefix (n (len (fn2-run-entries-octets *fn2-overview-index* rows)))
                      (m (len (fn2-layout-octets *fn2-overview-index* row))) (at *fn2-run-entries-base*)
                      (slot dst) (gen dg) (pk 9) (ps 0) (pg 1) (pool after)))
           :cases ((equal (mod (len rows) *fn2-run-restart-interval*) 0))
           :in-theory (e/d (fn2-run-stored-index-rows-p)
                    (fn2-run-saved-offsets fn2-run-read-bytes fn2-run-spliced-entry-bytes fn2-run-entries-octets
                     fn2-run-restart-offsets-spec fn2-run-values-layoutp fn2-run-entries-layoutp fn2-layout-octets
                     binary-append mod)))))
