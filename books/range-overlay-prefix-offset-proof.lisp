; Appending an encoded row leaves each earlier byte offset unchanged.
; The new final position starts at the length of the old byte stream.
(in-package "ACL2")
(include-book "range-overlay-arena-proof")

(local
 (defthm fn2-ov-appended-bytes-length
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-ov-append-associates
   (equal (append (append a b) c) (append a (append b c)))))

(defthmd fn2-ov-entries-plus-one
  (implies (true-listp (fn2-layout-octets layout row))
           (equal (fn2-run-entries-octets layout (append rows (list row)))
                  (append (fn2-run-entries-octets layout rows) (fn2-layout-octets layout row))))
  :hints (("Goal" :induct (len rows) :in-theory (disable fn2-layout-octets))))

(local
 (defthm fn2-ov-row-offset-after-append
   (implies (and (natp j) (<= j (len rows)))
            (equal (fn2-run-row-offset j layout (append rows (list row)) off)
                   (fn2-run-row-offset j layout rows off)))
   :hints (("Goal" :induct (fn2-run-row-offset j layout rows off)
            :expand ((fn2-run-row-offset j layout (append rows (list row)) off))
            :in-theory (disable fn2-layout-octets)))))

(local
 (defun-nx fn2-ov-walk-to-end (layout rows off)
   (if (atom rows) off
     (fn2-ov-walk-to-end layout (cdr rows) (+ off (len (fn2-layout-octets layout (car rows))))))))

(local
 (defthm fn2-ov-last-offset
   (implies (natp off)
            (equal (fn2-run-row-offset (len rows) layout rows off)
                   (+ off (len (fn2-run-entries-octets layout rows)))))
   :hints (("Goal" :induct (fn2-ov-walk-to-end layout rows off)
            :expand ((fn2-run-entries-octets layout rows) (fn2-run-row-offset (len rows) layout rows off))
            :in-theory (disable fn2-layout-octets)))))

(defun-nx fn2-ov-index-agrees-before-p (n b ix ix2)
  (if (zp n) t
    (and (equal (fn2-overlay-index-off (+ b (1- n)) ix) (fn2-overlay-index-off (+ b (1- n)) ix2))
         (fn2-ov-index-agrees-before-p (1- n) b ix ix2))))

(local
 (defthm fn2-ov-saved-prefix-offsets
   (implies (and (natp n) (<= n (len rows)) (fn2-ov-index-agrees-before-p n b ix ix2)
                 (fn2-ov-prefix-offsets-p n rows b ix))
            (fn2-ov-prefix-offsets-p n (append rows (list row)) b ix2))
   :hints (("Goal" :induct (fn2-ov-prefix-offsets-p n rows b ix)
            :in-theory (disable fn2-run-row-offset fn2-overlay-index-off len binary-append)))))

(defthm fn2-ov-append-extends-prefix-offsets
  (let ((n (len rows)) (off (len (fn2-run-entries-octets *fn2-overview-entry* rows))))
    (implies (and (fn2-ov-prefix-offsets-p n rows b ix) (fn2-ov-index-agrees-before-p n b ix ix2)
                  (equal (fn2-overlay-index-off (+ b n) ix2) off))
             (fn2-ov-prefix-offsets-p (1+ n) (append rows (list row)) b ix2)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-ov-saved-prefix-offsets (n (len rows))))
           :expand ((fn2-ov-prefix-offsets-p (1+ (len rows)) (append rows (list row)) b ix2))
           :in-theory (disable fn2-ov-saved-prefix-offsets fn2-ov-prefix-offsets-p fn2-ov-index-agrees-before-p
                       fn2-run-row-offset fn2-overlay-index-off fn2-run-entries-octets binary-append len))))
