; Pure layout arithmetic shared by allocation admission and C's static schema
; inventory. A guard reservation is not an entry write footprint.
(in-package "ACL2")
(include-book "format-base")
(fn2-book-layer :b)
(defconst *fn2-succ-slots* 24)
(defun fn2-successor-block-fields (fields values)
 (declare (xargs :guard (and (natp fields) (natp values))))
 (+ (* 3 (nfix fields)) (nfix values) 1))
(defun fn2-successor-required-fields (fields values slots entry-guard reader-fields)
 (declare (xargs :guard (and (natp fields) (natp values) (natp slots) (natp entry-guard) (natp reader-fields))))
 (let ((block (fn2-successor-block-fields fields values)))
  (max (+ (* (nfix slots) block) 4 (nfix entry-guard) (nfix reader-fields))
       (+ (* (nfix (- (nfix slots) 1)) block) (nfix entry-guard)))))
(defun fn2-successor-scratch-bytes (octets)
 (declare (xargs :guard (natp octets)))
 (* *fn2-format-sector-size* (max 1 (ceiling (nfix octets) *fn2-format-sector-size*))))
(defthm fn2-successor-block-fields-covers-regions
 (implies (and (natp fields) (natp values))
  (and (<= fields (* 2 fields))
       (<= (* 2 fields) (* 3 fields))
       (< (+ (* 3 fields) values) (fn2-successor-block-fields fields values))))
 :hints (("Goal" :in-theory (enable fn2-successor-block-fields))))

; Pool octets only: rehome read+write, each search/final order decode+key
; compare, then the encoder's source reads and destination writes.
(defun fn2-successor-slot-bind-byte-bound (entry key-octets octets search)
 (declare (xargs :guard (and (natp entry) (natp key-octets) (natp octets) (natp search))))
 (+ (* 2 (nfix octets))
    (* (+ 1 (nfix search)) (+ (nfix entry) (* 2 (nfix key-octets))))
    (nfix entry) (nfix octets)))
