; Relate each restart index to the row number and byte offset that it names.
(in-package "ACL2")
(include-book "runs-page")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defun-nx fn2-run-row-offset (n layout rows off)
  (if (or (zp n) (atom rows)) off
    (fn2-run-row-offset (1- n) layout (cdr rows) (+ off (len (fn2-layout-octets layout (car rows)))))))

(local
 (defthm fn2-run-restart-distance-residue
   (let ((i (+ (* 16 q) r)))
     (implies (and (integerp q) (natp r) (< r 16))
              (and (equal (equal (mod (- i) 16) 0) (equal (mod i 16) 0))
                   (equal (mod (- (1+ i)) 16)
                          (if (equal (mod i 16) 0) 15 (1- (mod (- i) 16)))))))
   :rule-classes nil
   :hints (("Goal" :cases ((equal r 0) (equal r 1) (equal r 2) (equal r 3) (equal r 4) (equal r 5) (equal r 6) (equal r 7) (equal r 8) (equal r 9) (equal r 10) (equal r 11) (equal r 12) (equal r 13) (equal r 14) (equal r 15))))))
(local
 (defthm fn2-run-restart-distance-step
   (implies (natp i)
            (and (equal (equal (mod (- i) 16) 0) (equal (mod i 16) 0))
                 (equal (mod (- (1+ i)) 16)
                        (if (equal (mod i 16) 0) 15 (1- (mod (- i) 16))))))
   :hints (("Goal" :use ((:instance fn2-run-restart-distance-residue (q (floor i 16)) (r (mod i 16))))))))

(local
 (defun-nx fn2-run-seek-restart-row (j i layout rows off)
   (declare (xargs :measure (len rows)))
   (if (atom rows) off
     (if (and (equal (mod i *fn2-run-restart-interval*) 0) (zp j)) off
       (fn2-run-seek-restart-row (if (equal (mod i *fn2-run-restart-interval*) 0) (1- j) j)
         (1+ i) layout (cdr rows) (+ off (len (fn2-layout-octets layout (car rows)))))))))

(local (defun fn2-run-distance-to-restart (i)
         (declare (xargs :verify-guards nil)) (mod (- i) *fn2-run-restart-interval*)))
(local
 (defthm fn2-run-restart-distance-after-row
   (implies (natp i)
      (and (natp (fn2-run-distance-to-restart i))
           (equal (equal (fn2-run-distance-to-restart i) 0) (equal (mod i 16) 0))
           (equal (fn2-run-distance-to-restart (1+ i))
                  (if (equal (mod i 16) 0) 15 (1- (fn2-run-distance-to-restart i))))))
   :hints (("Goal" :use fn2-run-restart-distance-step :in-theory (disable fn2-run-restart-distance-step mod)))))
(local
 (defthm fn2-run-distance-at-restart
   (implies (and (natp i) (equal (mod i 16) 0))
            (equal (fn2-run-distance-to-restart i) 0))
   :hints (("Goal" :use fn2-run-restart-distance-after-row
            :in-theory (disable fn2-run-distance-to-restart fn2-run-restart-distance-after-row mod)))))
(local
 (defthm fn2-run-distance-before-restart
   (implies (and (natp i) (not (equal (mod i 16) 0)))
            (< 0 (fn2-run-distance-to-restart i)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :use fn2-run-restart-distance-after-row
            :in-theory (disable fn2-run-distance-to-restart fn2-run-restart-distance-after-row mod)))))
(local
 (defthm fn2-run-restart-distance-natural
   (implies (integerp i) (natp (fn2-run-distance-to-restart i)))
   :rule-classes :type-prescription))
(local
 (defthmd fn2-run-specified-restart-row-offset
  (let* ((offsets (fn2-run-restart-offsets-spec layout rows i off))
         (p (+ (fn2-run-distance-to-restart i) (* j *fn2-run-restart-interval*))))
    (implies (and (natp i) (natp j) (< j (len offsets)))
             (and (< p (len rows))
                  (equal (nth j offsets) (fn2-run-row-offset p layout rows off)))))
  :hints (("Goal" :induct (fn2-run-seek-restart-row j i layout rows off)
           :do-not '(preprocess)
           :expand ((fn2-run-restart-offsets-spec layout rows i off) (len rows)
                    (:free (p) (fn2-run-row-offset p layout rows off)))
           :in-theory (disable fn2-run-row-offset fn2-run-restart-offsets-spec fn2-layout-octets fn2-run-distance-to-restart mod)))))

(defthmd fn2-run-page-restart-names-row
  (let ((offsets (fn2-run-restart-offsets-spec layout rows 0 off)))
    (implies (and (natp j) (< j (len offsets)))
             (and (< (* j *fn2-run-restart-interval*) (len rows))
                  (equal (nth j offsets)
                         (fn2-run-row-offset (* j *fn2-run-restart-interval*) layout rows off)))))
  :hints (("Goal" :use ((:instance fn2-run-specified-restart-row-offset (i 0)))
           :in-theory (disable fn2-run-restart-offsets-spec fn2-run-row-offset))))

(local
 (defthm fn2-run-restart-intervals-cover-remaining-rows
   (implies (natp i)
            (<= (len rows)
                (+ (fn2-run-distance-to-restart i)
                   (* *fn2-run-restart-interval* (len (fn2-run-restart-offsets-spec layout rows i off))))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-restart-offsets-spec layout rows i off)
            :do-not '(preprocess)
            :expand ((:free (k) (fn2-run-restart-offsets-spec layout rows k off)) (len rows))
            :in-theory (disable fn2-run-distance-to-restart (:definition fn2-run-restart-offsets-spec) fn2-layout-octets mod)))))

(defthmd fn2-run-page-restarts-cover-rows
  (<= (len rows) (* *fn2-run-restart-interval* (len (fn2-run-restart-offsets-spec layout rows 0 off))))
  :hints (("Goal" :use ((:instance fn2-run-restart-intervals-cover-remaining-rows (i 0)))
           :in-theory (disable fn2-run-restart-offsets-spec))))
