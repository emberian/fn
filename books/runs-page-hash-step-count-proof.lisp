; Before the padding boundary, chunk alignment can leave a short tail.
; Beyond it, every nonfinal full-budget page span consumes at least 3 KiB.
(in-package "ACL2")
(include-book "format-check")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defun fn2-run-page-hash-spans-left (pos pad)
  (declare (xargs :guard (and (natp pos) (natp pad))))
  (+ (if (< pos pad) (if (< (- pad pos) 1024) 1 2) 0)
     (if (< pos 65536) (1+ (floor (- 65535 pos) 1024)) 0)))

(local
 (defthm fn2-run-hash-alignment-leaves-short-tail
   (let ((k (fn2-fc-aligned-count size used more)))
     (implies (and (posp size) (natp used))
              (and (posp k) (<= k size) (< (- size k) 1024)
                   (implies (or (not more) (< size 1024)) (equal k size)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance mod-bounds-2 (x (+ used size)) (y 1024)))
            :in-theory (enable fn2-fc-aligned-count)))))

(defthmd fn2-run-page-hash-span-size
  (let ((k (fn2-fc-span-size 4096 pos pad 65536 used)))
    (implies (and (natp pos) (< pos 65536) (natp pad) (<= pad 2048) (natp used))
             (and (posp k) (<= (+ pos k) 65536)
                  (if (< pos pad)
                      (and (<= (+ pos k) pad) (< (- pad (+ pos k)) 1024)
                           (implies (< (- pad pos) 1024) (equal (+ pos k) pad)))
                    (if (<= (- 65536 pos) 4096) (equal (+ pos k) 65536) (< 3072 k))))))
  :hints (("Goal" :cases ((< pos pad) (< pos 61440) (equal pos 61440))
           :use ((:instance fn2-run-hash-alignment-leaves-short-tail (size (- pad pos)) (more (< pad 65536)))
                 (:instance fn2-run-hash-alignment-leaves-short-tail (size (- 65536 pos)) (more nil))
                 (:instance fn2-run-hash-alignment-leaves-short-tail (size 4096) (more (< pos 61440))))
           :in-theory (e/d (fn2-fc-span-size) (fn2-fc-aligned-count floor mod)))))

(local
 (defthm fn2-run-page-hash-rank-decreases
   (implies (and (natp pos) (< pos 65536) (natp pad) (<= pad 2048)
                 (posp k) (<= (+ pos k) 65536)
                 (if (< pos pad)
                     (and (<= (+ pos k) pad) (< (- pad (+ pos k)) 1024)
                          (implies (< (- pad pos) 1024) (equal (+ pos k) pad)))
                   (or (equal (+ pos k) 65536) (< 3072 k))))
            (< (fn2-run-page-hash-spans-left (+ pos k) pad) (fn2-run-page-hash-spans-left pos pad)))
   :hints (("Goal" :in-theory (enable fn2-run-page-hash-spans-left)))))

(defthmd fn2-run-full-budget-hash-span-decreases-count
  (let ((k (fn2-fc-span-size 4096 pos pad 65536 used))
        (left (fn2-run-page-hash-spans-left pos pad)))
    (implies (and (natp pos) (< pos 65536) (natp pad) (<= pad 2048) (natp used))
             (and (posp left) (<= left 66)
                  (natp (fn2-run-page-hash-spans-left (+ pos k) pad))
                  (< (fn2-run-page-hash-spans-left (+ pos k) pad) left))))
  :hints (("Goal" :use (fn2-run-page-hash-span-size
                 (:instance fn2-run-page-hash-rank-decreases (k (fn2-fc-span-size 4096 pos pad 65536 used))))
           :in-theory (e/d (fn2-run-page-hash-spans-left) (fn2-fc-span-size fn2-run-page-hash-rank-decreases)))))
