; Scalar physical allocation for the census-driven private history writer.
; This does not allocate a vector, run, singles list, file or resource lease.
(in-package "ACL2")
(include-book "pagestore-exec")

(defun fn-hpl-layout (n)
  (declare (xargs :guard t))
  (if (not (and (natp n) (< n 18446744073709551616)))
      (list :refused :out-of-range)
    (let* ((nt (pgs-x-ntables n))
           ; Do NOT call pgs-dir-run-pages here: its pgs-ntables executes
           ; the logical per-table loop. The concrete O(1) count is above.
           (m (pgs-ptab-run-pages nt))
           (data (+ 1 m)) (table (+ data n)) (end (+ table nt)))
      (if (or (<= 4294967296 m) (<= 18446744073709551616 end))
          (list :refused :out-of-range)
        (list :layout n nt m data table end)))))

(local
 (defthm fn-hpl-take-fresh-singles
   (implies (and (natp n) (natp h))
            (equal (pgs-take-singles n nil h)
                   (mv (pgs-run h n) nil (+ h n))))
   :hints (("Goal" :induct (pgs-take-singles n nil h)
            :in-theory (enable pgs-take-singles pgs-run)))))

(defthm fn-hpl-fresh-allocation
  (implies (and (natp singles) (posp m))
           (equal (pgs-alloc singles m '(nil 1))
                  (list 1 (pgs-run (+ 1 m) singles) nil (+ 1 m singles))))
  :hints (("Goal" :in-theory (enable pgs-alloc pgs-find-free-run)
           :cases ((equal m 1)))))

; The returned scalar layout names exactly the production allocator's
; directory start, singles base and high water. PGS-RUN appears only in
; the theorem's model: executable construction never materializes it.
(defthm fn-hpl-layout-refines-fresh-allocation
  (implies (equal (car (fn-hpl-layout n)) :layout)
           (let ((p (fn-hpl-layout n)))
             (equal (pgs-alloc (+ n (nth 2 p)) (nth 3 p) '(nil 1))
                    (list 1 (pgs-run (nth 4 p) (+ n (nth 2 p)))
                          nil (nth 6 p)))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-run pgs-ntables
                                      pgs-x-ntables pgs-ptab-run-pages))))

(in-theory (disable fn-hpl-layout))

(defun fn-hpl-single-address (i m)
  ; I is the data-page index, or N + table-page index. No run allocation.
  (declare (xargs :guard (and (natp i) (posp m))))
  (+ 1 m i))

(local
 (defun fn-hpl-nth-ind (i a n)
   (if (zp i) (list a n)
     (fn-hpl-nth-ind (1- i) (+ 1 (nfix a)) (1- n)))))

(local
 (defthm fn-hpl-nth-run
   (implies (and (natp i) (natp a) (natp n) (< i n))
            (equal (nth i (pgs-run a n)) (+ a i)))
   :hints (("Goal" :induct (fn-hpl-nth-ind i a n)
            :expand ((pgs-run a n))
            :in-theory (enable pgs-run nth)))))

(defthm fn-hpl-single-address-is-allocated
  (implies (and (natp i) (natp singles) (< i singles) (posp m))
           (equal (fn-hpl-single-address i m)
                  (nth i (cadr (pgs-alloc singles m '(nil 1))))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-run))))
