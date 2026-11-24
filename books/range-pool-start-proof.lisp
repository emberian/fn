; Range images start from a fresh single-class pool. The head, count,
; capacities, and next links below are observations of the real initializer.
(in-package "ACL2")
(include-book "range-served")

(defun fn2-range-free-slot-p (i fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp i) (< i (fn2-pool-rows fn2-pool)))))
  (and (equal (fn2-pool-state i fn2-pool) *fn2-pool-state-free*)
       (equal (fn2-pool-class i fn2-pool) 0) (equal (fn2-pool-gen i fn2-pool) 1)
       (equal (fn2-pool-out-count i fn2-pool) 0) (equal (fn2-pool-query-ref-count i fn2-pool) 0)
       (equal (fn2-pool-cap i fn2-pool) 65536) (equal (fn2-pool-base i fn2-pool) (* i 65536))
       (equal (fn2-pool-next-free i fn2-pool) (if (< (1+ i) 327) (1+ i) *fn2-none*))))

(defun fn2-range-free-suffix-p (n fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (<= n 327) (equal (fn2-pool-rows fn2-pool) 327))))
  (if (zp n) t
    (and (fn2-range-free-slot-p (- 327 n) fn2-pool)
         (fn2-range-free-suffix-p (1- n) fn2-pool))))

(defun fn2-range-pool-available-p (n fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (and (natp n) (<= n 327) (equal (fn2-pool-rows fn2-pool) 327)
       (equal (fn2-pool-nclasses fn2-pool) 1) (equal (fn2-pool-credit-configured fn2-pool) 0)
       (equal (fn2-pool-class-countsi 0 fn2-pool) n)
       (equal (fn2-pool-class-headsi 0 fn2-pool) (if (zp n) *fn2-none* (- 327 n)))
       (equal (fn2-pool-capacity-bytes fn2-pool) (* 327 65536))
       (fn2-range-free-suffix-p n fn2-pool)))

(local
 (defun fn2-range-inspect-initial-pool (fn2-pool)
   (declare (xargs :stobjs fn2-pool :guard t))
   (let ((fn2-pool (fn2-pool-init '((327 . 65536)) 1 100 fn2-pool)))
     (mv (fn2-range-pool-available-p 327 fn2-pool) fn2-pool))))

(local
 (defun fn2-range-initial-pool-available-p ()
   (declare (xargs :guard t))
   (with-local-stobj fn2-pool
     (mv-let (answer fn2-pool) (fn2-range-inspect-initial-pool fn2-pool) answer))))

(local
 (defthm fn2-range-initial-pool-checked
   (fn2-range-initial-pool-available-p)
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '((:e fn2-range-initial-pool-available-p)))))))

(defthm fn2-range-initial-pool-has-all-reservations
  (fn2-range-pool-available-p 327 (fn2-pool-init '((327 . 65536)) 1 100 (create-fn2-pool)))
  :rule-classes nil
  :hints (("Goal" :use fn2-range-initial-pool-checked
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-range-initial-pool-available-p fn2-range-inspect-initial-pool mv-nth car-cons cdr-cons (:e zp) (:e equal) (:e unary--) (:e binary-+))))))

(defthm fn2-range-setup-has-all-reservations
  (implies (equal fn2-pool (create-fn2-pool))
           (fn2-range-pool-available-p 327 (mv-nth 13 (fn2-rga-call fn2-rga-setup))))
  :rule-classes nil
  :hints (("Goal" :use fn2-range-initial-pool-has-all-reservations
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-rga-setup mv-nth car-cons cdr-cons (:e mv-nth) (:e unary--) (:e binary-+)
                       (:e equal) (:e zp) (:e consp))))))
