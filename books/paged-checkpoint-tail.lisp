; Bounded partial-page summary, shared by the open and delta staging.
(in-package "ACL2")
(include-book "pagestore-exec")
(local (include-book "arithmetic-5/top" :dir :system))
(defun fn-pck-x-tail (cnt pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard t :verify-guards nil))
  (let* ((cnt (nfix cnt))
         (k (mod cnt 2048))
         (a (+ 16384 (- cnt k))))
    (if (and (natp a) (natp k) (<= (+ a k) (pgs-x-len 0 pgs-mem)))
        (pgs-x-words 0 a k pgs-mem)
      nil)))
(verify-guards fn-pck-x-tail)

(defthm pck-tail-word-count-bound
  (implies (natp cnt)
           (and (natp (mod cnt 2048)) (< (mod cnt 2048) 2048)
                (<= (mod cnt 2048) cnt)
                (equal (- cnt (mod cnt 2048)) (* 2048 (floor cnt 2048)))))
  :rule-classes nil)

(defun pck-tail-ind (a n k)
  (if (zp n) (list a k) (pck-tail-ind (+ 1 a) (1- n) k)))
(defthm pck-tail-words-nthcdr
  (implies (and (natp n) (natp k) (natp a))
           (equal (nthcdr n (pgs-x-words 0 a (+ n k) pgs-mem))
                  (pgs-x-words 0 (+ a n) k pgs-mem)))
  :hints (("Goal" :induct (pck-tail-ind a n k)
           :in-theory (e/d (pgs-x-words) (pgs-x-words-split)))))

(defthm fn-pck-x-tail-is-the-partial-page
  (implies (and (natp cnt) (<= (+ 16384 cnt) (pgs-x-len 0 pgs-mem))
                (equal (pgs-x-words 0 16384 cnt pgs-mem) words))
           (equal (fn-pck-x-tail cnt pgs-mem)
                  (nthcdr (* 2048 (floor cnt 2048)) words)))
  :rule-classes nil
  :hints (("Goal" :use (pck-tail-word-count-bound
                        (:instance pck-tail-words-nthcdr
                         (a 16384) (n (- cnt (mod cnt 2048))) (k (mod cnt 2048))))
           :in-theory (union-theories '(fn-pck-x-tail nfix natp fix
                            associativity-of-+ commutativity-of-+ inverse-of-+
                            unicity-of-0) (theory 'minimal-theory)))))
