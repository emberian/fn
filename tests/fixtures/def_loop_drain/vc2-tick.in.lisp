(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-own-feed-tick-loop (names tbl obs acc)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((one (fn-own-feed-tick-peer (car names) tbl obs)))
        (fn-own-feed-tick-loop (cdr names) (car one) obs
                               (fn-ag-rev-onto (cdr one) acc)))
    (cons tbl (fn-ag-rev-onto acc nil))))

(defun fn-own-feed-tick (names tbl obs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp names)
           (let* ((one (fn-own-feed-tick-peer (car names) tbl obs))
                  (rest (fn-own-feed-tick (cdr names) (car one) obs)))
             (cons (car rest) (append (cdr one) (cdr rest))))
         (cons tbl nil))
       :exec (fn-own-feed-tick-loop names tbl obs nil)))

(local
 (defthm fn-own-feed-tick-rev-onto-of-rev-onto
   (equal (fn-ag-rev-onto (fn-ag-rev-onto a acc) b)
          (fn-ag-rev-onto acc (append a b)))))

(defthm fn-own-feed-tick-loop-is-rev-onto
  (equal (fn-own-feed-tick-loop names tbl obs acc)
         (let ((r (fn-own-feed-tick names tbl obs)))
           (cons (car r) (fn-ag-rev-onto acc (cdr r)))))
  :hints (("Goal" :induct (fn-own-feed-tick-loop names tbl obs acc)
                  :in-theory (union-theories
                              '(fn-own-feed-tick-loop fn-own-feed-tick fn-ag-rev-onto
                                fn-own-feed-tick-rev-onto-of-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-own-feed-tick
  :hints (("Goal" :in-theory (union-theories
                              '(fn-own-feed-tick fn-ag-rev-onto fn-own-feed-tick-loop-is-rev-onto
                                car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))
