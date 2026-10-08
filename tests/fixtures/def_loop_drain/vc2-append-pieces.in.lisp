(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-nntp-append-pieces-loop (pieces acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp pieces)
      (fn-nntp-append-pieces-loop (fn-ag-cdr pieces)
                                  (fn-ag-rev-onto (fn-ag-car pieces) acc))
    (revappend acc nil)))

(defun fn-nntp-append-pieces (pieces)
  (mbe :logic
       (if (consp pieces)
           (append (car pieces) (fn-nntp-append-pieces (cdr pieces)))
         nil)
       :exec (fn-nntp-append-pieces-loop pieces nil)))

(local
 (defthm fn-nntp-append-pieces-revappend-rev-onto
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-nntp-append-pieces-loop-is-revappend
   (equal (fn-nntp-append-pieces-loop pieces acc)
          (revappend acc (fn-nntp-append-pieces pieces)))
   :hints (("Goal" :induct (fn-nntp-append-pieces-loop pieces acc)))))

(verify-guards fn-nntp-append-pieces-loop)

(verify-guards fn-nntp-append-pieces
  :hints (("Goal" :in-theory (disable fn-nntp-append-pieces-loop)
                  :use ((:instance fn-nntp-append-pieces-loop-is-revappend (acc nil))))))
