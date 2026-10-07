(include-book "peer-feed-invariants")

(defun fn-own-feed-targets-loop (tbl origin groups path acc)
  (declare (xargs :guard t))
  (if (consp tbl)
      (fn-own-feed-targets-loop (cdr tbl) origin groups path
       (if (fn-own-feed-offerablep (fn-own-feed-entry-record (car tbl))
                               origin groups path) (cons (fn-own-feed-entry-name (car tbl)) acc) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-own-feed-targets (tbl origin groups path)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp tbl)
           (let ((rest (fn-own-feed-targets (cdr tbl) origin groups path)))
             (if (fn-own-feed-offerablep (fn-own-feed-entry-record (car tbl))
                                         origin groups path)
                 (cons (fn-own-feed-entry-name (car tbl)) rest)
               rest))
         nil)
       :exec (fn-own-feed-targets-loop tbl origin groups path nil)))

(defthm fn-own-feed-targets-loop-is-rev-onto
  (equal (fn-own-feed-targets-loop tbl origin groups path acc)
         (fn-ag-rev-onto acc (fn-own-feed-targets tbl origin groups path)))
  :hints (("Goal" :induct (fn-own-feed-targets-loop tbl origin groups path acc)
                  :in-theory (union-theories
                              '(fn-own-feed-targets-loop fn-own-feed-targets fn-ag-rev-onto not car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-own-feed-targets
  :hints (("Goal" :in-theory (union-theories
                              '(fn-own-feed-targets fn-ag-rev-onto fn-own-feed-targets-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defthm fn-own-feed-targets-true-listp
  (true-listp (fn-own-feed-targets tbl origin groups path)))
