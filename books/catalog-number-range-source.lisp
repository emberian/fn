; Exact old logical range enumeration; never used as new served locator.
(in-package "ACL2")
(include-book "catalog-number-read")

(defun fn-cnx-range-aux-loop (group k top v fn-cat acc)
  (declare (xargs :stobjs fn-cat :measure (nfix (- (+ 1 (nfix top)) (nfix k))) :guard (and (and (natp k) (natp top) (natp v)) (true-listp acc)) :verify-guards nil))
  (if (and (natp k) (natp top) (<= k top))
      (let ((s (fn-cnx-view-seq group k v fn-cat)))
        (if s
            (fn-cnx-range-aux-loop group (+ 1 k) top v fn-cat (cons s acc))
          (fn-cnx-range-aux-loop group (+ 1 k) top v fn-cat acc)))
    (revappend acc nil)))

(defun fn-cnx-range-aux (group k top v fn-cat)
  (declare (xargs :verify-guards nil :stobjs fn-cat :guard (and (natp k) (natp top) (natp v))
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (mbe :logic
       (if (and (natp k) (natp top) (<= k top))
           (let ((s (fn-cnx-view-seq group k v fn-cat)))
             (if s
                 (cons s (fn-cnx-range-aux group (+ 1 k) top v fn-cat))
               (fn-cnx-range-aux group (+ 1 k) top v fn-cat)))
         nil)
       :exec (fn-cnx-range-aux-loop group k top v fn-cat nil)))

(local
 (defthm fn-cnx-range-aux-loop-is-revappend
   (equal (fn-cnx-range-aux-loop group k top v fn-cat acc)
          (revappend acc (fn-cnx-range-aux group k top v fn-cat)))
   :hints (("Goal" :induct (fn-cnx-range-aux-loop group k top v fn-cat acc)
                   :in-theory (union-theories '(fn-cnx-range-aux-loop fn-cnx-range-aux revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cnx-range-aux-loop)

(verify-guards fn-cnx-range-aux
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cnx-range-aux)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cnx-range-aux-loop-is-revappend (acc nil))))))


