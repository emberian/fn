; Resumable exact length of a retained immutable report source spine.  A
; scheduling step consumes one cons; it never calls LEN on the source.
(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-orc-countp (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 3)
       (equal (car cursor) :report-count) (natp (nth 2 cursor))))

(defun fn-orc-count-begin (source)
  (declare (xargs :guard t))
  (list :report-count source 0))

(defun fn-orc-count-one (cursor)
  (declare (xargs :guard (fn-orc-countp cursor)))
  (let ((source (nth 1 cursor)) (count (nth 2 cursor)))
    (if (consp source)
        (mv :yield (list :report-count (cdr source) (+ 1 count)))
      (mv :counted cursor))))

(defun fn-orc-count-run (fuel cursor)
  (declare (xargs :guard (and (natp fuel) (fn-orc-countp cursor))
                  :measure (nfix fuel) :verify-guards nil))
  (if (zp fuel) (mv :yield cursor)
    (mv-let (word cursor) (fn-orc-count-one cursor)
      (if (eq word :counted) (mv word cursor)
        (fn-orc-count-run (1- fuel) cursor)))))

(defthm fn-orc-count-one-carry
  (implies (fn-orc-countp cursor)
           (fn-orc-countp (mv-nth 1 (fn-orc-count-one cursor)))))

(defthm fn-orc-count-run-carry
  (implies (fn-orc-countp cursor)
           (fn-orc-countp (mv-nth 1 (fn-orc-count-run fuel cursor))))
  :hints (("Goal" :induct (fn-orc-count-run fuel cursor))))

(verify-guards fn-orc-count-run)

(defthm fn-orc-count-run-conservation
  (implies (fn-orc-countp cursor)
           (equal (+ (nth 2 (mv-nth 1 (fn-orc-count-run fuel cursor)))
                     (len (nth 1 (mv-nth 1 (fn-orc-count-run fuel cursor)))))
                  (+ (nth 2 cursor) (len (nth 1 cursor)))))
  :hints (("Goal" :induct (fn-orc-count-run fuel cursor)))
  :rule-classes nil)

(defthm fn-orc-count-run-completed-empty
  (implies (equal (mv-nth 0 (fn-orc-count-run fuel cursor)) :counted)
           (not (consp (nth 1 (mv-nth 1 (fn-orc-count-run fuel cursor))))))
  :hints (("Goal" :induct (fn-orc-count-run fuel cursor)))
  :rule-classes nil)

(defthm fn-orc-count-completed-is-length
  (implies (equal (mv-nth 0 (fn-orc-count-run fuel (fn-orc-count-begin source))) :counted)
           (equal (nth 2 (mv-nth 1 (fn-orc-count-run fuel (fn-orc-count-begin source))))
                  (len source)))
  :hints (("Goal" :use ((:instance fn-orc-count-run-conservation
                                   (cursor (fn-orc-count-begin source)))
                           (:instance fn-orc-count-run-completed-empty
                                      (cursor (fn-orc-count-begin source)))
                           (:instance fn-orc-count-run-carry
                                      (cursor (fn-orc-count-begin source))))
           :in-theory (e/d (fn-orc-count-begin fn-orc-countp)
                           (fn-orc-count-run fn-orc-count-one fn-orc-count-run-carry
                            fn-orc-count-one-carry))))
  :rule-classes nil)

(defthm fn-orc-count-run-result-listp
  (implies (fn-orc-countp cursor)
           (true-listp (mv-nth 1 (fn-orc-count-run fuel cursor))))
  :hints (("Goal" :use ((:instance fn-orc-count-run-carry))
           :in-theory (e/d (fn-orc-countp)
                           (fn-orc-count-run fn-orc-count-run-carry)))))
