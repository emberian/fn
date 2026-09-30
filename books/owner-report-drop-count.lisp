; Unchanged original health tally and loop guard proof; reference only here.
(in-package "ACL2")
(include-book "owner-report-feed-model")

(defun fn-nh-dropped-count-loop (xs acc)
  (declare (xargs :guard (acl2-numberp acc) :verify-guards nil))
  (if (consp xs)
      (fn-nh-dropped-count-loop (cdr xs)
                                (+ (if (equal (fn-feed-entry-state (car xs))
                                              '(:dropped :retry-bound))
                                       1
                                     0)
                                   acc))
    (+ acc 0)))

(defun fn-nh-dropped-count (xs)
  "Entries dropped at their retry bound (`fn-feed-give-up' :retry-bound)."
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs)
           (+ (if (equal (fn-feed-entry-state (car xs)) '(:dropped :retry-bound)) 1 0)
              (fn-nh-dropped-count (cdr xs)))
         0)
       :exec (fn-nh-dropped-count-loop xs 0)))

(local
 (defthm fn-nh-dropped-count-loop-is-plus
   (implies (acl2-numberp acc)
            (equal (fn-nh-dropped-count-loop xs acc)
                   (+ acc (fn-nh-dropped-count xs))))
   :hints (("Goal" :induct (fn-nh-dropped-count-loop xs acc)
                   :in-theory (disable fn-feed-entry-state)))))

(verify-guards fn-nh-dropped-count-loop)

(verify-guards fn-nh-dropped-count
  :hints (("Goal"
           :in-theory
           (disable fn-nh-dropped-count-loop fn-feed-entry-state)
           :use
           ((:instance fn-nh-dropped-count-loop-is-plus (acc 0))))))


