; Literal logical count relation; served mutation proofs remain in their books.
(in-package "ACL2")
(include-book "owner-report-feed-accessors")

(defun fn-feed-entry-state (x)
  (declare (xargs :guard t))
  (fn-bp-nth 1 x))

(defun fn-fct-retry-drop-bit (st)
  (declare (xargs :guard t))
  (if (equal st '(:dropped :retry-bound)) 1 0))

(defun fn-fct-retry-drops-model (queue)
  (declare (xargs :guard t))
  (if (consp queue)
      (+ (fn-fct-retry-drop-bit (fn-feed-entry-state (car queue)))
         (fn-fct-retry-drops-model (cdr queue)))
    0))

(defun fn-feed-count-relationp (f)
  (declare (xargs :guard t))
  (and (equal (fn-feed-undelivered f) (len (fn-feed-queue f)))
       (equal (fn-feed-retry-dropped f)
              (fn-fct-retry-drops-model (fn-feed-queue f)))))
