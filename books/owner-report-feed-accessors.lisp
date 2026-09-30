; Unchanged served nine-slot feed and table projections.
(in-package "ACL2")
(include-book "owner-report-selectors")

(defun fn-own-feed-entry-name (e)
  (declare (xargs :guard t))
  (fn-frame-item 0 e))

(defun fn-own-feed-entry-feed (e)
  (declare (xargs :guard t))
  (fn-frame-item 2 e))

(defun fn-feed-queue (x)
  (declare (xargs :guard t))
  (fn-bp-nth 2 x))

(defun fn-feed-undelivered (x)
  (declare (xargs :guard t))
  (fn-bp-nth 7 x))

(defun fn-feed-retry-dropped (x)
  (declare (xargs :guard t))
  (fn-bp-nth 8 x))
