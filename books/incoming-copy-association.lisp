; Exact readonly association getters factored from the actual pool adapter.
; No new authority, copy controller or backing observation is introduced.
(in-package "ACL2")
(include-book "incoming-buffer-carrier-shape")
(include-book "incoming-copy-stobj")
(include-book "page-read-pool-state")

(defun fn-owner-incoming-row (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool)))

(defun fn-owner-incoming-backing (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-ibc-carrier-descriptor (fn-prp-incoming-slot fn-page-read-pool)))

(defun fn-owner-incoming-copy-associatedp (token fn-input-copy fn-page-read-pool)
  (declare (xargs :stobjs (fn-input-copy fn-page-read-pool)))
  (let* ((row (fn-owner-incoming-row fn-page-read-pool))
         (job (fn-prl-nth 3 row)))
    (and (fn-ioh-matches row token)
         (equal (fn-input-copy-token fn-input-copy) token)
         (consp job) (equal (car job) :incoming-controller)
         (consp (cdr job)) (equal (cadr job) token) (null (cddr job)))))
