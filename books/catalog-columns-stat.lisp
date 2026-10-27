;; Route A3, first read arm: STAT (by number, by message-id, current) over the
;; columns.  It replaces fn-rcompat-retrieval-cat at kind :stat.  The arm is
;; resident: the reclaimed flag and the number and message-id columns decide it,
;; no payload and no log are read, so LOG is not an argument here.
(in-package "ACL2")
(include-book "catalog-columns-served")

(defun fn-lbc-stat-reply (session args v fn-lbc)
  (declare (xargs :stobjs fn-lbc :verify-guards nil))
  (let ((selected (fn-lbc-select session :stat args v fn-lbc)))
    (if (equal (car selected) :refusal)
        (fn-nntp-single session (cadr selected))
      (fn-lbc-resident-reply session selected :stat nil fn-lbc nil))))
