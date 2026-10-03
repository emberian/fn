; SCN-1092: the paged representation carries the same sparse availability.
; Direct live implementation exports; generic attachment/native use is separate.
(in-package "ACL2")
(include-book "../../books/catalog-paged")
(include-book "catalog-availability-tests")

(defun cav-paged-fill (i n survivors fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (if (>= i n) fn-cat$p
    (let ((fn-cat$p (fn-cat$p-commit-w (cav-row i (not (member-equal (+ 1 i) survivors))) fn-cat$p)))
      (cav-paged-fill (+ 1 i) n survivors fn-cat$p))))

(defun cav-paged-observe (fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (list (fn-cat$p-group-live-count "fn.available" fn-cat$p)
        (fn-cat$p-group-live-low "fn.available" fn-cat$p)
        (fn-cat$p-group-live-high "fn.available" fn-cat$p)
        (fn-cat$p-group-next "fn.available" fn-cat$p)
        (fn-cat$p-group-number "fn.available" 2 fn-cat$p)
        (fn-cat$p-msgid-seqs "<1@available.test>" fn-cat$p)
        (fn-cat$p-livep "fn.available" 2 fn-cat$p)
        (fn-cat$p-next "fn.available" 1 fn-cat$p)
        (fn-cat$p-prev "fn.available" 34 fn-cat$p)))

(defun cav-paged-run (survivors fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (let* ((fn-cat$p (fn-cat$p-clear-w fn-cat$p))
         (fn-cat$p (cav-paged-fill 0 34 survivors fn-cat$p))
         (before (cav-paged-observe fn-cat$p))
         (fn-cat$p (fn-cat$p-withdraw-w 1 33 fn-cat$p))
         (after (cav-paged-observe fn-cat$p)))
    (mv (list before after) fn-cat$p)))

(defun cav-paged-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat$p
    (mv-let (answer fn-cat$p) (cav-paged-run survivors fn-cat$p) answer)))

(assert-event (equal (cav-paged-local '(1 34))
                    '((2 1 34 35 1 (1) nil 34 1) (2 1 34 35 1 (1) nil 34 1))))
(assert-event (equal (cav-paged-local '(33 34))
                    '((2 33 34 35 1 (1) nil 0 33) (2 33 34 35 1 (1) nil 0 33))))
(assert-event (equal (cav-paged-local '(1))
                    '((1 1 1 35 1 (1) nil 0 0) (1 1 1 35 1 (1) nil 0 0))))
(assert-event (equal (cav-paged-local nil)
                    '((0 0 0 35 1 (1) nil 0 0) (0 0 0 35 1 (1) nil 0 0))))
