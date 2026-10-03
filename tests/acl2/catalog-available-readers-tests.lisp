; SCN-1092: actual generic writer and available summary/range/navigation.
(in-package "ACL2")
(include-book "../../books/catalog-available-readers")
(include-book "catalog-availability-tests")

(defun cav-reader-fill (i n survivors fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (if (>= i n) fn-cat
    (let ((fn-cat (fn-cat-commit (cav-row i (not (member-equal (+ 1 i) survivors))) fn-cat)))
      (cav-reader-fill (+ 1 i) n survivors fn-cat))))

(defun cav-reader-observe (v fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (let ((archive (fn-make-state '("fn.available") '(("fn.available" . 35)) nil 0 nil nil)))
    (list (fn-scat-available-summary archive "fn.available" v fn-cat)
          (fn-scat-available-low "fn.available" v fn-cat)
          (fn-scat-available-range-numbers "fn.available" 1 34 v fn-cat)
          (fn-scat-available-next-number "fn.available" 1 v fn-cat)
          (fn-scat-available-previous-number "fn.available" 34 v fn-cat)
          (fn-scat-available-next-number "fn.available" 34 v fn-cat)
          (fn-scat-available-previous-number "fn.available" 1 v fn-cat)
          (fn-cat-group-next "fn.available" fn-cat)
          (fn-cat-group-number "fn.available" 2 fn-cat)
          (fn-cat-msgid-seqs "<1@available.test>" fn-cat))))

(defun cav-reader-run (survivors fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (cav-reader-fill 0 34 survivors fn-cat))
         (before (cav-reader-observe 34 fn-cat))
         (fn-cat (fn-cat-withdraw 1 33 fn-cat))
         (after (cav-reader-observe 35 fn-cat)))
    (mv (list before after) fn-cat)))

(defun cav-reader-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat
    (mv-let (answer fn-cat) (cav-reader-run survivors fn-cat) answer)))

(assert-event
 (equal (cav-reader-local '(1 34))
        '(((2 1 34) 1 (1 34) 34 1 0 0 35 1 (1))
          ((2 1 34) 1 (1 34) 34 1 0 0 35 1 (1)))))
(assert-event
 (equal (cav-reader-local '(33 34))
        '(((2 33 34) 33 (33 34) 33 33 0 0 35 1 (1))
          ((2 33 34) 33 (33 34) 33 33 0 0 35 1 (1)))))
(assert-event
 (equal (cav-reader-local '(1))
        '(((1 1 1) 1 (1) 0 1 0 0 35 1 (1))
          ((1 1 1) 1 (1) 0 1 0 0 35 1 (1)))))
(assert-event
 (equal (cav-reader-local nil)
        '(((0 35 34) 0 nil 0 0 0 0 35 1 (1))
          ((0 35 34) 0 nil 0 0 0 0 35 1 (1)))))

(assert-event
 (and (eq (symbol-class 'fn-scat-available-summary (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scat-available-low (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scat-available-range-numbers (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scat-available-next-number (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scat-available-previous-number (w state)) :common-lisp-compliant)))
