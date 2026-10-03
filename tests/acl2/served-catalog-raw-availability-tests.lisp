; Raw identity and available membership remain distinct on a real generic
; catalog built through the writer. SCN-1092 includes sparse tombstone data.
(in-package "ACL2")
(include-book "../../books/served-catalog")
(include-book "catalog-available-readers-tests")

(defun cav-raw-observe (fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (let ((archive (fn-make-state '("fn.available") '(("fn.available" . 35)) nil 0 nil nil)))
    (list (fn-scat-group-summary archive "fn.available" 34 fn-cat)
          (fn-scat-available-summary archive "fn.available" 34 fn-cat)
          (fn-scat-group-low "fn.available" 34 fn-cat)
          (fn-scat-next-number "fn.available" 1 34 fn-cat)
          (fn-scat-available-next-number "fn.available" 1 34 fn-cat)
          (fn-scat-previous-number "fn.available" 34 34 fn-cat)
          (fn-scat-available-previous-number "fn.available" 34 34 fn-cat)
          (fn-scat-raw-keptp "fn.available" 2 34 fn-cat)
          (fn-scv-keptp "fn.available" 2 34 fn-cat)
          (len (fn-scat-range-numbers "fn.available" 1 34 34 fn-cat))
          (fn-scat-available-range-numbers "fn.available" 1 34 34 fn-cat))))

(defun cav-raw-run (fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (cav-reader-fill 0 34 '(1 34) fn-cat)))
    (mv (cav-raw-observe fn-cat) fn-cat)))

(defun cav-raw-local ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat
    (mv-let (answer fn-cat) (cav-raw-run fn-cat) answer)))

(assert-event
 (equal (cav-raw-local)
        '((34 1 34) (2 1 34) 1 2 34 33 1 t nil 34 (1 34))))

(assert-event
 (and (eq (symbol-class 'fn-scat-raw-keptp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scat-raw-first-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scat-raw-last-p (w state)) :common-lisp-compliant)))
