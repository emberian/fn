; SCN-1092: real recovery loader fills missing availability from its arena.
; Program fixture setup; actual loader/readers are guard verified.
(in-package "ACL2")
(include-book "../../books/catalog-availability-owner-load")
(include-book "catalog-available-readers-tests")

(defun cav-loader-prepare (i n survivors rows index fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (>= i n) (mv (reverse rows) index fn-arena)
    (let* ((bytes (cav-bytes i (not (member-equal (+ 1 i) survivors))))
           (h (fn-held-with-facts (cav-row i nil) (fn-hf-make 0 nil 0 nil)))
           (index (fn-midx-put-chars (fn-midx-key-chars (fn-record-msgid h)) t index))
           (fn-arena (fn-arena-seal-list bytes fn-arena)))
      (cav-loader-prepare (+ 1 i) n survivors (cons h rows) index fn-arena))))

(defun cav-loader-run (survivors fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((fn-arena (fn-arena-clear fn-arena)))
    (mv-let (rows index fn-arena)
      (cav-loader-prepare 0 34 survivors nil nil fn-arena)
      (let* ((fn-cat (fn-sca-load-held-rows rows index fn-arena fn-cat))
             (before (cav-reader-observe 34 fn-cat))
             (fn-cat (fn-cat-withdraw 1 33 fn-cat))
             (after (cav-reader-observe 35 fn-cat)))
        (mv (list before after) fn-arena fn-cat)))))

(defun cav-loader-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat)
          (cav-loader-run survivors fn-arena fn-cat) (mv answer fn-arena)))
      answer)))

(assert-event
 (equal (cav-loader-local '(1 34))
        '(((2 1 34) 1 (1 34) 34 1 0 0 35 1 (1))
          ((2 1 34) 1 (1 34) 34 1 0 0 35 1 (1)))))
(assert-event
 (equal (cav-loader-local '(33 34))
        '(((2 33 34) 33 (33 34) 33 33 0 0 35 1 (1))
          ((2 33 34) 33 (33 34) 33 33 0 0 35 1 (1)))))
(assert-event
 (equal (cav-loader-local '(1))
        '(((1 1 1) 1 (1) 0 1 0 0 35 1 (1))
          ((1 1 1) 1 (1) 0 1 0 0 35 1 (1)))))
(assert-event
 (equal (cav-loader-local nil)
        '(((0 35 34) 0 nil 0 0 0 0 35 1 (1))
          ((0 35 34) 0 nil 0 0 0 0 35 1 (1)))))

(defun cav-loader-invalid-local ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (let* ((h (fn-held-with-facts (cav-row 0 nil) (fn-hf-make 0 nil 0 nil)))
             (prepared (fn-cat-prepare-row-availability h fn-arena)))
        (mv (and (equal prepared h)
                 (not (fn-cat-row-facts-decidedp prepared))
                 (not (fn-cat-row-availablep prepared))) fn-arena))
      answer)))
(assert-event (cav-loader-invalid-local))
(assert-event
 (and (eq (symbol-class 'fn-cat-prepare-row-availability (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sca-load-held-rows (w state)) :common-lisp-compliant)))
