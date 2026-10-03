; SCN-1092: the actual foundation writer carries classified availability.
; This first classification fixture is not a native reclaim execution.
(in-package "ACL2")
(include-book "../../books/catalog-logic")

(defun cav-bytes (i tomb)
  (declare (xargs :mode :program))
  (if tomb
      (append *fn-rcl-magic* (make-list 137 :initial-element 0))
    (append (fn-record-string-octets
              (concatenate 'string "Message-ID: <" (coerce (explode-atom i 10) 'string)
                           "@available.test>"))
            '(13 10 83 117 98 106 101 99 116 58 32 97 13 10 13 10 97 13 10))))

(defun cav-row (i tomb)
  (declare (xargs :mode :program))
  (let* ((bytes (cav-bytes i tomb))
         (h (fn-held-plain
              (fn-record-make i (+ 1 i) 0
                (concatenate 'string "<" (coerce (explode-atom i 10) 'string)
                             "@available.test>")
                bytes '("fn.available") "o" "s" "e" 1 5) i)))
    (fn-held-with-facts h (fn-held-facts-of bytes))))

(defun cav-fill (i n survivors fn-cat$c)
  (declare (xargs :mode :program :stobjs fn-cat$c))
  (if (>= i n) fn-cat$c
    (let ((fn-cat$c (fn-cat$c-commit-w (cav-row i (not (member-equal (+ 1 i) survivors)))
                                     fn-cat$c)))
      (cav-fill (+ 1 i) n survivors fn-cat$c))))

(defun cav-observe (fn-cat$c)
  (declare (xargs :mode :program :stobjs fn-cat$c))
  (list (fn-cat$c-group-live-count "fn.available" fn-cat$c)
        (fn-cat$c-group-live-low "fn.available" fn-cat$c)
        (fn-cat$c-group-live-high "fn.available" fn-cat$c)
        (fn-cat$c-group-next "fn.available" fn-cat$c)
        (fn-cat$c-group-number "fn.available" 2 fn-cat$c)
        (fn-cat$c-msgid-seqs "<1@available.test>" fn-cat$c)
        (fn-cat$c-count fn-cat$c)))

(defun cav-run (survivors fn-cat$c)
  (declare (xargs :mode :program :stobjs fn-cat$c))
  (let* ((fn-cat$c (fn-cat$c-clear-w fn-cat$c))
         (fn-cat$c (cav-fill 0 34 survivors fn-cat$c))
         (before (cav-observe fn-cat$c))
         ; Number 2 was already unavailable: cancel must not decrement again.
         (fn-cat$c (fn-cat$c-withdraw-w 1 33 fn-cat$c))
         (after (cav-observe fn-cat$c)))
    (mv (list before after) fn-cat$c)))

(assert-event
 (and (fn-cat-row-facts-decidedp (cav-row 1 t))
      (not (fn-cat-row-availablep (cav-row 1 t)))
      (fn-cat-row-availablep (cav-row 0 nil))
      (fn-held-p (cav-row 0 nil)) (fn-held-p (cav-row 1 t))))

(defun cav-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat$c
    (mv-let (answer fn-cat$c) (cav-run survivors fn-cat$c) answer)))

(assert-event (equal (cav-local '(1 34))
                     '((2 1 34 35 1 (1) 34) (2 1 34 35 1 (1) 34))))
(assert-event (equal (cav-local '(33 34))
                     '((2 33 34 35 1 (1) 34) (2 33 34 35 1 (1) 34))))
(assert-event (equal (cav-local '(1))
                     '((1 1 1 35 1 (1) 34) (1 1 1 35 1 (1) 34))))
(assert-event (equal (cav-local nil)
                     '((0 0 0 35 1 (1) 34) (0 0 0 35 1 (1) 34))))
