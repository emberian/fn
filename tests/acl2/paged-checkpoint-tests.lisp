; Premises inhabited and teeth for books/paged-checkpoint.lisp (the
; keystones fn-pck-dirty-is-the-delta, fn-pck-dirty-bound,
; fn-pck-open-after-commit-is-full-recover, fn-pck-crash-recovers-from-old-or-new).
;
; Each tooth is a must-fail AND a concrete witness that its claim is false for
; the right reason, so a stale or untranslatable body cannot pass for a tooth:
;   1. the premises (fn-pck-recordsp, fn-pck-root-fitsp) hold of a nonempty
;      record list with a wide record, executed;
;   2. a dirty set that forgets the root region is not the delta (the root
;      changes with the records);
;   3. a bound of K (the root pages alone) is false: a wide delta takes more;
;   4. a log compacted past the old checkpoint's S cannot reach the records
;      the old slot lacks.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint")
(include-book "../../books/catalog-pages")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *pckt-wide* (make-list 20000 :initial-element 7))
(defconst *pckt-prefix* (list '(1 2) "x"))
(defconst *pckt-delta* (list *pckt-wide* *pckt-wide* *pckt-wide*))

; 1. Premises.
(assert-event (and (fn-pck-recordsp nil (append *pckt-prefix* *pckt-delta*))
                   (fn-pck-root-fitsp nil (append *pckt-prefix* *pckt-delta*))
                   (fn-pck-recordsp nil *pckt-prefix*)
                   (fn-pck-root-fitsp nil *pckt-prefix*)))

; The image reads back as the records (the capture decodes, event index included).
(assert-event (equal (fn-pck-capture-of-pages (fn-pck-pages nil (append *pckt-prefix* *pckt-delta*)))
                     (fn-sco-capture nil (append *pckt-prefix* *pckt-delta*))))

; The dirty set applies to the old image and yields the new one.
(assert-event (equal (pgs-apply-dirty (fn-pck-pages nil *pckt-prefix*)
                                      (fn-pck-dirty nil *pckt-prefix* *pckt-delta*))
                     (fn-pck-pages nil (append *pckt-prefix* *pckt-delta*))))

; 2. A dirty set without the root region.
(defun pckt-bad-dirty (configs prefix delta)
  (declare (xargs :verify-guards nil) (ignore configs))
  (pck-shift *fn-pck-root-pages*
             (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows delta))))

(must-fail-checked
 (defthm pckt-bad-dirty-is-the-delta
   (implies (and (true-listp prefix) (true-listp delta)
                 (fn-pck-sccb-listp (append prefix delta)))
            (equal (pgs-apply-dirty (fn-pck-pages configs prefix) (pckt-bad-dirty configs prefix delta))
                   (fn-pck-pages configs (append prefix delta))))))

(assert-event (not (equal (pgs-apply-dirty (fn-pck-pages nil nil) (pckt-bad-dirty nil nil '((1 2))))
                          (fn-pck-pages nil '((1 2))))))

; 3. A bound of the root pages alone.
(must-fail-checked
 (defthm pckt-bound-root-only
   (<= (len (fn-pck-dirty configs prefix delta)) *fn-pck-root-pages*)))

(assert-event (< *fn-pck-root-pages* (len (fn-pck-dirty nil nil *pckt-delta*))))

; The real bound at the witness, and no term in the prefix: the same delta
; after a long prefix needs the same number of pages or one more.
(assert-event (<= (len (fn-pck-dirty nil *pckt-prefix* *pckt-delta*))
                  (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckt-delta*))))
(assert-event (<= (len (fn-pck-dirty nil (make-list 3000 :initial-element '(1 2)) *pckt-delta*))
                  (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckt-delta*))))

; 4. A log compacted past the old checkpoint's S.
(must-fail-checked
 (defthm pckt-crash-compacted-log
   (implies (and (true-listp prefix) (true-listp delta) (true-listp suffix)
                 (fn-pck-recordsp configs (append prefix delta))
                 (fn-pck-recordsp configs prefix)
                 (fn-pck-root-fitsp configs (append prefix delta))
                 (fn-pck-root-fitsp configs prefix)
                 (fn-pck-log-retains log (+ (len prefix) (len delta)))
                 (equal (nthcdr (car log) (append prefix delta suffix)) (cdr log))
                 (equal v (list t0 (fn-pck-pages configs prefix))))
            (equal (fn-pck-recover-view v log configs frontier max-conns)
                   (fn-ock-recover-full configs frontier (append prefix delta suffix) max-conns)))))

; The witness: opening the old checkpoint (S = 2) with a log that starts at 5
; replays no record of the delta, so the recovered records lack them.
(defconst *pckt-log* (cons 5 '(5 6)))
(assert-event
 (let* ((c (fn-pck-capture-of-pages (fn-pck-pages nil *pckt-prefix*)))
        (e (fn-sco-extend c nil (nthcdr (nfix (- (len (fn-sco-records c)) (nfix (car *pckt-log*)))) (cdr *pckt-log*)))))
   (and (equal (fn-sco-records e) (append *pckt-prefix* '(5 6)))
        (not (equal (fn-sco-records e) (append *pckt-prefix* '(a b c) '(5 6)))))))

; -----------------------------------------------------------------------------
; PCK-ADOPT (books/catalog-pages.lisp): the catalog's page image follows the
; catalog.  Premise inhabitation, then teeth.


(defun pckt-cat-row (i payload)
  (declare (xargs :mode :program))
  (let* ((art (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10)))
         (h (fn-held-plain (fn-record-make i (+ 1 i) 0
                                           (concatenate 'string "<" (coerce (explode-atom i 10) 'string) "@x>")
                                           art '("fn.test") "o" "s" "e" 1 5)
                           payload)))
    (fn-held-with-facts h (fn-held-facts-of art))))

(defun pckt-cat (n payload)
  (declare (xargs :mode :program))
  (if (zp n) nil (fn-cat$a-commit (pckt-cat-row (- n 1) payload) (pckt-cat (- n 1) payload))))

(defconst *pckt-h* (pckt-cat 3 7))
(defconst *pckt-new* (pckt-cat-row 3 7))

; 1. Premises: a nonempty catalog of rows the columns carry (no payload
; escape), a held row to commit, a target to withdraw; executed.
(assert-event (and (consp *pckt-h*) (equal (len *pckt-h*) 3)
                   (fn-cat-rowsp *pckt-h*) (fn-pck-carriedp *pckt-h*)
                   (fn-held-p *pckt-new*)
                   (not (fn-cp-escapedp (nth 1 *pckt-h*)))
                   (fn-cp-smallp 5) (fn-cp-smallp (len *pckt-h*))))

; The three claims at the witness.
(assert-event (equal (fn-crow-of-pages (fn-pck-cat-pages *pckt-h*)) (fn-pck-crow-rows *pckt-h*)))
(assert-event (equal (pgs-apply-dirty (fn-pck-cat-pages *pckt-h*) (fn-pck-cat-commit-dirty *pckt-h* *pckt-new*))
                     (fn-pck-cat-pages (fn-cat$a-commit *pckt-new* *pckt-h*))))
(assert-event (equal (pgs-apply-dirty (fn-pck-cat-pages *pckt-h*) (fn-pck-cat-withdraw-dirty *pckt-h* 1 5))
                     (fn-pck-cat-pages (fn-cat$a-withdraw 1 5 *pckt-h*))))
; The withdrawal changed the image (so the equation is not between equal inputs).
(assert-event (not (equal (fn-pck-cat-pages *pckt-h*) (fn-pck-cat-pages (fn-cat$a-withdraw 1 5 *pckt-h*)))))

; 2. A dirty set missing the row's page: the empty one.
(defun pckt-empty-commit-dirty (h row) (declare (ignore h row)) nil)
(must-fail-checked
 (defthm pckt-commit-dirty-empty
   (equal (pgs-apply-dirty (fn-pck-cat-pages h) (pckt-empty-commit-dirty h row))
          (fn-pck-cat-pages (fn-cat$a-commit row h)))))
(assert-event (not (equal (pgs-apply-dirty (fn-pck-cat-pages *pckt-h*) (pckt-empty-commit-dirty *pckt-h* *pckt-new*))
                          (fn-pck-cat-pages (fn-cat$a-commit *pckt-new* *pckt-h*)))))

; 3. A bound of 0 pages: the commit dirties at least one.
(must-fail-checked
 (defthm pckt-commit-bound-zero
   (<= (len (fn-pck-cat-commit-dirty h row)) 0)))
(assert-event (< 0 (len (fn-pck-cat-commit-dirty *pckt-h* *pckt-new*))))

; 4. The withdraw clause without its premises is false: a row whose payload
; handle is the sentinel is ESCAPED, its remainder tree carries the withdrawal,
; so the withdrawn row is wider and the same-width set does not give the image.
; Wide enough to span pages (2048 words a page, a row about 32 words), so a
; row that grows shifts the rows after it across a page boundary.
(defconst *pckt-esc-h* (pckt-cat 150 (1- (expt 2 64))))
(defconst *pckt-wide-h* (pckt-cat 150 7))
(assert-event (and (fn-cat-rowsp *pckt-esc-h*) (fn-pck-carriedp *pckt-esc-h*)
                   (fn-cp-escapedp (nth 10 *pckt-esc-h*))))
(assert-event (not (equal (pgs-apply-dirty (fn-pck-cat-pages *pckt-esc-h*) (fn-pck-cat-withdraw-dirty *pckt-esc-h* 10 5))
                          (fn-pck-cat-pages (fn-cat$a-withdraw 10 5 *pckt-esc-h*)))))
(must-fail-checked
 (defthm pckt-withdraw-image-unpremised
   (implies (and (fn-cat-rowsp h) (fn-pck-carriedp h) (natp target) (< target (len h)) (natp by))
            (equal (pgs-apply-dirty (fn-pck-cat-pages h) (fn-pck-cat-withdraw-dirty h target by))
                   (fn-pck-cat-pages (fn-cat$a-withdraw target by h))))))

; The same multi-page catalog without the escape: the premised clause holds.
(assert-event (and (fn-pck-carriedp *pckt-wide-h*) (< 2048 (len (adt-tp-seq-words *fn-crow-schema* (fn-pck-crow-rows *pckt-wide-h*))))
                   (equal (pgs-apply-dirty (fn-pck-cat-pages *pckt-wide-h*) (fn-pck-cat-withdraw-dirty *pckt-wide-h* 10 5))
                          (fn-pck-cat-pages (fn-cat$a-withdraw 10 5 *pckt-wide-h*)))))
