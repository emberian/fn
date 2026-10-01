; Teeth for books/catalog-paged.lisp's reader and probe keystones.
;
; fn-cp-isort-of-asc / fn-cp-isort-of-desc (the withdrawals-by-version
; reader's fast paths) and fn-cp-msort-is-isort (its fallback, Codex r30
; F3): reachable positive witnesses and hypothesis-removal witnesses; a
; labelled MUTATION of the merge's tie order.  fn-cat$p-next-is-probe /
; -prev-is-probe (Codex r30 F1): a positive witness on a state the
; executables built (commit N rows, withdraw the middle), and Codex's
; CORRUPTED-STATE construction (the tables erased: the PREV read of N then
; scans down to 1) -- unreachable from a corresponding state, which carries
; coverage.

(in-package "ACL2")
(include-book "../../books/catalog-paged")

; --- fn-cp-isort-of-asc: positive, and without its hypothesis.
(assert-event (and (fn-cp-asc-natsp '(1 3 5 9)) (equal (fn-cp-isort '(1 3 5 9)) '(1 3 5 9))))
(assert-event (and (not (fn-cp-asc-natsp '(3 1 5))) (not (equal (fn-cp-isort '(3 1 5)) '(3 1 5)))))

; --- fn-cp-isort-of-desc: positive, and without its hypothesis.
(assert-event (and (fn-cp-desc-natsp '(9 5 3 1)) (equal (fn-cp-isort '(9 5 3 1)) (rev '(9 5 3 1)))))
(assert-event (and (not (fn-cp-desc-natsp '(1 3))) (not (equal (fn-cp-isort '(1 3)) (rev '(1 3))))))

; --- the reader on each path equals the logical sort.
(assert-event (equal (fn-cp-sort-asc '(1 3 5 9)) '(1 3 5 9)))
(assert-event (equal (fn-cp-sort-asc '(9 5 3 1)) '(1 3 5 9)))
(assert-event (equal (fn-cp-sort-asc '(5 9 1 7 3 8 2)) (fn-cp-isort '(5 9 1 7 3 8 2))))

; --- fn-cp-msort-is-isort: a multi-row bucket (a scrambled one, both
; halves several rows, so the merge interleaves).
(assert-event
 (and (equal (fn-cp-msort '(5 9 1 7 3 8 2 6 4)) (fn-cp-isort '(5 9 1 7 3 8 2 6 4)))
      (equal (fn-cp-msort '(5 9 1 7 3 8 2 6 4)) '(1 2 3 4 5 6 7 8 9))))

; MUTATION (tie order): a merge that takes the RIGHT element on a tie is no
; longer the insertion sort when two elements share a key (x and 0 both
; nfix to 0): the stable merge keeps x first, as the insertion does.
(defun cpt-merge-right (x y)
  (declare (xargs :guard t :verify-guards nil :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((atom x) y)
        ((atom y) x)
        ((< (nfix (car x)) (nfix (car y))) (cons (car x) (cpt-merge-right (cdr x) y)))
        (t (cons (car y) (cpt-merge-right x (cdr y))))))

(assert-event
 (and (equal (fn-cp-msort '(x 0)) (fn-cp-isort '(x 0)))
      (equal (fn-cp-isort '(x 0)) '(x 0))
      (equal (cpt-merge-right (fn-cp-msort '(x)) (fn-cp-msort '(0))) '(0 x))
      (not (equal (cpt-merge-right (fn-cp-msort '(x)) (fn-cp-msort '(0))) (fn-cp-isort '(x 0))))))

; --- the probe: N rows of "fn.test" (row i is number i+1), the middle
; withdrawn (rows 1 .. N-2: numbers 2 .. N-1), then N's PREV and 1's NEXT.
(defun cpt-row (i)
  (declare (xargs :mode :program))
  (let ((art (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10))))
    (fn-held-plain (fn-record-make i (+ 1 i) 0
                                   (concatenate 'string "<" (coerce (explode-atom i 10) 'string) "@x>")
                                   art '("fn.test") "o" "s" "e" 1 5
                                   (fn-ab-for-received :post-d25 art))
                   i)))

(defun cpt-commit (i n fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (if (>= i n) fn-cat$p
    (let ((fn-cat$p (fn-cat$p-commit-w (cpt-row i) fn-cat$p)))
      (cpt-commit (1+ i) n fn-cat$p))))

(defun cpt-withdraw (i n fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (if (>= i n) fn-cat$p
    (let ((fn-cat$p (fn-cat$p-withdraw-w i 7 fn-cat$p)))
      (cpt-withdraw (1+ i) n fn-cat$p))))

; (live-N live-1 probe-prev-N prev-N probe-next-1 next-1), then the same
; after the tables are erased (CORRUPTED: no write the exports perform
; erases them without emptying the rows).
(defun cpt-probe (n corrupt)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat$p
    (mv-let (r fn-cat$p)
      (let* ((fn-cat$p (cpt-commit 0 n fn-cat$p))
             (fn-cat$p (cpt-withdraw 1 (- n 1) fn-cat$p))
             (fn-cat$p (if corrupt (fn-cat$p-lprev-clear fn-cat$p) fn-cat$p))
             (fn-cat$p (if corrupt (fn-cat$p-lnext-clear fn-cat$p) fn-cat$p)))
        (mv (list (fn-cat$p-live-at-p "fn.test" n fn-cat$p)
                  (fn-cat$p-live-at-p "fn.test" 1 fn-cat$p)
                  (fn-cat$p-lprev-get (cons "fn.test" n) fn-cat$p)
                  (fn-cat$p-prev "fn.test" n fn-cat$p)
                  (fn-cat$p-lnext-get (cons "fn.test" 1) fn-cat$p)
                  (fn-cat$p-next "fn.test" 1 fn-cat$p))
            fn-cat$p))
      r)))

; Positive (reachable: built by the executables the exports run): both
; numbers live, each probe bound, a natural, and the read.
(assert-event (equal (cpt-probe 8 nil) '(t t 1 1 8 8)))

; CORRUPTED-STATE (Codex r30 F1's construction): the tables erased, the
; probes are unbound and the reads fall back to the scans (the same
; answers, by the scans' soundness -- reached only off a corresponding
; state).
(assert-event (equal (cpt-probe 8 t) '(t t nil 1 nil 8)))
