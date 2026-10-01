; Teeth for books/catalog-paged.lisp's reader and probe keystones.
;
; Every state here is BUILT by the executables the abstract stobj's exports
; run (fn-cat$p-commit-w, fn-cat$p-withdraw-w), with the logical catalog
; built beside it by the exports' :logic functions (fn-cat$a-commit,
; fn-cat$a-withdraw).  fn-cat$pcorr is a defun-nx over a defun-sk
; (coverage), so it is not evaluated; each witness instead asserts its
; observable content on the built pair (cpt-corr-evidence: the count, every
; row, the live summary, the withdrawals reader, and for every number of
; the group the coverage and goodness of both link tables against the
; logical catalog) -- or, for the CORRUPTED state, affirms its failure by
; exhibiting the defun-sk's counterexample (a live number unbound).
;
; fn-cpt-list-of-add (books/catalog-wbv-trie.lisp, the withdrawals-by-
; version reader): writer-built buckets in ascending, descending and
; scrambled withdrawal order (Codex r33 F3), each read through
; fn-cat$p-withdrawn-at and equal to the logical fn-cat$a-withdrawn-at; the
; keystone's antecedent and conclusion on the bucket before and after the
; last withdrawal; its natp removal; a labelled MUTATION of the walk order.
; fn-cat$p-next-is-probe / -prev-is-probe (Codex r30 F1, r33 F1): the
; positive on the built pair, a LIVENESS-removal witness (a withdrawn
; number: correspondence holds, the probes are unbound, the scans answer),
; and the CORRUPTED-STATE correspondence-removal witness (tables erased).

(in-package "ACL2")
(include-book "../../books/catalog-paged")

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

(defun cpt-withdraw (l fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (if (atom l) fn-cat$p
    (let ((fn-cat$p (fn-cat$p-withdraw-w (car l) 7 fn-cat$p)))
      (cpt-withdraw (cdr l) fn-cat$p))))

(defun cpt-a-commit (i n c)
  (declare (xargs :mode :program))
  (if (>= i n) c (cpt-a-commit (1+ i) n (fn-cat$a-commit (cpt-row i) c))))

(defun cpt-a-withdraw (l c)
  (declare (xargs :mode :program))
  (if (atom l) c (cpt-a-withdraw (cdr l) (fn-cat$a-withdraw (car l) 7 c))))

(defun cpt-logical (n l)
  (declare (xargs :mode :program))
  (cpt-a-withdraw l (cpt-a-commit 0 n nil)))

; The observable content of fn-cat$pcorr on a built pair, numbers 1..n of
; "fn.test" (every number the group has).
(defun cpt-links-ok (k n c fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (or (> k n)
      (and (or (not (fn-cat-live-numberp "fn.test" k c))
               (let ((nx (fn-cat$p-lnext-get (cons "fn.test" k) fn-cat$p))
                     (pv (fn-cat$p-lprev-get (cons "fn.test" k) fn-cat$p)))
                 (and (natp nx) (natp pv)
                      (equal nx (fn-cpl-next-of "fn.test" k c))
                      (equal pv (fn-cpl-prev-of "fn.test" k c)))))
           (cpt-links-ok (1+ k) n c fn-cat$p))))

(defun cpt-rows-ok (s c fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (or (>= s (len c))
      (and (equal (fn-cat$p-at s fn-cat$p) (fn-cat$a-at s c))
           (cpt-rows-ok (1+ s) c fn-cat$p))))

(defun cpt-corr-evidence (n c fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (and (equal (fn-cat$p-count fn-cat$p) (fn-cat$a-count c))
       (cpt-rows-ok 0 c fn-cat$p)
       (equal (fn-cat$p-group-live-low "fn.test" fn-cat$p) (fn-cat$a-group-live-low "fn.test" c))
       (equal (fn-cat$p-group-live-high "fn.test" fn-cat$p) (fn-cat$a-group-live-high "fn.test" c))
       (equal (fn-cat$p-group-live-count "fn.test" fn-cat$p) (fn-cat$a-group-live-count "fn.test" c))
       (equal (fn-cat$p-withdrawn-at n fn-cat$p) (fn-cat$a-withdrawn-at n c))
       (cpt-links-ok 1 n c fn-cat$p)))

; ---------------------------------------------------------------------------
; The reader.  n rows, the rows of l withdrawn in l's order (one version, n):
; (paged answer, logical answer, the bucket's trie, evidence).
(defun cpt-read (n l)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat$p
    (mv-let (r fn-cat$p)
      (let* ((fn-cat$p (cpt-commit 0 n fn-cat$p))
             (fn-cat$p (cpt-withdraw l fn-cat$p))
             (c (cpt-logical n l)))
        (mv (list (fn-cat$p-withdrawn-at n fn-cat$p)
                  (fn-cat$a-withdrawn-at n c)
                  (fn-cat$p-wbv-get n fn-cat$p)
                  (cpt-corr-evidence n c fn-cat$p))
            fn-cat$p))
      r)))

; fn-cpt-list-of-add on a writer-built bucket: the trie before the last
; withdrawal (l less its last) and after it; the antecedent (natp s) and
; the conclusion; the reader's answer is the logical catalog's.
(defun cpt-reader-witness (n l want)
  (declare (xargs :mode :program))
  (let* ((s (car (last l)))
         (before (cpt-read n (butlast l 1)))
         (after (cpt-read n l)))
    (and (natp s)
         (equal (third after) (fn-cpt-add s (third before)))
         (equal (fn-cpt-list (fn-cpt-add s (third before)))
                (fn-cpt-insert s (fn-cpt-list (third before))))
         (equal (first after) want)
         (equal (second after) want)
         (fourth before) (fourth after))))

(assert-event (cpt-reader-witness 10 '(1 3 5 9) '(1 3 5 9)))              ; ascending arrival
(assert-event (cpt-reader-witness 10 '(9 5 3 1) '(1 3 5 9)))              ; descending arrival
(assert-event (cpt-reader-witness 10 '(5 9 1 7 3 8 2) '(1 2 3 5 7 8 9)))  ; scrambled arrival
(assert-event (cpt-reader-witness 40 '(33 0 17 39 2 31 8)                 ; scrambled, a deeper trie
                                  '(0 2 8 17 31 33 39)))

; fn-cpt-list-of-add without (natp s): a non-natural is filed as 0, so the
; trie answers 0 where the insertion answers the symbol.  (Run on the
; definitions: x is outside fn-cpt-add's guard.)
(with-guard-checking-event
 :none
 (assert-event
  (and (not (natp 'x))
       (equal (fn-cpt-list (fn-cpt-add 'x nil)) '(0))
       (not (equal (fn-cpt-list (fn-cpt-add 'x nil)) (fn-cpt-insert 'x (fn-cpt-list nil)))))))

; MUTATION (walk order): a reader that walks the LOW subtree first onto its
; accumulator answers the bucket descending -- not the logical list.
(defun cpt-walk-low-first (d base tr acc)
  (declare (xargs :mode :program))
  (cond ((zp d) (fn-cpt-rep (nfix tr) base acc))
        ((atom tr) acc)
        (t (cpt-walk-low-first (1- d) (+ base (expt 2 (1- d))) (cdr tr)
                               (cpt-walk-low-first (1- d) base (car tr) acc)))))

(assert-event
 (let ((v (third (cpt-read 10 '(5 9 1 7 3 8 2)))))
   (and (equal (fn-cpt-list v) '(1 2 3 5 7 8 9))
        (equal (cpt-walk-low-first (fn-cpt-d v) 0 (fn-cpt-tr v) nil) '(9 8 7 5 3 2 1))
        (not (equal (cpt-walk-low-first (fn-cpt-d v) 0 (fn-cpt-tr v) nil) (fn-cpt-list v))))))

; ---------------------------------------------------------------------------
; The probe: n rows of "fn.test" (row i is number i+1), the middle withdrawn
; (rows 1 .. n-2: numbers 2 .. n-1); k is queried.  (live-k-logical,
; NEXT probe, NEXT read, PREV probe, PREV read, evidence), the tables
; optionally erased (CORRUPTED: no export erases them without emptying the
; rows).
(defun cpt-middle (i n)
  (declare (xargs :mode :program))
  (if (>= i n) nil (cons i (cpt-middle (1+ i) n))))

(defun cpt-probe (n k corrupt)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat$p
    (mv-let (r fn-cat$p)
      (let* ((l (cpt-middle 1 (- n 1)))
             (c (cpt-logical n l))
             (fn-cat$p (cpt-commit 0 n fn-cat$p))
             (fn-cat$p (cpt-withdraw l fn-cat$p))
             (fn-cat$p (if corrupt (fn-cat$p-lprev-clear fn-cat$p) fn-cat$p))
             (fn-cat$p (if corrupt (fn-cat$p-lnext-clear fn-cat$p) fn-cat$p)))
        (mv (list (fn-cat-live-numberp "fn.test" k c)
                  (fn-cat$p-lnext-get (cons "fn.test" k) fn-cat$p)
                  (fn-cat$p-next "fn.test" k fn-cat$p)
                  (fn-cat$p-lprev-get (cons "fn.test" k) fn-cat$p)
                  (fn-cat$p-prev "fn.test" k fn-cat$p)
                  (cpt-corr-evidence n c fn-cat$p))
            fn-cat$p))
      r)))

; Positive: the correspondence's content holds, k live; each probe bound,
; a natural, and the read (1's NEXT is 8, 8's PREV is 1).
(assert-event (equal (cpt-probe 8 1 nil) '(t 8 8 0 0 t)))
(assert-event (equal (cpt-probe 8 8 nil) '(t 0 0 1 1 t)))

; LIVENESS removed (Codex r33 F1): 2 is withdrawn; the correspondence's
; content still holds; both probes are unbound (not naturals: the
; conclusion fails) and the scans answer 8 and 1.
(assert-event (equal (cpt-probe 8 2 nil) '(nil nil 8 nil 1 t)))

; CORRESPONDENCE removed (CORRUPTED-STATE, Codex r30 F1): the tables erased
; and the logical catalog unchanged.  8 is live in it and unbound in both
; tables -- the counterexample to fn-cpl-coverp, so fn-cat$pcorr fails --
; and the conclusion fails (the probes are not naturals); the reads fall
; back to the scans (the same answers, by the scans' soundness).
(assert-event (equal (cpt-probe 8 8 t) '(t nil 0 nil 1 nil)))
(assert-event (equal (cpt-probe 8 1 t) '(t nil 8 nil 0 nil)))
