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

; The live numbers 1..n of "fn.test" in c: the two link tables hold exactly
; this many entries when they bind the live numbers and nothing else
; (Codex r35 F1: a dead key bound in NEXT is a counterexample to
; fn-cpl-okp that the per-number check alone cannot see; the count sees it).
(defun cpt-live-count (k n c)
  (declare (xargs :mode :program))
  (if (> k n) 0
    (+ (if (fn-cat-live-numberp "fn.test" k c) 1 0) (cpt-live-count (1+ k) n c))))

; The observable content of fn-cat$pcorr on a built pair whose only group
; is "fn.test" with numbers 1..n: the count, every row, the live summary,
; the version's withdrawals, and the two link tables EXACTLY (the live
; numbers' entries are their neighbours and the tables have no other
; entry).  fn-cat$pcorr itself is a defun-sk over the tables and is not
; executable; on such a pair this observation is its content for the link
; conjuncts, and the exports' equalities for the view's.
(defun cpt-corr-evidence (n c fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (and (equal (fn-cat$p-count fn-cat$p) (fn-cat$a-count c))
       (equal (fn-cat$p-lnext-count fn-cat$p) (cpt-live-count 1 n c))
       (equal (fn-cat$p-lprev-count fn-cat$p) (cpt-live-count 1 n c))
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

; A DUPLICATE withdrawal (Codex r35 F2): the second withdrawal of row 1
; finds it withdrawn and changes nothing -- the bucket, the paged answer
; and the logical answer are those of the single withdrawal, and the
; correspondence's content holds after both.
(assert-event (let ((once (cpt-read 10 '(1))) (twice (cpt-read 10 '(1 1))))
                (and (equal (first once) '(1)) (equal (second once) '(1))
                     (equal (first twice) '(1)) (equal (second twice) '(1))
                     (equal (third twice) (third once))
                     (fourth once) (fourth twice))))

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

; KEYSTONE fn-cat$p-livep-is-live, executed (Codex r39): on the probe state
; (livep 1, live 1, livep n, live n, livep 2, live 2, evidence), the NEXT
; table optionally erased (CORRUPTED: coverage refuted) or given an entry
; for the dead 2 (CORRUPTED: goodness refuted; the entry count sees it).
(defun cpt-livep (n mode)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat$p
    (mv-let (r fn-cat$p)
      (let* ((l (cpt-middle 1 (- n 1)))
             (c (cpt-logical n l))
             (fn-cat$p (cpt-commit 0 n fn-cat$p))
             (fn-cat$p (cpt-withdraw l fn-cat$p))
             (fn-cat$p (if (eq mode :erase) (fn-cat$p-lnext-clear fn-cat$p) fn-cat$p))
             (fn-cat$p (if (eq mode :bind-dead)
                           (fn-cat$p-lnext-put (cons "fn.test" 2) n fn-cat$p)
                         fn-cat$p)))
        (mv (list (fn-cat$p-livep "fn.test" 1 fn-cat$p) (fn-cat-live-numberp "fn.test" 1 c)
                  (fn-cat$p-livep "fn.test" n fn-cat$p) (fn-cat-live-numberp "fn.test" n c)
                  (fn-cat$p-livep "fn.test" 2 fn-cat$p) (fn-cat-live-numberp "fn.test" 2 c)
                  (cpt-corr-evidence n c fn-cat$p))
            fn-cat$p))
      r)))

; Positive: the probe is liveness at the live low, the live high and the
; dead middle; the correspondence's content holds.
(assert-event (equal (cpt-livep 8 nil) '(t t t t nil nil t)))
; CORRESPONDENCE removed, two ways: NEXT erased (1 and 8 live, their probes
; false: coverage refuted); the dead 2 bound in NEXT (its probe true, 2 not
; live: okp refuted).  The conclusion fails and so does the evidence.
(assert-event (equal (cpt-livep 8 :erase) '(nil t nil t nil nil nil)))
(assert-event (equal (cpt-livep 8 :bind-dead) '(t t t t t nil nil)))

; Positive: the correspondence's content holds, k live; each probe bound,
; a natural, and the read (1's NEXT is 8, 8's PREV is 1).
(assert-event (equal (cpt-probe 8 1 nil) '(t 8 8 0 0 t)))
(assert-event (equal (cpt-probe 8 8 nil) '(t 0 0 1 1 t)))

; LIVENESS removed (Codex r33 F1): 2 is withdrawn; the correspondence's
; content still holds; both probes are unbound (not naturals: the
; conclusion fails), and the reads answer 0 -- there is no scan to fall
; back on: the executables never read a row to answer a neighbour.
(assert-event (equal (cpt-probe 8 2 nil) '(nil nil 0 nil 0 t)))

; CORRESPONDENCE removed (CORRUPTED-STATE, Codex r30 F1): the tables erased
; and the logical catalog unchanged.  8 is live in it and unbound in both
; tables -- the counterexample to fn-cpl-coverp, so fn-cat$pcorr fails --
; and the conclusion fails (the probes are not naturals; the reads answer
; 0 where the true neighbours are 1 and 8: on a state that does not
; correspond the probe is wrong, which is why the correspondence carries
; coverage).
(assert-event (equal (cpt-probe 8 8 t) '(t nil 0 nil 0 nil)))
(assert-event (equal (cpt-probe 8 1 t) '(t nil 0 nil 0 nil)))
