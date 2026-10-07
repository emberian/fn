; Premises inhabited and teeth for books/catalog-pool.lisp, phase A (lane
; s-pool): the STATEMENTS in that book's header, evaluated at a ground carried
; catalog of 150 rows over 3 pages.
;   1. premises (carried, >= 3 rows, >= 2 pages, a pool of 1 frame and of 2);
;   2. the claims at the witness, for every frame count;
;   3. teeth: a reader that skips the retry, a bound without the straddle
;      term, a candidate set that misses an answer, a fill that never evicts,
;      a wrong dense-map answer.  Each is an executed witness that its claim
;      is false, plus a must-fail-checked theorem form.

(in-package "ACL2")
(include-book "../../books/catalog-pool")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defun cpt-row (i)
  (declare (xargs :mode :program))
  (let* ((art (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10)))
         (h (fn-held-plain (fn-record-make i (+ 1 i) 0
                                           (concatenate 'string "<" (coerce (explode-atom i 10) 'string) "@x>")
                                           art '("fn.test") "o" "s" "e" 1 5)
                           7)))
    (fn-held-with-facts h (fn-held-facts-of art))))

(defun cpt-cat (n)
  (declare (xargs :mode :program))
  (if (zp n) nil (fn-cat$a-commit (cpt-row (- n 1)) (cpt-cat (- n 1)))))

(defconst *cpt-h* (cpt-cat 150))
(defconst *cpt-pages* (fn-pck-cat-pages *cpt-h*))
(defconst *cpt-dir* (fn-cpg-dir (fn-pck-crow-rows *cpt-h*)))

; 1. Premises.
(assert-event (and (fn-cat-rowsp *cpt-h*) (fn-pck-carriedp *cpt-h*)
                   (<= 3 (len *cpt-h*)) (<= 2 (len *cpt-pages*))
                   (equal (len *cpt-dir*) 151)
                   (fn-cpg-res-okp nil *cpt-pages*) (fn-cpg-res-okp '(2 0) *cpt-pages*)
                   (posp 1) (posp 2)))

(defconst *cpt-msgid* (fn-record-msgid (nth 100 *cpt-h*)))
(defconst *cpt-cands* '(3 100 101))     ; the mlh's answer: a superset, ascending

; 2. Statements 1, 2, 3, 4 at the witness, frames 1, 2, 3, resident sets empty and warm.
(defun cpt-run (frames res)
  (fn-cpg-msgid-seqs *cpt-msgid* *cpt-cands* *cpt-dir* *cpt-pages* res frames))

(assert-event (equal (fn-cat$a-msgid-seqs *cpt-msgid* *cpt-h*) '(100)))
(assert-event (and (equal (nth 0 (cpt-run 1 nil)) '(100))
                   (equal (nth 0 (cpt-run 2 nil)) '(100))
                   (equal (nth 0 (cpt-run 3 '(1 0))) '(100))))
(assert-event (and (<= (len (nth 2 (cpt-run 1 nil))) (fn-cpg-bound *cpt-cands* *cpt-h*))
                   (<= (len (nth 2 (cpt-run 3 nil))) (fn-cpg-bound *cpt-cands* *cpt-h*))))
(assert-event (and (<= (len (nth 1 (cpt-run 1 nil))) (fn-cpg-cap 1))
                   (<= (len (nth 1 (cpt-run 2 nil))) (fn-cpg-cap 2))
                   (<= (len (nth 1 (cpt-run 3 '(1 0)))) (fn-cpg-cap 3))))
(assert-event (equal (nth 1 (cpt-run 1 nil)) '(1)))     ; one frame: the last candidate's page

(defconst *cpt-num* (fn-cat$a-group-number "fn.test" 101 *cpt-h*))
(defun cpt-gn (cand frames res)
  (fn-cpg-group-number "fn.test" 101 cand *cpt-dir* *cpt-pages* res frames))
(assert-event (and (natp *cpt-num*)
                   (equal (nth 0 (cpt-gn *cpt-num* 1 nil)) *cpt-num*)
                   (equal (nth 0 (cpt-gn *cpt-num* 2 '(2))) *cpt-num*)
                   (<= (len (nth 2 (cpt-gn *cpt-num* 1 nil)))
                       (fn-cpg-bound (list *cpt-num*) *cpt-h*))
                   (equal (nth 0 (cpt-gn nil 1 nil)) nil)
                   (equal (fn-cat$a-group-number "fn.test" 9999 *cpt-h*) nil)))

; A row that straddles a page boundary takes 2 fills though it is 1 row-page.
(defun cpt-fills (seq)
  (declare (xargs :mode :program))
  (mv-let (row res fills) (fn-cpg-read-row seq *cpt-dir* *cpt-pages* nil 2 nil)
    (declare (ignore row res))
    (len fills)))

(defun cpt-straddler (seq)
  (declare (xargs :mode :program))
  (if (>= seq 150) nil
    (if (and (equal (cpt-fills seq) 2)
             (equal (fn-crow-pool-pages-of-row (fn-cp-row-of (nth seq *cpt-h*))) 1))
        seq (cpt-straddler (+ 1 seq)))))
(defconst *cpt-s* (cpt-straddler 0))
(assert-event (natp *cpt-s*))
(assert-event (equal (len (nth 2 (cpt-gn *cpt-s* 1 nil))) 2))     ; one frame still completes

; 3. Teeth.
; (a) No retry: the verdict is read as a word.
(defun cpt-noretry-words (j end)
  (declare (xargs :mode :program))
  (if (< j end) (cons (fn-cpg-word j *cpt-pages* nil) (cpt-noretry-words (+ 1 j) end)) nil))
(defun cpt-noretry-row (seq)
  (declare (xargs :mode :program))
  (cpt-noretry-words (nth seq *cpt-dir*) (nth (+ 1 seq) *cpt-dir*)))
(assert-event (member-equal '(:need-page 0) (cpt-noretry-row 3)))
(assert-event (not (equal (car (adt-tp-dseq *fn-crow-schema* (cpt-noretry-row 100)))
                          (nth 100 (fn-pck-crow-rows *cpt-h*)))))
(must-fail-checked
 (defthm cpt-noretry-reads-the-row
   (equal (car (adt-tp-dseq *fn-crow-schema* (cpt-noretry-row 100)))
          (nth 100 (fn-pck-crow-rows *cpt-h*)))))

; (b) The bound without the candidate straddle term: rows' own pages only.
(defun cpt-bound-nostraddle (cands h)
  (declare (xargs :mode :program))
  (if (consp cands)
      (+ (fn-crow-pool-pages-of-row (fn-cp-row-of (nth (car cands) h))) (cpt-bound-nostraddle (cdr cands) h))
    0))
(assert-event (< (cpt-bound-nostraddle (list *cpt-s*) *cpt-h*)
                 (len (nth 2 (cpt-gn *cpt-s* 1 nil)))))
(must-fail-checked
 (defthm cpt-bound-without-straddle
   (<= (len (nth 2 (cpt-gn *cpt-s* 1 nil))) (cpt-bound-nostraddle (list *cpt-s*) *cpt-h*))))

; (c) Candidates that miss an answer: no cover, wrong answer.
(assert-event (and (not (subsetp-equal '(100) '(3 101)))
                   (not (equal (nth 0 (fn-cpg-msgid-seqs *cpt-msgid* '(3 101) *cpt-dir* *cpt-pages* nil 2))
                               (fn-cat$a-msgid-seqs *cpt-msgid* *cpt-h*)))))
(must-fail-checked
 (defthm cpt-msgid-seqs-uncovered
   (equal (nth 0 (fn-cpg-msgid-seqs *cpt-msgid* '(3 101) *cpt-dir* *cpt-pages* nil 2))
          (fn-cat$a-msgid-seqs *cpt-msgid* *cpt-h*))))

; (d) A fill that never evicts exceeds the frames.
(defun cpt-fill-noevict (p res frames)
  (declare (ignore frames))
  (cons p (remove p res)))
(assert-event (< (fn-cpg-cap 1) (len (cpt-fill-noevict 1 (cpt-fill-noevict 0 nil 1) 1))))
(assert-event (<= (len (fn-cpg-fill 1 (fn-cpg-fill 0 nil 1) 1)) (fn-cpg-cap 1)))
(must-fail-checked
 (defthm cpt-fill-noevict-cap
   (<= (len (cpt-fill-noevict p res frames)) (fn-cpg-cap frames))))

; (e) A dense-map answer that is not the number's row.
(assert-event (not (equal (nth 0 (cpt-gn 7 2 nil)) (fn-cat$a-group-number "fn.test" 101 *cpt-h*))))
(assert-event (equal (nth 0 (cpt-gn 7 2 nil)) '(:index-mismatch 7)))
(must-fail-checked
 (defthm cpt-group-number-unpremised
   (equal (nth 0 (cpt-gn 7 2 nil)) (fn-cat$a-group-number "fn.test" 101 *cpt-h*))))
