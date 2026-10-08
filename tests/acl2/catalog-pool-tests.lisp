; Premises inhabited and teeth for books/catalog-pool.lisp (lane s-pool, phase
; 2b): fn-cpg-msgid-seqs-of-pages, fn-cpg-group-number-of-pages (and its core),
; fn-cpg-msgid-seqs-fills, fn-cpg-group-number-fills,
; fn-cpg-msgid-seqs-residency, fn-cpg-group-number-residency, and the library
; theorems they stand on (books/def-representation-pageread.lisp).
;
;   1. premises (a carried catalog of 150 rows on 3 pages, its directory, the
;      tape below 2^64, a FAITHFUL msgid index built by the writer the host
;      runs, a pool of 1, 2 and 3 frames), evaluated;
;   2. the claims at the witness;
;   3. teeth, each an executed witness that the claim is false for the right
;      reason, plus a must-fail-checked theorem form: a reader with no retry,
;      a bound without the directory term, candidates that miss an answer, a
;      fill that never evicts, a wrong dense-map answer, a catalog with an
;      overflow row (not carried).
;   Not witnessed: (fn-cat$pcorr fn-cat$p h) -- the dense-map composition is
;   fn-cat-paged-group-number{correspondence} (books/catalog-paged.lisp), proved
;   there; the core theorem (cand = the answer) is the part evaluated here.
;   And fn-cpg-tape-ok: a tape of 2^64 words cannot be built, so its removal
;   has no executable witness.

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
(defconst *cpt-dpages* (fn-cpg-dir-pages *cpt-h*))
(defconst *cpt-key* (make-list 32 :initial-element 7))

; The msgid index as the host's loader builds it, and its lookup for MSGID.
(defun cpt-index (rows msgid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-mlh
    (mv-let (result fn-mlh)
      (let ((fn-mlh (fn-mlh-set-key *cpt-key* fn-mlh)))
        (mv-let (u fn-mlh)
          (fn-mlh-build-from 0 0 rows fn-mlh)
          (mv (list u (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh) (fn-mlh-faithful rows fn-mlh)
                    (fn-mlh-candidates (fn-mlh-tag-of msgid fn-mlh) fn-mlh))
              fn-mlh)))
      result)))

(defconst *cpt-msgid* (fn-record-msgid (nth 100 *cpt-h*)))
(defconst *cpt-idx* (cpt-index *cpt-h* *cpt-msgid*))

; 1. Premises.
(assert-event (and (fn-cat-rowsp *cpt-h*) (fn-pck-carriedp *cpt-h*) (fn-cpg-tape-ok *cpt-h*)
                   (<= 3 (len *cpt-h*)) (<= 2 (len *cpt-pages*)) (equal (len *cpt-pages*) 3)))
(assert-event (and (equal (nth 0 *cpt-idx*) 0)            ; nothing unplaced
                   (nth 1 *cpt-idx*) (nth 2 *cpt-idx*) (nth 3 *cpt-idx*)   ; mlhp, wfp, faithful
                   (member 100 (nth 4 *cpt-idx*))))

(defun cpt-run (frames res)
  (fn-cpg-msgid-seqs *cpt-msgid* (nth 4 *cpt-idx*) (len *cpt-h*) *cpt-dpages* *cpt-pages* res frames))

; 2. The claims at the witness, for 1, 2 and 3 frames and a warm pool.
(assert-event (equal (fn-cat$a-msgid-seqs *cpt-msgid* *cpt-h*) '(100)))
(assert-event (and (equal (nth 0 (cpt-run 1 nil)) '(100))
                   (equal (nth 0 (cpt-run 2 nil)) '(100))
                   (equal (nth 0 (cpt-run 3 '((:rows . 1) (:dir . 0)))) '(100))))
(assert-event (and (<= (len (nth 2 (cpt-run 1 nil))) (fn-cpg-bound (nth 4 *cpt-idx*) *cpt-h*))
                   (<= (len (nth 2 (cpt-run 3 nil))) (fn-cpg-bound (nth 4 *cpt-idx*) *cpt-h*))))
(assert-event (and (<= (len (nth 1 (cpt-run 1 nil))) (adt-pr-cap 1))
                   (<= (len (nth 1 (cpt-run 2 nil))) (adt-pr-cap 2))
                   (<= (len (nth 1 (cpt-run 3 '((:rows . 1) (:dir . 0))))) (adt-pr-cap 3))))
; the second candidate's pages: one frame holds exactly the last page read
(assert-event (equal (nth 1 (cpt-run 1 nil)) '((:rows . 1))))

(defconst *cpt-num* (fn-cat$a-group-number "fn.test" 101 *cpt-h*))
(defun cpt-gn (cand frames res)
  (fn-cpg-group-number "fn.test" 101 cand (len *cpt-h*) *cpt-dpages* *cpt-pages* res frames))
(assert-event (and (natp *cpt-num*)
                   (equal (nth 0 (cpt-gn *cpt-num* 1 nil)) *cpt-num*)
                   (equal (nth 0 (cpt-gn *cpt-num* 2 '((:dir . 0)))) *cpt-num*)
                   (<= (len (nth 2 (cpt-gn *cpt-num* 1 nil))) (fn-cpg-bound (list *cpt-num*) *cpt-h*))
                   (equal (nth 0 (cpt-gn nil 1 nil)) nil)
                   (equal (fn-cat$a-group-number "fn.test" 9999 *cpt-h*) nil)))

; A row that straddles a page boundary takes more fills than its own pages.
(defun cpt-fills (seq)
  (declare (xargs :mode :program))
  (mv-let (row res fills) (fn-crow-read-indexed seq *cpt-dpages* *cpt-pages* nil 2 nil)
    (declare (ignore row res))
    (len fills)))
(defun cpt-straddler (seq)
  (declare (xargs :mode :program))
  (if (>= seq 150) nil
    (if (and (equal (cpt-fills seq) 3)
             (equal (fn-crow-pool-pages-of-row (fn-cp-row-of (nth seq *cpt-h*))) 1))
        seq (cpt-straddler (+ 1 seq)))))
(defconst *cpt-s* (cpt-straddler 0))
(assert-event (natp *cpt-s*))
(assert-event (equal (len (nth 2 (cpt-gn *cpt-s* 1 nil))) 3))   ; one frame still completes

; 3. Teeth.
; (a) No retry: the verdict is read as a word.
(defun cpt-noretry-words (j end)
  (declare (xargs :verify-guards nil :measure (nfix (- (nfix end) (nfix j)))))
  (if (< (nfix j) (nfix end)) (cons (adt-pr-word :rows j *cpt-pages* nil) (cpt-noretry-words (+ 1 (nfix j)) end)) nil))
(defun cpt-noretry-row (seq)
  (declare (xargs :verify-guards nil))
  (cpt-noretry-words (nth 0 (nth seq (fn-crow-dir-rows (fn-pck-crow-rows *cpt-h*))))
                     (+ (nth 0 (nth seq (fn-crow-dir-rows (fn-pck-crow-rows *cpt-h*)))) (nth 1 (nth seq (fn-crow-dir-rows (fn-pck-crow-rows *cpt-h*)))))))
(assert-event (member-equal '(:need-page :rows 0) (cpt-noretry-row 3)))
(assert-event (not (equal (car (adt-tp-dseq *fn-crow-schema* (cpt-noretry-row 100)))
                          (nth 100 (fn-pck-crow-rows *cpt-h*)))))
(must-fail-checked
 (defthm cpt-noretry-reads-the-row
   (equal (car (adt-tp-dseq *fn-crow-schema* (cpt-noretry-row 100)))
          (nth 100 (fn-pck-crow-rows *cpt-h*)))))

; (b) The bound without the directory term (the row's own pages and its
; straddle only): false at the straddler, where the entry costs one more.
(assert-event (< (+ 1 (fn-crow-pool-pages-of-row (fn-cp-row-of (nth *cpt-s* *cpt-h*))))
                 (len (nth 2 (cpt-gn *cpt-s* 1 nil)))))
(must-fail-checked
 (defthm cpt-bound-without-directory
   (<= (len (nth 2 (cpt-gn *cpt-s* 1 nil)))
       (+ 1 (fn-crow-pool-pages-of-row (fn-cp-row-of (nth *cpt-s* *cpt-h*)))))))

; (c) Candidates that miss an answer: wrong answer.
(assert-event (not (equal (nth 0 (fn-cpg-msgid-seqs *cpt-msgid* '(3 101) 150 *cpt-dpages* *cpt-pages* nil 2))
                          (fn-cat$a-msgid-seqs *cpt-msgid* *cpt-h*))))
(must-fail-checked
 (defthm cpt-msgid-seqs-uncovered
   (equal (nth 0 (fn-cpg-msgid-seqs *cpt-msgid* '(3 101) 150 *cpt-dpages* *cpt-pages* nil 2))
          (fn-cat$a-msgid-seqs *cpt-msgid* *cpt-h*))))

; (d) A fill that never evicts exceeds the frames.
(defun cpt-fill-noevict (p res frames)
  (declare (ignore frames))
  (cons p (remove-equal p res)))
(assert-event (< (adt-pr-cap 1) (len (cpt-fill-noevict '(:rows . 1) (cpt-fill-noevict '(:rows . 0) nil 1) 1))))
(assert-event (<= (len (adt-pr-fill '(:rows . 1) (adt-pr-fill '(:rows . 0) nil 1) 1)) (adt-pr-cap 1)))
(must-fail-checked
 (defthm cpt-fill-noevict-cap
   (<= (len (cpt-fill-noevict p res frames)) (adt-pr-cap frames))))

; (e) A dense-map answer that is not the number's row.
(assert-event (not (equal (nth 0 (cpt-gn 7 2 nil)) (fn-cat$a-group-number "fn.test" 101 *cpt-h*))))
(assert-event (equal (nth 0 (cpt-gn 7 2 nil)) '(:index-mismatch 7)))
(must-fail-checked
 (defthm cpt-group-number-wrong-cand
   (equal (nth 0 (cpt-gn 7 2 nil)) (fn-cat$a-group-number "fn.test" 101 *cpt-h*))))

; (f) A catalog with an overflow row is not carried: the pages do not give
; back the catalog, so the reader's row is not the catalog's.
(defconst *cpt-ovf-h* (append (cpt-cat 3) (list 7)))        ; 7 is no catalog row
(assert-event (and (not (fn-pck-carriedp *cpt-ovf-h*))
                   (not (equal (fn-cp-row-held (nth 3 (fn-pck-crow-rows *cpt-ovf-h*))) 7))))
