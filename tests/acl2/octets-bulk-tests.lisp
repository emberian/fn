; fn: teeth for the octet buffer's bulk exports (lane octets-bulk,
; books/octets-stobj.lisp): fn-octets-append-back, fn-octets-get-word,
; fn-octets-append-word, and the round trip fn-oct-word-octets-of-word-at
; that a word copy between two buffers rests on.
;
; Each correspondence obligation gets a ground positive witness asserting
; its complete antecedent and conclusion, and for each hypothesis a
; witness on which every retained hypothesis holds, the omitted one fails,
; and the conclusion fails.  The executable path runs on a live local
; buffer (overlapping and non-overlapping back copies, a copy across the
; array's resize, a word past 2^56 that takes the octet-list path).

(in-package "ACL2")
(include-book "../../books/octets-stobj")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-octets$c-append-back (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-back-loop (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-get-word (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-word7 (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-word-down (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-octets$c-append-word (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-word-loop (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-back-copy (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-word-at (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-oct-word-octets (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The executable path on a live local buffer.

(defun obt-exec-run (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let* ((fn-octets (fn-octets-from-list '(1 2 3) fn-octets))
         (fn-octets (fn-octets-append-back 1 4 fn-octets))     ; overlap: one octet repeats
         (a (fn-octets-list fn-octets))
         (fn-octets (fn-octets-from-list '(1 2 3) fn-octets))
         (fn-octets (fn-octets-append-back 3 7 fn-octets))     ; overlap: a period of three
         (b (fn-octets-list fn-octets))
         (fn-octets (fn-octets-from-list '(1 2 3 4 5) fn-octets))
         (fn-octets (fn-octets-append-back 5 2 fn-octets))     ; no overlap
         (c (fn-octets-list fn-octets))
         (d (list (fn-octets-get-word 0 7 fn-octets)            ; the unrolled read
                  (fn-octets-get-word 1 3 fn-octets)            ; the loop read
                  (fn-octets-get-word 2 0 fn-octets)))
         (fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-word 197121 3 fn-octets)) ; 1 2 3
         (fn-octets (fn-octets-append-word 258 5 fn-octets))    ; 2 1 0 0 0
         (fn-octets (fn-octets-append-word (+ 7 (expt 2 60)) 9 fn-octets)) ; past 2^56
         (e (fn-octets-list fn-octets)))
    (mv (list a b c d e) fn-octets)))

(defun obt-exec-run-value ()
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (obt-exec-run fn-octets) v)))

(assert-event
 (equal (obt-exec-run-value)
        '((1 2 3 3 3 3 3)
          (1 2 3 1 2 3 1 2 3 1)
          (1 2 3 4 5 1 2)
          (#x02010504030201 #x040302 0)
          (1 2 3 2 1 0 0 0 7 0 0 0 0 0 0 16 0))))

; A run of 5000 from one seed octet: the array (reserved at 16) resizes
; inside the export, and every cell is the seed.
(defun obt-exec-big (fn-octets)
  (declare (xargs :stobjs fn-octets))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-octet 42 fn-octets))
         (fn-octets (fn-octets-append-octet 43 fn-octets))
         (fn-octets (fn-octets-append-back 2 5000 fn-octets))
         (r (list (fn-octets-len fn-octets) (fn-octets-get 5001 fn-octets)
                  (fn-octets-get 5000 fn-octets)
                  (equal (fn-octets-list fn-octets)
                         (fn-oct-back-copy 2 5000 '(42 43))))))
    (mv r fn-octets)))

(defun obt-exec-big-value ()
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (obt-exec-big fn-octets) v)))

(assert-event (equal (obt-exec-big-value) '(5002 43 42 t)))

; -----------------------------------------------------------------------------
; fn-octets-append-back{correspondence}: (corr c a), (natp off), (<= 1 off),
; (<= off (len a)), (natp n).  A concrete object is (array fill).

(defconst *obt-c* '((1 2 3 0) 3))
(defconst *obt-a* '(1 2 3))

(defthm obt-w-back ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c* *obt-a*)
       (natp 2) (<= 1 2) (<= 2 (fn-octets$a-len *obt-a*)) (natp 5)
       (fn-octets$corr (fn-octets$c-append-back 2 5 *obt-c*)
                       (fn-octets$a-append-back 2 5 *obt-a*))
       (equal (fn-octets$a-append-back 2 5 *obt-a*) '(1 2 3 2 3 2 3 2)))
  :rule-classes nil)

; Without (<= off (len a)): the executable writes N cells it did not read
; (the source index is below the array), the logic appends nothing.
(defthm obt-w-back-no-within ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c* *obt-a*)
       (natp 4) (<= 1 4) (not (<= 4 (fn-octets$a-len *obt-a*))) (natp 2)
       (not (fn-octets$corr (fn-octets$c-append-back 4 2 *obt-c*)
                            (fn-octets$a-append-back 4 2 *obt-a*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-back-no-within
   (implies (and (fn-octets$corr *obt-c* *obt-a*) (natp 4) (<= 1 4) (natp 2))
            (fn-octets$corr (fn-octets$c-append-back 4 2 *obt-c*)
                            (fn-octets$a-append-back 4 2 *obt-a*)))
   :hints (("Goal" :do-not-induct t))))

; Without (<= 1 off): offset 0 names no octet; the executable still counts
; N more cells, the logic appends nothing.
(defthm obt-w-back-no-positive ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c* *obt-a*)
       (natp 0) (not (<= 1 0)) (<= 0 (fn-octets$a-len *obt-a*)) (natp 2)
       (not (fn-octets$corr (fn-octets$c-append-back 0 2 *obt-c*)
                            (fn-octets$a-append-back 0 2 *obt-a*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-back-no-positive
   (implies (and (fn-octets$corr *obt-c* *obt-a*) (natp 0) (<= 0 (fn-octets$a-len *obt-a*))
                 (natp 2))
            (fn-octets$corr (fn-octets$c-append-back 0 2 *obt-c*)
                            (fn-octets$a-append-back 0 2 *obt-a*)))
   :hints (("Goal" :do-not-induct t))))

; Without (natp n): a negative count moves the fill count back, the logic
; keeps the list.
(defthm obt-w-back-no-natp-n ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c* *obt-a*)
       (natp 1) (<= 1 1) (<= 1 (fn-octets$a-len *obt-a*)) (not (natp -1))
       (not (fn-octets$corr (fn-octets$c-append-back 1 -1 *obt-c*)
                            (fn-octets$a-append-back 1 -1 *obt-a*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-back-no-natp-n
   (implies (and (fn-octets$corr *obt-c* *obt-a*) (natp 1) (<= 1 1)
                 (<= 1 (fn-octets$a-len *obt-a*)))
            (fn-octets$corr (fn-octets$c-append-back 1 -1 *obt-c*)
                            (fn-octets$a-append-back 1 -1 *obt-a*)))
   :hints (("Goal" :do-not-induct t))))

; Without the correspondence: a fill count past the abstraction.
(defconst *obt-c-long* '((1 2 3 9) 4))
(defthm obt-w-back-no-corr ; a ground witness, proved by evaluation
  (and (not (fn-octets$corr *obt-c-long* *obt-a*))
       (natp 1) (<= 1 1) (<= 1 (fn-octets$a-len *obt-a*)) (natp 1)
       (not (fn-octets$corr (fn-octets$c-append-back 1 1 *obt-c-long*)
                            (fn-octets$a-append-back 1 1 *obt-a*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-back-no-corr
   (implies (and (natp 1) (<= 1 1) (<= 1 (fn-octets$a-len *obt-a*)) (natp 1))
            (fn-octets$corr (fn-octets$c-append-back 1 1 *obt-c-long*)
                            (fn-octets$a-append-back 1 1 *obt-a*)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-octets-get-word{correspondence}: (corr c a), (natp i), (natp k),
; (<= (+ i k) (len a)).

(defthm obt-w-word ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c* *obt-a*)
       (natp 1) (natp 2) (<= (+ 1 2) (fn-octets$a-len *obt-a*))
       (equal (fn-octets$c-get-word 1 2 *obt-c*) (fn-octets$a-get-word 1 2 *obt-a*))
       (equal (fn-octets$a-get-word 1 2 *obt-a*) (+ 2 (* 256 3))))
  :rule-classes nil)

; Without the bound: the array's spare cell (0) is read where the
; abstraction has nothing; a nonzero spare cell shows the difference.
(defconst *obt-c-spare* '((1 2 3 9) 3))
(defthm obt-w-word-no-bound ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c-spare* *obt-a*)
       (natp 2) (natp 2) (not (<= (+ 2 2) (fn-octets$a-len *obt-a*)))
       (not (equal (fn-octets$c-get-word 2 2 *obt-c-spare*)
                   (fn-octets$a-get-word 2 2 *obt-a*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-word-no-bound
   (implies (and (fn-octets$corr *obt-c-spare* *obt-a*) (natp 2) (natp 2))
            (equal (fn-octets$c-get-word 2 2 *obt-c-spare*)
                   (fn-octets$a-get-word 2 2 *obt-a*)))
   :hints (("Goal" :do-not-induct t))))

; Without the correspondence: the array's cells differ from the list.
(defconst *obt-a-other* '(1 7 3))
(defthm obt-w-word-no-corr ; a ground witness, proved by evaluation
  (and (not (fn-octets$corr *obt-c* *obt-a-other*))
       (natp 1) (natp 1) (<= (+ 1 1) (fn-octets$a-len *obt-a-other*))
       (not (equal (fn-octets$c-get-word 1 1 *obt-c*)
                   (fn-octets$a-get-word 1 1 *obt-a-other*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-word-no-corr
   (implies (and (natp 1) (natp 1) (<= (+ 1 1) (fn-octets$a-len *obt-a-other*)))
            (equal (fn-octets$c-get-word 1 1 *obt-c*)
                   (fn-octets$a-get-word 1 1 *obt-a-other*)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-octets-append-word{correspondence}: (corr c a), (natp w), (natp k).

(defthm obt-w-append-word ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c* *obt-a*) (natp 258) (natp 3)
       (fn-octets$corr (fn-octets$c-append-word 258 3 *obt-c*)
                       (fn-octets$a-append-word 258 3 *obt-a*))
       (equal (fn-octets$a-append-word 258 3 *obt-a*) '(1 2 3 2 1 0)))
  :rule-classes nil)

; Without (natp k): a negative count moves the fill count back.
(defthm obt-w-append-word-no-natp-k ; a ground witness, proved by evaluation
  (and (fn-octets$corr *obt-c* *obt-a*) (natp 258) (not (natp -1))
       (not (fn-octets$corr (fn-octets$c-append-word 258 -1 *obt-c*)
                            (fn-octets$a-append-word 258 -1 *obt-a*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-append-word-no-natp-k
   (implies (and (fn-octets$corr *obt-c* *obt-a*) (natp 258))
            (fn-octets$corr (fn-octets$c-append-word 258 -1 *obt-c*)
                            (fn-octets$a-append-word 258 -1 *obt-a*)))
   :hints (("Goal" :do-not-induct t))))

; Without the correspondence.
(defthm obt-w-append-word-no-corr ; a ground witness, proved by evaluation
  (and (not (fn-octets$corr *obt-c-long* *obt-a*)) (natp 258) (natp 1)
       (not (fn-octets$corr (fn-octets$c-append-word 258 1 *obt-c-long*)
                            (fn-octets$a-append-word 258 1 *obt-a*))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-append-word-no-corr
   (implies (and (natp 258) (natp 1))
            (fn-octets$corr (fn-octets$c-append-word 258 1 *obt-c-long*)
                            (fn-octets$a-append-word 258 1 *obt-a*)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-oct-word-octets-of-word-at: (fn-cbor-octet-listp xs), (natp i),
; (<= (+ i k) (len xs)).  (A K that is not a natural gives nil on both
; sides; the theorem is proved without (natp k).)

(defthm obt-w-rt ; a ground witness, proved by evaluation
  (and (fn-cbor-octet-listp '(9 255 0 17 4)) (natp 1)
       (<= (+ 1 3) (len '(9 255 0 17 4)))
       (equal (fn-oct-word-octets (fn-oct-word-at 1 3 '(9 255 0 17 4)) 3)
              (take 3 (nthcdr 1 '(9 255 0 17 4))))
       (equal (take 3 (nthcdr 1 '(9 255 0 17 4))) '(255 0 17)))
  :rule-classes nil)

; Without the octet list: a cell of 256 is carried into the next octet.
(defthm obt-w-rt-no-octets ; a ground witness, proved by evaluation
  (and (not (fn-cbor-octet-listp '(256 0))) (natp 0) (<= (+ 0 2) (len '(256 0)))
       (not (equal (fn-oct-word-octets (fn-oct-word-at 0 2 '(256 0)) 2)
                   (take 2 (nthcdr 0 '(256 0))))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-rt-no-octets
   (implies (and (natp 0) (<= (+ 0 2) (len '(256 0))))
            (equal (fn-oct-word-octets (fn-oct-word-at 0 2 '(256 0)) 2)
                   (take 2 (nthcdr 0 '(256 0)))))
   :hints (("Goal" :do-not-induct t))))

; Without the bound: past the end `take' pads with nil, the word with 0.
(defthm obt-w-rt-no-bound ; a ground witness, proved by evaluation
  (and (fn-cbor-octet-listp '(5)) (natp 0) (not (<= (+ 0 2) (len '(5))))
       (not (equal (fn-oct-word-octets (fn-oct-word-at 0 2 '(5)) 2)
                   (take 2 (nthcdr 0 '(5))))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-rt-no-bound
   (implies (and (fn-cbor-octet-listp '(5)) (natp 0))
            (equal (fn-oct-word-octets (fn-oct-word-at 0 2 '(5)) 2)
                   (take 2 (nthcdr 0 '(5)))))
   :hints (("Goal" :do-not-induct t))))

; Without (natp i): a negative index still reads K cells from cell 0 (the
; word reads through `nfix'), while the bound (+ i k) no longer keeps them
; within the list, and `take' pads with nil.
(defthm obt-w-rt-no-natp-i ; a ground witness, proved by evaluation
  (and (fn-cbor-octet-listp '(1)) (not (natp -5)) (<= (+ -5 3) (len '(1)))
       (not (equal (fn-oct-word-octets (fn-oct-word-at -5 3 '(1)) 3)
                   (take 3 (nthcdr -5 '(1))))))
  :rule-classes nil)
(must-fail
 (defthm obt-t-rt-no-natp-i
   (implies (and (fn-cbor-octet-listp '(1)) (<= (+ -5 3) (len '(1))))
            (equal (fn-oct-word-octets (fn-oct-word-at -5 3 '(1)) 3)
                   (take 3 (nthcdr -5 '(1)))))
   :hints (("Goal" :do-not-induct t))))
