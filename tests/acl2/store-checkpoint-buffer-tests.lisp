; fn: teeth for books/store-checkpoint-buffer.lisp (rep-wave-d-2, PRF-133).
;
; The exec path on a live local buffer: the plan of a ground value at three
; segment sizes, its octets against `fn-scc-file-octets', its buffer against
; `fn-scc-encode', its segments read back by the unchanged reader; the
; refusal; and, per keystone hypothesis, a witness that the conclusion fails
; without it with every retained hypothesis true, and the `must-fail'.

(in-package "ACL2")
(include-book "../../books/store-checkpoint-buffer")
(include-book "std/testing/must-fail" :dir :system)

; Every executable function of the book is guard-verified: the host runs the
; compiled stobj code.
(assert-event
 (and (eq (symbol-class 'fn-sccb-append-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-cons-ops (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-treep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-renc (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-chunk-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-frames (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-slice-acc (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-frames-acc (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-frame-octets (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-plan-octets (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccb-plan (w state)) :common-lisp-compliant)))

; A ground checkpoint-shaped value: a string, the count slot, a cons tree
; with an octets leaf, a keyword, a natural, a negative, a character and
; nil, then two octets leaves.  Its program is 56 octets, so segment size 7
; cuts it into eight frames.
(defconst *sccbt-c*
  (list "fn" 3 (list (list 1 2 3 4 5 6 7) :k 42 -7 #\a nil)
        (list 10 20) (list 200 255 0)))

(assert-event (and (fn-sccb-treep *sccbt-c*) (fn-scc-treep *sccbt-c*)
                   (equal (fn-scc-value-sequence *sccbt-c*) 3)))

; Each frame's octets as the reader takes them.
(defun sccbt-segments (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard (true-list-listp plan)))
  (if (consp plan)
      (cons (fn-sccb-frame-octets (car plan) fn-octets)
            (sccbt-segments (cdr plan) fn-octets))
    nil))

; The exec path: (PLAN OCTETS SEGMENTS BUFFER) of C at SEG on a live buffer.
(defun sccbt-run (c seg)
  (declare (xargs :guard (natp seg)))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (plan fn-octets) (fn-sccb-plan c seg fn-octets)
        (mv (if (true-list-listp plan)
                (list plan
                      (fn-sccb-plan-octets plan fn-octets)
                      (sccbt-segments plan fn-octets)
                      (fn-octets-list fn-octets))
              (list plan nil nil (fn-octets-list fn-octets)))
            fn-octets))
      result)))

; KEYSTONE fn-sccb-plan-is-file-octets, the positive witness at seven
; frames: the antecedent, the conclusion, and the conclusion non-degenerate
; (a nonempty file, several chunks, the reader recovering the value).
(assert-event
 (let* ((r (sccbt-run *sccbt-c* 7))
        (plan (nth 0 r)) (octets (nth 1 r)) (segments (nth 2 r)) (buffer (nth 3 r)))
   (and (fn-sccb-treep *sccbt-c*)
        (equal octets (fn-scc-file-octets *sccbt-c* 7))
        (consp octets)
        (equal buffer (fn-scc-encode *sccbt-c*))
        (equal (len buffer) 56)
        (equal (len plan) 8)
        (equal (len plan) (len (fn-scc-segments *sccbt-c* 7)))
        (equal segments (fn-scc-segments *sccbt-c* 7))
        (equal (fn-scc-decode-segments segments) (list :ok *sccbt-c*)))))

; One frame: segment size 0 (the whole file) and a size past the file.
(assert-event
 (let ((r (sccbt-run *sccbt-c* 0)))
   (and (equal (nth 1 r) (fn-scc-file-octets *sccbt-c* 0))
        (equal (len (nth 0 r)) 1)
        (equal (fn-scc-decode-segments (nth 2 r)) (list :ok *sccbt-c*)))))
(assert-event
 (let ((r (sccbt-run *sccbt-c* 1000)))
   (and (equal (nth 1 r) (fn-scc-file-octets *sccbt-c* 1000))
        (equal (len (nth 0 r)) 1))))
; A chunk boundary exactly at the end: 56 = 56, one frame; 55: two.
(assert-event
 (and (equal (len (nth 0 (sccbt-run *sccbt-c* 56))) 1)
      (equal (nth 1 (sccbt-run *sccbt-c* 56)) (fn-scc-file-octets *sccbt-c* 56))
      (equal (len (nth 0 (sccbt-run *sccbt-c* 55))) 2)
      (equal (nth 1 (sccbt-run *sccbt-c* 55)) (fn-scc-file-octets *sccbt-c* 55))))
; The empty value (program: one NIL op).
(assert-event
 (let ((r (sccbt-run nil 7)))
   (and (equal (nth 1 r) (fn-scc-file-octets nil 7))
        (equal (nth 3 r) (list *fn-scc-op-nil*)))))

; The refusal: a rational is no atom of the codec.  The plan refuses where
; the list codec refuses (fn-sccb-plan-refuses-what-the-codec-refuses).
(assert-event
 (let ((r (sccbt-run (list 1/2) 7)))
   (and (not (fn-scc-treep (list 1/2)))
        (equal (nth 0 r) :unencodable)
        (equal (fn-scc-file-octets (list 1/2) 7) :unencodable))))

; KEYSTONE without (fn-sccb-treep c): the plan is :unencodable, whose
; octets are nil, and the list codec's answer is :unencodable, not nil.
(assert-event
 (let ((r (sccbt-run (list 1/2) 7)))
   (and (not (fn-sccb-treep (list 1/2)))
        (equal (nth 1 r) nil)
        (not (equal (nth 1 r) (fn-scc-file-octets (list 1/2) 7))))))
; (:do-not-induct keeps a doomed search from costing the book seconds; the
; refutation is the witness above, never the failed search.)
(must-fail
 (defthm sccbt-r-plan-without-treep
   (equal (fn-sccb-plan-octets (mv-nth 0 (fn-sccb-plan c seg fn-octets))
                               (mv-nth 1 (fn-sccb-plan c seg fn-octets)))
          (fn-scc-file-octets c seg))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; fn-sccb-treep-encodes-octets without its hypothesis: the program of a
; rational carries NIL (no package index) among its octets.  The program
; is guarded by `fn-scc-treep', so the witness is a ground theorem (proved
; by evaluation in the logic), not an `assert-event'.
(defthm sccbt-w-encodes-octets-without-treep
  (and (not (fn-sccb-treep (list 1/2)))
       (not (fn-scc-octet-listp (fn-scc-program (list 1/2)))))
  :rule-classes nil)
(assert-event (fn-scc-octet-listp (fn-scc-program *sccbt-c*)))
(must-fail
 (defthm sccbt-r-encodes-octets-without-treep
   (fn-scc-octet-listp (fn-scc-program x))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; fn-sccb-renc-is-program has no hypothesis: the buffer's append is `append'
; of one element on any object, so the equation holds even of an improper
; buffer value (the hypothesis (true-listp fn-octets) was dropped after the
; weakened theorem was proved).  The ground instance, by evaluation.
(defthm sccbt-w-renc-on-an-improper-buffer
  (and (not (true-listp '(1 . 2)))
       (equal (fn-sccb-renc 5 0 '(1 . 2))
              (append '(1 . 2) (fn-scc-program 5)
                      (fn-scc-repeat 0 *fn-scc-op-cons*)))
       (equal (fn-sccb-renc *sccbt-c* 0 nil) (fn-scc-program *sccbt-c*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sccb-renc fn-sccb-append-list
                                     fn-sccb-cons-ops))))

; fn-sccb-append-list-is-append and fn-sccb-cons-ops-is-append-repeat
; without (true-listp fn-octets): an empty write leaves an improper value
; as it is, and `append' of nil onto it does not.
(defthm sccbt-w-append-list-without-true-listp-buffer
  (and (not (true-listp '(1 . 2))) (true-listp nil)
       (not (equal (fn-sccb-append-list nil '(1 . 2)) (append '(1 . 2) nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sccb-append-list))))
(must-fail
 (defthm sccbt-r-append-list-without-true-listp-buffer
   (implies (true-listp xs)
            (equal (fn-sccb-append-list xs fn-octets) (append fn-octets xs)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))
(defthm sccbt-w-cons-ops-without-true-listp-buffer
  (and (not (true-listp '(1 . 2)))
       (not (equal (fn-sccb-cons-ops 0 '(1 . 2))
                   (append '(1 . 2) (fn-scc-repeat 0 *fn-scc-op-cons*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sccb-cons-ops))))
(must-fail
 (defthm sccbt-r-cons-ops-without-true-listp-buffer
   (equal (fn-sccb-cons-ops n fn-octets)
          (append fn-octets (fn-scc-repeat (nfix n) *fn-scc-op-cons*)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; fn-sccb-append-list-is-append without (true-listp xs): the writer walks
; the conses and `append' keeps the dotted tail.
(defthm sccbt-w-append-list-without-true-listp-xs
  (and (not (true-listp '(1 . 2)))
       (not (equal (fn-sccb-append-list '(1 . 2) '(9)) (append '(9) '(1 . 2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sccb-append-list))))
(must-fail
 (defthm sccbt-r-append-list-without-true-listp-xs
   (equal (fn-sccb-append-list xs fn-octets) (append fn-octets xs))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))
