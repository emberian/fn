; fn: teeth for books/store-checkpoint-reader.lisp (rep-wave-d-3, PRF-135).
;
; The exec path on a live local buffer: the writer's plan of a ground value
; decoded back by the reader (the keystone's positive witness, several
; frames and every leaf kind), the same at one frame and at a chunk
; boundary; the reader against the list decoder on the frames' octets, on
; the intact plan and on corrupted ones (a flipped octet, a dropped frame,
; a wrong first header, a wrong sequence), same verdict each time; the
; index machine against the list machine; the admission's two bounds; and,
; per keystone hypothesis, a witness that the conclusion fails without it
; with every retained hypothesis true, and the `must-fail'.

(in-package "ACL2")
(include-book "../../books/store-checkpoint-reader")
(include-book "std/testing/must-fail" :dir :system)

; Every executable function of the book is guard-verified: the host runs the
; compiled stobj code at open.
(assert-event
 (and (eq (symbol-class 'fn-sccr-cell (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-read-nat (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-read-string (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-run (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-decode-tree (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-at (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-framep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-planp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-plan-segments (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-open-frame (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-join (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-decode-plan (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-file-read-bound (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sccr-admit-segment (w state)) :common-lisp-compliant)))

; The ground checkpoint-shaped value of the writer's teeth: a string, the
; count slot, a cons tree with an octets leaf, a keyword, a natural, a
; negative, a character and nil, then two octets leaves; program 56 octets,
; eight frames at segment size 7.
(defconst *sccrt-c*
  (list "fn" 3 (list (list 1 2 3 4 5 6 7) :k 42 -7 #\a nil)
        (list 10 20) (list 200 255 0)))

(assert-event (and (fn-sccb-treep *sccrt-c*)
                   (equal (fn-scc-value-sequence *sccrt-c*) 3)
                   (< (+ 1 (len (fn-scc-encode *sccrt-c*))) *fn-scc-u64-bound*)))

; The list decoder over what the host's file bytes would be, guarded at
; run time (the teeth never run on a served path).
(defun sccrt-listed (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (true-list-listp plan)
      (let ((segments (fn-sccr-plan-segments plan fn-octets)))
        (if (fn-scc-segment-listp segments)
            (fn-scc-decode-segments segments)
          :bad))
    :bad))

; (PLAN DECODED SEGMENTS LIST-DECODED) of C at SEG, on a live buffer: the
; writer's plan, the reader over it, the frames' octets and the list
; decoder over them.
(defun sccrt-round (c seg)
  (declare (xargs :guard (natp seg)))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (plan fn-octets) (fn-sccb-plan c seg fn-octets)
        (mv (list plan
                  (fn-sccr-decode-plan plan fn-octets)
                  (if (true-list-listp plan) (fn-sccr-plan-segments plan fn-octets) nil)
                  (sccrt-listed plan fn-octets))
            fn-octets))
      result)))

; KEYSTONE fn-sccr-decode-of-plan, the positive witness at eight frames:
; every hypothesis, the conclusion, and the conclusion non-degenerate (a
; nonempty tree with every leaf kind, several chunks, a payload leaf that
; straddles a chunk boundary since 7 does not divide the leaf's offset).
(assert-event
 (let* ((r (sccrt-round *sccrt-c* 7))
        (plan (nth 0 r)) (decoded (nth 1 r)) (segments (nth 2 r)) (listed (nth 3 r)))
   (and (fn-sccb-treep *sccrt-c*)
        (equal decoded (list :ok *sccrt-c*))
        (equal (len plan) 8)
        (equal segments (fn-scc-segments *sccrt-c* 7))
        (equal listed decoded))))

; One frame (segment size 0: the whole program; 1000: past it), and the
; chunk boundary exactly at the end (56: one frame; 55: two).
(assert-event
 (and (equal (nth 1 (sccrt-round *sccrt-c* 0)) (list :ok *sccrt-c*))
      (equal (len (nth 0 (sccrt-round *sccrt-c* 0))) 1)
      (equal (nth 1 (sccrt-round *sccrt-c* 1000)) (list :ok *sccrt-c*))
      (equal (nth 1 (sccrt-round *sccrt-c* 56)) (list :ok *sccrt-c*))
      (equal (len (nth 0 (sccrt-round *sccrt-c* 56))) 1)
      (equal (nth 1 (sccrt-round *sccrt-c* 55)) (list :ok *sccrt-c*))
      (equal (len (nth 0 (sccrt-round *sccrt-c* 55))) 2)))
; The empty value (program: one NIL op).
(assert-event (equal (nth 1 (sccrt-round nil 7)) (list :ok nil)))

; -----------------------------------------------------------------------------
; The twin on corrupted plans: the reader and the list decoder over the same
; frames' octets, the same verdict.  Each mutation is applied after the plan
; is made, on the buffer or on the plan.

; (READER LISTED) after mutating the buffer's cell AT.
(defun sccrt-flip (c seg at)
  (declare (xargs :guard (and (natp seg) (natp at))))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (plan fn-octets) (fn-sccb-plan c seg fn-octets)
        (if (< at (fn-octets-len fn-octets))
            (let* ((x (fn-sccr-cell at fn-octets))
                   (fn-octets (fn-octets-put at (if (< x 255) (+ x 1) 0) fn-octets)))
              (mv (list (fn-sccr-decode-plan plan fn-octets)
                        (sccrt-listed plan fn-octets))
                  fn-octets))
          (mv (list :bad :bad) fn-octets)))
      result)))

; A flipped octet in the third chunk: that segment's seal fails, on both.
(assert-event
 (let ((r (sccrt-flip *sccrt-c* 7 16)))
   (and (equal (nth 0 r) (list :refused :segment))
        (equal (nth 1 r) (list :refused :segment)))))
; A flipped octet in the first chunk: the first segment's seal fails.
(assert-event
 (let ((r (sccrt-flip *sccrt-c* 7 0)))
   (and (equal (nth 0 r) (list :refused :segment))
        (equal (nth 1 r) (list :refused :segment)))))

; (READER LISTED) after a change to the plan itself.
(defun sccrt-replan (c seg how)
  (declare (xargs :guard (natp seg)))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (plan fn-octets) (fn-sccb-plan c seg fn-octets)
        (if (and (true-listp plan) (consp plan))
            (let* ((first (car plan))
                   (h (fn-sccr-at 0 first)) (a (fn-sccr-at 1 first))
                   (b (fn-sccr-at 2 first)) (tr (fn-sccr-at 3 first))
                   (rest (if (consp h) (cdr h) nil))
                   (plan (cond ((eq how :drop-last) (take (len (cdr plan)) plan))
                               ((eq how :drop-first) (cdr plan))
                               ((eq how :bad-header)
                                (cons (list (cons 0 rest) a b tr) (cdr plan)))
                               ((eq how :short-header)
                                (cons (list rest a b tr) (cdr plan)))
                               (t plan))))
              (mv (list (fn-sccr-decode-plan plan fn-octets)
                        (sccrt-listed plan fn-octets))
                  fn-octets))
          (mv (list :bad :bad) fn-octets)))
      result)))

; The last frame dropped: truncated, on both.
(assert-event
 (let ((r (sccrt-replan *sccrt-c* 7 :drop-last)))
   (and (equal (nth 0 r) (list :refused :truncated))
        (equal (nth 1 r) (list :refused :truncated)))))
; The first frame dropped: the next frame's index is 1, not 0 (:segment),
; on both; the reader's plan begins at that frame's own A.
(assert-event
 (let ((r (sccrt-replan *sccrt-c* 7 :drop-first)))
   (and (equal (nth 0 r) (list :refused :segment))
        (equal (nth 1 r) (list :refused :segment)))))
; The first header's magic broken: no header, on both.
(assert-event
 (let ((r (sccrt-replan *sccrt-c* 7 :bad-header)))
   (and (equal (nth 0 r) (list :refused :header))
        (equal (nth 1 r) (list :refused :header)))))

; A wrong sequence: the frames sealed under sequence 4 over the program of
; a value whose count is 3 verify as segments and are refused as a value,
; on both.
(defun sccrt-resequence (c seg)
  (declare (xargs :guard (natp seg)))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (plan fn-octets) (fn-sccb-plan c seg fn-octets)
        (declare (ignore plan))
        (let ((plan (fn-sccb-frames-acc 0 0
                                        (fn-sccb-chunk-count (fn-octets-len fn-octets) seg)
                                        (nfix (+ 1 (fn-scc-value-sequence c)))
                                        *fn-scc-genesis* seg nil fn-octets)))
          (mv (list (fn-sccr-decode-plan plan fn-octets)
                    (sccrt-listed plan fn-octets))
              fn-octets)))
      result)))

(assert-event
 (let ((r (sccrt-resequence *sccrt-c* 7)))
   (and (equal (nth 0 r) (list :refused :value))
        (equal (nth 1 r) (list :refused :value)))))

; -----------------------------------------------------------------------------
; fn-sccr-run-is-run, the index machine against the list machine, on the
; program and on its every proper suffix (a suffix is a program that runs
; to a stack of several values, or refuses at a CONS with one operand).
(defun sccrt-runs (i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))))
  (if (or (not (natp i)) (not (natp end)) (>= i end))
      t
    (let ((xs (fn-oct-slice-list i end fn-octets)))
      (and (fn-scc-octet-listp xs)
           (equal (fn-sccr-run i end nil fn-octets) (fn-scc-run xs nil))
           (sccrt-runs (+ 1 i) end fn-octets)))))

(defun sccrt-machine-check (c)
  (declare (xargs :guard t))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let ((program (if (fn-scc-treep c) (fn-scc-encode c) :bad)))
        (if (fn-cbor-octet-listp program)
            (let ((fn-octets (fn-octets-from-list program fn-octets)))
              (mv (and (equal (fn-sccr-run 0 (fn-octets-len fn-octets) nil fn-octets)
                              (list c))
                       (sccrt-runs 0 (fn-octets-len fn-octets) fn-octets))
                  fn-octets))
          (mv :bad fn-octets)))
      result)))

(assert-event (equal (sccrt-machine-check *sccrt-c*) t))

; -----------------------------------------------------------------------------
; The admission: the header of the ground value's first frame at segment
; size 7 (index 0 of 8, chunk 7, sequence 3; extent 76).  A constant, since
; a frame's trailer is the attached digest, which a defconst cannot run.
(defconst *sccrt-h* (fn-scc-header 0 8 7 3))
(assert-event
 (and (equal *sccrt-h* (fn-sccr-at 0 (car (nth 0 (sccrt-round *sccrt-c* 7)))))
      (equal (fn-sccr-admit-segment *sccrt-h* 0 76 1000) (list :ok 76 7))
      (equal (fn-sccr-admit-segment *sccrt-h* 924 76 1000) (list :ok 76 7))
      ; The segment bound: one octet short.
      (equal (fn-sccr-admit-segment *sccrt-h* 0 75 1000) (list :refused :exceeds-bound))
      ; The file bound: the running total leaves one octet short.
      (equal (fn-sccr-admit-segment *sccrt-h* 925 76 1000) (list :refused :exceeds-bound))
      ; A header the codec does not parse.
      (equal (fn-sccr-admit-segment (cons 0 (cdr *sccrt-h*)) 0 76 1000) (list :refused :header))
      (equal (fn-sccr-admit-segment :not-a-list 0 76 1000) (list :refused :header))
      ; The file bound from the profile's fields: 3 H + one segment's framing.
      (equal (fn-sccr-file-read-bound 1000 64) (+ 3000 37 64 32))))

; -----------------------------------------------------------------------------
; Per hypothesis of the keystone fn-sccr-decode-of-plan.

; Without (fn-sccb-treep c): the plan is :unencodable, which the reader
; refuses as :layout, and the conclusion (:ok c) fails; the retained width
; hypotheses hold of the value.  The encoder's guard is the tree
; recognizer, so the witness is a ground theorem (evaluated in the logic),
; not an `assert-event'.
(defthm sccrt-w-decode-of-plan-without-treep
  (and (not (fn-sccb-treep (list 1/2)))
       (< (+ 1 (len (fn-scc-encode (list 1/2)))) *fn-scc-u64-bound*)
       (< (fn-scc-value-sequence (list 1/2)) *fn-scc-u64-bound*)
       (equal (mv-nth 0 (fn-sccb-plan (list 1/2) 7 nil)) :unencodable)
       (equal (fn-sccr-decode-plan (mv-nth 0 (fn-sccb-plan (list 1/2) 7 nil))
                                   (mv-nth 1 (fn-sccb-plan (list 1/2) 7 nil)))
              (list :refused :layout))
       (not (equal (fn-sccr-decode-plan (mv-nth 0 (fn-sccb-plan (list 1/2) 7 nil))
                                        (mv-nth 1 (fn-sccb-plan (list 1/2) 7 nil)))
                   (list :ok (list 1/2)))))
  :rule-classes nil)
(assert-event
 (let ((r (sccrt-round (list 1/2) 7)))
   (and (equal (nth 0 r) :unencodable)
        (equal (nth 1 r) (list :refused :layout)))))
(must-fail
 (defthm sccrt-r-decode-of-plan-without-treep
   (implies (and (< (+ 1 (len (fn-scc-encode c))) *fn-scc-u64-bound*)
                 (< (fn-scc-value-sequence c) *fn-scc-u64-bound*))
            (equal (fn-sccr-decode-plan (mv-nth 0 (fn-sccb-plan c seg fn-octets))
                                        (mv-nth 1 (fn-sccb-plan c seg fn-octets)))
                   (list :ok c)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; Without (< (fn-scc-value-sequence c) *fn-scc-u64-bound*): a value whose
; count slot is 2^64 encodes, its header's u64 sequence field wraps to 0,
; and the reader refuses the value; the retained hypotheses hold.
(defconst *sccrt-wide* (list "fn" *fn-scc-u64-bound* nil))
(assert-event
 (let ((r (sccrt-round *sccrt-wide* 7)))
   (and (fn-sccb-treep *sccrt-wide*)
        (< (+ 1 (len (fn-scc-encode *sccrt-wide*))) *fn-scc-u64-bound*)
        (not (< (fn-scc-value-sequence *sccrt-wide*) *fn-scc-u64-bound*))
        (equal (nth 1 r) (list :refused :value))
        (not (equal (nth 1 r) (list :ok *sccrt-wide*))))))
(must-fail
 (defthm sccrt-r-decode-of-plan-without-sequence-width
   (implies (and (fn-sccb-treep c)
                 (< (+ 1 (len (fn-scc-encode c))) *fn-scc-u64-bound*))
            (equal (fn-sccr-decode-plan (mv-nth 0 (fn-sccb-plan c seg fn-octets))
                                        (mv-nth 1 (fn-sccb-plan c seg fn-octets)))
                   (list :ok c)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; Without (< (+ 1 (len (fn-scc-encode c))) *fn-scc-u64-bound*): the
; header's u64 LENGTH field of a one-chunk file (segment size 0) would wrap
; for a program of 2^64 octets or more.  No such value can be built and
; evaluated (the program would be 2^64 octets), so there is no evaluated
; witness; the hypothesis is the codec's own (fn-scc-decode-segments-of-segments)
; and the `must-fail' below records the prover's refusal of the weakened
; statement, which is not a counterexample.
; teeth: prover-refusal the counter-witness is a program of 2^64 octets or more
(must-fail
 (defthm sccrt-r-decode-of-plan-without-length-width
   (implies (and (fn-sccb-treep c)
                 (< (fn-scc-value-sequence c) *fn-scc-u64-bound*))
            (equal (fn-sccr-decode-plan (mv-nth 0 (fn-sccb-plan c seg fn-octets))
                                        (mv-nth 1 (fn-sccb-plan c seg fn-octets)))
                   (list :ok c)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; Per hypothesis of the twin fn-sccr-decode-plan-is-decode-segments.

; Without the plan's shape (fn-sccr-planp): the last chunk's bytes copied
; to the end of the buffer and the last frame pointed at the copy.  The
; frames' octets are unchanged, so the list decoder accepts; the plan is
; not contiguous, so the reader refuses it as :layout.  The buffer is an
; octet buffer (the retained hypothesis).
(defun sccrt-move-last (c seg)
  (declare (xargs :guard (natp seg)))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (mv-let (plan fn-octets) (fn-sccb-plan c seg fn-octets)
        (let* ((last (if (and (true-listp plan) (consp plan)) (car (last plan)) nil))
               (a (fn-sccr-at 1 last)) (b (fn-sccr-at 2 last))
               (h (fn-sccr-at 0 last)) (tr (fn-sccr-at 3 last)))
          (if (and (true-listp plan) (consp plan)
                   (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
              (let* ((chunk (fn-sccb-slice-acc a b nil fn-octets))
                     (l (fn-octets-len fn-octets)))
                (if (fn-scc-octet-listp chunk)
                    (let* ((fn-octets (fn-sccb-append-list chunk fn-octets))
                           (moved (append (take (len (cdr plan)) plan)
                                          (list (list h l (+ l (- b a)) tr)))))
                      (mv (list (fn-sccr-planp moved (fn-sccr-at 1 (fn-sccr-at 0 moved))
                                               fn-octets)
                                (fn-sccr-decode-plan moved fn-octets)
                                (sccrt-listed moved fn-octets))
                          fn-octets))
                  (mv (list :bad :bad :bad) fn-octets)))
            (mv (list :bad :bad :bad) fn-octets))))
      result)))

(assert-event
 (let ((r (sccrt-move-last *sccrt-c* 7)))
   (and (equal (nth 0 r) nil)
        (equal (nth 1 r) (list :refused :layout))
        (equal (nth 2 r) (list :ok *sccrt-c*))
        (not (equal (nth 1 r) (nth 2 r))))))
(must-fail
 (defthm sccrt-r-twin-without-planp
   (implies (fn-octets-p fn-octets)
            (equal (fn-sccr-decode-plan plan fn-octets)
                   (fn-scc-decode-segments (fn-sccr-plan-segments plan fn-octets))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))

; A header one octet short is the other way the shape fails: the list
; decoder parses the concatenation (the chunk's first octet completes the
; header), the reader refuses the layout.
(assert-event
 (let ((r (sccrt-replan *sccrt-c* 7 :short-header)))
   (and (equal (nth 0 r) (list :refused :layout))
        (not (equal (nth 1 r) (list :refused :layout))))))

; Without (fn-octets-p fn-octets): the buffer's value is a stobj's, always
; an octet list; the hypothesis is the stobj recognizer and has no witness
; on the executable path.  In the logic a non-octet buffer value makes
; fn-sccr-cell's `nfix' and `nth' differ; the `must-fail' records the
; prover's refusal, which is not a counterexample.
; teeth: prover-refusal the stobj recogniser holds of every executable buffer; no evaluated non-octet buffer exists
(must-fail
 (defthm sccrt-r-twin-without-octets-p
   (implies (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
            (equal (fn-sccr-decode-plan plan fn-octets)
                   (fn-scc-decode-segments (fn-sccr-plan-segments plan fn-octets))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t))))
