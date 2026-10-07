; Witnesses and teeth for books/store-log-entry-bound.lisp (sweep 2026-10-03
; S048: the entry length the host reads is bounded before the read).
;
; The segment is tests/acl2/store-log-stream-tests's (three workload records
; chained from genesis, zero padded).  KEYSTONES fn-lgw-entry-len-bounded-step
; and fn-lgdm-entry-len-bounded-step:
;   (1) REACHABLE: the host's walk with the bounded length reads the same
;       records to the same state as with the unbounded one.
;   (2) POSITIVE, CORRUPTED SEGMENT (labelled): the first entry's u32 length
;       field set to 5000, within the extent and past the bound at MAX: the
;       unbounded length names a 5042-octet read, the bounded one NIL, and
;       the stream's and the probe's steps over those octets are their steps
;       over no entry; every hypothesis holds.
;   (3) HYPOTHESIS REMOVAL, one per hypothesis: each case checks the
;       retained hypotheses, the omitted one false, the conclusion false.
(in-package "ACL2")
(include-book "store-log-stream-tests")
(include-book "../../books/defkeystone")
(include-book "../../books/store-log-entry-bound")

(assert-event
 (and (eq (symbol-class 'fn-lgw-entry-len-bounded (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgdm-entry-len-bounded (w state)) :common-lisp-compliant)))

(defun sleb-extent () (declare (xargs :guard t)) 8192)

; The segment padded to SLEB-EXTENT, and the same with the first entry's
; declared payload length 5000 (big-endian u32 at octets 6..9).
(defun sleb-seg () (declare (xargs :guard t :verify-guards nil))
  (let ((l (slw-log3))) (append l (fn-bs-zeros (- (sleb-extent) (len l))))))
(defun sleb-long () (declare (xargs :guard t :verify-guards nil))
  (let ((c (sleb-seg)))
    (append (fn-bs-take 6 c) (list 0 0 19 136) (nthcdr 10 c))))

(defun sleb-walk (c st fuel acc bounded)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-lgw-stop st))
      (mv (reverse acc) st)
    (let* ((pos (fn-lgw-pos st))
           (h (fn-bs-take (fn-lgw-header-len st (len c)) (nthcdr pos c)))
           (n (if bounded
                  (fn-lgw-entry-len-bounded h st (len c) (slw-max))
                (fn-lgw-entry-len h st (len c))))
           (e (and n (fn-bs-take n (nthcdr pos c)))))
      (mv-let (took records st2) (fn-lgw-step e st (slw-unit) (slw-max) (len c))
        (sleb-walk c st2 (1- fuel) (if took (revappend records acc) acc) bounded)))))

; The stream's step as one value (its three results).
(defun sleb-step (e st c)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (took records st2) (fn-lgw-step e st (slw-unit) (slw-max) (len c))
    (list took records st2)))

; (1) REACHABLE.
(assert-event
 (let ((st0 (fn-lgw-start *fn-lg-genesis* 1)))
   (mv-let (r1 s1) (sleb-walk (sleb-seg) st0 100 nil t)
     (mv-let (r2 s2) (sleb-walk (sleb-seg) st0 100 nil nil)
       (and (equal r1 (list (slw-rec 1) (slw-rec 2) (slw-rec 3)))
            (equal r1 r2) (equal s1 s2)
            (fn-lgw-entry-len-bounded (fn-bs-take 10 (sleb-seg)) st0 (sleb-extent) (slw-max)))))))

; (2) POSITIVE (corrupted segment).
(assert-event
 (let* ((c (sleb-long)) (st0 (fn-lgw-start *fn-lg-genesis* 1))
        (h (fn-bs-take 10 c))
        (n (fn-lgw-entry-len h st0 (len c)))
        (e (fn-bs-take n c))
        (ps (fn-lgdm-start st0)))
   (and (equal n 5042)
        (equal (fn-lgdm-entry-len h ps (len c)) 5042)
        (not (fn-lgw-entry-len-bounded h st0 (len c) (slw-max)))
        (not (fn-lgdm-entry-len-bounded h ps (len c) (slw-max)))
        (equal (len e) n) (consp h) (equal (nth 5 e) (nth 5 h))
        (equal (sleb-step e st0 c) (sleb-step nil st0 c))
        (equal (fn-lgdm-step h e ps (slw-unit) (slw-max))
               (fn-lgdm-step h nil ps (slw-unit) (slw-max))))))

; (3) Without "the bounded length is NIL": the real first entry, which the
; bounded length names; the step over it takes a record, over nothing not.
(assert-event
 (let* ((c (sleb-seg)) (st0 (fn-lgw-start *fn-lg-genesis* 1))
        (h (fn-bs-take 10 c))
        (n (fn-lgw-entry-len h st0 (len c)))
        (e (fn-bs-take n c)))
   (and (equal (len e) n) (consp h) (equal (nth 5 e) (nth 5 h))
        (fn-lgw-entry-len-bounded h st0 (len c) (slw-max))
        (not (equal (sleb-step e st0 c) (sleb-step nil st0 c))))))

; (3) Without "E is the octets the length named": the real first entry
; against a segment too short to hold it (no length named).
(assert-event
 (let* ((c (sleb-seg)) (st0 (fn-lgw-start *fn-lg-genesis* 1))
        (h (fn-bs-take 10 c))
        (e (fn-bs-take (fn-lgw-entry-len h st0 (len c)) c))
        (short 20))
   (and (not (fn-lgw-entry-len-bounded h st0 short (slw-max)))
        (consp h) (equal (nth 5 e) (nth 5 h))
        (not (equal (len e) (fn-lgw-entry-len h st0 short)))
        (not (equal (sleb-step e st0 c) (sleb-step nil st0 c))))))

; TEETH-62 BEGIN
; The two entry-len-bounded-is-entry-len keystones with their teeth (TEETH CONTRACT v1).  fn-lgw-entry-len-bounded-step and fn-lgdm-entry-len-bounded-step state `(equal (fn-lgw-step ...) (fn-lgw-step ...))` over multiple values and stay owed with the TEETH-OWED-MV-CLAIM class.
(defteeth fn-lgw-entry-len-bounded-is-entry-len
  :claim (((within-bound (fn-lgw-entry-len-bounded h st extent max)))
          (equal (fn-lgw-entry-len-bounded h st extent max)
                  (fn-lgw-entry-len h st extent)))
  :subject fn-lgw-entry-len-bounded
  :witness ((h (fn-bs-take 10 (sleb-seg))) (st (fn-lgw-start *fn-lg-genesis* 1)) (extent (sleb-extent)) (max (slw-max)))
  :breaks ((within-bound ((h (fn-bs-take 10 (sleb-long))) (st (fn-lgw-start *fn-lg-genesis* 1)) (extent (sleb-extent)) (max (slw-max)))))
  :mutations ((refuses-in-bound
               (:conclusion (equal (fn-lgw-entry-len-bounded h st extent max) nil))
               ((h (fn-bs-take 10 (sleb-seg))) (st (fn-lgw-start *fn-lg-genesis* 1)) (extent (sleb-extent)) (max (slw-max)))
               :fault "the bounded length refusing a record that is within the bound")))

(defteeth fn-lgdm-entry-len-bounded-is-entry-len
  :claim (((within-bound (fn-lgdm-entry-len-bounded h ps extent max)))
          (equal (fn-lgdm-entry-len-bounded h ps extent max)
                  (fn-lgdm-entry-len h ps extent)))
  :subject fn-lgdm-entry-len-bounded
  :witness ((h (fn-bs-take 10 (sleb-seg))) (ps (fn-lgdm-start (fn-lgw-start *fn-lg-genesis* 1))) (extent (sleb-extent)) (max (slw-max)))
  :breaks ((within-bound ((h (fn-bs-take 10 (sleb-long))) (ps (fn-lgdm-start (fn-lgw-start *fn-lg-genesis* 1))) (extent (sleb-extent)) (max (slw-max)))))
  :mutations ((refuses-in-bound
               (:conclusion (equal (fn-lgdm-entry-len-bounded h ps extent max) nil))
               ((h (fn-bs-take 10 (sleb-seg))) (ps (fn-lgdm-start (fn-lgw-start *fn-lg-genesis* 1))) (extent (sleb-extent)) (max (slw-max)))
               :fault "the bounded probe length refusing a record that is within the bound")))

; ---------------------------------------------------------------------------
; The two *-entry-len-bounded-step keystones with their teeth (TEETH CONTRACT
; v1).  The kind-octet hypothesis (nth 5 e) = (nth 5 h) has no counterexample
; (the step over an oversized entry equals the step over none whatever its
; kind octet; checked for 0..255 at the long segment), so each claim keeps the
; whole implication as its conclusion.
;
; fn-lgdm-entry-len-bounded-step: executable witnesses.  Besides the
; conclusion mutation, the oversized and length hypotheses are removed as
; conclusion mutations that drop them, at a segment where the dropped one
; fails and the probe step over E differs from the step over none.
;
; fn-lgw-entry-len-bounded-step: fn-lgw-step returns three values, so its
; witnesses are ground theorems (:witness-lemma / :lemma; TEETH-OWED-MV-CLAIM
; lemma debt).  Only the oversized witness can be a ground theorem: the step
; over a real entry calls fn-record-decode-exact, whose attachment proofs
; ignore, so the dropped-hypothesis mutations (which need the step over a real
; entry to differ) stay owed.
(defconst *sleb-c* (sleb-long))
(defconst *sleb-c-ok* (sleb-seg))
(defconst *sleb-st* (fn-lgw-start *fn-lg-genesis* 1))
(defconst *sleb-ps* (fn-lgdm-start (fn-lgw-start *fn-lg-genesis* 1)))
(defconst *sleb-h* (fn-bs-take 10 *sleb-c*))
(defconst *sleb-h-ok* (fn-bs-take 10 *sleb-c-ok*))
(defconst *sleb-e* (fn-bs-take 5042 *sleb-c*))
(defconst *sleb-e-ok* (fn-bs-take (fn-lgw-entry-len *sleb-h-ok* *sleb-st* 8192) *sleb-c-ok*))
(defconst *sleb-max* (slw-max))
(defconst *sleb-unit* (slw-unit))

(defthm sleb-lgw-step-witness
  (implies (and (not (fn-lgw-entry-len-bounded *sleb-h* *sleb-st* 8192 *sleb-max*)) (equal (len *sleb-e*) (fn-lgw-entry-len *sleb-h* *sleb-st* 8192)) (equal (nth 5 *sleb-e*) (nth 5 *sleb-h*))) (equal (fn-lgw-step *sleb-e* *sleb-st* *sleb-unit* *sleb-max* 8192) (fn-lgw-step nil *sleb-st* *sleb-unit* *sleb-max* 8192))))
(defthm sleb-lgw-step-mutant-conclusion
  (and (implies (and (not (fn-lgw-entry-len-bounded *sleb-h* *sleb-st* 8192 *sleb-max*)) (equal (len *sleb-e*) (fn-lgw-entry-len *sleb-h* *sleb-st* 8192)) (equal (nth 5 *sleb-e*) (nth 5 *sleb-h*))) (equal (fn-lgw-step *sleb-e* *sleb-st* *sleb-unit* *sleb-max* 8192) (fn-lgw-step nil *sleb-st* *sleb-unit* *sleb-max* 8192))) (not (implies (and (not (fn-lgw-entry-len-bounded *sleb-h* *sleb-st* 8192 *sleb-max*)) (equal (len *sleb-e*) (fn-lgw-entry-len *sleb-h* *sleb-st* 8192)) (equal (nth 5 *sleb-e*) (nth 5 *sleb-h*))) (not (equal (fn-lgw-step *sleb-e* *sleb-st* *sleb-unit* *sleb-max* 8192) (fn-lgw-step nil *sleb-st* *sleb-unit* *sleb-max* 8192)))))))
(defteeth fn-lgw-entry-len-bounded-step
  :claim (() (implies (and (not (fn-lgw-entry-len-bounded h st extent max)) (equal (len e) (fn-lgw-entry-len h st extent)) (equal (nth 5 e) (nth 5 h))) (equal (fn-lgw-step e st unit max extent) (fn-lgw-step nil st unit max extent))))
  :subject fn-lgw-step
  :witness-lemma sleb-lgw-step-witness
  :witness ((h *sleb-h*) (st *sleb-st*) (extent 8192) (max *sleb-max*) (e *sleb-e*) (unit *sleb-unit*))
  :mutations ((step-told-apart
               (:conclusion (implies (and (not (fn-lgw-entry-len-bounded h st extent max)) (equal (len e) (fn-lgw-entry-len h st extent)) (equal (nth 5 e) (nth 5 h))) (not (equal (fn-lgw-step e st unit max extent) (fn-lgw-step nil st unit max extent)))))
               ((h *sleb-h*) (st *sleb-st*) (extent 8192) (max *sleb-max*) (e *sleb-e*) (unit *sleb-unit*))
               :fault "a step that tells an oversized entry from no entry"
               :lemma sleb-lgw-step-mutant-conclusion)))
