; Witnesses and teeth for books/owner-scheduler.lisp (PRF-248; lane
; owner-scheduler, 2026-09-26).
;
; The keystone `fn-osch-control-waits-at-most-the-bound' has one hypothesis
; (control has a waiter at every pick) and concludes that at most three
; quanta of other classes run first.  Here: reachable witnesses from every
; cursor (the worst case, cursor 1 with every class waiting, spends exactly
; three quanta); the must-fail for the hypothesis (control absent at the
; first four picks and present at the fifth: the delay is four); the pick's
; own facts (a waiter is picked, nil exactly when idle, the wrap); the fold
; (one hold to one class and one bucket; the row stays consistent); and the
; health lines as text.
(in-package "ACL2")
(include-book "../../books/owner-scheduler")
(include-book "must-fail-checked")

; Every class waiting, at four successive picks.
(defconst *osch-all* '((2 3 1 1) (2 3 1 1) (2 3 1 1) (2 3 1 1) (2 3 1 1)))
; Readers only, then control arrives at the fifth pick.
(defconst *osch-late* '((0 3 0 0) (0 3 0 0) (0 3 0 0) (0 3 0 0) (1 3 0 0)))

; -----------------------------------------------------------------------------
; KEYSTONE: reachable witnesses.  From cursor 1 the picks are reader, poster,
; transit, control: three quanta, the bound itself.
(assert-event (fn-osch-control-waitsp *osch-all*))
(assert-event (equal (fn-osch-control-delay 1 *osch-all*) 3))
(assert-event (equal (fn-osch-control-delay 2 *osch-all*) 2))
(assert-event (equal (fn-osch-control-delay 3 *osch-all*) 1))
(assert-event (equal (fn-osch-control-delay 0 *osch-all*) 0))
; A saturating reader storm with nobody else: from cursor 1 one reader
; quantum, then control (the empty poster and transit slots cost nothing).
(assert-event (equal (fn-osch-control-delay 1 '((1 40 0 0) (1 40 0 0) (1 40 0 0))) 1))

; MUST-FAIL for the hypothesis: control absent at the first four picks, the
; delay is four.  The hypothesis fails and so does the conclusion.
(assert-event (not (fn-osch-control-waitsp *osch-late*)))
(assert-event (equal (fn-osch-control-delay 1 *osch-late*) 4))
(must-fail-checked
 (assert-event (<= (fn-osch-control-delay 1 *osch-late*) *fn-osch-bound*)))

; -----------------------------------------------------------------------------
; The pick: a waiter, nil exactly when idle, the wrap past the last slot.
(assert-event (equal (fn-osch-pick 0 '(0 0 0 0)) nil))
(assert-event (fn-osch-idlep '(0 0 0 0)))
(assert-event (equal (fn-osch-pick 3 '(0 1 0 0)) 1))       ; wraps 3, 0, 1
(assert-event (equal (fn-osch-pick 2 '(1 1 1 1)) 2))
(assert-event (equal (fn-osch-pick 17 '(0 0 0 1)) 3))      ; a cursor out of range reads as 0
(must-fail-checked (assert-event (equal (fn-osch-pick 3 '(0 1 0 0)) 3)))

; fn-osch-next: the class and the cursor after it; the rows are kept.
(assert-event
 (mv-let (class s2) (fn-osch-next (fn-osch-init) '(0 2 0 0))
   (and (eq class :reader)
        (equal (fn-osch-cursor s2) 2)
        (equal (fn-osch-rows s2) (fn-osch-rows (fn-osch-init))))))
(assert-event
 (mv-let (class s2) (fn-osch-next (list 3 (fn-osch-rows (fn-osch-init))) '(1 1 1 1))
   (and (eq class :transit) (equal (fn-osch-cursor s2) 0))))
(assert-event
 (mv-let (class s2) (fn-osch-next (fn-osch-init) '(0 0 0 0))
   (and (null class) (equal s2 (fn-osch-init)))))

; -----------------------------------------------------------------------------
; The fold: one observation, one class, one bucket; the row stays consistent
; (fn-osch-row-observe-keeps-okp: the input row is consistent, asserted, and
; so is the output).
(assert-event (fn-osch-row-okp (fn-osch-row 1 (fn-osch-init))))
(defconst *osch-s1* (fn-osch-observe (fn-osch-init) :reader 5 1200))
(assert-event (equal (fn-osch-holds 1 *osch-s1*) 1))
(assert-event (equal (fn-osch-holds 0 *osch-s1*) 0))
(assert-event (equal (fn-osch-row 1 *osch-s1*) '(1 0 1 0 0 0 5 1200 1)))
(assert-event (fn-osch-row-okp (fn-osch-row 1 *osch-s1*)))
(defconst *osch-s2* (fn-osch-observe *osch-s1* :reader 2500 0))
(assert-event (equal (fn-osch-row 1 *osch-s2*) '(2 0 1 0 0 1 2500 1200 1)))
(assert-event (fn-osch-row-okp (fn-osch-row 1 *osch-s2*)))
(assert-event (equal (fn-osch-cursor *osch-s2*) 0))
; MUTATION (labelled): bumping the count without a bucket breaks the invariant.
(must-fail-checked
 (assert-event (fn-osch-row-okp (fn-osch-bump 0 (fn-osch-row 1 *osch-s2*)))))
; MUST-FAIL for fn-osch-row-observe-keeps-okp's hypothesis: a row that is
; not consistent, observed, is not consistent after either.
(defconst *osch-bad-row* (fn-osch-bump 0 (fn-osch-row 1 *osch-s2*)))
(assert-event (not (fn-osch-row-okp *osch-bad-row*)))
(must-fail-checked (assert-event (fn-osch-row-okp (fn-osch-row-observe *osch-bad-row* 5 0))))

; -----------------------------------------------------------------------------
; The health lines, as text.
(defun osch-chars (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (cons (if (and (natp (car octets)) (< (car octets) 256)) (code-char (car octets)) #\?)
            (osch-chars (cdr octets)))
    nil))

(defun osch-text (octets)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (osch-chars octets) 'string))

(assert-event
 (equal (osch-text (fn-osch-health-lines *osch-s2*))
        (concatenate
         'string
         "sched order=control,reader,poster,transit bound=3 cursor=0" (coerce (list (code-char 10)) (quote string))
         "sched control holds=0 hold<1ms=0 hold<10ms=0 hold<100ms=0 hold<1s=0 hold>=1s=0 hold-max-ms=0 wait-max-ms=0 waits>=1s=0" (coerce (list (code-char 10)) (quote string))
         "sched reader holds=2 hold<1ms=0 hold<10ms=1 hold<100ms=0 hold<1s=0 hold>=1s=1 hold-max-ms=2500 wait-max-ms=1200 waits>=1s=1" (coerce (list (code-char 10)) (quote string))
         "sched poster holds=0 hold<1ms=0 hold<10ms=0 hold<100ms=0 hold<1s=0 hold>=1s=0 hold-max-ms=0 wait-max-ms=0 waits>=1s=0" (coerce (list (code-char 10)) (quote string))
         "sched transit holds=0 hold<1ms=0 hold<10ms=0 hold<100ms=0 hold<1s=0 hold>=1s=0 hold-max-ms=0 wait-max-ms=0 waits>=1s=0" (coerce (list (code-char 10)) (quote string)))))
