; Q1's honest classification, step 2 (build/coordinator/fn2/lanes/a-dm4-q1-classification.md
; section 3): the independent contract per machine kind. Q1's case rows are a refinement of the
; scheduler over shared handlers; what a kind's handlers do is claimed here, by rows whose
; oracle does not call the handler. Each row is a defthm-owed with evaluating teeth.
(in-package "ACL2")
(include-book "conn-unit")
(include-book "../sim/check-wire")

; ------------------------------------------------------------------------
; fn2-conn: WIRE correctness. The served connection, alone, given any client
; octets in any chunks, answers a wire that WIRE's model oracle
; (sim/check-wire.lisp, written over octet lists without calling fn2-conn's
; handlers) accepts. WIRE is permissive by design: it checks the greeting,
; the admitted reply codes per command keyword, multi-line framing and the
; close, not exact reply text. T1 (safe execution) and T8 (fragmentation,
; privacy) are other claims.
(defthm-owed fn2-conn-wire-correct (octets sizes)
  (implies (and (fn2-gram-octetsp octets) (nat-listp sizes))
           (let ((r (fn2-conn-wire-solo octets sizes)))
             (fn2-wire-pass-p octets (car r) (cadr r))))
  :schema :invariant :claim :semantic
  :teeth (fn2-conn-wire-correct-positive fn2-conn-wire-correct-negative)
  :doc "WIRE correctness of the served connection: every client's octets, in any chunks, get a wire WIRE's independent model oracle accepts (greeting, admitted codes, framing, close; not exact text).")

(defun fn2-q1c-wire-ok (octets sizes)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-conn-wire-solo octets sizes)))
    (fn2-wire-pass-p octets (car r) (cadr r))))
(defun fn2-q1c-fixtures-ok (fixtures sizes)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) t
    (and (fn2-q1c-wire-ok (nth 1 (car fixtures)) sizes)
         (fn2-q1c-fixtures-ok (cdr fixtures) sizes))))
(defun fn2-q1c-random-ok (n seed)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (and (fn2-q1c-wire-ok (fn2-cu-random-transcript seed) (list (+ 1 (mod seed 13))))
         (fn2-q1c-random-ok (- n 1) (+ 7919 seed)))))
; Positive: every conn-unit fixture whole and in 3-octet chunks, and six
; seeded random transcripts, satisfy the antecedent and the conclusion.
(defun fn2-conn-wire-correct-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-q1c-fixtures-ok *fn2-cu-fixtures* nil)
       (fn2-q1c-fixtures-ok *fn2-cu-fixtures* '(3))
       (fn2-q1c-random-ok 6 101)))
; Negative: the conclusion refuses a wrong wire: the served wire of the
; pipelined fixture passes, and with its greeting code changed to 900 fails.
; (WIRE accepts that wire cut before its final 205 when the connection is
; closed: a close ends the expected replies early. That is WIRE's
; permissiveness, reported to D, not a property this row claims.)
(defun fn2-q1c-regreet (wire)
  (declare (xargs :verify-guards nil))
  (if (and (consp wire) (consp (cdr wire)) (consp (cddr wire))) (list* 57 48 48 (cdddr wire)) wire))
(defun fn2-conn-wire-correct-negative ()
  (declare (xargs :verify-guards nil))
  (let* ((octets (nth 1 (nth 1 *fn2-cu-fixtures*)))
         (r (fn2-conn-wire-solo octets nil)))
    (and (fn2-wire-pass-p octets (car r) (cadr r))
         (not (fn2-wire-pass-p octets (fn2-q1c-regreet (car r)) (cadr r))))))

; ------------------------------------------------------------------------
; fn2-echo: the served echo, alone, returns exactly the octets its client
; sent, in any chunks. The oracle is the client's own input: nothing on the
; checking side calls an echo handler. The runner is owed-conn's lossless
; adapter loop (fn2-cw-loop) on the tiny profile, whose listeners admit echo;
; the length bound keeps the run inside the loop's fuel.
(defconst *fn2-q1c-echo-profile*
  (put-assoc-equal :pool-classes '((8 . 1024) (4 . 256)) *fn2-profile-tiny*))
(defun fn2-echo-solo (input sizes)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (let ((fn2-core (fn2-init-executor *fn2-q1c-echo-profile* :echo nil fn2-core)))
        (mv-let (status clients fn2-core)
          (fn2-cw-loop 2600 0 0 (fn2-cw-clients (list (list input sizes))) fn2-core)
          (mv (list status (car (fn2-cw-results clients)) (fn2-core-stop-reason fn2-core)) fn2-core)))
      result)))
(defthm-owed fn2-echo-replies-its-input (input sizes)
  (implies (and (fn2-gram-octetsp input) (nat-listp sizes) (<= (len input) 512))
           (let ((r (fn2-echo-solo input sizes)))
             (and (equal (car r) :quiet) (equal (nth 2 r) 0)
                  (equal (car (nth 1 r)) input))))
  :schema :invariant :claim :semantic
  :teeth (fn2-echo-replies-positive fn2-echo-replies-without-octets)
  :doc "The served echo, alone, quiesces unstopped and returns exactly its client's octets, in any chunks (up to 512 octets, inside the runner's fuel); the oracle is the client's own input.")
(defun fn2-q1c-echo-ok (input sizes)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-echo-solo input sizes)))
    (and (equal (car r) :quiet) (equal (nth 2 r) 0) (equal (car (nth 1 r)) input))))
(defun fn2-q1c-echo-random-ok (n seed)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (and (fn2-q1c-echo-ok (fn2-cu-random-transcript seed) (list (+ 1 (mod seed 11)) (+ 2 (mod seed 5))))
         (fn2-q1c-echo-random-ok (- n 1) (+ 7919 seed)))))
; Positive: a line whole, the same line one octet at a time, and six seeded
; random transcripts in two-size chunks satisfy antecedent and conclusion.
(defun fn2-echo-replies-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-q1c-echo-ok '(72 69 76 76 79 13 10) nil)
       (fn2-q1c-echo-ok '(72 69 76 76 79 13 10) '(1 1 1 1 1 1 1))
       (fn2-q1c-echo-random-ok 6 101)))
; Negative: without the octet hypothesis the conclusion is false: a 300 sent
; by the client cannot come back as 300 (the pool holds bytes).
(defun fn2-echo-replies-without-octets ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-gram-octetsp '(72 300 10)))
       (not (fn2-q1c-echo-ok '(72 300 10) nil))))

(fn2-assert-owed-teeth fn2-conn-wire-correct fn2-echo-replies-its-input)
(value-triple (cw "Q1 CONTRACTS: fn2-conn-wire-correct and fn2-echo-replies-its-input teeth PASS~%"))
