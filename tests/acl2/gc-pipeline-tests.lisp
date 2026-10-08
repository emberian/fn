; PHASE 1c ground tests. Do not load statements.lisp: no keystone is assumed.
; Start on contracts' cached dependency world, send its definitions, load the
; existing must-fail-checked book, then send this file FROM *gc-init*.
(in-package "ACL2")
(include-book "../../books/owner-commit-durability-concrete")
(include-book "must-fail-checked")
(defconst *gc-init* (fn-ocp-gc-init 512 65536 2 4096))
(defconst *gc-warm-events*
  '((:start) (:reserve :current 1) (:take :current (65) 1) (:member :current (:accepted t)) (:seal :current)
    (:io :current :ok) (:io :current :ok) (:io :current :ok)
    (:io :current :ok) (:io :current :ok) (:collect) (:advance)))
(defconst *gc-warm* (fn-ocp-gc-run *gc-init* *gc-warm-events*))
(defconst *gc-a-events*
  '((:start) (:reserve :current 2) (:take :current (66) 2) (:member :current (:accepted t)) (:seal :current)
    (:io :current :ok) (:io :current :ok) (:io :current :ok)))
(defconst *gc-a* (fn-ocp-gc-run *gc-warm* *gc-a-events*))
(defconst *gc-next-events*
  '((:next) (:reserve :next 3) (:take :next (67) 3) (:member :next (:accepted nil)) (:seal :next) (:io :next :ok) (:io :next :ok)))
(defconst *gc-preappend* (fn-ocp-gc-run *gc-a* *gc-next-events*))
(defconst *gc-issued* (fn-ocp-gc-entry-append-issue *gc-preappend*))
(defconst *gc-pipelined* (fn-ocp-gc-host-step *gc-issued* '(:io :next :ok)))
(defconst *gc-fenced* (fn-ocp-gc-host-step *gc-pipelined* '(:io :current :ok)))
(defconst *gc-resolved* (fn-ocp-gc-host-step *gc-fenced* '(:io :current :ok)))
(defconst *gc-collected* (fn-ocp-gc-entry-complete *gc-resolved*))
(defconst *gc-promoted* (fn-ocp-gc-entry-reader-advance *gc-collected*))
(defconst *gc-tail-events* '((:io :current :ok) (:io :current :ok) (:collect) (:advance)))
(defconst *gc-completed* (fn-ocp-gc-run *gc-promoted* *gc-tail-events*))

; W1: initial keystone's WHOLE antecedent and conclusion.
(defconst *gc-w1*
  (and (fn-ocp-gc-profilep 512 65536 2 4096) (fn-ocp-gc-linkedp *gc-init*)))
(assert-event *gc-w1*)

; Preservation regression: the original draft admitted this idle state but
; START kept both empty captures, leaving the second capture stale. Clear
; idle captures in the step, without narrowing the invariant's hypothesis.
(defconst *gc-idle-captures*
  (update-nth 2 (fn-ocvm-make 0 0 0 0 '(0 0)) *gc-init*))
(assert-event
 (and (fn-ocp-gc-linkedp *gc-idle-captures*)
      (fn-ocp-gc-linkedp
       (fn-ocp-gc-entry-start *gc-idle-captures*))))

; W2: accepted append-behind, not a vacuous refusal; real encoded write plan.
(defconst *gc-w2*
  (let* ((p (nth 0 *gc-preappend*)) (q (nth 0 *gc-pipelined*))
         (h (nth 3 *gc-pipelined*)) (ks (fn-lgk-pipe-ks p)))
    (and (fn-lgk-pipe-okp p h) (fn-lgk-behind-admitsp p 512 65536)
         (mv-let (word after effect) (fn-lgk-append-behind p 512 65536)
           (declare (ignore after effect)) (equal word :appended))
         (fn-lgk-pipe-behind q) (consp (fn-lgk-inflight ks)) (consp (fn-lgk-batch ks))
         (equal (fn-lgk-append ks 512 65536) ks)
         (fn-lgk-pipe-okp q h) (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
         (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q))
         (equal (car (nth 14 *gc-issued*)) :write)
         (equal (nth 1 (nth 14 *gc-issued*)) 1024)
         (equal (len (nth 2 (nth 14 *gc-issued*))) 512))))
(assert-event *gc-w2*)

; W3: each reached transition asserts the full preservation antecedent and
; conclusion, plus emitted cuts and monotonicity. No theorem is used to skip
; evaluation. Includes normal ACKs, view advance, invalid early collection,
; reader and gate steps, and promotion of the already appended second batch.
(defun fn-gc-walk-okp (x events)
  (declare (xargs :measure (len events)
    :hints (("Goal" :in-theory (e/d (len) (fn-ocp-gc-host-step fn-ocp-gc-linkedp
                                      fn-ocp-gc-reveals-okp fn-lgk-pipe-d fn-lgk-pipe-acked))))))
  (if (atom events) (fn-ocp-gc-linkedp x)
    (let ((y (fn-ocp-gc-host-step x (car events))))
      (and (fn-ocp-gc-linkedp x) (fn-ocp-gc-linkedp y)
           (fn-ocp-gc-reveals-okp y)
           (<= (fn-lgk-pipe-d (nth 0 x)) (fn-lgk-pipe-d (nth 0 y)))
           (<= (fn-lgk-pipe-acked (nth 0 y)) (fn-lgk-pipe-d (nth 0 y)))
           (fn-gc-walk-okp y (cdr events))))))
(defconst *gc-success-events*
  (append *gc-warm-events* *gc-a-events* *gc-next-events*
    '((:append-issue) (:io :next :ok) (:reader) (:collect) (:advance) (:pick (0 1 0 0 0 0))
      (:io :current :ok) (:io :current :ok) (:collect) (:advance)) *gc-tail-events*))
(defconst *gc-w3*
  (and (fn-gc-walk-okp *gc-init* *gc-success-events*)
       (equal (fn-lgk-pipe-acked (nth 0 *gc-completed*)) 3)
       (equal (fn-ocvm-c (nth 2 *gc-completed*)) 3)))
(assert-event *gc-w3*)

; W4: pipelined reader reveal is the old durable prefix, with both batches
; nonempty and B physically represented by an append receipt/write plan.
(defconst *gc-w4*
  (let ((r (fn-ocp-gc-host-step *gc-pipelined* '(:reader))))
    (and (fn-ocp-gc-linkedp *gc-pipelined*)
         (fn-ocp-gc-linkedp r) (fn-ocp-gc-reveals-okp r)
         (equal (nth 8 r) '(1)) (equal (fn-lgk-pipe-d (nth 0 r)) 1))))
(assert-event *gc-w4*)

; W5: fence moves only A to durable; feed resolution observes through A.
(defconst *gc-w5*
  (let ((p (nth 0 *gc-pipelined*)) (q (nth 0 *gc-fenced*)))
    (and (fn-lgk-pipe-okp p (nth 3 *gc-pipelined*))
         (fn-lgk-pipe-okp q (nth 3 *gc-fenced*))
         (<= (fn-lgk-pipe-d p) (fn-lgk-pipe-d q))
         (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q))
         (equal (fn-lgk-pipe-d q) 2) (fn-lgk-pipe-behind q)
         (equal (fn-lgk-batch (fn-lgk-pipe-ks q)) '((67)))
         (fn-ocp-gc-linkedp *gc-fenced*) (fn-ocp-gc-linkedp *gc-resolved*)
         (fn-ocp-gc-reveals-okp *gc-resolved*) (equal (nth 8 *gc-resolved*) '(2)))))
(assert-event *gc-w5*)

; W6: collect releases A only, ACK stops at 2; B is promoted without rewrite.
; Check the named ACK refinement and the exact planned offset/octet equation.
(defconst *gc-w6*
  (let* ((p (nth 0 *gc-preappend*)) (f (fn-lgk-pipe-ks (nth 0 *gc-fenced*))))
    (and (fn-ocp-gc-linkedp *gc-resolved*) (fn-ocp-gc-linkedp *gc-promoted*)
         (fn-ocp-gc-reveals-okp *gc-promoted*)
         (fn-ocp-gc-linkedp *gc-collected*)
         (equal (nth 9 *gc-collected*) '(:rendered))
         (equal (nth 9 *gc-promoted*) nil)
         (equal (fn-lgk-pipe-acked (nth 0 *gc-promoted*)) 2)
         (equal (fn-lgk-inflight (fn-lgk-pipe-ks (nth 0 *gc-promoted*))) '((67)))
         (equal (nth 4 *gc-promoted*) :fence)
         (equal (fn-lgk-behind-effect p 512 65536)
                (list :write (fn-lgk-frontier f) (fn-lgk-append-octets f 512)))
         (equal (fn-lgc-of (fn-lgk-pipe-ks (fn-lgk-pipe-ack (nth 0 *gc-fenced*) 1)))
                (fn-lgu-acknowledge (fn-lgc-of f) 1)))))
(assert-event *gc-w6*)

; W7: failed barrier, both batches nonempty, both members uncertain. A late
; success, collect, new start and read cannot acknowledge or resurrect them.
(defconst *gc-late-events*
  '((:io :current :ok) (:collect) (:advance) (:start) (:reserve :current 4) (:take :current (68) 4) (:member :current (:accepted t)) (:seal :current) (:reader)))
(defconst *gc-w7*
  (let ((y (fn-ocp-gc-host-step *gc-pipelined* '(:io :current :uncertain))))
    (and (fn-ocp-gc-failure-hyp *gc-pipelined*)
         (consp (fn-lgk-inflight (fn-lgk-pipe-ks (nth 0 *gc-pipelined*))))
         (consp (fn-lgk-batch (fn-lgk-pipe-ks (nth 0 *gc-pipelined*))))
         (fn-ocp-gc-failure-okp *gc-pipelined* *gc-late-events*)
         (equal (nth 9 y) '(:uncertain-reply :close))
         (fn-gc-walk-okp *gc-pipelined* (cons '(:io :current :uncertain) *gc-late-events*)))))
(assert-event *gc-w7*)

; W8: membership keystone's whole hypothesis/conclusion on the new kernel,
; taking B behind A. Once B is appended, any further take must yield :full.
(defconst *gc-w8*
  (let ((p (nth 0 *gc-a*)) (h (nth 3 *gc-a*)))
    (and (fn-olr-gc-membership-hyp h p '(67) 3 0 0 2 4096 512)
         (fn-olr-gc-membership-okp h p '(67) 3 0 0 2 4096 512)
         (equal (car (fn-lgk-pipe-take (nth 0 *gc-pipelined*) '(68) 4 1 5 2 4096 512)) :full))))
(assert-event *gc-w8*)

; T1: explicit reply-at-append mutant. Current COLLECT correctly emits none.
(defconst *gc-bad-reply*
  (update-nth 8 '(2) (update-nth 9 '(:rendered) *gc-pipelined*)))
(assert-event
 (and (fn-ocp-gc-linkedp *gc-pipelined*)
      (equal (nth 9 (fn-ocp-gc-host-step *gc-pipelined* '(:collect))) nil)
      (not (fn-ocp-gc-reveals-okp *gc-bad-reply*))))
(must-fail-checked (assert-event (fn-ocp-gc-reveals-okp *gc-bad-reply*)))

; T2: view advanced at append, instead of after fence/ACK/COMPLETE.
(defconst *gc-bad-view*
  (update-nth 2 (fn-ocvm-step (nth 2 *gc-pipelined*) '(:complete)) *gc-pipelined*))
(defconst *gc-bad-read* (fn-ocp-gc-host-step *gc-bad-view* '(:reader)))
(assert-event
 (and (not (fn-ocp-gc-linkedp *gc-bad-view*))
      (> (car (nth 8 *gc-bad-read*)) (fn-lgk-pipe-d (nth 0 *gc-bad-read*)))
      (not (fn-ocp-gc-reveals-okp *gc-bad-read*))))
(must-fail-checked (assert-event (fn-ocp-gc-reveals-okp *gc-bad-read*)))

; T3: remove ONLY the :fence phase premise. This reached :done state retains
; both member lists and linkedp, but an out-of-phase failure receipt stutters.
(assert-event
 (and (fn-ocp-gc-linkedp *gc-resolved*) (consp (nth 6 *gc-resolved*))
      (consp (nth 7 *gc-resolved*)) (not (equal (nth 4 *gc-resolved*) :fence))
      (not (fn-ocp-gc-failure-hyp *gc-resolved*))
      (not (fn-ocp-gc-failure-okp *gc-resolved* nil))))
(must-fail-checked (assert-event (fn-ocp-gc-failure-okp *gc-resolved* nil)))

; T4: remove the new profile preflight by using the existing raw TAKE.
; Its packed bytes (5) fit OMAX=5, but encoded/padded log bytes (512) do not.
(defconst *gc-raw-oversize*
  (fn-olr-take (fn-lgk-pipe-ks (nth 0 *gc-a*)) '(67) 3 0 0 2 5 512))
(assert-event
 (and (equal (car *gc-raw-oversize*) :taken)
      (not (fn-olr-gc-profile-fitp (fn-lgk-pipe-ks (nth 0 *gc-a*)) '(67) 2 5 512))
      (equal (car (fn-lgk-pipe-take (nth 0 *gc-a*) '(67) 3 0 0 2 5 512)) :full)
      (equal (fn-lgc-append-len (fn-lgc-of (cadr *gc-raw-oversize*)) 512) 512)))
(must-fail-checked
 (assert-event (<= (fn-lgc-append-len (fn-lgc-of (cadr *gc-raw-oversize*)) 512) 5)))

; T5: remove count correspondence; the raw decision can overfill BMAX=1.
; The other membership assumptions and preflight remain true.
(defconst *gc-stale-take*
  (fn-lgk-pipe-take (nth 0 *gc-preappend*) '(68) 4 0 5 1 4096 512))
(assert-event
 (and (fn-lgk-pipe-okp (nth 0 *gc-preappend*) (nth 3 *gc-preappend*))
      (equal (car *gc-stale-take*) :taken)
      (not (fn-olr-gc-membership-hyp (nth 3 *gc-preappend*) (nth 0 *gc-preappend*) '(68) 4 0 5 1 4096 512))
      (not (fn-olr-gc-membership-okp (nth 3 *gc-preappend*) (nth 0 *gc-preappend*) '(68) 4 0 5 1 4096 512))))
(must-fail-checked
 (assert-event (fn-olr-gc-membership-okp (nth 3 *gc-preappend*) (nth 0 *gc-preappend*) '(68) 4 0 5 1 4096 512)))

; T6: failing the first barrier must not let the next member's acceptance out.
(assert-event
 (not (subsetp-equal (fn-ocs-member-releases :complete (nth 7 *gc-pipelined*))
                    '(:own-uncertain :uncertain-reply :close))))
(must-fail-checked
 (assert-event (subsetp-equal (fn-ocs-member-releases :complete (nth 7 *gc-pipelined*))
                             '(:own-uncertain :uncertain-reply :close))))
; T7: an ACK-at-append mutant violates the initial ACK prefix premise.
(defconst *gc-early-ack*
  (let* ((p (nth 0 *gc-pipelined*)) (ks (fn-lgk-pipe-ks p)))
    (update-nth 0 (fn-lgk-pipe-make (update-nth 7 3 ks) t) *gc-pipelined*)))
(assert-event
 (and (not (fn-ocp-gc-linkedp *gc-early-ack*))
      (not (fn-ocp-gc-failure-okp *gc-early-ack* *gc-late-events*))))
(must-fail-checked (assert-event (fn-ocp-gc-failure-okp *gc-early-ack* *gc-late-events*)))
; T8: original singleton loophole even when packed bytes exceed OMAX=1.
(defconst *gc-singleton-overflow*
  (fn-olr-take (fn-lgk-pipe-ks (nth 0 *gc-a*)) '(67) 3 0 0 2 1 512))
(assert-event
 (and (equal (car *gc-singleton-overflow*) :taken)
      (equal (car (fn-lgk-pipe-take (nth 0 *gc-a*) '(67) 3 0 0 2 1 512)) :full)
      (> (fn-lg-pack-len (fn-lgk-batch (cadr *gc-singleton-overflow*))) 1)))
(must-fail-checked
 (assert-event (<= (fn-lg-pack-len (fn-lgk-batch (cadr *gc-singleton-overflow*))) 1)))

; W9: branch control, not a universal proof. From every prefix of the success
; trace, try every event kind and OK/uncertain/fault, including invalid orders.
(defun fn-gc-events-okp (x events)
  (declare (xargs :measure (len events)
    :hints (("Goal" :in-theory (e/d (len) (fn-ocp-gc-host-step fn-ocp-gc-linkedp
                                      fn-ocp-gc-reveals-okp fn-lgk-pipe-d fn-lgk-pipe-acked))))))
  (if (atom events) t
    (let ((y (fn-ocp-gc-host-step x (car events))))
      (and (fn-ocp-gc-linkedp x) (fn-ocp-gc-linkedp y) (fn-ocp-gc-reveals-okp y)
           (equal (fn-ocp-gc-project y)
                  (fn-ocp-gc-host-step (fn-ocp-gc-project x) (car events)))
           (<= (fn-lgk-pipe-d (nth 0 x)) (fn-lgk-pipe-d (nth 0 y)))
           (fn-gc-events-okp x (cdr events))))))
(defun fn-gc-matrix-okp (x trace events)
  (declare (xargs :measure (len trace)
    :hints (("Goal" :in-theory (e/d (len) (fn-gc-events-okp fn-ocp-gc-host-step))))))
  (and (fn-gc-events-okp x events)
       (if (atom trace) t
         (fn-gc-matrix-okp (fn-ocp-gc-host-step x (car trace)) (cdr trace) events))))
(defconst *gc-probe-events*
  '((:start) (:reserve :current 4) (:take :current (68) 4) (:member :current (:accepted t)) (:seal :current) (:next) (:reserve :next 5) (:take :next (69) 5) (:member :next (:accepted t)) (:seal :next)
    (:io :current :ok) (:io :current :uncertain) (:io :current :fault)
    (:io :next :ok) (:io :next :uncertain) (:io :next :fault)
    (:append-issue) (:collect) (:advance) (:reader) (:pick (1 1 1 1 1 1)) (:unknown)
    (:start) (:reserve :current 4) (:take :current (68) 4) (:reserve :current 5) (:take :current (69) 5) (:reserve :current 6) (:take :current (70) 6) (:member :current (:accepted t)) (:seal :current)))
(defconst *gc-w9* (fn-gc-matrix-okp *gc-init* *gc-success-events* *gc-probe-events*))
(assert-event *gc-w9*)
(assert-event
 (let ((x (fn-ocp-gc-project *gc-pipelined*)))
   (and (equal (nth 3 x) 3)
        (equal (fn-lgc-count (fn-lgk-pipe-ks (nth 0 x))) 1)
        (consp (fn-lgk-inflight (fn-lgk-pipe-ks (nth 0 x))))
        (consp (fn-lgk-batch (fn-lgk-pipe-ks (nth 0 x)))))))
(value-triple (list :positives *gc-w1* *gc-w2* *gc-w3* *gc-w4* *gc-w5* *gc-w6* *gc-w7* *gc-w8* *gc-w9*))
(value-triple (list :matrix-cases (* (+ 1 (len *gc-success-events*)) (len *gc-probe-events*))))
