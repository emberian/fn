; Bounded exhaustive exploration of the executable immutable-file kernel.
;
; This is a finite graph check over the functions in books/store-files.lisp.
; It records only transitions whose post-state stays inside the declared
; frontier/record bounds.  Completion is part of the result and is asserted;
; a fuel exhaustion is therefore a failed test, never an exhaustive claim.
;
; Three counts are reported and asserted, and they are different things:
;   states        distinct reachable kernel states inside the bounds;
;   applications  (state, event) pairs whose post-state is inside the bounds,
;                 including no-op applications where the kernel refused or
;                 ignored the event and returned the same state;
;   transitions   applications whose post-state differs from the source.
; Distinct (source, destination) pairs among transitions are reported as well,
; since several events can select the same successor.
(in-package "ACL2")
(include-book "../../books/store-files")

(defconst *sfe-groups* '("fn.letters" "fn.test"))
(defconst *sfe-capacity* 4)
(defconst *sfe-max-frontier* 2)
(defconst *sfe-max-records* 2)
(defconst *sfe-fuel* 10000)

(defconst *sfe-record-0*
  (fn-record-make 0 0 0 "<zero@example.invalid>" '(90)
                  '("fn.letters") "archive-zero" "content-zero"
                  "release-zero" 1))
(defconst *sfe-record-1*
  (fn-record-make 1 1 1 "<one@example.invalid>" '(79)
                  '("fn.test") "archive-one" "content-one"
                  "release-one" 1))
; A txid-gap record: sequence 0 at txid 1.  It is preparable only after
; reservation 0 was consumed without a record (refusal or known abort) and
; reservation 1 was made durable, so its presence in the graph shows the gap
; path refuse-then-publish is explored.
(defconst *sfe-record-0-gap*
  (fn-record-make 0 1 1 "<gap@example.invalid>" '(71)
                  '("fn.letters") "archive-gap" "content-gap"
                  "release-gap" 1))

; The event dispatcher calls the storage kernel directly.  It deliberately
; carries no alternate phase or acceptance semantics.  fn-sf-lose-success is
; not in the vocabulary: it is unreachable-in-composition (store-files.lisp).
(defun sfe-dispatch (s event)
  (cond
   ((equal event '(:start-frontier))
    (fn-sf-start-frontier s))
   ((equal (car event) :frontier-file)
    (fn-sf-frontier-file-result s (car (cdr event))))
   ((equal (car event) :frontier-replace)
    (fn-sf-frontier-replace-result s (car (cdr event))))
   ((equal (car event) :frontier-dir)
    (fn-sf-frontier-dir-result s (car (cdr event))))
   ((equal (car event) :refuse-reservation)
    (fn-sf-refuse-reservation s (car (cdr event))))
   ((equal (car event) :prepare-record)
    (fn-sf-prepare-record s (car (cdr event)) *sfe-groups* *sfe-capacity*))
   ((equal (car event) :record-file)
    (fn-sf-record-file-result s (car (cdr event))))
   ((equal event '(:prepublish-abort))
    (fn-sf-prepublish-abort s))
   ((equal (car event) :abort-completion)
    (fn-sf-abort-completion s (car (cdr event))
                            (car (cdr (cdr event)))))
   ((equal (car event) :record-link)
    (fn-sf-record-link-result s (car (cdr event))))
   ((equal (car event) :record-dir)
    (fn-sf-record-dir-result s (car (cdr event))))
   ((equal (car event) :core-completion)
    (fn-sf-core-completion s (car (cdr event))
                           (car (cdr (cdr event)))))
   ((equal (car event) :emit-success)
    (fn-sf-emit-success s (car (cdr event))
                        (car (cdr (cdr event)))))
   ((equal (car event) :crash)
    (fn-sf-crash s (car (cdr event)) (car (cdr (cdr event)))))
   ((equal event '(:recover))
    (fn-sf-recover s *sfe-groups* *sfe-capacity*))
   ((equal (car event) :recovery-barrier)
    (fn-sf-recovery-barrier s (car (cdr event))))
   (t s)))

; Keep the graph finite while retaining the actual state recognizer as the
; semantic validity check.  A candidate frontier of 3, or a third stable
; record, is outside this deliberately small exploration domain.
(defun sfe-bounded-statep (s)
  (and (fn-sf-statep s)
       (<= (fn-sf-frontier s) *sfe-max-frontier*)
       (<= (len (fn-sf-records s)) *sfe-max-records*)))

(defun sfe-state-memberp (s states)
  (if (consp states)
      (or (equal s (car states))
          (sfe-state-memberp s (cdr states)))
    nil))

; Each edge is (source event destination).
(defun sfe-edges-for-events (s events)
  (if (consp events)
      (let ((child (sfe-dispatch s (car events))))
        (if (sfe-bounded-statep child)
            (cons (list s (car events) child)
                  (sfe-edges-for-events s (cdr events)))
          (sfe-edges-for-events s (cdr events))))
    nil))

(defun sfe-children-from-edges (edges seen fresh)
  (if (consp edges)
      (let ((child (car (cdr (cdr (car edges))))))
        (if (or (sfe-state-memberp child seen)
                (sfe-state-memberp child fresh))
            (sfe-children-from-edges (cdr edges) seen fresh)
          (sfe-children-from-edges (cdr edges) seen
                                   (append fresh (list child)))))
    fresh))

(defun sfe-explore-aux (fuel queue seen edges events)
  (if (or (zp fuel) (not (consp queue)))
      (list :sfe-result (not (consp queue)) seen edges)
    (let* ((s (car queue))
           (remaining (cdr queue))
           (new-edges (sfe-edges-for-events s events))
           (fresh (sfe-children-from-edges new-edges seen nil)))
      (sfe-explore-aux (1- fuel)
                       (append remaining fresh)
                       (append seen fresh)
                       (append edges new-edges)
                       events))))

(defun sfe-result-completep (result) (car (cdr result)))
(defun sfe-result-states (result) (car (cdr (cdr result))))
(defun sfe-result-edges (result) (car (cdr (cdr (cdr result)))))

; The event set is the cross-product of the meaningful result cuts the host
; can report, plus every pair the three records can name.  The dispatcher
; rejects mismatched events through each real kernel function, so this also
; exercises repeated recovery and stale completions.
(defconst *sfe-events*
  (list
   '(:start-frontier)
   '(:frontier-file :ok) '(:frontier-file :known-fail)
   '(:frontier-replace :ok) '(:frontier-replace :error)
   '(:frontier-dir :ok) '(:frontier-dir :error)
   '(:refuse-reservation 0) '(:refuse-reservation 1)
   (list :prepare-record *sfe-record-0*)
   (list :prepare-record *sfe-record-1*)
   (list :prepare-record *sfe-record-0-gap*)
   '(:record-file :ok) '(:record-file :known-fail)
   '(:prepublish-abort)
   '(:abort-completion 0 0) '(:abort-completion 1 1) '(:abort-completion 0 1)
   '(:record-link :ok) '(:record-link :error)
   '(:record-dir :ok) '(:record-dir :error)
   '(:core-completion 0 0) '(:core-completion 1 1) '(:core-completion 0 1)
   '(:emit-success 0 0) '(:emit-success 1 1) '(:emit-success 0 1)
   '(:crash :old :absent) '(:crash :old :present)
   '(:crash :new :absent) '(:crash :new :present)
   '(:recover)
   '(:recovery-barrier :ok)
   '(:recovery-barrier :uncertain)))

(defconst *sfe-result*
  (sfe-explore-aux *sfe-fuel*
                   (list (fn-sf-initial-state))
                   (list (fn-sf-initial-state))
                   nil
                   *sfe-events*))

(defun sfe-edge-source (edge) (car edge))
(defun sfe-edge-event (edge) (car (cdr edge)))
(defun sfe-edge-destination (edge) (car (cdr (cdr edge))))

(defun sfe-list-prefixp (xs ys)
  (if (consp xs)
      (and (consp ys)
           (equal (car xs) (car ys))
           (sfe-list-prefixp (cdr xs) (cdr ys)))
    t))

(defun sfe-all-states-validp (states)
  (if (consp states)
      (and (sfe-bounded-statep (car states))
           (sfe-all-states-validp (cdr states)))
    t))

(defun sfe-all-edges-preservep (edges)
  (if (consp edges)
      (let ((edge (car edges)))
        (and (sfe-list-prefixp
              (fn-sf-records (sfe-edge-source edge))
              (fn-sf-records (sfe-edge-destination edge)))
             (sfe-list-prefixp
              (fn-sf-successes (sfe-edge-source edge))
              (fn-sf-successes (sfe-edge-destination edge)))
             (sfe-all-edges-preservep (cdr edges))))
    t))

; Counting.  Transitions are state-changing applications; pairs are the
; distinct (source . destination) among them.
(defun sfe-count-transitions (edges)
  (if (consp edges)
      (+ (if (equal (sfe-edge-source (car edges))
                    (sfe-edge-destination (car edges)))
             0
           1)
         (sfe-count-transitions (cdr edges)))
    0))

(defun sfe-pair-memberp (pair pairs)
  (if (consp pairs)
      (or (equal pair (car pairs))
          (sfe-pair-memberp pair (cdr pairs)))
    nil))

(defun sfe-distinct-transition-pairs (edges acc)
  (if (consp edges)
      (let ((pair (cons (sfe-edge-source (car edges))
                        (sfe-edge-destination (car edges)))))
        (if (or (equal (car pair) (cdr pair))
                (sfe-pair-memberp pair acc))
            (sfe-distinct-transition-pairs (cdr edges) acc)
          (sfe-distinct-transition-pairs (cdr edges) (cons pair acc))))
    acc))

(defun sfe-count-phase (phase states)
  (if (consp states)
      (+ (if (equal phase (fn-sf-phase (car states))) 1 0)
         (sfe-count-phase phase (cdr states)))
    0))

(defun sfe-any-phasep (phase states)
  (if (consp states)
      (or (equal phase (fn-sf-phase (car states)))
          (sfe-any-phasep phase (cdr states)))
    nil))

(defun sfe-any-changing-eventp (event edges)
  (if (consp edges)
      (or (and (equal event (sfe-edge-event (car edges)))
               (not (equal (sfe-edge-source (car edges))
                           (sfe-edge-destination (car edges)))))
          (sfe-any-changing-eventp event (cdr edges)))
    nil))

(defun sfe-any-edge-at-phasep (phase event edges)
  (if (consp edges)
      (or (and (equal phase (fn-sf-phase (sfe-edge-source (car edges))))
               (equal event (sfe-edge-event (car edges))))
          (sfe-any-edge-at-phasep phase event (cdr edges)))
    nil))

; A crash edge at the phase whose :new choice yields the candidate frontier.
(defun sfe-crash-new-selects-candidate-at-phasep (phase edges)
  (if (consp edges)
      (let ((edge (car edges)))
        (or (and (equal phase (fn-sf-phase (sfe-edge-source edge)))
                 (equal (sfe-edge-event edge) '(:crash :new :absent))
                 (equal (fn-sf-frontier (sfe-edge-destination edge))
                        (fn-sf-frontier-candidate (sfe-edge-source edge))))
            (sfe-crash-new-selects-candidate-at-phasep phase (cdr edges))))
    nil))

; A crash edge at the phase whose :present choice appends the candidate.
(defun sfe-crash-present-appends-candidate-at-phasep (phase edges)
  (if (consp edges)
      (let ((edge (car edges)))
        (or (and (equal phase (fn-sf-phase (sfe-edge-source edge)))
                 (equal (sfe-edge-event edge) '(:crash :old :present))
                 (equal (fn-sf-records (sfe-edge-destination edge))
                        (append (fn-sf-records (sfe-edge-source edge))
                                (list (fn-sf-record-candidate
                                       (sfe-edge-source edge))))))
            (sfe-crash-present-appends-candidate-at-phasep phase (cdr edges))))
    nil))

; Any crash edge at the phase that changes the frontier / the records.
(defun sfe-crash-changes-frontier-at-phasep (phase edges)
  (if (consp edges)
      (let ((edge (car edges)))
        (or (and (equal phase (fn-sf-phase (sfe-edge-source edge)))
                 (equal (car (sfe-edge-event edge)) :crash)
                 (not (equal (fn-sf-frontier (sfe-edge-destination edge))
                             (fn-sf-frontier (sfe-edge-source edge)))))
            (sfe-crash-changes-frontier-at-phasep phase (cdr edges))))
    nil))

(defun sfe-crash-changes-records-at-phasep (phase edges)
  (if (consp edges)
      (let ((edge (car edges)))
        (or (and (equal phase (fn-sf-phase (sfe-edge-source edge)))
                 (equal (car (sfe-edge-event edge)) :crash)
                 (not (equal (fn-sf-records (sfe-edge-destination edge))
                             (fn-sf-records (sfe-edge-source edge)))))
            (sfe-crash-changes-records-at-phasep phase (cdr edges))))
    nil))

(defun sfe-any-edge-to-recordsp (records edges)
  (if (consp edges)
      (or (equal records (fn-sf-records (sfe-edge-destination (car edges))))
          (sfe-any-edge-to-recordsp records (cdr edges)))
    nil))

(defun sfe-any-state-with-successesp (successes states)
  (if (consp states)
      (or (equal successes (fn-sf-successes (car states)))
          (sfe-any-state-with-successesp successes (cdr states)))
    nil))

(defun sfe-any-recovering-barrier-countp (count states)
  (if (consp states)
      (or (and (equal (fn-sf-phase (car states)) :recovering)
               (equal (fn-sf-barriers (car states)) count))
          (sfe-any-recovering-barrier-countp count (cdr states)))
    nil))

(assert-event (equal (car *sfe-result*) :sfe-result))
; The finite graph must be exhausted before this result can be called an
; exhaustive exploration.  If this assertion fails, increase no budget
; silently: reduce the domain or report the bounded run as incomplete.
(assert-event (sfe-result-completep *sfe-result*))
(assert-event (sfe-all-states-validp (sfe-result-states *sfe-result*)))
(assert-event (sfe-all-edges-preservep (sfe-result-edges *sfe-result*)))

(defconst *sfe-states* (len (sfe-result-states *sfe-result*)))
(defconst *sfe-applications* (len (sfe-result-edges *sfe-result*)))
(defconst *sfe-transitions* (sfe-count-transitions (sfe-result-edges *sfe-result*)))
(defconst *sfe-transition-pairs*
  (len (sfe-distinct-transition-pairs (sfe-result-edges *sfe-result*) nil)))
(defconst *sfe-transient-states*
  (+ (sfe-count-phase :aborting (sfe-result-states *sfe-result*))
     (sfe-count-phase :completed (sfe-result-states *sfe-result*))))

; Emit reproducible evidence into the certification log.  These values are
; computed from the actual graph, not hand-entered counts.
(value-triple
 (cw "SFE_BOUNDED_EXHAUSTIVE fuel=~x0 max-frontier=~x1 max-records=~x2 events=~x3 states=~x4 applications=~x5 transitions=~x6 transition-pairs=~x7 transient-states=~x8~%"
      *sfe-fuel* *sfe-max-frontier* *sfe-max-records* (len *sfe-events*)
      *sfe-states* *sfe-applications* *sfe-transitions*
      *sfe-transition-pairs* *sfe-transient-states*))

; The counts are computed from the actual graph above; these assertions pin
; the recorded run so a silent change in the kernel or the domain is noticed.
(assert-event (equal *sfe-states* 240))
(assert-event (equal *sfe-applications* 8337))
(assert-event (equal *sfe-transitions* 1127))
(assert-event (equal *sfe-transition-pairs* 524))
(assert-event (equal *sfe-transient-states* 8))

; Every semantic phase that can be reached in this domain occurs.  The three
; fenced phases removed in the crash-fidelity revision (:fenced-reservation,
; :fenced-before-record, :fenced-core) no longer exist.
(assert-event (sfe-any-phasep :ready (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :reserved (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :frontier-staged (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :frontier-data-durable (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :frontier-attempted (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :record-staged (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :record-data-durable (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :aborting (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :record-attempted (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :completing (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :completed (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :replaying (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :recovering (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :fenced-frontier (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :fenced-record (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-phasep :fenced-recovery (sfe-result-states *sfe-result*)))
(assert-event (not (sfe-any-phasep :fault (sfe-result-states *sfe-result*))))

; The txid-gap path is explored: reservation 0 refused, reservation 1 used
; by sequence 0, published, acknowledged, and aborted variants.
(assert-event (sfe-any-changing-eventp '(:refuse-reservation 0)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-changing-eventp (list :prepare-record *sfe-record-0-gap*)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-to-recordsp (list *sfe-record-0-gap*)
                                        (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-to-recordsp (list *sfe-record-0* *sfe-record-1*)
                                        (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-state-with-successesp '((0 . 1))
                                             (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-state-with-successesp '((0 . 0) (1 . 1))
                                             (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-changing-eventp '(:abort-completion 0 1)
                                       (sfe-result-edges *sfe-result*)))

; The two syscall-issued-unobserved crash points are genuine choices in the
; graph: from :frontier-data-durable a crash reaches the candidate frontier
; (crash point frontier-replace) and from :record-data-durable a crash reaches
; the appended candidate (crash point final-link); the earlier staged phases
; offer no such choice, and the phases after each completed barrier offer
; none either.
(assert-event (sfe-crash-new-selects-candidate-at-phasep
               :frontier-data-durable (sfe-result-edges *sfe-result*)))
(assert-event (sfe-crash-new-selects-candidate-at-phasep
               :frontier-attempted (sfe-result-edges *sfe-result*)))
(assert-event (sfe-crash-new-selects-candidate-at-phasep
               :fenced-frontier (sfe-result-edges *sfe-result*)))
(assert-event (not (sfe-crash-changes-frontier-at-phasep
                    :frontier-staged (sfe-result-edges *sfe-result*))))
(assert-event (not (sfe-crash-changes-frontier-at-phasep
                    :reserved (sfe-result-edges *sfe-result*))))
(assert-event (sfe-crash-present-appends-candidate-at-phasep
               :record-data-durable (sfe-result-edges *sfe-result*)))
(assert-event (sfe-crash-present-appends-candidate-at-phasep
               :record-attempted (sfe-result-edges *sfe-result*)))
(assert-event (sfe-crash-present-appends-candidate-at-phasep
               :fenced-record (sfe-result-edges *sfe-result*)))
(assert-event (not (sfe-crash-changes-records-at-phasep
                    :record-staged (sfe-result-edges *sfe-result*))))
(assert-event (not (sfe-crash-changes-records-at-phasep
                    :aborting (sfe-result-edges *sfe-result*))))
(assert-event (not (sfe-crash-changes-records-at-phasep
                    :completing (sfe-result-edges *sfe-result*))))
(assert-event (not (sfe-crash-changes-records-at-phasep
                    :ready (sfe-result-edges *sfe-result*))))

; Both whole frontier choices and both exact-file choices are exercised from
; the phases where each choice is observable.
(assert-event (sfe-any-edge-at-phasep :frontier-attempted
                                       '(:crash :old :absent)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-at-phasep :frontier-attempted
                                       '(:crash :new :absent)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-at-phasep :record-attempted
                                       '(:crash :old :absent)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-at-phasep :record-attempted
                                       '(:crash :old :present)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-at-phasep :record-attempted
                                       '(:crash :new :absent)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-at-phasep :record-attempted
                                       '(:crash :new :present)
                                       (sfe-result-edges *sfe-result*)))

; Repeated recovery is in the event domain, and all five barrier counts are
; reached.  Readiness is therefore gated by the final barrier in the explored
; states, while uncertainty reaches a fenced recovery state.
(assert-event (sfe-any-changing-eventp '(:recover) (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-edge-at-phasep :recovering '(:recover)
                                       (sfe-result-edges *sfe-result*)))
(assert-event (sfe-any-recovering-barrier-countp 0
                                                 (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-recovering-barrier-countp 1
                                                 (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-recovering-barrier-countp 2
                                                 (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-recovering-barrier-countp 3
                                                 (sfe-result-states *sfe-result*)))
(assert-event (sfe-any-recovering-barrier-countp 4
                                                 (sfe-result-states *sfe-result*)))
