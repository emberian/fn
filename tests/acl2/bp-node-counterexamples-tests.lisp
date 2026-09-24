; The spec 11.1 counterexample suite over the host-called BP step, and the
; teeth of the two bp-node-progress-bridge keystones.
;
; Every witness below is a trace through fn-bpnp-step, the function
; host/native/bp-service.lisp:172 calls, from a booted initial state, with
; receptions prepared by the production receive boundary.  Recovery events
; carry a model replay result (the held rows the ordered FNBS replay would
; return), not an observed name/byte scan; that is the same fixture shape
; bp-node-machine-teeth-tests uses.  A label whose scenario this machine
; cannot express is listed at the end with the missing transition named.
(in-package "ACL2")
(include-book "../../books/bp-node-progress-bridge")
(include-book "../../books/bp-node-progress-selection-invariants")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

;; ---------------------------------------------------------------------
;; Fixtures: one small transit bundle A received, dispatched, attempted.

(defconst *bpcx-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpcx-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpcx-dest* (cons :dtn '(47 47 98 112 45 100 101 115 116 47)))
(defconst *bpcx-config* (fn-bpn-config *bpcx-local* 3600000 2 32 1048576))
(defconst *bpcx-sender-config* (fn-bpn-config *bpcx-sender* 3600000 2 32 1048576))
(defconst *bpcx-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpcx-ingress*
  (list :cl (cons 0 1) 1 *bpcx-sender* '(115 101 110 100 101 114) 0))
(defun bpcx-receive-event (wire)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-receive-wire-event-value
   (fn-bpnf-receive-wire-event *bpcx-config* wire *bpcx-obs* *bpcx-ingress*)))
(defun bpcx-durable (answer)
  (declare (xargs :guard t :verify-guards nil))
  (let ((effect (car (fn-bpnf-answer-effects answer))))
    (fn-bpnp-step (fn-bpnf-answer-state answer)
                  (list :persist-result (fn-bpn-nth 1 effect)
                        (fn-bpn-nth 2 effect) :durable))))
(defconst *bpcx-raw-s0* (fn-bpnf-initial-state *bpcx-config* 8 1048576))
(defconst *bpcx-s0*
  (fn-bpnf-answer-state
   (fn-bpnp-step *bpcx-raw-s0*
                 (fn-bpnf-family-recover-auto-event *bpcx-raw-s0* nil :ready nil))))
(defconst *bpcx-a*
  (fn-bpn-send-bundle *bpcx-sender-config* *bpcx-dest* '(1 2 3 4) 7 *bpcx-obs*))
(defconst *bpcx-a-wire* (fn-bpb-encode *bpcx-a*))
(defconst *bpcx-a-proposal* (fn-bpnp-step *bpcx-s0* (bpcx-receive-event *bpcx-a-wire*)))
(defconst *bpcx-s1* (fn-bpnf-answer-state (bpcx-durable *bpcx-a-proposal*)))
(defconst *bpcx-route*
  (list :route '(104) 4556 '(110) 30 65536 65536))
(defconst *bpcx-enqueue*
  (list :enqueue '(119) '(97) 0 9 *bpcx-route* *bpcx-dest* '(5 6 7) *bpcx-obs*))


(defconst *bpcx-routes* (list (list *bpcx-dest* *bpcx-dest*)))
(defconst *bpcx-progress* (list :progress *bpcx-local* *bpcx-obs* *bpcx-routes* 1))
(make-event `(defconst *bpcx-dispatch* ',(fn-bpnp-step *bpcx-s1* *bpcx-progress*)))
(defconst *bpcx-s2* (fn-bpnf-answer-state (bpcx-durable *bpcx-dispatch*)))
(defconst *bpcx-session* (cons 1 1))
(defconst *bpcx-session-event*
  (list :session *bpcx-dest* *bpcx-session* t 32768 *bpcx-obs*))
(make-event `(defconst *bpcx-open* ',(fn-bpnp-step *bpcx-s2* *bpcx-session-event*)))
(defconst *bpcx-attempt-effect* (car (fn-bpnf-answer-effects *bpcx-open*)))
(defconst *bpcx-s3-answer* (bpcx-durable *bpcx-open*))
(defconst *bpcx-s3* (fn-bpnf-answer-state *bpcx-s3-answer*))
(defconst *bpcx-sent-event*
  (list :forward-result (fn-bpn-nth 1 *bpcx-attempt-effect*)
        (fn-bpn-nth 2 *bpcx-attempt-effect*) *bpcx-session* :sent *bpcx-obs*))
(make-event `(defconst *bpcx-sent* ',(fn-bpnp-step *bpcx-s3* *bpcx-sent-event*)))
(defconst *bpcx-s4-answer* (bpcx-durable *bpcx-sent*))


(defconst *bpcx-request*
  (fn-bpa-encode
   (fn-bpa-make-request "w" "s" "dtn://bp-sender/" "dtn://bp-local/"
                        "p" "i" "c" "t" '(88 13 10))))
(defconst *bpcx-req*
  (fn-bpn-send-bundle *bpcx-sender-config* *bpcx-local* *bpcx-request* 8 *bpcx-obs*))
(defconst *bpcx-q1*
  (fn-bpnf-answer-state
   (bpcx-durable (fn-bpnp-step *bpcx-s0* (bpcx-receive-event (fn-bpb-encode *bpcx-req*))))))
(defconst *bpcx-deliver* (fn-bpnp-step *bpcx-q1* (list :progress *bpcx-local* *bpcx-obs* nil 0)))
(defconst *bpcx-deliver-effect* (car (fn-bpnf-answer-effects *bpcx-deliver*)))
(defconst *bpcx-du*
  (fn-bpnp-step (fn-bpnf-answer-state *bpcx-deliver*)
                (list :deliver-result (fn-bpn-nth 1 *bpcx-deliver-effect*)
                      (fn-bpn-nth 2 *bpcx-deliver-effect*)
                      (fn-bpn-nth 3 *bpcx-deliver-effect*) :uncertain '(0))))
(defconst *bpcx-du-s* (fn-bpnf-answer-state *bpcx-du*))


(assert-event
 (and (fn-bpb-bundlep *bpcx-a*)
      (fn-bpnp-host-eventp (bpcx-receive-event *bpcx-a-wire*))
      (null (fn-bpnf-issued *bpcx-s0*))
      (equal (len (fn-bpnf-held-list *bpcx-s1*)) 1)
      (null (fn-bpnf-issued *bpcx-s1*))
      (fn-bpnp-host-eventp *bpcx-progress*)
      (equal (car (car (fn-bpnf-answer-effects *bpcx-dispatch*))) :persist-dispatch)
      (fn-bpnp-host-eventp *bpcx-session-event*)
      (equal (car *bpcx-attempt-effect*) :persist-attempt)
      (equal (car (car (fn-bpnf-answer-effects *bpcx-s3-answer*))) :cl-send)
      (equal (fn-bpn-nth 0 (fn-bpn-nth 13 (car (fn-bpnf-held-list *bpcx-s3*))))
             :forwarding)))

;; ---------------------------------------------------------------------
;; Teeth of fn-bpnp-step-base-event-refines-fn-bpn-step.
;; Witness, first branch: the booted state has nothing issued and no
;; uncertain delivery; the host's (:base (:enqueue ...)) answers exactly
;; fn-bpn-step's nonempty effects and base.
(defconst *bpcx-enqueue-answer* (fn-bpnp-step *bpcx-s0* (list :base *bpcx-enqueue*)))
(defconst *bpcx-enqueue-low* (fn-bpn-step (fn-bpnf-base *bpcx-s0*) *bpcx-enqueue*))
(assert-event
 (and (fn-bpnp-host-eventp (list :base *bpcx-enqueue*))
      (fn-bpn-machine-eventp *bpcx-enqueue*)
      (not (fn-bpnf-issued *bpcx-s0*))
      (not (fn-bpah-delivery-uncertainp *bpcx-s0*))
      (equal (car (car (fn-bpnf-answer-effects *bpcx-enqueue-answer*))) :persist)
      (equal (fn-bpnf-answer-effects *bpcx-enqueue-answer*)
             (fn-bpn-answer-effects *bpcx-enqueue-low*))
      (equal (fn-bpnf-base (fn-bpnf-answer-state *bpcx-enqueue-answer*))
             (fn-bpn-answer-state *bpcx-enqueue-low*))
      (not (equal (fn-bpn-answer-state *bpcx-enqueue-low*)
                  (fn-bpnf-base *bpcx-s0*)))))
;; Hypothesis (not issued) dropped: with the kind-5 proposal issued, the
;; lower machine would propose, but the served step answers nothing.
(defconst *bpcx-issued-s* (fn-bpnf-answer-state *bpcx-a-proposal*))
(assert-event
 (and (fn-bpnf-issued *bpcx-issued-s*)
      (not (fn-bpah-delivery-uncertainp *bpcx-issued-s*))
      (null (fn-bpnf-answer-effects
             (fn-bpnp-step *bpcx-issued-s* (list :base *bpcx-enqueue*))))
      (fn-bpn-answer-effects
       (fn-bpn-step (fn-bpnf-base *bpcx-issued-s*) *bpcx-enqueue*))))
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects
          (fn-bpnp-step *bpcx-issued-s* (list :base *bpcx-enqueue*)))
         (fn-bpn-answer-effects
          (fn-bpn-step (fn-bpnf-base *bpcx-issued-s*) *bpcx-enqueue*)))))
;; Hypothesis (no uncertain delivery) dropped: a reached :deliver-result
;; :uncertain leaves nothing issued but fences the base event.
(assert-event
 (and (equal (car (car (fn-bpnf-answer-effects *bpcx-deliver*))) :deliver)
      (equal (fn-bpnf-answer-effects *bpcx-du*) '((:delivery-answer :uncertain)))
      (not (fn-bpnf-issued *bpcx-du-s*))
      (fn-bpah-delivery-uncertainp *bpcx-du-s*)
      (null (fn-bpnf-answer-effects
             (fn-bpnp-step *bpcx-du-s* (list :base *bpcx-enqueue*))))))
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects
          (fn-bpnp-step *bpcx-du-s* (list :base *bpcx-enqueue*)))
         (fn-bpn-answer-effects
          (fn-bpn-step (fn-bpnf-base *bpcx-du-s*) *bpcx-enqueue*)))))

;; ---------------------------------------------------------------------
;; Teeth of fn-bpnp-step-emits-no-release-and-no-receipt-prepare (no
;; hypotheses).  Reachable nonempty witnesses: the kind-8 send, the kind-9
;; proposal and the durable :sent result, the transport completion that
;; must not discharge anything.
(defconst *bpcx-s4-effects* (fn-bpnf-answer-effects *bpcx-s4-answer*))
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-sent-event*)
      (equal *bpcx-s4-effects* '((:forward-ready 0 :sent)))
      (fn-bpnpb-effects-confinedp *bpcx-s4-effects*)
      (fn-bpnpb-effects-confinedp (fn-bpnf-answer-effects *bpcx-s3-answer*))
      (fn-bpnpb-effects-confinedp (fn-bpnf-answer-effects *bpcx-sent*))))
;; Mutation: a step that turns the durable :sent result into a release is
;; caught by the confinement predicate, so the conclusion is not vacuous.
(defun bpcx-mutant-release (effects)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom effects) nil
    (cons (if (and (consp (car effects))
                   (equal (car (car effects)) :forward-ready))
              (cons :release (cdr (car effects)))
            (car effects))
          (bpcx-mutant-release (cdr effects)))))
(must-fail
 (assert-event (fn-bpnpb-effects-confinedp (bpcx-mutant-release *bpcx-s4-effects*))))

;; ---------------------------------------------------------------------
;; Spec 11.1 labels.  Fixtures for N05, N06, N08, N11, BP-R02, R06, R07,
;; R15, R16.
(defconst *bpcx-n08-recover-event*
  (list :recover-fnbs (1+ (fn-bpnf-epoch *bpcx-s3*)) nil :ready
        (list :ready (fn-bpnf-held-list *bpcx-s3*) nil) 3))
(defconst *bpcx-n08-recovered* (fn-bpnp-step *bpcx-s3* *bpcx-n08-recover-event*))
(defconst *bpcx-n08-r* (fn-bpnf-answer-state *bpcx-n08-recovered*))
(make-event `(defconst *bpcx-n08-reopen*
   ',(fn-bpnp-step *bpcx-n08-r* (list :session *bpcx-dest* (cons 1 2) t 32768 *bpcx-obs*))))
(make-event `(defconst *bpcx-n08-tick*
   ',(fn-bpnp-step *bpcx-n08-r* *bpcx-progress*)))
(defun bpcx-recover (st used)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state
   (fn-bpnp-step st (list :recover-fnbs (1+ (nfix (fn-bpnf-epoch st))) nil :ready
                          (list :ready (fn-bpnf-held-list st) nil) used))))
(defconst *bpcx-s2-debt* (fn-bpnd-debt *bpcx-s2* *bpcx-local*))
(defun bpcx-n05-state (f)
  (declare (xargs :guard t :verify-guards nil))
  (bpcx-recover *bpcx-s2* (- *fn-bpnf-received-max-records* (+ *bpcx-s2-debt* 1 f))))
(make-event `(defconst *bpcx-n05-f1-open*
   ',(fn-bpnp-step (bpcx-n05-state 1) *bpcx-session-event*)))
(make-event `(defconst *bpcx-n05-f2-open*
   ',(fn-bpnp-step (bpcx-n05-state 2) *bpcx-session-event*)))
(defconst *bpcx-n05-f2-s1-answer* (bpcx-durable *bpcx-n05-f2-open*))
(defconst *bpcx-n05-f2-s1* (fn-bpnf-answer-state *bpcx-n05-f2-s1-answer*))
(defconst *bpcx-n05-f2-attempt* (car (fn-bpnf-answer-effects *bpcx-n05-f2-open*)))
(make-event `(defconst *bpcx-n05-failed*
   ',(fn-bpnp-step *bpcx-n05-f2-s1*
       (list :forward-result (fn-bpn-nth 1 *bpcx-n05-f2-attempt*)
             (fn-bpn-nth 2 *bpcx-n05-f2-attempt*) *bpcx-session* :failed *bpcx-obs*))))
(defconst *bpcx-n05-f2-s2-answer* (bpcx-durable *bpcx-n05-failed*))
(defconst *bpcx-n05-f2-s2* (fn-bpnf-answer-state *bpcx-n05-f2-s2-answer*))
(defconst *bpcx-r02-r* (bpcx-recover *bpcx-s1* 1))
(make-event `(defconst *bpcx-r02-tick* ',(fn-bpnp-step *bpcx-r02-r* *bpcx-progress*)))
(defconst *bpcx-a-aged*
  (fn-bpb-make-bundle (fn-bpb-bundle-primary *bpcx-a*)
                      (list (first (fn-bpb-bundle-blocks *bpcx-a*))
                            (list :fn-bpb-block 7 3 0 2 '(24 100)))
                      (fn-bpb-bundle-payload *bpcx-a*)))
(defconst *bpcx-a-changed*
  (fn-bpn-send-bundle *bpcx-sender-config* *bpcx-dest* '(1 2 3 5) 7 *bpcx-obs*))
(defconst *bpcx-r06* (fn-bpnp-step *bpcx-s1* (bpcx-receive-event (fn-bpb-encode *bpcx-a-aged*))))
(defconst *bpcx-r07* (fn-bpnp-step *bpcx-s1* (bpcx-receive-event (fn-bpb-encode *bpcx-a-changed*))))
(defconst *bpcx-n11-bundle*
  (fn-bpb-make-bundle
   (update-nth 3 *bpcx-local*
               (update-nth 1 *fn-bpp-flag-administrative* (fn-bpb-bundle-primary *bpcx-a*)))
   (fn-bpb-bundle-blocks *bpcx-a*) (fn-bpb-bundle-payload *bpcx-a*)))
(defconst *bpcx-n11* (fn-bpnp-step *bpcx-s1* (bpcx-receive-event (fn-bpb-encode *bpcx-n11-bundle*))))
(defconst *bpcx-late-obs* (fn-clock-observation 3602000 0 0 nil))
(defconst *bpcx-r16-event* (list :progress *bpcx-local* *bpcx-late-obs* *bpcx-routes* 1))
(make-event `(defconst *bpcx-r16* ',(fn-bpnp-step *bpcx-s1* *bpcx-r16-event*)))
(defconst *bpcx-r15-event*
  (list :forward-result (fn-bpn-nth 1 *bpcx-attempt-effect*)
        (fn-bpn-nth 2 *bpcx-attempt-effect*) (cons 1 9) :sent *bpcx-obs*))
(defconst *bpcx-r15* (fn-bpnp-step *bpcx-s3* *bpcx-r15-event*))
(defconst *bpcx-n06-proposal* *bpcx-a-proposal*)
(defconst *bpcx-n06-effect* (car (fn-bpnf-answer-effects *bpcx-n06-proposal*)))
(defconst *bpcx-n06-uncertain*
  (fn-bpnp-step (fn-bpnf-answer-state *bpcx-n06-proposal*)
                (list :persist-result (fn-bpn-nth 1 *bpcx-n06-effect*)
                      (fn-bpn-nth 2 *bpcx-n06-effect*) :uncertain)))
(defconst *bpcx-n06-u* (fn-bpnf-answer-state *bpcx-n06-uncertain*))
(defconst *bpcx-n06-fenced* (fn-bpnp-step *bpcx-n06-u* *bpcx-progress*))
(defconst *bpcx-n06-recovered* (fn-bpnp-step *bpcx-n06-u*
   (list :recover-fnbs (1+ (fn-bpnf-epoch *bpcx-n06-u*)) nil :ready
         (list :ready (fn-bpnf-held-list *bpcx-s1*) nil) 1)))

;; N05 (journal debt, the attempt half).  F = remaining - D - R - control.
;; At F=1 a kind-8 attempt is refused without durable mutation: no proposal,
;; nothing issued, held rows unchanged, a :credit wait recorded.  At F=2 the
;; kind 8 and its failed kind 9 both complete, and free credit is zero above
;; the margin afterwards.
(defconst *bpcx-n05-f1* (bpcx-n05-state 1))
(defconst *bpcx-n05-f2* (bpcx-n05-state 2))
(assert-event
 (and (equal (fn-bpnd-free (fn-bpnp-used *bpcx-n05-f1*) (fn-bpnp-debt *bpcx-n05-f1*)
                           *fn-bpnp-control-margin*) 1)
      (equal (fn-bpnp-debt *bpcx-n05-f1*) (fn-bpnd-debt *bpcx-n05-f1* *bpcx-local*))
      (not (fn-bpnf-issued *bpcx-n05-f1*))
      (not (fn-bpn-effect-kind-memberp :persist-attempt
                                       (fn-bpnf-answer-effects *bpcx-n05-f1-open*)))
      (not (fn-bpnf-issued (fn-bpnf-answer-state *bpcx-n05-f1-open*)))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpcx-n05-f1-open*))
             (fn-bpnf-held-list *bpcx-n05-f1*))
      (equal (fn-bpn-nth 2 (car (fn-bpnp-waits (fn-bpnf-answer-state *bpcx-n05-f1-open*))))
             :credit)))
(must-fail
 (assert-event
  (fn-bpn-effect-kind-memberp :persist-attempt (fn-bpnf-answer-effects *bpcx-n05-f1-open*))))
(assert-event
 (and (equal (fn-bpnd-free (fn-bpnp-used *bpcx-n05-f2*) (fn-bpnp-debt *bpcx-n05-f2*)
                           *fn-bpnp-control-margin*) 2)
      (equal (car (car (fn-bpnf-answer-effects *bpcx-n05-f2-open*))) :persist-attempt)
      (equal (car (car (fn-bpnf-answer-effects *bpcx-n05-f2-s1-answer*))) :cl-send)
      (equal (car (car (fn-bpnf-answer-effects *bpcx-n05-failed*))) :persist-forward-result)
      (equal (fn-bpnf-answer-effects *bpcx-n05-f2-s2-answer*) '((:forward-ready 0 :failed)))
      (equal (fn-bpnd-free (fn-bpnp-used *bpcx-n05-f2-s2*) (fn-bpnp-debt *bpcx-n05-f2-s2*)
                           *fn-bpnp-control-margin*) 0)
      (equal (fn-bpnp-debt *bpcx-n05-f2-s2*) (fn-bpnd-debt *bpcx-n05-f2-s2* *bpcx-local*))))
(must-fail
 (assert-event
  (< (fn-bpnd-free (fn-bpnp-used *bpcx-n05-f2-s2*) (fn-bpnp-debt *bpcx-n05-f2-s2*)
                   *fn-bpnp-control-margin*) 0)))

;; N06, machine half.  A kind-5 publication answered :uncertain reports
;; uncertainty (never :stored), fences every later event until recovery, and
;; recovery from a journal in which the record is visible admits the row
;; with no fabricated confirmation.  The byte-store physical half is below.
(assert-event
 (and (equal (car *bpcx-n06-effect*) :persist)
      (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-n06-uncertain*)))
             '(:uncertain :persistence))
      (equal (fn-bpn-nth 5 (fn-bpnf-issued *bpcx-n06-u*)) :uncertain)
      (null (fn-bpnf-answer-effects *bpcx-n06-fenced*))
      (equal (fn-bpnf-answer-state *bpcx-n06-fenced*) *bpcx-n06-u*)
      (equal (fn-bpnf-answer-effects *bpcx-n06-recovered*) '((:restart-ready 1)))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpcx-n06-recovered*))
             (fn-bpnf-held-list *bpcx-s1*))
      (null (fn-bpnf-issued (fn-bpnf-answer-state *bpcx-n06-recovered*)))))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-n06-uncertain*))) :stored)))

;; N08 (unanchored attempt cleared at restart): NOT HELD TODAY.  A durable
;; kind 8 replayed at recovery keeps its :forwarding slot, and neither a new
;; session nor a progress tick re-offers the row: the kind-8 liveness gap of
;; planning/evidence/bp-forwarding-2026-09-24.md.  The spec's outcome is the
;; must-fail; the assertion records today's stranded behaviour.  When the
;; recovery settlement (ember's retry decision) lands, both flip.
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-n08-recover-event*)
      (equal (fn-bpnf-answer-effects *bpcx-n08-recovered*) '((:restart-ready 1)))
      (equal (fn-bpn-nth 0 (fn-bpn-nth 13 (car (fn-bpnf-held-list *bpcx-n08-r*))))
             :forwarding)
      (null (fn-bpnf-answer-effects *bpcx-n08-reopen*))
      (null (fn-bpnf-answer-effects *bpcx-n08-tick*))))
(must-fail
 (assert-event
  (null (fn-bpn-nth 13 (car (fn-bpnf-held-list *bpcx-n08-r*))))))
;; Recovery clears both volatile fields.  Teeth of
;; fn-bpnp-recovery-success-clears-sessions-and-pending-image
;; (bp-node-progress-premises).  Witness: *bpcx-s3* carries the open session
;; to the destination; the successful N08 recovery drops it and leaves no
;; pending kind-8 wire.  (Before the fix the recovery flag compared the
;; whole first effect with the bare keyword and kept the session table.)
(assert-event
 (and (consp (fn-bpnp-sessions *bpcx-s3*))
      (equal (fn-cbor-ag-car *bpcx-n08-recover-event*) :recover-fnbs)
      (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects *bpcx-n08-recovered*)))
             :restart-ready)
      (null (fn-bpnp-sessions *bpcx-n08-r*))
      (null (fn-bpnp-pending-image *bpcx-n08-r*))))

;; Without the :restart-ready hypothesis: a recovery event from the same
;; state whose epoch does not advance faults, and the fault keeps the
;; session table.  Premises other than the dropped one hold; the conclusion
;; is false.  The recovery-event hypothesis has no separating case: only
;; fn-bpnf-recover-fnbs-step builds a :restart-ready effect.
(defconst *bpcx-stale-recover-event*
  (list :recover-fnbs (fn-bpnf-epoch *bpcx-s3*) nil :ready
        (list :ready (fn-bpnf-held-list *bpcx-s3*) nil) 3))
(defconst *bpcx-stale-recovered*
  (fn-bpnp-step *bpcx-s3* *bpcx-stale-recover-event*))
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-stale-recover-event*)
      (equal (fn-cbor-ag-car *bpcx-stale-recover-event*) :recover-fnbs)
      (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects *bpcx-stale-recovered*)))
             :restart-fault)
      (not (and (null (fn-bpnp-sessions (fn-bpnf-answer-state *bpcx-stale-recovered*)))
                (null (fn-bpnp-pending-image
                       (fn-bpnf-answer-state *bpcx-stale-recovered*)))))
      (equal (fn-bpnp-sessions (fn-bpnf-answer-state *bpcx-stale-recovered*))
             (fn-bpnp-sessions *bpcx-s3*))))
(must-fail
 (assert-event
  (and (null (fn-bpnp-sessions (fn-bpnf-answer-state *bpcx-stale-recovered*)))
       (null (fn-bpnp-pending-image (fn-bpnf-answer-state *bpcx-stale-recovered*))))))

;; N11, refusal half: a structurally valid local administrative bundle
;; whose identity conflicts with a held bundle is refused :identity-conflict
;; with no publication.  The kind-14 conflict record is not a transition.
(assert-event
 (and (fn-bpb-bundlep *bpcx-n11-bundle*)
      (equal (fn-bpp-destination (fn-bpb-bundle-primary *bpcx-n11-bundle*)) *bpcx-local*)
      (equal (fn-bpp-flags (fn-bpb-bundle-primary *bpcx-n11-bundle*))
             *fn-bpp-flag-administrative*)
      (equal (fn-bpb-bundle-id *bpcx-n11-bundle*) (fn-bpb-bundle-id *bpcx-a*))
      (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-n11*))) :identity-conflict)
      (null (fn-bpnf-issued (fn-bpnf-answer-state *bpcx-n11*)))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpcx-n11*))
             (fn-bpnf-held-list *bpcx-s1*))))
(must-fail
 (assert-event
  (fn-bpn-effect-kind-memberp :persist (fn-bpnf-answer-effects *bpcx-n11*))))

;; BP-R02: a durable kind 5, then death before dispatch; recovery from the
;; journal's row alone lets the next progress tick propose the dispatch,
;; with no second arrival.
(assert-event
 (and (equal (fn-bpnf-held-list *bpcx-r02-r*) (fn-bpnf-held-list *bpcx-s1*))
      (equal (car (car (fn-bpnf-answer-effects *bpcx-r02-tick*))) :persist-dispatch)))
(must-fail
 (assert-event (null (fn-bpnf-answer-effects *bpcx-r02-tick*))))

;; BP-R06: a retransmission differing only in Bundle Age is a duplicate.
;; BP-R07: the same bundle id with a changed payload is an identity
;; conflict, never a replacement or a duplicate.
(assert-event
 (and (fn-bpb-bundlep *bpcx-a-aged*)
      (not (equal (fn-bpb-encode *bpcx-a-aged*) *bpcx-a-wire*))
      (equal (fn-bpb-bundle-id *bpcx-a-aged*) (fn-bpb-bundle-id *bpcx-a*))
      (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-r06*))) :duplicate)
      (equal (fn-bpb-bundle-id *bpcx-a-changed*) (fn-bpb-bundle-id *bpcx-a*))
      (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-r07*))) :identity-conflict)
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpcx-r07*))
             (fn-bpnf-held-list *bpcx-s1*))))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-r06*))) :identity-conflict)))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-r07*))) :duplicate)))

;; BP-R15: a carrier result naming another session while the attempt is in
;; flight is stale and changes nothing.
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-r15-event*)
      (equal (fn-bpnf-answer-effects *bpcx-r15*) '((:forward-stale 1 2 (1 . 9))))
      (equal (fn-bpnf-answer-state *bpcx-r15*) *bpcx-s3*)))
(must-fail
 (assert-event (equal (fn-bpnf-answer-state *bpcx-r15*) (fn-bpnf-answer-state *bpcx-sent*))))

;; BP-R16: a held bundle already past its lifetime at the progress
;; observation gets no dispatch, delivery or send from that tick; the same
;; tick at a live observation dispatches it.
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-r16-event*)
      (equal (fn-bpnp-held-expiry (car (fn-bpnf-held-list *bpcx-s1*)) *bpcx-late-obs*)
             :expired)
      (null (fn-bpnf-answer-effects *bpcx-r16*))))
(must-fail
 (assert-event
  (equal (car (car (fn-bpnf-answer-effects *bpcx-r16*))) :persist-dispatch)))

;; ---------------------------------------------------------------------
;; Coverage of spec 11.1 over this machine (each row names its subject).
;; Present elsewhere: N03 (bp-node-machine-teeth-tests), N04
;; (bp-node-forwarding-teeth-tests), N09 (bp-fragment-tests), N15
;; unlabelled (bp-channel-ingress-tests, fn-bpaj-tcpcl-ingress-result).
;; Not expressible through fn-bpnp-step today, missing transition named:
;;   N01, N13, BP-R03..R05, R19: application join and FNRJ receipt outbox
;;     (bp-native-app / workflow), not a node-machine event.
;;   N02, BP-R08, R09: workflow overdue/retry (bp-workflow), no node event.
;;   N06 physical half: FNBS byte-store publisher relation and crash cuts.
;;   N07: fn-clock-observation carries no boot domain; no domain gate.
;;   N08: recovery settlement of a replayed kind-8 row (asserted above as
;;     the stranded behaviour).
;;   N10: machine-level reassembly order (slice C2).
;;   N11 kind-14 half: no kind-14 conflict record transition.
;;   N12, BP-R10: TCPCL segment/END ACK machine (tcpcl books).
;;   N14: Store pin release join (bp-release).
;;   N16, BP-R21: journal rotation (slice E), no generation transition.
;;   N17, BP-R23: codec seam / cross-implementation vectors, not a trace.
;;   N18, BP-R24: owner-progress monitor and bounded service turn (slice B).
;;   BP-R01: FNWF scheduler persistence (scheduler, no native caller).
;;   BP-R11..R13, R22: fragment family capacity, crash prefixes, scaling.
;;   BP-R14: route change against historical replay (no route in replay
;;     input; the replay half needs the ordered-row scan, not a fixture).
;;   BP-R17: no busy delivery outcome; a :deliver-result is accepted,
;;     duplicate, returned, refused or uncertain, with no deferred-redelivery
;;     (class-3 backoff) transition.
;;   BP-R18, R20: local report processing and reverse relay routing.
