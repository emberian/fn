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
(include-book "../../books/bp-node-machine-gaps")
(include-book "../../books/bp-node-busy-delivery")
(include-book "../../books/bp-fnbs-conflict-publication")
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
(make-event `(defconst *bpcx-r07* ',(fn-bpnp-step *bpcx-s1* (bpcx-receive-event (fn-bpb-encode *bpcx-a-changed*)))))
(defconst *bpcx-n11-bundle*
  (fn-bpb-make-bundle
   (update-nth 3 *bpcx-local*
               (update-nth 1 *fn-bpp-flag-administrative* (fn-bpb-bundle-primary *bpcx-a*)))
   (fn-bpb-bundle-blocks *bpcx-a*) (fn-bpb-bundle-payload *bpcx-a*)))
(make-event `(defconst *bpcx-n11* ',(fn-bpnp-step *bpcx-s1* (bpcx-receive-event (fn-bpb-encode *bpcx-n11-bundle*)))))
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

;; N08 (death after durable kind 8, restart), under the retry policy adopted
;; by the coordinator on 2026-09-24 pending ember (spec 4.3.1).  Recovery
;; keeps the durable attempt; the attempt's epoch precedes the recovered
;; epoch, so the row is a forward candidate again, and the next session to
;; its next hop re-offers it: a fresh kind 8 naming the same arrival and the
;; same primary identity, the same forwarding image, retry count 1.  The
;; progress tick still offers nothing (forwarding is session-driven).  The
;; stranded-after-bound case is in bp-node-forward-retry-tests.
(defconst *bpcx-n08-offer* (car (fn-bpnf-answer-effects *bpcx-n08-reopen*)))
(defconst *bpcx-n08-resent* (bpcx-durable *bpcx-n08-reopen*))
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-n08-recover-event*)
      (equal (fn-bpnf-answer-effects *bpcx-n08-recovered*) '((:restart-ready 1)))
      (equal (fn-bpn-nth 0 (fn-bpn-nth 13 (car (fn-bpnf-held-list *bpcx-n08-r*))))
             :forwarding)
      (equal (car *bpcx-n08-offer*) :persist-attempt)
      (equal (fn-bpn-nth 3 (fn-bpn-nth 3 *bpcx-n08-offer*))
             (fn-bpn-nth 3 (fn-bpn-nth 3 *bpcx-attempt-effect*)))
      (equal (fn-bpn-nth 4 (fn-bpn-nth 3 *bpcx-n08-offer*))
             (fn-bpn-nth 4 (fn-bpn-nth 3 *bpcx-attempt-effect*)))
      (equal (car (car (fn-bpnf-answer-effects *bpcx-n08-resent*))) :cl-send)
      (equal (fn-bpn-nth 6 (car (fn-bpnf-answer-effects *bpcx-n08-resent*)))
             (fn-bpn-nth 6 (car (fn-bpnf-answer-effects *bpcx-s3-answer*))))
      (equal (fn-bpnp-attempt-retries
              (fn-bpn-nth 13 (car (fn-bpnf-held-list
                                   (fn-bpnf-answer-state *bpcx-n08-resent*)))))
             1)
      (null (fn-bpnf-answer-effects *bpcx-n08-tick*))))
;; Today's selector would strand it: the pre-policy candidate test (no
;; attempt slot at all) rejects the recovered row.
(must-fail
 (assert-event
  (null (fn-bpn-nth 13 (car (fn-bpnf-held-list *bpcx-n08-r*))))))
(must-fail
 (assert-event (null (fn-bpnf-answer-effects *bpcx-n08-reopen*))))
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

;; N11: a structurally valid local administrative bundle whose identity
;; conflicts with a held bundle is refused :identity-conflict, the held row
;; is kept, and within the journal's credit the refusal is preceded by a
;; durable kind-14 conflict record naming the held row, the ingress and the
;; carrier's content id (spec 4.1 step 4).  Keystones:
;; fn-bpnp-step-identity-conflict-is-refused-or-recorded and
;; fn-bpnp-step-conflict-publication-answers-refusal (bp-node-machine-gaps).
(defconst *bpcx-n11-event* (bpcx-receive-event (fn-bpb-encode *bpcx-n11-bundle*)))
(defconst *bpcx-n11-record* (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bpcx-n11*))))
(defconst *bpcx-n11-s* (fn-bpnf-answer-state *bpcx-n11*))
(defun bpcx-n11-result (result)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-step *bpcx-n11-s*
                (list :persist-result (fn-bpnf-epoch *bpcx-s1*)
                      (fn-bpnf-next-op *bpcx-s1*) result)))
(defconst *bpcx-n11-refusal*
  (list (list :receive-answer *bpcx-ingress* :identity-conflict)))
(assert-event
 (and (fn-bpb-bundlep *bpcx-n11-bundle*)
      (fn-bpnp-host-eventp *bpcx-n11-event*)
      (equal (fn-bpp-destination (fn-bpb-bundle-primary *bpcx-n11-bundle*)) *bpcx-local*)
      (equal (fn-bpp-flags (fn-bpb-bundle-primary *bpcx-n11-bundle*))
             *fn-bpp-flag-administrative*)
      (equal (fn-bpb-bundle-id *bpcx-n11-bundle*) (fn-bpb-bundle-id *bpcx-a*))
      ;; the keystone's full antecedent, on the reachable state S1
      (not (fn-bpnf-issued *bpcx-s1*))
      (not (fn-bpah-delivery-uncertainp *bpcx-s1*))
      (fn-frame-natp (fn-bpnf-epoch *bpcx-s1*))
      (fn-frame-natp (fn-bpnf-next-op *bpcx-s1*))
      (fn-frame-natp (fn-bpnf-next-arrival *bpcx-s1*))
      (< (fn-bpnf-next-op *bpcx-s1*) *fn-frame-max-nat*)
      (equal (fn-bpnf-receive-decision (fn-bpnf-held-list *bpcx-s1*)
                                       *bpcx-ingress* *bpcx-n11-bundle*)
             :identity-conflict)
      ;; the recorded branch: the kind-14 proposal, well formed and framed
      (equal (car (car (fn-bpnf-answer-effects *bpcx-n11*))) :persist-conflict)
      (fn-bpnf-conflict-recordp *bpcx-n11-record*)
      (equal (fn-bpn-nth 3 *bpcx-n11-record*)
             (fn-bpn-nth 3 (car (fn-bpnf-held-list *bpcx-s1*))))
      (equal (fn-bpn-nth 5 *bpcx-n11-record*) *bpcx-sender*)
      (equal (fn-bpn-nth 8 *bpcx-n11-record*) (fn-digest (fn-bpb-encode *bpcx-n11-bundle*)))
      (equal (fn-bpnf-conflict-unframe (fn-bpnf-conflict-frame *bpcx-n11-record*))
             *bpcx-n11-record*)
      (equal (fn-bpnf-held-list *bpcx-n11-s*) (fn-bpnf-held-list *bpcx-s1*))
      ;; while the record is issued, another reception waits (:busy)
      (equal (fn-bpnf-answer-effects (fn-bpnp-step *bpcx-n11-s* *bpcx-n11-event*))
             (list (list :receive-answer *bpcx-ingress* '(:refused :busy))))
      ;; every publication outcome answers the refusal; held row kept
      (equal (fn-bpnf-answer-effects (bpcx-n11-result :durable)) *bpcx-n11-refusal*)
      (equal (fn-bpnf-answer-effects (bpcx-n11-result :refused)) *bpcx-n11-refusal*)
      (equal (fn-bpnf-answer-effects (bpcx-n11-result :uncertain)) *bpcx-n11-refusal*)
      (null (fn-bpnf-issued (fn-bpnf-answer-state (bpcx-n11-result :durable))))
      (equal (fn-bpnp-used (fn-bpnf-answer-state (bpcx-n11-result :durable)))
             (1+ (nfix (fn-bpnp-used *bpcx-s1*))))
      (equal (fn-bpnp-used (fn-bpnf-answer-state (bpcx-n11-result :refused)))
             (fn-bpnp-used *bpcx-s1*))
      (equal (fn-bpn-nth 5 (fn-bpnf-issued (fn-bpnf-answer-state (bpcx-n11-result :uncertain))))
             :uncertain)
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state (bpcx-n11-result :durable)))
             (fn-bpnf-held-list *bpcx-s1*))
      (equal (fn-bpnf-callback-result
              (fn-bpnf-answer-effects (bpcx-n11-result :durable)) *bpcx-ingress* nil)
             '(:refused :identity-conflict))
      ;; replay of the durable kind-14 frame keeps the held row and faults
      ;; on a record naming no held arrival
      (equal (fn-bpnf-conflict-apply *bpcx-n11-record* (fn-bpnf-held-list *bpcx-s1*))
             (list :ready (fn-bpnf-held-list *bpcx-s1*)))
      (equal (fn-bpnf-conflict-apply *bpcx-n11-record* nil)
             '(:fault :conflict-row))))
;; Mutation: the pre-kind-14 machine (the lower step's bare refusal) writes
;; no record, so the recorded-branch conjunct has teeth.
(must-fail
 (assert-event
  (fn-bpn-effect-kind-memberp :persist-conflict
   (fn-bpnf-answer-effects (fn-bpnf-step *bpcx-s1* *bpcx-n11-event*)))))
;; Branch predicate dropped (spec 11.1 T5 row): the kind-14 :persist-conflict
;; is an effect of a local administrative input, so the widened class must
;; admit it; the conflict is never :stored.
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects *bpcx-n11*) *bpcx-n11-refusal*)))
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects (bpcx-n11-result :durable))
         (list (list :receive-answer *bpcx-ingress* :stored)))))
;; Teeth of fn-bpnp-step-identity-conflict-is-refused-or-recorded, one per
;; hypothesis; each keeps the others and shows the conclusion false.
(defun bpcx-conflict-concl (st event)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((ans (fn-bpnp-step st event))
         (ingress (fn-bpn-nth 3 event))
         (effects (fn-bpnf-answer-effects ans)))
    (and (equal (fn-bpnf-held-list (fn-bpnf-answer-state ans))
                (fn-bpnf-held-list st))
         (or (equal effects (list (list :receive-answer ingress :identity-conflict)))
             (equal (car (car effects)) :persist-conflict)))))
(assert-event (bpcx-conflict-concl *bpcx-s1* *bpcx-n11-event*))
;; host-eventp dropped: the four-field legacy receive arm refuses without a
;; record although the record would be well formed and admitted.
(defconst *bpcx-n11-legacy* (butlast *bpcx-n11-event* 1))
(assert-event (not (fn-bpnp-host-eventp *bpcx-n11-legacy*)))
(must-fail
 (assert-event
  (equal (car (car (fn-bpnf-answer-effects (fn-bpnp-step *bpcx-s1* *bpcx-n11-legacy*))))
         :persist-conflict)))
;; not-issued dropped: the record-issued state answers :busy.
(assert-event (fn-bpnf-issued *bpcx-n11-s*))
(must-fail (assert-event (bpcx-conflict-concl *bpcx-n11-s* *bpcx-n11-event*)))
;; no-uncertain-delivery dropped: a delivery-uncertain state holding the
;; request answers nothing to a conflicting copy of it.
(defconst *bpcx-req-conflict*
  (fn-bpb-make-bundle (update-nth 1 *fn-bpp-flag-administrative*
                                  (fn-bpb-bundle-primary *bpcx-req*))
                      (fn-bpb-bundle-blocks *bpcx-req*)
                      (fn-bpb-bundle-payload *bpcx-req*)))
(defconst *bpcx-req-conflict-event* (bpcx-receive-event (fn-bpb-encode *bpcx-req-conflict*)))
(assert-event
 (and (fn-bpb-bundlep *bpcx-req-conflict*)
      (fn-bpnp-host-eventp *bpcx-req-conflict-event*)
      (fn-bpah-delivery-uncertainp *bpcx-du-s*)
      (not (fn-bpnf-issued *bpcx-du-s*))
      (equal (fn-bpnf-receive-decision (fn-bpnf-held-list *bpcx-du-s*)
                                       *bpcx-ingress* *bpcx-req-conflict*)
             :identity-conflict)))
(must-fail (assert-event (bpcx-conflict-concl *bpcx-du-s* *bpcx-req-conflict-event*)))
;; next-op bound dropped (corrupted-state witness): at the terminal
;; operation ID the reception is refused :arguments.  Not reachable through
;; fn-bpnp-step: recovery resets next-op to 0 and each operation advances it
;; by one, so the terminal ID needs 2^64 operations in one epoch.
(defconst *bpcx-s1-terminal* (update-nth 9 *fn-frame-max-nat* *bpcx-s1*))
(must-fail (assert-event (bpcx-conflict-concl *bpcx-s1-terminal* *bpcx-n11-event*)))
;; epoch and next-op natp dropped (corrupted-state witnesses).  Neither is
;; reachable through fn-bpnp-step: the initial state has epoch 0 and next-op
;; 0, recovery admits only a fn-frame-natp new epoch and resets next-op to
;; 0, and next-op only grows by one below the bound above.
(must-fail (assert-event (bpcx-conflict-concl (update-nth 8 -1 *bpcx-s1*) *bpcx-n11-event*)))
(must-fail (assert-event (bpcx-conflict-concl (update-nth 9 -1 *bpcx-s1*) *bpcx-n11-event*)))
;; next-arrival natp dropped, REACHED through fn-bpnp-step: recovery admits
;; an arrival frontier of 2^64 (fn-bpnf-recover-fnbs-step bounds it by
;; *fn-frame-max-nat* + 1), so the recovered S1 keeps A held, has a frame
;; epoch and next-op 0, and next-arrival outside the frame.  The conflicting
;; reception then gets neither the refusal nor the record.
(defconst *bpcx-arrival-exhausted*
  (fn-bpnf-answer-state
   (fn-bpnp-step *bpcx-s1*
                 (list :recover-fnbs (1+ (fn-bpnf-epoch *bpcx-s1*)) nil :ready
                       (list :ready (fn-bpnf-held-list *bpcx-s1*) nil nil
                             (1+ *fn-frame-max-nat*))
                       (fn-bpnp-used *bpcx-s1*)))))
(assert-event
 (and (equal (fn-bpnf-held-list *bpcx-arrival-exhausted*) (fn-bpnf-held-list *bpcx-s1*))
      (not (fn-bpnf-issued *bpcx-arrival-exhausted*))
      (not (fn-bpah-delivery-uncertainp *bpcx-arrival-exhausted*))
      (fn-frame-natp (fn-bpnf-epoch *bpcx-arrival-exhausted*))
      (equal (fn-bpnf-next-op *bpcx-arrival-exhausted*) 0)
      (not (fn-frame-natp (fn-bpnf-next-arrival *bpcx-arrival-exhausted*)))
      (equal (fn-bpnf-receive-decision (fn-bpnf-held-list *bpcx-arrival-exhausted*)
                                       *bpcx-ingress* *bpcx-n11-bundle*)
             :identity-conflict)))
(assert-event (not (bpcx-conflict-concl *bpcx-arrival-exhausted* *bpcx-n11-event*)))
;; Event-kind hypothesis dropped: a six-field recovery event carrying the
;; conflicting bundle, its exact encoding and the ingress in the fields the
;; other hypotheses read satisfies every other hypothesis on S1, and the
;; step answers a restart outcome, neither the refusal nor the record.
(defconst *bpcx-n11-as-recovery*
  (list :recover-fnbs *bpcx-n11-bundle* (fn-bpb-encode *bpcx-n11-bundle*)
        *bpcx-ingress* (list :ready (fn-bpnf-held-list *bpcx-s1*) nil) 0))
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-n11-as-recovery*)
      (not (equal (fn-cbor-ag-car *bpcx-n11-as-recovery*) :receive-bundle))
      (equal (fn-bpn-nth 2 *bpcx-n11-as-recovery*)
             (fn-bpb-encode (fn-bpn-nth 1 *bpcx-n11-as-recovery*)))
      (equal (fn-bpnf-receive-decision (fn-bpnf-held-list *bpcx-s1*)
                                       (fn-bpn-nth 3 *bpcx-n11-as-recovery*)
                                       (fn-bpn-nth 1 *bpcx-n11-as-recovery*))
             :identity-conflict)))
(assert-event (not (bpcx-conflict-concl *bpcx-s1* *bpcx-n11-as-recovery*)))
;; wire = encoding dropped: other octets under the same bundle are invalid.
(defconst *bpcx-n11-badwire*
  (update-nth 2 (fn-bpb-encode *bpcx-a*) *bpcx-n11-event*))
(assert-event (fn-bpnp-host-eventp *bpcx-n11-badwire*))
(must-fail (assert-event (bpcx-conflict-concl *bpcx-s1* *bpcx-n11-badwire*)))
;; identity-conflict decision dropped: BP-R06's aged retransmission is a
;; duplicate, answered :duplicate with no record.
(must-fail
 (assert-event
  (bpcx-conflict-concl *bpcx-s1* (bpcx-receive-event (fn-bpb-encode *bpcx-a-aged*)))))
;; Credit conjunct: at exhausted journal credit the same reception gets the
;; refusal alone, never a record and never silence.
(defconst *bpcx-s1-full* (fn-bpnp-with-credit *bpcx-s1* *fn-bpnf-received-max-records* 0))
(assert-event
 (and (not (fn-bpnd-admitp (fn-bpnp-used *bpcx-s1-full*) (fn-bpnp-debt *bpcx-s1-full*)
                           *fn-bpnp-control-margin* 0 :spend))
      (equal (fn-bpnf-answer-effects (fn-bpnp-step *bpcx-s1-full* *bpcx-n11-event*))
             *bpcx-n11-refusal*)))
;; Teeth of fn-bpnp-step-conflict-publication-answers-refusal: a stale
;; operation ID changes nothing (operation-match dropped); a pending store
;; operation answers :stored, not the refusal (:conflict kind dropped).
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects
          (fn-bpnp-step *bpcx-n11-s* (list :persist-result (fn-bpnf-epoch *bpcx-s1*)
                                           (1+ (fn-bpnf-next-op *bpcx-s1*)) :durable)))
         *bpcx-n11-refusal*)))
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects (bpcx-durable *bpcx-a-proposal*))
         (list (list :receive-answer *bpcx-ingress* :identity-conflict)))))
;; status :pending dropped: the uncertain record fences; its persist result
;; is ignored.
(defconst *bpcx-n11-u* (fn-bpnf-answer-state (bpcx-n11-result :uncertain)))
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects
          (fn-bpnp-step *bpcx-n11-u* (list :persist-result (fn-bpnf-epoch *bpcx-s1*)
                                           (fn-bpnf-next-op *bpcx-s1*) :durable)))
         *bpcx-n11-refusal*)))

;; Kind-14 publication authority (fn-bpnf-conflict-publication-authorize,
;; host/native/bp-service.lisp fnn-bps-persist-kind-fourteen).  Keystone:
;; fn-bpnf-conflict-publication-success-binds-exact-echo.  Witness: the
;; reachable issued record of *bpcx-n11-s* is authorized at its stored
;; record name with the codec's frame.
(defun bpcx-n11-authorize (st epoch op record lock final-absent)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-conflict-publication-authorize st epoch op record lock final-absent))
(defconst *bpcx-n11-epoch* (fn-bpnf-epoch *bpcx-s1*))
(defconst *bpcx-n11-op* (fn-bpnf-next-op *bpcx-s1*))
(make-event
 `(defconst *bpcx-n11-auth*
    ',(bpcx-n11-authorize *bpcx-n11-s* *bpcx-n11-epoch* *bpcx-n11-op* *bpcx-n11-record* t t)))
(assert-event
 (and (fn-bpnf-operationp (fn-bpnf-issued *bpcx-n11-s*))
      (equal (fn-bpn-nth 3 (fn-bpnf-issued *bpcx-n11-s*)) :conflict)
      (fn-bpnf-conflict-publication-operationp *bpcx-n11-auth*)
      (equal (fn-bpnf-conflict-publication-name *bpcx-n11-auth*)
             (fn-bpnf-stored-record-name *bpcx-n11-epoch* *bpcx-n11-op*))
      (equal (fn-bpnf-conflict-publication-frame *bpcx-n11-auth*)
             (fn-bpnf-conflict-frame *bpcx-n11-record*))
      (equal (fn-bpnf-conflict-unframe
              (fn-bpnf-conflict-publication-frame *bpcx-n11-auth*))
             *bpcx-n11-record*)))
;; The issued :conflict operation is an fn-bpnf-operationp only because the
;; kind list names :conflict: the same row with an unlisted kind is not one.
(must-fail
 (assert-event
  (fn-bpnf-operationp (update-nth 3 :rotate (fn-bpnf-issued *bpcx-n11-s*)))))
;; Each binding the keystone concludes, broken alone, refuses authority:
;; lock not held, final name present, another operation id, another record,
;; the operation no longer pending (after an uncertain outcome), and a state
;; with nothing issued (S1).
(defun bpcx-auth-ok (answer)
  (declare (xargs :guard t))
  (equal (fn-cbor-ag-car answer) :ok))
(assert-event (not (bpcx-auth-ok (bpcx-n11-authorize *bpcx-n11-s* *bpcx-n11-epoch* *bpcx-n11-op* *bpcx-n11-record* nil t))))
(assert-event (not (bpcx-auth-ok (bpcx-n11-authorize *bpcx-n11-s* *bpcx-n11-epoch* *bpcx-n11-op* *bpcx-n11-record* t nil))))
(assert-event (not (bpcx-auth-ok (bpcx-n11-authorize *bpcx-n11-s* *bpcx-n11-epoch* (1+ *bpcx-n11-op*) *bpcx-n11-record* t t))))
(assert-event (not (bpcx-auth-ok (bpcx-n11-authorize *bpcx-n11-s* *bpcx-n11-epoch* *bpcx-n11-op*
                                                     (update-nth 3 7 *bpcx-n11-record*) t t))))
(assert-event (not (bpcx-auth-ok (bpcx-n11-authorize *bpcx-n11-u* *bpcx-n11-epoch* *bpcx-n11-op* *bpcx-n11-record* t t))))
(assert-event (not (bpcx-auth-ok (bpcx-n11-authorize *bpcx-s1* *bpcx-n11-epoch* *bpcx-n11-op* *bpcx-n11-record* t t))))

;; N07: a durable attempt (kind 8, S3), then a restart in a different boot:
;; the saved clock-domain record names boot A, this boot observes boot B.
;; The seven-field recovery event carries fn-bpnf-clock-domain-plan's
;; decision; the step fences before any retained Bundle Age anchor is
;; compared, keeps the attempt and every held row, and a later tick far
;; past the bundle's lifetime changes nothing.  The same trace in boot A
;; recovers.  Keystones: fn-bpnp-step-different-boot-fences,
;; fn-bpnp-step-domain-disagreement-fences,
;; fn-bpnp-step-ready-recovery-is-same-boot (bp-node-machine-gaps).
(defun bpcx-boot (last)
  (declare (xargs :guard t :verify-guards nil))
  (append (coerce "3f2504e0-4f89-41d3-9a0c-0305e82c330" 'list) (list last)))
(defun bpcx-octets (chars)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom chars) nil
    (cons (if (characterp (car chars)) (char-code (car chars)) 0)
          (bpcx-octets (cdr chars)))))
(make-event `(defconst *bpcx-boot-a* ',(bpcx-octets (bpcx-boot #\1))))
(make-event `(defconst *bpcx-boot-b* ',(bpcx-octets (bpcx-boot #\2))))
(make-event `(defconst *bpcx-observed-a* ',(append *bpcx-boot-a* '(10))))
(make-event `(defconst *bpcx-observed-b* ',(append *bpcx-boot-b* '(10))))
(make-event `(defconst *bpcx-saved-a* ',(fn-bpcd-frame *bpcx-boot-a*)))
(defun bpcx-domain-event (plan)
  (declare (xargs :guard t :verify-guards nil))
  (append *bpcx-n08-recover-event* (list plan)))
(make-event `(defconst *bpcx-plan-b*
 ',(fn-bpnf-clock-domain-plan *bpcx-saved-a* t *bpcx-observed-b* nil t nil)))
(make-event `(defconst *bpcx-plan-a*
 ',(fn-bpnf-clock-domain-plan *bpcx-saved-a* t *bpcx-observed-a* nil t nil)))
(make-event `(defconst *bpcx-n07* ',(fn-bpnp-step *bpcx-s3* (bpcx-domain-event *bpcx-plan-b*))))
(make-event `(defconst *bpcx-n07-s* ',(fn-bpnf-answer-state *bpcx-n07*)))
(make-event `(defconst *bpcx-n07-same* ',(fn-bpnp-step *bpcx-s3* (bpcx-domain-event *bpcx-plan-a*))))
(make-event `(defconst *bpcx-late-tick*
 ',(list :progress *bpcx-local* *bpcx-late-obs* *bpcx-routes* 1)))
(assert-event
 (and (fn-bpnp-host-eventp (bpcx-domain-event *bpcx-plan-b*))
      (fn-bpnp-domain-recover-eventp (bpcx-domain-event *bpcx-plan-b*))
      (fn-bpcd-unframe *bpcx-saved-a*)
      (fn-bpcd-observed-id *bpcx-observed-b*)
      (not (equal (fn-bpcd-unframe *bpcx-saved-a*) (fn-bpcd-observed-id *bpcx-observed-b*)))
      (equal *bpcx-plan-b* '(:fence :different-boot))
      (equal (fn-bpnf-answer-effects *bpcx-n07*)
             '((:restart-fault :clock-domain :different-boot)))
      (equal (fn-bpnf-held-list *bpcx-n07-s*) (fn-bpnf-held-list *bpcx-s3*))
      (equal (fn-bpn-nth 0 (fn-bpn-nth 13 (car (fn-bpnf-held-list *bpcx-n07-s*))))
             :forwarding)
      (equal (fn-bpnp-held-expiry (car (fn-bpnf-held-list *bpcx-s3*)) *bpcx-late-obs*)
             :expired)
      (fn-bpnp-host-eventp *bpcx-late-tick*)
      (equal (fn-bpnp-step *bpcx-n07-s* *bpcx-late-tick*) (fn-bpnf-answer *bpcx-n07-s* nil))
      (equal (fn-bpnp-step *bpcx-n07-s* *bpcx-session-event*)
             (fn-bpnf-answer *bpcx-n07-s* nil))
      ;; a later recovery in boot A is still admitted
      (equal (car (car (fn-bpnf-answer-effects
                        (fn-bpnp-step *bpcx-n07-s* (bpcx-domain-event *bpcx-plan-a*)))))
             :restart-ready)
      (equal (car (car (fn-bpnf-answer-effects *bpcx-n07-same*))) :restart-ready)))
;; Teeth of fn-bpnp-step-different-boot-fences, one per hypothesis.
(defun bpcx-fences-different-boot (event)
  (declare (xargs :guard t :verify-guards nil))
  (equal (fn-bpnf-answer-effects (fn-bpnp-step *bpcx-s3* event))
         '((:restart-fault :clock-domain :different-boot))))
(assert-event (bpcx-fences-different-boot (bpcx-domain-event *bpcx-plan-b*)))
;; seven-field event dropped: the six-field recovery carries no domain and
;; recovers across the boot change (why the host must pass the decision).
(must-fail (assert-event (bpcx-fences-different-boot *bpcx-n08-recover-event*)))
;; plan equality dropped: an event claiming (:same A) while boot B observed.
(must-fail (assert-event (bpcx-fences-different-boot
                          (bpcx-domain-event (list :same *bpcx-boot-a*)))))
;; present dropped: no saved record, legacy rows present.
(must-fail (assert-event (bpcx-fences-different-boot
                          (bpcx-domain-event
                           (fn-bpnf-clock-domain-plan nil nil *bpcx-observed-b* t t t)))))
;; saved record decodes dropped: damaged saved bytes.
(must-fail (assert-event (bpcx-fences-different-boot
                          (bpcx-domain-event
                           (fn-bpnf-clock-domain-plan '(1 2 3) t *bpcx-observed-b* nil t nil)))))
;; observed ID decodes dropped: an observation without its LF.
(must-fail (assert-event (bpcx-fences-different-boot
                          (bpcx-domain-event
                           (fn-bpnf-clock-domain-plan *bpcx-saved-a* t *bpcx-boot-b* nil t nil)))))
;; the IDs differ dropped: the same boot recovers.
(must-fail (assert-event (bpcx-fences-different-boot (bpcx-domain-event *bpcx-plan-a*))))
;; Teeth of fn-bpnp-step-ready-recovery-is-same-boot: with boot B observed
;; and boot A saved (conclusion false), a ready answer needs each
;; hypothesis dropped: the six-field event, or an event whose domain is not
;; the plan of those observations.
(must-fail
 (assert-event
  (not (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpnp-step *bpcx-s3* *bpcx-n08-recover-event*))))
              :restart-ready))))
(must-fail
 (assert-event
  (not (equal (car (car (fn-bpnf-answer-effects
                         (fn-bpnp-step *bpcx-s3* (bpcx-domain-event
                                                  (list :same *bpcx-boot-a*))))))
              :restart-ready))))
;; ready dropped: the different-boot answer is the fence.
(assert-event (not (equal (car (car (fn-bpnf-answer-effects *bpcx-n07*))) :restart-ready)))
;; Teeth of fn-bpnp-step-domain-disagreement-fences: admitted domain (:same)
;; is not fenced; a six-field event is not fenced.
(must-fail
 (assert-event
  (equal (car (car (fn-bpnf-answer-effects *bpcx-n07-same*))) :restart-fault)))
(must-fail
 (assert-event
  (equal (car (car (fn-bpnf-answer-effects *bpcx-n08-recovered*))) :restart-fault)))
;; :initialize admits only a recovery with nothing retained.
(assert-event
 (and (fn-bpnp-clock-domain-admitsp
       (list :recover-fnbs 1 nil :ready '(:ready nil nil) 0 '(:initialize (1) nil)))
      (not (fn-bpnp-clock-domain-admitsp
            (bpcx-domain-event '(:initialize (1) nil))))))

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
      (equal (car (car (fn-bpnf-answer-effects *bpcx-r07*))) :persist-conflict)
      (equal (fn-bpnf-answer-effects (bpcx-durable *bpcx-r07*))
             (list (list :receive-answer *bpcx-ingress* :identity-conflict)))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpcx-r07*))
             (fn-bpnf-held-list *bpcx-s1*))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state (bpcx-durable *bpcx-r07*)))
             (fn-bpnf-held-list *bpcx-s1*))))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects *bpcx-r06*))) :identity-conflict)))
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-effects (bpcx-durable *bpcx-r07*))
         (list (list :receive-answer *bpcx-ingress* :duplicate)))))

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
;; BP-R17: the owner answers a local delivery busy.  The row stays held
;; and :dispatch-pending, nothing is proposed, and class 3 offers it again
;; after the backoff; at the kind-8 retry bound it is stranded, still held,
;; and not offered until recovery clears the volatile wait.
(defun bpcx-obs-at (m) (fn-clock-observation m 0 0 nil))
(defun bpcx-busy-event (deliver-answer m)
  (let ((effect (car (fn-bpnf-answer-effects deliver-answer))))
    (list :deliver-result (fn-bpn-nth 1 effect) (fn-bpn-nth 2 effect)
          (fn-bpn-nth 3 effect) :busy '(0) (bpcx-obs-at m))))
(defun bpcx-tick (st m)
  (fn-bpnp-step st (list :progress *bpcx-local* (bpcx-obs-at m) nil 0)))
(defconst *bpcx-r17-d1* (fn-bpnf-answer-state *bpcx-deliver*))
(defconst *bpcx-r17-busy1-event* (bpcx-busy-event *bpcx-deliver* 1000))
(defconst *bpcx-r17-busy1* (fn-bpnp-step *bpcx-r17-d1* *bpcx-r17-busy1-event*))
(defconst *bpcx-r17-b1* (fn-bpnf-answer-state *bpcx-r17-busy1*))
(defconst *bpcx-r17-early* (bpcx-tick *bpcx-r17-b1* 3000))
(defconst *bpcx-r17-redeliver2* (bpcx-tick *bpcx-r17-b1* 6000))
(defconst *bpcx-r17-busy2*
  (fn-bpnp-step (fn-bpnf-answer-state *bpcx-r17-redeliver2*)
                (bpcx-busy-event *bpcx-r17-redeliver2* 6000)))
(defconst *bpcx-r17-redeliver3*
  (bpcx-tick (fn-bpnf-answer-state *bpcx-r17-busy2*) 11000))
(defconst *bpcx-r17-busy3*
  (fn-bpnp-step (fn-bpnf-answer-state *bpcx-r17-redeliver3*)
                (bpcx-busy-event *bpcx-r17-redeliver3* 11000)))
(defconst *bpcx-r17-b3* (fn-bpnf-answer-state *bpcx-r17-busy3*))
(defconst *bpcx-r17-late* (bpcx-tick *bpcx-r17-b3* 60000))
(defconst *bpcx-r17-key* (fn-bpn-nth 3 *bpcx-r17-busy1-event*))

(defun bpcx-busy-defers-p (st event)
  (let* ((ans (fn-bpnp-step st event))
         (key (fn-bpn-nth 3 event))
         (wait (fn-bpnp-busy-wait key (fn-bpnp-waits st) (fn-bpn-nth 6 event))))
    (and (equal (fn-bpnf-answer-state ans)
                (update-nth 11 (cons wait (fn-bpnp-remove-wait
                                           key (fn-bpnp-waits st)))
                            (update-nth 7 nil st)))
         (equal (fn-bpnf-held-list (fn-bpnf-answer-state ans))
                (fn-bpnf-held-list st))
         (null (fn-bpnf-issued (fn-bpnf-answer-state ans)))
         (member-equal (car (car (fn-bpnf-answer-effects ans)))
                       '(:delivery-deferred :delivery-stranded)))))

;; Positive: the keystone's full antecedent and conclusion on the reached
;; busy answer, then redelivery after the backoff and the stranded bound.
(assert-event
 (and (fn-bpnp-host-eventp *bpcx-r17-busy1-event*)
      (fn-bpnp-busy-eventp *bpcx-r17-busy1-event*)
      (true-listp *bpcx-r17-d1*)
      (equal (fn-bpnf-waits *bpcx-r17-d1*)
             (list :delivery (fn-bpn-nth 1 *bpcx-r17-busy1-event*)
                   (fn-bpn-nth 2 *bpcx-r17-busy1-event*) *bpcx-r17-key*))
      (equal (fn-bpnf-epoch *bpcx-r17-d1*) (fn-bpn-nth 1 *bpcx-r17-busy1-event*))
      (null (fn-bpnf-issued *bpcx-r17-d1*))
      (bpcx-busy-defers-p *bpcx-r17-d1* *bpcx-r17-busy1-event*)
      (equal (fn-bpnf-answer-effects *bpcx-r17-busy1*)
             (list (list :delivery-deferred *bpcx-r17-key* 1 6000)))
      ;; held, pending, nothing proposed; the handoffs are untouched
      (equal (fn-bpnf-held-list *bpcx-r17-b1*) (fn-bpnf-held-list *bpcx-q1*))
      (equal (fn-bpnf-handoffs *bpcx-r17-b1*) (fn-bpnf-handoffs *bpcx-q1*))
      ;; before the backoff: nothing; after it: the same row is offered
      (null (fn-bpnf-answer-effects *bpcx-r17-early*))
      (equal (car (car (fn-bpnf-answer-effects *bpcx-r17-redeliver2*))) :deliver)
      (equal (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bpcx-r17-redeliver2*)))
             *bpcx-r17-key*)
      (equal (fn-bpnf-answer-effects *bpcx-r17-busy2*)
             (list (list :delivery-deferred *bpcx-r17-key* 2 11000)))
      ;; the third busy answer reaches the kind-8 bound: stranded, held
      (equal (fn-bpnf-answer-effects *bpcx-r17-busy3*)
             (list (list :delivery-stranded *bpcx-r17-key*
                         *fn-bpnp-max-forward-retries*)))
      (equal (fn-bpnf-held-list *bpcx-r17-b3*) (fn-bpnf-held-list *bpcx-q1*))
      (null (fn-bpnf-answer-effects *bpcx-r17-late*))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpcx-r17-late*))
             (fn-bpnf-held-list *bpcx-q1*))
      ;; recovery clears the volatile wait and the row is offered again
      (equal (car (car (fn-bpnf-answer-effects
                        (bpcx-tick (bpcx-recover *bpcx-r17-b3* 1) 60000))))
             :deliver)))

;; Teeth of fn-bpnp-step-busy-delivery-defers, one per hypothesis.
;; busy-eventp dropped: the six-field busy event (no observation) reaches
;; the foundation, which answers the host :refused and keeps the marker.
(must-fail
 (assert-event
  (bpcx-busy-defers-p *bpcx-r17-d1* (take 6 *bpcx-r17-busy1-event*))))
;; the same with an :uncertain outcome: the delivery-uncertain fence.
(must-fail
 (assert-event
  (bpcx-busy-defers-p *bpcx-r17-d1*
                      (update-nth 4 :uncertain *bpcx-r17-busy1-event*))))
;; marker dropped: the event names another operation id.
(must-fail
 (assert-event
  (bpcx-busy-defers-p *bpcx-r17-d1*
                      (update-nth 2 (1+ (fn-bpn-nth 2 *bpcx-r17-busy1-event*))
                                  *bpcx-r17-busy1-event*))))
;; epoch dropped: marker and event agree on an epoch the state is not in.
(must-fail
 (assert-event
  (let ((e2 (update-nth 1 (1+ (fn-bpn-nth 1 *bpcx-r17-busy1-event*))
                        *bpcx-r17-busy1-event*)))
    (bpcx-busy-defers-p
     (update-nth 7 (list :delivery (fn-bpn-nth 1 e2) (fn-bpn-nth 2 e2)
                         (fn-bpn-nth 3 e2))
                 *bpcx-r17-d1*)
     e2))))
;; issued dropped: a pending operation is issued.
(must-fail
 (assert-event
  (bpcx-busy-defers-p
   (update-nth 6 (fn-bpnf-operation (fn-bpnf-epoch *bpcx-r17-d1*) 99
                                    :store nil :pending)
               *bpcx-r17-d1*)
   *bpcx-r17-busy1-event*)))
;; true-listp dropped (corrupted state, not reachable): a dotted state.
(must-fail
 (assert-event
  (bpcx-busy-defers-p (append *bpcx-r17-d1* 7) *bpcx-r17-busy1-event*)))
;; Teeth of fn-bpnp-busy-deferral-ends-at-its-reading: the reading before m
;; holds the row back (the early tick above answered nothing), and at the
;; bound it is held back at every reading.
(assert-event
 (let ((h (car (fn-bpnf-held-list *bpcx-r17-b1*))))
   (and (fn-bpnp-busy-blockedp h (fn-bpnp-waits *bpcx-r17-b1*) (bpcx-obs-at 5999))
        (not (fn-bpnp-busy-blockedp h (fn-bpnp-waits *bpcx-r17-b1*)
                                    (bpcx-obs-at 6000))))))
(must-fail
 (assert-event
  (not (fn-bpnp-busy-blockedp (car (fn-bpnf-held-list *bpcx-r17-b1*))
                              (fn-bpnp-waits *bpcx-r17-b1*) (bpcx-obs-at 5999)))))
(must-fail
 (assert-event
  (not (fn-bpnp-busy-blockedp (car (fn-bpnf-held-list *bpcx-r17-b3*))
                              (fn-bpnp-waits *bpcx-r17-b3*) (bpcx-obs-at 60000)))))
;; Tooth of fn-bpnp-busy-stranded-row-is-not-offered: under the bound the
;; deferred row is the selection once its reading is reached.
(must-fail
 (assert-event
  (null (fn-bpnf-answer-effects *bpcx-r17-redeliver2*))))

;; ---------------------------------------------------------------------
;; Coverage of spec 11.1 over this machine (each row names its subject).
;; Present here: N05, N06 (machine half), N07 (the seven-field recovery
;; event, which the host builds at bp-service.lisp fnn-bps-open with the
;; decision fnn-bps-clock-domain-gate returns; the six-field form stays
;; ungated for callers that pass no decision), N08, N11 (both halves, and
;; the kind-14 publication authority), BP-R02, R06, R07, R15, R16, BP-R17
;; (the seven-field busy delivery event, bp-node-busy-delivery; the host
;; issues it at bp-node.lisp fnn-bpnode-dispatch-one).
;; Present elsewhere: N03 (bp-node-machine-teeth-tests), N04
;; (bp-node-forwarding-teeth-tests), N09 (bp-fragment-tests), N15
;; unlabelled (bp-channel-ingress-tests, fn-bpaj-tcpcl-ingress-result).
;; Not expressible through fn-bpnp-step today, missing transition named:
;;   N01, N13, BP-R03..R05, R19: application join and FNRJ receipt outbox
;;     (bp-native-app / workflow), not a node-machine event.
;;   N02, BP-R08, R09: workflow overdue/retry (bp-workflow), no node event.
;;   N06 physical half: FNBS byte-store publisher relation and crash cuts.
;;   N08: recovery settlement of a replayed kind-8 row (asserted above as
;;     the stranded behaviour).
;;   N10: machine-level reassembly order (slice C2).
;;   N12, BP-R10: TCPCL segment/END ACK machine (tcpcl books).
;;   N14: Store pin release join (bp-release).
;;   N16, BP-R21: journal rotation (slice E), no generation transition.
;;   N17, BP-R23: codec seam / cross-implementation vectors, not a trace.
;;   N18, BP-R24: owner-progress monitor and bounded service turn (slice B).
;;   BP-R01: FNWF scheduler persistence (scheduler, no native caller).
;;   BP-R11..R13, R22: fragment family capacity, crash prefixes, scaling.
;;   BP-R14: route change against historical replay (no route in replay
;;     input; the replay half needs the ordered-row scan, not a fixture).
;;   BP-R18, R20: local report processing and reverse relay routing.
