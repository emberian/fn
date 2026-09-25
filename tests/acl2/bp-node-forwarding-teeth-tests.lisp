; N04/N05 forwarding fixtures use actual received kind-5 rows and the outer
; host-called FNBS step.  The later assertions in this book exercise kind
; 6/8/9 once the forwarding extension is present.
(in-package "ACL2")
(include-book "../../books/bp-node-progress")
(include-book "../../books/bp-node-debt")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpfx-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpfx-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpfx-dest* (cons :dtn '(47 47 98 112 45 100 101 115 116 47)))
(defconst *bpfx-config* (fn-bpn-config *bpfx-local* 3600000 2 32 1048576))
(defconst *bpfx-sender-config*
  (fn-bpn-config *bpfx-sender* 3600000 2 32 1048576))
(defconst *bpfx-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bpfx-ingress*
  (list :cl (cons 0 1) 1 *bpfx-sender* '(115 101 110 100 101 114) 0))

; The older entry is inside the 131072-octet held-image bound but cannot fit
; a 32768-octet session MRU.  Its no-fragment flag makes this a real MRU wait
; even when a later fragmentation policy is enabled.  The younger entry fits.
(defconst *bpfx-old-base*
  (fn-bpn-send-bundle *bpfx-sender-config* *bpfx-dest*
                      (make-list 49152 :initial-element 65)
                      7 *bpfx-observation*))
(defconst *bpfx-old-bundle*
  (fn-bpb-make-bundle
   (update-nth 1 *fn-bpp-flag-no-fragment*
               (fn-bpb-bundle-primary *bpfx-old-base*))
   (fn-bpb-bundle-blocks *bpfx-old-base*)
   (fn-bpb-bundle-payload *bpfx-old-base*)))
(defconst *bpfx-new-bundle*
  (fn-bpn-send-bundle *bpfx-sender-config* *bpfx-dest*
                      (make-list 8192 :initial-element 66)
                      8 *bpfx-observation*))
(defconst *bpfx-old-wire* (fn-bpb-encode *bpfx-old-bundle*))
(defconst *bpfx-new-wire* (fn-bpb-encode *bpfx-new-bundle*))

(assert-event
 (and (fn-bpb-bundlep *bpfx-old-bundle*)
      (fn-bpb-bundlep *bpfx-new-bundle*)
      (fn-bpp-no-fragmentp
       (fn-bpp-flags (fn-bpb-bundle-primary *bpfx-old-bundle*)))
      (> (len *bpfx-old-wire*) 32768)
      (<= (len *bpfx-old-wire*) *fn-bpnf-max-held-image*)
      (< (len *bpfx-new-wire*) 32768)
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpfx-config* *bpfx-old-wire* *bpfx-observation* *bpfx-ingress*))
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpfx-config* *bpfx-new-wire* *bpfx-observation* *bpfx-ingress*))))

(defun bpfx-durable-receive (st wire)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((prepared (fn-bpnf-receive-wire-event
                    *bpfx-config* wire *bpfx-observation* *bpfx-ingress*))
         (proposed (fn-bpnp-step
                    st (fn-bpnf-receive-wire-event-value prepared)))
         (effect (car (fn-bpnf-answer-effects proposed))))
    (if (and (fn-bpnf-receive-wire-readyp prepared)
             (equal (car effect) :persist))
        (fn-bpnf-answer-state
         (fn-bpnp-step
          (fn-bpnf-answer-state proposed)
          (list :persist-result (fn-bpn-nth 1 effect)
                (fn-bpn-nth 2 effect) :durable)))
      st)))

(defconst *bpfx-raw-s0* (fn-bpnf-initial-state *bpfx-config* 8 1048576))
(defconst *bpfx-boot-event*
  (fn-bpnf-family-recover-auto-event *bpfx-raw-s0* nil :ready nil))
(defconst *bpfx-boot* (fn-bpnp-step *bpfx-raw-s0* *bpfx-boot-event*))
(defconst *bpfx-s0* (fn-bpnf-answer-state *bpfx-boot*))
(assert-event
 (and (fn-bpnp-host-eventp *bpfx-boot-event*)
      (equal (car (car (fn-bpnf-answer-effects *bpfx-boot*)))
             :restart-ready)
      (equal (fn-bpnp-used *bpfx-s0*) 0)
      (equal (fn-bpnp-debt *bpfx-s0*) 0)))
(defconst *bpfx-s1* (bpfx-durable-receive *bpfx-s0* *bpfx-old-wire*))
(defconst *bpfx-s2* (bpfx-durable-receive *bpfx-s1* *bpfx-new-wire*))
(defconst *bpfx-old-held* (second (fn-bpnf-held-list *bpfx-s2*)))
(defconst *bpfx-new-held* (first (fn-bpnf-held-list *bpfx-s2*)))

(assert-event
 (and (equal (len (fn-bpnf-held-list *bpfx-s2*)) 2)
      (equal (fn-bpn-nth 3 *bpfx-old-held*) 0)
      (equal (fn-bpn-nth 3 *bpfx-new-held*) 1)
      (not (fn-bpnf-issued *bpfx-s2*))
      (equal (fn-bpnd-held-debt *bpfx-old-held* *bpfx-local*) 2)
      (equal (fn-bpnd-held-debt *bpfx-new-held* *bpfx-local*) 2)))

; Both received rows become forward-pending only after their own durable
; kind-6 finals.  This trace enters the same outer step called by bp-service.
(defconst *bpfx-routes* (list (list *bpfx-dest* *bpfx-dest*)))
(defconst *bpfx-progress-event*
  (list :progress *bpfx-local* *bpfx-observation* *bpfx-routes* 1))
(make-event
 `(defconst *bpfx-old-dispatch*
    ',(fn-bpnp-step *bpfx-s2* *bpfx-progress-event*)))
(defconst *bpfx-old-dispatch-effect*
  (car (fn-bpnf-answer-effects *bpfx-old-dispatch*)))
(defconst *bpfx-s3-answer*
  (fn-bpnp-step
   (fn-bpnf-answer-state *bpfx-old-dispatch*)
   (list :persist-result (fn-bpn-nth 1 *bpfx-old-dispatch-effect*)
         (fn-bpn-nth 2 *bpfx-old-dispatch-effect*) :durable)))
(defconst *bpfx-s3* (fn-bpnf-answer-state *bpfx-s3-answer*))
(make-event
 `(defconst *bpfx-new-dispatch*
    ',(fn-bpnp-step *bpfx-s3* *bpfx-progress-event*)))
(defconst *bpfx-new-dispatch-effect*
  (car (fn-bpnf-answer-effects *bpfx-new-dispatch*)))
(defconst *bpfx-s4-answer*
  (fn-bpnp-step
   (fn-bpnf-answer-state *bpfx-new-dispatch*)
   (list :persist-result (fn-bpn-nth 1 *bpfx-new-dispatch-effect*)
         (fn-bpn-nth 2 *bpfx-new-dispatch-effect*) :durable)))
(defconst *bpfx-s4* (fn-bpnf-answer-state *bpfx-s4-answer*))

(assert-event
 (and (fn-bpnp-host-eventp *bpfx-progress-event*)
      (equal (car *bpfx-old-dispatch-effect*) :persist-dispatch)
      (equal (fn-bpn-nth 3 (fn-bpn-nth 3 *bpfx-old-dispatch-effect*)) 0)
      (equal (car (car (fn-bpnf-answer-effects *bpfx-s3-answer*)))
             :dispatch-ready)
      (equal (car *bpfx-new-dispatch-effect*) :persist-dispatch)
      (equal (fn-bpn-nth 3 (fn-bpn-nth 3 *bpfx-new-dispatch-effect*)) 1)
      (equal (car (car (fn-bpnf-answer-effects *bpfx-s4-answer*)))
             :dispatch-ready)
      (equal (fn-bpnp-used *bpfx-s4*) 4)
      (equal (fn-bpnp-debt *bpfx-s4*) 4)
      (equal (fn-bpnp-debt *bpfx-s4*)
             (fn-bpnd-debt *bpfx-s4* *bpfx-local*))))

; The live :session event scans oldest first.  The no-fragment older row
; cannot fit this MRU, so its volatile per-key wait is retained while the
; younger row proposes a kind-8 attempt on the same session.  No debt is
; spent until the kind-8 final is durable.
(defconst *bpfx-session* (cons 1 1))
;; The routed session (spec 4.6): the host opens an outbound session only to
;; the boundary the route table names, and a :session without VIA offers
;; nothing.  This fixture's table sends dtn://bp-dest/ to the boundary "relay".
(defconst *bpfx-via*
  (list :via "relay" (fn-record-string-octets "dtn://relay/")
        (list (fn-bprt-route 100 "dtn://bp-dest/" "relay" "dtn://relay/" 4556))))
(defconst *bpfx-session-event*
  (list :session *bpfx-dest* *bpfx-session* t 32768 *bpfx-observation* *bpfx-via*))
(make-event
 `(defconst *bpfx-open*
    ',(fn-bpnp-step *bpfx-s4* *bpfx-session-event*)))
(defconst *bpfx-attempt-effect*
  (car (fn-bpnf-answer-effects *bpfx-open*)))
(defconst *bpfx-attempt-record* (fn-bpn-nth 3 *bpfx-attempt-effect*))
(assert-event
 (and (fn-bpnp-host-eventp *bpfx-session-event*)
      (equal (car *bpfx-attempt-effect*) :persist-attempt)
      (equal (fn-bpn-nth 3 *bpfx-attempt-record*) 1)
      (equal (fn-bpn-nth 2
                         (fn-bpnp-wait-for
                          (fn-bpnp-wait-key *bpfx-old-held*)
                          (fn-bpnp-waits (fn-bpnf-answer-state *bpfx-open*))))
             :mru)
      (equal (fn-bpnp-used (fn-bpnf-answer-state *bpfx-open*)) 4)
      (equal (fn-bpnp-debt (fn-bpnf-answer-state *bpfx-open*)) 4)))

; At an MRU that fits the no-fragment older image, the age priority reverses
; the selected arrival.  The small-MRU younger selection is therefore a
; consequence of the negotiated limit, not the held-list storage order.
(defconst *bpfx-wide-session-event*
  (list :session *bpfx-dest* *bpfx-session* t 65536 *bpfx-observation* *bpfx-via*))
(make-event
 `(defconst *bpfx-wide-open*
    ',(fn-bpnp-step *bpfx-s4* *bpfx-wide-session-event*)))
(assert-event
 (and (equal (car (car (fn-bpnf-answer-effects *bpfx-wide-open*)))
             :persist-attempt)
      (equal (fn-bpn-nth
              3 (fn-bpn-nth
                 3 (car (fn-bpnf-answer-effects *bpfx-wide-open*))))
             0)))
(must-fail
 (assert-event
  (equal (fn-bpn-nth 3 *bpfx-attempt-record*)
         (fn-bpn-nth
          3 (fn-bpn-nth
             3 (car (fn-bpnf-answer-effects *bpfx-wide-open*)))))))
(defconst *bpfx-s5-answer*
  (fn-bpnp-step
   (fn-bpnf-answer-state *bpfx-open*)
   (list :persist-result (fn-bpn-nth 1 *bpfx-attempt-effect*)
         (fn-bpn-nth 2 *bpfx-attempt-effect*) :durable)))
(defconst *bpfx-s5* (fn-bpnf-answer-state *bpfx-s5-answer*))
(defconst *bpfx-send-effect*
  (car (fn-bpnf-answer-effects *bpfx-s5-answer*)))
(assert-event
 (and (equal (car *bpfx-send-effect*) :cl-send)
      (< (len (fn-bpn-nth 6 *bpfx-send-effect*)) 32768)
      (equal (fn-bpnp-used *bpfx-s5*) 5)
      (equal (fn-bpnp-debt *bpfx-s5*) 5)
      (equal (fn-bpnp-debt *bpfx-s5*)
             (fn-bpnd-debt *bpfx-s5* *bpfx-local*))
      (equal (fn-bpn-nth 12
                         (fn-bpnf-find-arrival 0 (fn-bpnf-held-list *bpfx-s5*)))
             '(:forward-pending))
      (equal (fn-bpn-nth 0
                         (fn-bpn-nth 13
                                     (fn-bpnf-find-arrival
                                      1 (fn-bpnf-held-list *bpfx-s5*))))
             :forwarding)))

; A carrier result is a proposal until its own kind-9 final.  Only the
; durable :sent result closes the younger row and pays its attempt debt.
(defconst *bpfx-result-event*
  (list :forward-result
        (fn-bpn-nth 1 *bpfx-attempt-effect*)
        (fn-bpn-nth 2 *bpfx-attempt-effect*)
        *bpfx-session* :sent *bpfx-observation*))
(make-event
 `(defconst *bpfx-result-proposal*
    ',(fn-bpnp-step *bpfx-s5* *bpfx-result-event*)))
(defconst *bpfx-result-effect*
  (car (fn-bpnf-answer-effects *bpfx-result-proposal*)))
(defconst *bpfx-s6-answer*
  (fn-bpnp-step
   (fn-bpnf-answer-state *bpfx-result-proposal*)
   (list :persist-result (fn-bpn-nth 1 *bpfx-result-effect*)
         (fn-bpn-nth 2 *bpfx-result-effect*) :durable)))
(defconst *bpfx-s6* (fn-bpnf-answer-state *bpfx-s6-answer*))
(assert-event
 (and (fn-bpnp-host-eventp *bpfx-result-event*)
      (equal (car *bpfx-result-effect*) :persist-forward-result)
      (equal (fn-bpnp-used
              (fn-bpnf-answer-state *bpfx-result-proposal*)) 5)
      (equal (fn-bpnp-debt
              (fn-bpnf-answer-state *bpfx-result-proposal*)) 5)
      (equal (car (car (fn-bpnf-answer-effects *bpfx-s6-answer*)))
             :forward-ready)
      (equal (fn-bpnp-used *bpfx-s6*) 6)
      (equal (fn-bpnp-debt *bpfx-s6*) 3)
      (equal (fn-bpnp-debt *bpfx-s6*)
             (fn-bpnd-debt *bpfx-s6* *bpfx-local*))
      (equal (fn-bpn-nth 12
                         (fn-bpnf-find-arrival 0 (fn-bpnf-held-list *bpfx-s6*)))
             '(:forward-pending))
      (equal (fn-bpn-nth 12
                         (fn-bpnf-find-arrival 1 (fn-bpnf-held-list *bpfx-s6*)))
             '(:dispatch-done))))
