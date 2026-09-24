; A1 progress teeth start from the event admitted by the native BP boundary.
; These are reachable kind-5 receive/publication traces, not hand-built held
; rows.  The progress trace uses fn-bpnp-step, the native host's outer call.
(in-package "ACL2")
(include-book "../../books/bp-node-progress-selection-invariants")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnmt-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpnmt-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpnmt-unrouted* (cons :dtn '(47 47 98 112 45 111 116 104 101 114 47)))
(defconst *bpnmt-local-config*
  (fn-bpn-config *bpnmt-local* 3600000 2 32 1048576))
(defconst *bpnmt-sender-config*
  (fn-bpn-config *bpnmt-sender* 3600000 2 32 1048576))
(defconst *bpnmt-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnmt-ingress*
  (list :cl (cons 0 1) 1 *bpnmt-sender* '(115 101 110 100 101 114) 0))
(defconst *bpnmt-request*
  (fn-bpa-encode
   (fn-bpa-make-request "w" "s" "dtn://bp-sender/" "dtn://bp-local/"
                        "p" "i" "c" "t" '(88 13 10))))
(defconst *bpnmt-n03-old*
  (fn-bpn-send-bundle *bpnmt-sender-config* *bpnmt-unrouted*
                      '(1 2 3 4) 7 *bpnmt-observation*))
(defconst *bpnmt-n03-new*
  (fn-bpn-send-bundle *bpnmt-sender-config* *bpnmt-local*
                      *bpnmt-request* 8 *bpnmt-observation*))

(defun bpnmt-durable-receive (st bundle ingress observation)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((prepared (fn-bpnf-receive-wire-event
                    *bpnmt-local-config* (fn-bpb-encode bundle)
                    observation ingress))
         (proposal (fn-bpnp-step
                    st (fn-bpnf-receive-wire-event-value prepared)))
         (effect (car (fn-bpnf-answer-effects proposal)))
         (issued (fn-bpnf-answer-state proposal)))
    (if (and (fn-bpnf-receive-wire-readyp prepared)
             (equal (car effect) :persist)
             (equal (fn-bpn-nth 3 (fn-bpnf-issued issued)) :store))
        (fn-bpnf-answer-state
         (fn-bpnp-step
          issued (list :persist-result (fn-bpn-nth 1 effect)
                       (fn-bpn-nth 2 effect) :durable)))
      st)))

(defconst *bpnmt-n03-raw-s0*
  (fn-bpnf-initial-state *bpnmt-local-config* 8 1048576))
(defconst *bpnmt-n03-boot-event*
  (fn-bpnf-family-recover-auto-event *bpnmt-n03-raw-s0*
                                      nil :ready nil))
(defconst *bpnmt-n03-boot*
  (fn-bpnp-step *bpnmt-n03-raw-s0* *bpnmt-n03-boot-event*))
(defconst *bpnmt-n03-s0*
  (fn-bpnf-answer-state *bpnmt-n03-boot*))
(assert-event
 (and (fn-bpnp-host-eventp *bpnmt-n03-boot-event*)
      (equal (car (car (fn-bpnf-answer-effects *bpnmt-n03-boot*)))
             :restart-ready)
      (equal (fn-bpnp-used *bpnmt-n03-s0*) 0)
      (equal (fn-bpnp-debt *bpnmt-n03-s0*) 0)))
(defconst *bpnmt-n03-s1*
  (bpnmt-durable-receive *bpnmt-n03-s0* *bpnmt-n03-old*
                         *bpnmt-ingress* *bpnmt-observation*))
(defconst *bpnmt-n03-s2*
  (bpnmt-durable-receive *bpnmt-n03-s1* *bpnmt-n03-new*
                         *bpnmt-ingress* *bpnmt-observation*))

; N03's entire receive antecedent is asserted before any progress claim:
; the older transit bundle and newer local request are both admitted by the
; production receive boundary and durably held, with no issued operation.
(assert-event
 (and (fn-bpb-bundlep *bpnmt-n03-old*)
      (fn-bpb-bundlep *bpnmt-n03-new*)
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-old*)
        *bpnmt-observation* *bpnmt-ingress*))
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-new*)
        *bpnmt-observation* *bpnmt-ingress*))
      (fn-bpnp-host-eventp
       (fn-bpnf-receive-wire-event-value
        (fn-bpnf-receive-wire-event
         *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-old*)
         *bpnmt-observation* *bpnmt-ingress*)))
      (fn-bpnp-host-eventp
       (fn-bpnf-receive-wire-event-value
        (fn-bpnf-receive-wire-event
         *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-new*)
         *bpnmt-observation* *bpnmt-ingress*)))
      (equal (len (fn-bpnf-held-list *bpnmt-n03-s2*)) 2)
      (equal (fn-bpn-nth 3 (second (fn-bpnf-held-list *bpnmt-n03-s2*))) 0)
      (equal (fn-bpn-nth 3 (first (fn-bpnf-held-list *bpnmt-n03-s2*))) 1)
      (fn-bpnf-heldp (second (fn-bpnf-held-list *bpnmt-n03-s2*)))
      (fn-bpnf-heldp (first (fn-bpnf-held-list *bpnmt-n03-s2*)))
      (equal (fn-bpp-destination
              (fn-bpb-bundle-primary
               (fn-bpnf-held-bundle
                (second (fn-bpnf-held-list *bpnmt-n03-s2*)))))
             *bpnmt-unrouted*)
      (equal (fn-bpp-destination
              (fn-bpb-bundle-primary
               (fn-bpnf-held-bundle
                (first (fn-bpnf-held-list *bpnmt-n03-s2*)))))
             *bpnmt-local*)
      (equal (fn-bpah-held-class
              (first (fn-bpnf-held-list *bpnmt-n03-s2*))) :request)
      (equal (fn-bpah-held-expiry
              (first (fn-bpnf-held-list *bpnmt-n03-s2*))
              *bpnmt-observation*) :live)
      (equal (fn-bpah-held-expiry
              (second (fn-bpnf-held-list *bpnmt-n03-s2*))
              *bpnmt-observation*) :live)
      (not (fn-bpn-machine-state-fenced (fn-bpnf-base *bpnmt-n03-s2*)))
      (not (fn-bpnf-issued *bpnmt-n03-s2*))))

(defconst *bpnmt-n03-old-held*
  (second (fn-bpnf-held-list *bpnmt-n03-s2*)))
(defconst *bpnmt-n03-new-held*
  (first (fn-bpnf-held-list *bpnmt-n03-s2*)))
(defconst *bpnmt-n03-old-key* (fn-bpnp-wait-key *bpnmt-n03-old-held*))
(defconst *bpnmt-n03-new-key* (fn-bpnp-wait-key *bpnmt-n03-new-held*))
(defconst *bpnmt-n03-progress-event*
  (list :progress *bpnmt-local* *bpnmt-observation* nil 0))
(defconst *bpnmt-n03-first*
  (fn-bpnp-step *bpnmt-n03-s2* *bpnmt-n03-progress-event*))
(defconst *bpnmt-n03-waited* (fn-bpnf-answer-state *bpnmt-n03-first*))
(defconst *bpnmt-n03-second*
  (fn-bpnp-step *bpnmt-n03-waited* *bpnmt-n03-progress-event*))
(defconst *bpnmt-n03-delivering* (fn-bpnf-answer-state *bpnmt-n03-second*))

; N03 positive: a route-less old transit obligation remains held with its
; own volatile wait.  The unchanged-generation tick skips that exact key
; and starts delivery of the younger local request through the host-called
; outer machine, in two progress events (within the specified four).
(assert-event
 (and (fn-bpnp-host-eventp *bpnmt-n03-progress-event*)
      (equal (fn-bpnf-answer-effects *bpnmt-n03-first*)
             (list (list :progress-wait *bpnmt-n03-old-key* :route 0)))
      (equal (fn-bpnp-wait-for *bpnmt-n03-old-key*
                                (fn-bpnp-waits *bpnmt-n03-waited*))
             (list :bpnp-wait *bpnmt-n03-old-key* :route 0))
      (equal (len (fn-bpnf-held-list *bpnmt-n03-waited*)) 2)
      (not (fn-bpnf-issued *bpnmt-n03-waited*))
      (equal (car (car (fn-bpnf-answer-effects *bpnmt-n03-second*)))
             :deliver)
      (equal (fn-bpn-nth 3 (car (fn-bpnf-answer-effects *bpnmt-n03-second*)))
             *bpnmt-n03-new-key*)
      (equal (fn-bpnf-find-held *bpnmt-n03-old-key*
                                 (fn-bpnf-held-list *bpnmt-n03-delivering*))
             *bpnmt-n03-old-held*)
      (not (fn-bpnf-issued *bpnmt-n03-delivering*))))

; Tooth for the only hypothesis of the called-path invariant: remove the
; :progress event-kind premise.  A real matched kind-5 durable callback then
; changes the held list, so the theorem's conjunction is false.
(defconst *bpnmt-n03-receive-event*
  (fn-bpnf-receive-wire-event-value
   (fn-bpnf-receive-wire-event
    *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-old*)
    *bpnmt-observation* *bpnmt-ingress*)))
(defconst *bpnmt-n03-receive-proposal*
  (fn-bpnp-step *bpnmt-n03-s0* *bpnmt-n03-receive-event*))
(defconst *bpnmt-n03-receive-effect*
  (car (fn-bpnf-answer-effects *bpnmt-n03-receive-proposal*)))
(defconst *bpnmt-n03-kind5-durable-event*
  (list :persist-result (fn-bpn-nth 1 *bpnmt-n03-receive-effect*)
        (fn-bpn-nth 2 *bpnmt-n03-receive-effect*) :durable))
(assert-event
 (and (fn-bpnp-host-eventp *bpnmt-n03-kind5-durable-event*)
      (equal (car *bpnmt-n03-receive-effect*) :persist)
      (not (equal (fn-cbor-ag-car *bpnmt-n03-kind5-durable-event*) :progress))
      (null (fn-bpnf-held-list
             (fn-bpnf-answer-state *bpnmt-n03-receive-proposal*)))
      (equal (len (fn-bpnf-held-list
                   (fn-bpnf-answer-state
                    (fn-bpnp-step
                     (fn-bpnf-answer-state *bpnmt-n03-receive-proposal*)
                     *bpnmt-n03-kind5-durable-event*)))) 1)))
(must-fail
 (assert-event
  (equal
   (fn-bpnf-held-list
    (fn-bpnf-answer-state
     (fn-bpnp-step
      (fn-bpnf-answer-state *bpnmt-n03-receive-proposal*)
      *bpnmt-n03-kind5-durable-event*)))
   (fn-bpnf-held-list
    (fn-bpnf-answer-state *bpnmt-n03-receive-proposal*)))))

(defconst *bpnmt-n03-delivery-effect*
  (car (fn-bpnf-answer-effects *bpnmt-n03-second*)))
(defconst *bpnmt-n03-result*
  (fn-bpnp-step
   *bpnmt-n03-delivering*
   (list :deliver-result (fn-bpn-nth 1 *bpnmt-n03-delivery-effect*)
         (fn-bpn-nth 2 *bpnmt-n03-delivery-effect*)
         *bpnmt-n03-new-key* :request-accepted '(114 105 100))))
(defconst *bpnmt-n03-publication*
  (car (fn-bpnf-answer-effects *bpnmt-n03-result*)))
(defconst *bpnmt-n03-durable*
  (fn-bpnp-step
   (fn-bpnf-answer-state *bpnmt-n03-result*)
   (list :persist-result (fn-bpn-nth 1 *bpnmt-n03-publication*)
         (fn-bpn-nth 2 *bpnmt-n03-publication*) :durable)))

(assert-event
 (and (equal (car *bpnmt-n03-publication*) :persist-delivery)
      (equal (fn-bpnf-answer-effects *bpnmt-n03-durable*)
             '((:delivery-answer :durable)))
      (equal (fn-bpnf-find-held
              *bpnmt-n03-old-key*
              (fn-bpnf-held-list (fn-bpnf-answer-state *bpnmt-n03-durable*)))
             *bpnmt-n03-old-held*)
      (equal (fn-bpn-nth 12
              (fn-bpnf-find-held
               *bpnmt-n03-new-key*
               (fn-bpnf-held-list (fn-bpnf-answer-state *bpnmt-n03-durable*))))
             '(:dispatch-done))))

; Exact negative for unchanged route generation: a generation change
; rechecks the older transit row, so the second progress effect is not a
; delivery.  The old row is still live, held and unrouted in both traces.
(defconst *bpnmt-n03-woken*
  (fn-bpnp-step *bpnmt-n03-waited*
                (list :progress *bpnmt-local* *bpnmt-observation* nil 1)))
(assert-event
 (and (equal (fn-bpnf-answer-effects *bpnmt-n03-woken*)
             (list (list :progress-wait *bpnmt-n03-old-key* :route 1)))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpnmt-n03-woken*))
             (fn-bpnf-held-list *bpnmt-n03-s2*))))
(must-fail
 (assert-event
  (equal (car (car (fn-bpnf-answer-effects *bpnmt-n03-woken*)))
         :deliver)))

; A failed cold-recovery attempt cannot consume the volatile wait or any
; held work.  A successful model replay changes epoch and clears the wait;
; it must present its own recovered held rows from the durable journal.  These
; direct six-field events exercise the host boundary shape; the replay result
; here is a model fixture, not an observed name/byte scan.
(defconst *bpnmt-n03-fault-recovery*
  (fn-bpnp-step
   *bpnmt-n03-waited*
   (list :recover-fnbs 1 nil :ready
         (list :ready (fn-bpnf-held-list *bpnmt-n03-s2*) nil) 2)))
(assert-event
 (and (fn-bpnp-host-eventp
       (list :recover-fnbs 1 nil :ready
             (list :ready (fn-bpnf-held-list *bpnmt-n03-s2*) nil) 2))
      (equal (fn-bpnf-answer-effects *bpnmt-n03-fault-recovery*)
             '((:restart-fault :fnbs-or-base)))
      (equal (fn-bpnf-answer-state *bpnmt-n03-fault-recovery*)
             *bpnmt-n03-waited*)
      (equal (fn-bpnp-wait-for
              *bpnmt-n03-old-key*
              (fn-bpnp-waits
               (fn-bpnf-answer-state *bpnmt-n03-fault-recovery*)))
             (list :bpnp-wait *bpnmt-n03-old-key* :route 0))))
(must-fail
 (assert-event
  (not (fn-bpnp-waits
        (fn-bpnf-answer-state *bpnmt-n03-fault-recovery*)))))
(defconst *bpnmt-n03-recovered*
  (fn-bpnp-step
   *bpnmt-n03-waited*
   (list :recover-fnbs 2 nil :ready
         (list :ready (fn-bpnf-held-list *bpnmt-n03-s2*) nil) 2)))
(assert-event
 (and (fn-bpnp-host-eventp
       (list :recover-fnbs 2 nil :ready
             (list :ready (fn-bpnf-held-list *bpnmt-n03-s2*) nil) 2))
      (equal (car (car (fn-bpnf-answer-effects *bpnmt-n03-recovered*)))
             :restart-ready)
      (not (fn-bpnp-waits (fn-bpnf-answer-state *bpnmt-n03-recovered*)))
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpnmt-n03-recovered*))
             (fn-bpnf-held-list *bpnmt-n03-s2*))
      (equal (fn-bpnp-used (fn-bpnf-answer-state *bpnmt-n03-recovered*)) 2)))

; PENDING N03 general two-tick theorem and its remaining hypothesis teeth.
; PENDING N04: two *received* valid no-fragment bundles with 48 KiB and 8 KiB
; payloads, both encoded below 131072, are checked against a 32768-byte MRU;
; only the older exceeds it and only the younger is attempted.
; PENDING N05: with F=1, kind 8 refuses without mutation; with F=2, kind 8
; and a failed kind 9 settle; at remaining=D+R+margin, kind 11 still pays debt.
; The N04/N05 pending forms are not counted as tests or theorem teeth.
