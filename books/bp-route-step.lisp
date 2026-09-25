; fn: the routing call site's theorems over the step the host calls
; (specs/bp-node-machine.md section 4.6).
;
; The host (host/native/bp-service.lisp `fnn-bps-foundation-step', from
; host/native/bp-node.lisp `fnn-bpnode-forward-contact') calls
; `fn-bpnp-step' with a routed :session event
;   (:session PEER SESSION t MRU OBSERVATION (:via HOP ANNOUNCED TABLE) . EXTRA)
; where EXTRA is empty or the operator's budgets (fnn-bpnode-budgeted); the
; keystones below hold for any EXTRA, the scan running under the retry
; budget the event carries.  The host sends it after `fn-bprt-outbound-choice'
; named HOP and the TCPCL session to HOP's contact came up announcing
; ANNOUNCED.  Its :session arm calls `fn-bpnp-routed-start', which scans only
; the held rows `fn-bprt-offer-decision' (books/bp-route.lisp) routes to HOP
; (`fn-bpnp-routed-rows'), so an older row routed elsewhere or nowhere never
; blocks a younger routed row; a :session or :resume without VIA offers
; nothing.
(in-package "ACL2")
(include-book "bp-node-forward-retry")
(include-book "bp-route")
(set-verify-guards-eagerness 0)

; The scan the routed arm's start-one calls: over the held rows the table
; sends to the session's hop (fn-bpnp-routed-rows), with the state's own
; inputs; and the same scan over every held row, whose choice the no-route
; report names.
(defun fn-bprts-scan (st peer mru observation budget via)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-forward-scan
   (fn-bpnp-routed-rows (reverse (fn-bpnf-held-list st)) via) peer mru
   (fn-bpn-config-node-id (fn-bpn-machine-state-config (fn-bpnf-base st)))
   observation (fn-bpnp-waits st)
   (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st) *fn-bpnp-control-margin*)
   (fn-bpnf-epoch st) budget))

(defun fn-bprts-scan-all (st peer mru observation budget)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-forward-scan
   (reverse (fn-bpnf-held-list st)) peer mru
   (fn-bpn-config-node-id (fn-bpn-machine-state-config (fn-bpnf-base st)))
   observation (fn-bpnp-waits st)
   (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st) *fn-bpnp-control-margin*)
   (fn-bpnf-epoch st) budget))

; The retry budget a routed :session event carries (its field after VIA).
(defun fn-bprts-budget (event)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-budget-retries (fn-bpnp-event-budgets event 7)))

(local
 (defthm fn-bprts-via-is-not-budgets
   (not (fn-bpnp-budgetsp (cons :via x)))
   :hints (("Goal" :in-theory (enable fn-bpnp-budgetsp)))))

(defun fn-bprts-dest (h)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-held-dest h))

; The scan's choice is a row of the list it scans.
(local
 (defthm bprts-scan-ready-is-a-member
   (implies (equal (car (fn-bpnp-forward-scan ordered peer mru node observation
                                              waits free epoch budget))
                   :ready)
            (member-equal (fn-bpn-nth 1 (fn-bpnp-forward-scan
                                         ordered peer mru node observation
                                         waits free epoch budget))
                          ordered))
   :hints (("Goal" :induct (fn-bpnp-forward-scan ordered peer mru node observation
                                                 waits free epoch budget)
            :in-theory (union-theories
                        '(fn-bpnp-forward-scan member-equal fn-bpn-nth
                          fn-cbor-ag-car car-cons cdr-cons
                          (:e equal) (:e zp) natp (:e natp))
                        (theory 'minimal-theory))))))

; Every row of the routed list is one the gate offers on this session.
(local
 (defthm bprts-routed-row-is-offered
   (implies (member-equal h (fn-bpnp-routed-rows ordered via))
            (equal (fn-bprt-offer-decision (fn-bpnp-held-dest h) via) :offer))
   :hints (("Goal" :induct (fn-bpnp-routed-rows ordered via)
            :in-theory (union-theories '(fn-bpnp-routed-rows member-equal
                                         car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

; No blocking (bp-routing finding 3).  A row the gate does not offer on
; this session is not in the list the session scans: whatever an older
; row's route, the scan over the younger rows is the same.
(defthm fn-bpnp-routed-rows-skip-an-unrouted-row
  (implies (not (equal (fn-bprt-offer-decision (fn-bpnp-held-dest h) via) :offer))
           (equal (fn-bpnp-routed-rows (cons h rest) via)
                  (fn-bpnp-routed-rows rest via)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnp-routed-rows car-cons cdr-cons)
                                             (theory 'minimal-theory)))))

(local
 (defthm fn-bprts-with-runtime-keeps-selection-inputs
   (and (equal (fn-bpnf-held-list (fn-bpnp-with-runtime st s p)) (fn-bpnf-held-list st))
        (equal (fn-bpnf-base (fn-bpnp-with-runtime st s p)) (fn-bpnf-base st))
        (equal (fn-bpnp-waits (fn-bpnp-with-runtime st s p)) (fn-bpnp-waits st))
        (equal (fn-bpnp-used (fn-bpnp-with-runtime st s p)) (fn-bpnp-used st))
        (equal (fn-bpnp-debt (fn-bpnp-with-runtime st s p)) (fn-bpnp-debt st))
        (equal (fn-bpnf-epoch (fn-bpnp-with-runtime st s p)) (fn-bpnf-epoch st)))
   :hints (("Goal" :in-theory (enable fn-bpn-nth)))))

(defthm fn-bpnp-routed-start-offers-only-an-offer-decision
  (let* ((answer (fn-bpnp-routed-start st peer session mru observation via budget))
         (effect (car (fn-bpnf-answer-effects answer)))
         (record (fn-bpn-nth 3 effect))
         (scan (fn-bprts-scan st peer mru observation budget via))
         (h (fn-bpn-nth 1 scan)))
    (implies (equal (car effect) :persist-attempt)
             (and (equal (car scan) :ready)
                  (equal (fn-bpn-nth 3 record) (fn-bpn-nth 3 h))
                  (equal (fn-bpn-nth 4 record) (fn-bpah-held-primary-identity h))
                  (equal (fn-bprt-offer-decision (fn-bprts-dest h) via) :offer))))
  :rule-classes nil
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
           :use ((:instance fn-bpnp-start-one-offer-is-the-scan-choice
                            (ordered (fn-bpnp-routed-rows
                                      (reverse (fn-bpnf-held-list st)) via)))
                 (:instance bprts-scan-ready-is-a-member
                            (ordered (fn-bpnp-routed-rows
                                      (reverse (fn-bpnf-held-list st)) via))
                            (node (fn-bpn-config-node-id
                                   (fn-bpn-machine-state-config (fn-bpnf-base st))))
                            (waits (fn-bpnp-waits st))
                            (free (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                                                *fn-bpnp-control-margin*))
                            (epoch (fn-bpnf-epoch st)))
                 (:instance bprts-routed-row-is-offered
                            (ordered (reverse (fn-bpnf-held-list st)))
                            (h (fn-bpn-nth 1 (fn-bprts-scan st peer mru observation
                                                            budget via)))))
           :in-theory (union-theories
                       '(fn-bpnp-routed-start fn-bprts-scan fn-bprts-dest
                         fn-bpnf-answer fn-bpnf-answer-effects fn-bpn-nth fn-cbor-ag-car
                         car-cons cdr-cons (:executable-counterpart equal)
                         (:executable-counterpart zp) (:executable-counterpart not)
                         (:executable-counterpart natp) natp)
                       (theory 'minimal-theory)))))


; KEYSTONE.  Over the step the host calls: on a routed :session (the
; outbound session `bp-node serve' opened to boundary HOP, announcing
; ANNOUNCED, with the route table TABLE), a forwarding attempt is proposed
; only for the row the arrival-order scan chose, and only when the route
; decision for that row's own destination over the live set (HOP) names
; HOP: a route in TABLE whose pattern matches the destination names HOP,
; and the contact announced the EID HOP is enrolled under.
(defthm fn-bpnp-step-offers-only-the-routed-hop
  (let* ((answer (fn-bpnp-step
                  st (list* :session peer session t mru observation
                            (list :via hop announced table) extra)))
         (budget (fn-bprts-budget
                  (list* :session peer session t mru observation
                         (list :via hop announced table) extra)))
         (effect (car (fn-bpnf-answer-effects answer)))
         (record (fn-bpn-nth 3 effect))
         (h (fn-bpn-nth 1 (fn-bprts-scan st peer mru observation budget
                                           (list :via hop announced table))))
         (dest (fn-bprts-dest h))
         (route (fn-bprt-hop-route dest table (list hop))))
    (implies (equal (car effect) :persist-attempt)
             (and (equal (car (fn-bprts-scan st peer mru observation budget
                                            (list :via hop announced table)))
                         :ready)
                  (equal (fn-bpn-nth 3 record) (fn-bpn-nth 3 h))
                  (equal (fn-bpn-nth 4 record) (fn-bpah-held-primary-identity h))
                  (equal (fn-bprt-next-hop dest table (list hop)) hop)
                  (member-equal route table)
                  (fn-bprt-matchp (fn-bprt-route-pattern route) dest)
                  (equal (fn-bprt-route-boundary route) hop)
                  (equal (fn-record-string-octets (fn-bprt-route-eid route))
                         announced))))
  :hints (("Goal"
           :use ((:instance fn-bpnp-routed-start-offers-only-an-offer-decision
                            (st (fn-bpnp-with-runtime
                                 st (fn-bpnp-open-session
                                     (fn-bpnp-sessions st) peer session mru)
                                 (fn-bpnp-pending-image st)))
                            (via (list :via hop announced table))
                            (budget (fn-bprts-budget
                                     (list* :session peer session t mru observation
                                            (list :via hop announced table) extra))))
                 (:instance fn-bprt-offer-means-routed-hop-and-announced-eid
                            (dest (fn-bprts-dest
                                   (fn-bpn-nth 1 (fn-bprts-scan st peer mru observation
                                                  (fn-bprts-budget
                                                   (list* :session peer session t mru
                                                          observation
                                                          (list :via hop announced table)
                                                          extra))
                                                  (list :via hop announced table)))))
                            (via (list :via hop announced table)))
                 (:instance fn-bprt-offer-names-a-string-hop
                            (dest (fn-bprts-dest
                                   (fn-bpn-nth 1 (fn-bprts-scan st peer mru observation
                                                  (fn-bprts-budget
                                                   (list* :session peer session t mru
                                                          observation
                                                          (list :via hop announced table)
                                                          extra))
                                                  (list :via hop announced table)))))
                            (via (list :via hop announced table)))
                 (:instance fn-bprt-next-hop-names-a-live-matching-route
                            (dest (fn-bprts-dest
                                   (fn-bpn-nth 1 (fn-bprts-scan st peer mru observation
                                                  (fn-bprts-budget
                                                   (list* :session peer session t mru
                                                          observation
                                                          (list :via hop announced table)
                                                          extra))
                                                  (list :via hop announced table)))))
                            (live (list hop))))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bprts-with-runtime-keeps-selection-inputs
                         fn-bprts-scan fn-bprts-budget fn-bprts-via-is-not-budgets
                         fn-bpnp-session-via fn-bpnp-session-base-length
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-cbor-ag-car fn-bpn-nth fn-bprt-nth fix-true-list true-listp
                         fn-bpnf-answer-effects member-equal
                         fn-bpnf-answer fn-bpnf-answer-state natp
                         (:executable-counterpart natp)
                         (:executable-counterpart not)
                         (:executable-counterpart member-equal)
                         car-cons cdr-cons (:executable-counterpart equal)
                         (:executable-counterpart zp)
                         (:executable-counterpart fn-bpn-nth))
                       (theory 'minimal-theory))))
  :rule-classes nil)

; KEYSTONE.  A bundle with no route stays held and is reported: on a routed
; :session, when no row the table sends to HOP is ready and the oldest ready
; row has no route whose pattern matches its destination, the step proposes
; nothing, reports (:forward-no-route ARRIVAL HOP :no-route), and keeps every
; held row.
(defthm fn-bpnp-step-unrouted-bundle-stays-held-and-is-reported
  (let* ((via (list :via hop announced table))
         (event (list* :session peer session t mru observation via extra))
         (answer (fn-bpnp-step st event))
         (budget (fn-bprts-budget event))
         (all (fn-bprts-scan-all st peer mru observation budget))
         (h (fn-bpn-nth 1 all)))
    (implies (and (not (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain))
                  (not (equal (car (fn-bprts-scan st peer mru observation budget via))
                              :ready))
                  (equal (car all) :ready)
                  (not (consp (fn-bprt-matching (fn-bprts-dest h) table))))
             (and (equal (fn-bpnf-answer-effects answer)
                         (list (list :forward-no-route (fn-bpn-nth 3 h) hop
                                     :no-route)))
                  (equal (fn-bpnf-held-list (fn-bpnf-answer-state answer))
                         (fn-bpnf-held-list st)))))
  :hints (("Goal"
           :use ((:instance fn-bprt-offer-decision-without-a-matching-route
                            (dest (fn-bprts-dest
                                   (fn-bpn-nth 1 (fn-bprts-scan-all
                                                  st peer mru observation
                                                  (fn-bprts-budget
                                                   (list* :session peer session t mru
                                                          observation
                                                          (list :via hop announced table)
                                                          extra))))))
                            (via (list :via hop announced table))))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-routed-start
                         fn-bprts-with-runtime-keeps-selection-inputs
                         fn-bprts-scan fn-bprts-scan-all fn-bprts-dest fn-bprts-budget
                         fn-bprts-via-is-not-budgets
                         fn-bpnp-session-via fn-bpnp-session-base-length
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-cbor-ag-car fn-bpn-nth fn-bprt-nth
                         fn-bpnf-answer-effects fn-bpnf-answer fn-bpnf-answer-state
                         natp (:executable-counterpart natp)
                         (:executable-counterpart not)
                         car-cons cdr-cons (:executable-counterpart equal)
                         (:executable-counterpart zp)
                         (:executable-counterpart fn-bpn-nth))
                       (theory 'minimal-theory))))
  :rule-classes nil)
