; Teeth of books/bp-route.lisp and books/bp-route-step.lisp: the routing
; decision (spec bp-node-machine 4.6) and its call site in fn-bpnp-step,
; the function the native host calls (host/native/bp-service.lisp
; fnn-bps-foundation-step).  The fixture is bp-node-forward-retry-tests':
; one transit bundle to dtn://bp-dest/ received, dispatched and held.
(in-package "ACL2")
(include-book "../../books/bp-route-step")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)


(defconst *rt-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *rt-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *rt-dest* (cons :dtn '(47 47 98 112 45 100 101 115 116 47)))
(defconst *rt-config* (fn-bpn-config *rt-local* 3600000 2 32 1048576))
(defconst *rt-sender-config* (fn-bpn-config *rt-sender* 3600000 2 32 1048576))
(defconst *rt-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *rt-ingress*
  (list :cl (cons 0 1) 1 *rt-sender* '(115 101 110 100 101 114) 0))
(defun rt-receive-event (wire)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-receive-wire-event-value
   (fn-bpnf-receive-wire-event *rt-config* wire *rt-obs* *rt-ingress*)))
(defun rt-durable (answer)
  (declare (xargs :guard t :verify-guards nil))
  (let ((effect (car (fn-bpnf-answer-effects answer))))
    (fn-bpnp-step (fn-bpnf-answer-state answer)
                  (list :persist-result (fn-bpn-nth 1 effect)
                        (fn-bpn-nth 2 effect) :durable))))
(defconst *rt-raw-s0* (fn-bpnf-initial-state *rt-config* 8 1048576))
(defconst *rt-s0*
  (fn-bpnf-answer-state
   (fn-bpnp-step *rt-raw-s0*
                 (fn-bpnf-family-recover-auto-event *rt-raw-s0* nil :ready nil))))
(defconst *rt-a*
  (fn-bpn-send-bundle *rt-sender-config* *rt-dest* '(1 2 3 4) 7 *rt-obs*))
(defconst *rt-a-wire* (fn-bpb-encode *rt-a*))
(defconst *rt-a-proposal* (fn-bpnp-step *rt-s0* (rt-receive-event *rt-a-wire*)))
(defconst *rt-s1* (fn-bpnf-answer-state (rt-durable *rt-a-proposal*)))


(defconst *rt-routes* (list (list *rt-dest* *rt-dest*)))
(defconst *rt-progress* (list :progress *rt-local* *rt-obs* *rt-routes* 1))
(make-event `(defconst *rt-dispatch* ',(fn-bpnp-step *rt-s1* *rt-progress*)))
(defconst *rt-s2* (fn-bpnf-answer-state (rt-durable *rt-dispatch*)))
(defconst *rt-session* (cons 1 1))
(defconst *rt-session-event*
  (list :session *rt-dest* *rt-session* t 32768 *rt-obs*))

;; The route table.  *rt-dest* is dtn://bp-dest/.
(defconst *rt-relay-eid* "dtn://relay/")
(defconst *rt-route* (fn-bprt-route 100 "dtn://bp-dest/" "relay" *rt-relay-eid* 4556))
(defconst *rt-wild* (fn-bprt-route 100 "dtn://bp-dest/*" "relay-b" "dtn://relay-b/" 4557))
(defconst *rt-table* (list *rt-route*))
(assert-event (fn-bprt-tablep (list *rt-route* *rt-wild*)))
(assert-event (equal (fn-bpaj-eid-text *rt-dest*) "dtn://bp-dest/"))
(defun rt-routed-event (hop announced table)
  (declare (xargs :guard t :verify-guards nil))
  (list :session *rt-dest* *rt-session* t 32768 *rt-obs*
        (list :via hop announced table)))
(defun rt-first-effect (hop announced table)
  (declare (xargs :guard t :verify-guards nil))
  (car (fn-bpnf-answer-effects
        (fn-bpnp-step *rt-s2* (rt-routed-event hop announced table)))))
(defconst *rt-relay-octets* (fn-record-string-octets *rt-relay-eid*))
(assert-event (fn-bpnp-host-eventp (rt-routed-event "relay" *rt-relay-octets* *rt-table*)))
;; The operator's budgets ride after VIA (fnn-bpnode-budgeted): the routed
;; event with them is a host event, and the keystone's EXTRA tail is that
;; field.  Without VIA the budgets stand at slot 6 and are not read as a route.
(defconst *rt-budgets* (fn-bpnp-budgets 5000 3))
(defconst *rt-routed-budgeted*
  (append (rt-routed-event "relay" *rt-relay-octets* *rt-table*) (list *rt-budgets*)))
(assert-event (fn-bpnp-host-eventp *rt-routed-budgeted*))
(assert-event (equal (fn-bpnp-session-via *rt-routed-budgeted*)
                     (list :via "relay" *rt-relay-octets* *rt-table*)))
(assert-event (fn-bpnp-host-eventp (append *rt-session-event* (list *rt-budgets*))))
(assert-event (null (fn-bpnp-session-via (append *rt-session-event* (list *rt-budgets*)))))
(assert-event (not (fn-bpnp-host-eventp (append *rt-session-event* (list nil)))))

;; Teeth of fn-bpnp-step-offers-only-the-routed-hop.  Witness: the table
;; routes dtn://bp-dest/ to "relay", the session is to "relay" and the
;; contact announced dtn://relay/: the step proposes the attempt.
(assert-event (equal (car (rt-first-effect "relay" *rt-relay-octets* *rt-table*))
                     :persist-attempt))
;; The routed event with the budgets offers the same row.
(assert-event (equal (car (car (fn-bpnf-answer-effects
                                (fn-bpnp-step *rt-s2* *rt-routed-budgeted*))))
                     :persist-attempt))
;; The unrouted 6-field form (never sent open by the host) offers the same row.
(assert-event (equal (car (car (fn-bpnf-answer-effects (fn-bpnp-step *rt-s2* *rt-session-event*))))
                     :persist-attempt))
;; Hypothesis "the table names HOP": a session to an unlisted neighbour
;; proposes nothing, whatever it announces (even the listed hop's EID).
(must-fail (assert-event (equal (car (rt-first-effect "other" *rt-relay-octets* *rt-table*))
                                :persist-attempt)))
(assert-event (equal (rt-first-effect "other" *rt-relay-octets* *rt-table*)
                     (list :forward-no-route (fn-bpn-nth 3 (car (fn-bpnf-held-list *rt-s2*)))
                           "other" :no-live-hop)))
;; Hypothesis "the contact announced HOP's EID": the listed hop, a wrong
;; announcement.
(must-fail (assert-event (equal (car (rt-first-effect "relay" (fn-record-string-octets "dtn://evil/")
                                                      *rt-table*))
                                :persist-attempt)))
(assert-event (equal (fn-bpn-nth 3 (rt-first-effect "relay" (fn-record-string-octets "dtn://evil/")
                                                    *rt-table*))
                     :announced-mismatch))
;; A prefix route to another boundary: offered on that boundary's session only.
(assert-event (equal (car (rt-first-effect "relay-b" (fn-record-string-octets "dtn://relay-b/")
                                           (list *rt-wild*)))
                     :persist-attempt))
(must-fail (assert-event (equal (car (rt-first-effect "relay" *rt-relay-octets* (list *rt-wild*)))
                                :persist-attempt)))

;; Teeth of fn-bpnp-step-unrouted-bundle-stays-held-and-is-reported.
;; Witness: an empty table; the report names the arrival and :no-route and
;; the held rows are the state's own.
(defconst *rt-unrouted* (fn-bpnp-step *rt-s2* (rt-routed-event "relay" *rt-relay-octets* nil)))
(assert-event (equal (fn-bpnf-answer-effects *rt-unrouted*)
                     (list (list :forward-no-route
                                 (fn-bpn-nth 3 (car (fn-bpnf-held-list *rt-s2*)))
                                 "relay" :no-route))))
(assert-event (equal (fn-bpnf-held-list (fn-bpnf-answer-state *rt-unrouted*))
                     (fn-bpnf-held-list *rt-s2*)))
(assert-event (consp (fn-bpnf-held-list *rt-s2*)))
;; Hypothesis "no route matches": with the route, the effect is the attempt.
(must-fail (assert-event (equal (car (rt-first-effect "relay" *rt-relay-octets* *rt-table*))
                                :forward-no-route)))
;; A table whose only route is for another destination is no route.
(assert-event (equal (car (rt-first-effect "relay" *rt-relay-octets*
                                           (list (fn-bprt-route 1 "dtn://elsewhere/" "relay"
                                                                *rt-relay-eid* 4556))))
                     :forward-no-route))

;; Teeth of fn-bprt-next-hop-deterministic-in-the-table.  Witness: the same
;; matching set in another order, with a route for another destination.
(defconst *rt-other* (fn-bprt-route 1 "dtn://elsewhere/" "x" "dtn://x/" 1))
(defconst *rt-r2* (fn-bprt-route 50 "dtn://bp-dest/*" "relay-b" "dtn://relay-b/" 4557))
(assert-event (equal (fn-bprt-next-hop "dtn://bp-dest/" (list *rt-route* *rt-r2*) '("relay" "relay-b"))
                     (fn-bprt-next-hop "dtn://bp-dest/" (list *rt-other* *rt-r2* *rt-route* *rt-r2*)
                                       '("relay" "relay-b"))))
(assert-event (equal (fn-bprt-next-hop "dtn://bp-dest/" (list *rt-route* *rt-r2*) '("relay" "relay-b"))
                     "relay-b"))
;; Hypothesis "the matching sets agree": drop the preferred route and the
;; answer changes.
(must-fail (assert-event (equal (fn-bprt-next-hop "dtn://bp-dest/" (list *rt-route* *rt-r2*)
                                                  '("relay" "relay-b"))
                                (fn-bprt-next-hop "dtn://bp-dest/" (list *rt-route*)
                                                  '("relay" "relay-b")))))

;; Teeth of fn-bprt-next-hop-names-a-live-matching-route.  Witness above
;; ("relay-b", a live matching route); without a live one the answer is
;; :no-live-hop and names no route.
(assert-event (equal (fn-bprt-next-hop "dtn://bp-dest/" (list *rt-route*) '("relay-b"))
                     :no-live-hop))
(must-fail (assert-event (member-equal (fn-bprt-hop-route "dtn://bp-dest/" (list *rt-route*) '("relay-b"))
                                       (list *rt-route*))))
(assert-event (equal (fn-bprt-next-hop "dtn://nobody/" (list *rt-route*) '("relay")) :no-route))

;; Patterns: the one wildcard form.
(assert-event (fn-bprt-matchp "dtn://bp-dest/*" "dtn://bp-dest/inbox"))
(assert-event (fn-bprt-matchp "dtn://bp-dest/*" "dtn://bp-dest/"))
(assert-event (not (fn-bprt-matchp "dtn://bp-dest/" "dtn://bp-dest/inbox")))
(assert-event (not (fn-bprt-matchp "dtn://bp-dest/*" "dtn://bp-destx/")))
(assert-event (not (fn-bprt-patternp "dtn://bp-*")))
(assert-event (fn-bprt-patternp "ipn:1.2"))
(assert-event (not (fn-bprt-wildcardp "ipn:1.2")))

;; The outbound choice reads only boundaries with a contact port.
(assert-event (equal (fn-bprt-outbound-choice "dtn://bp-dest/" (list *rt-route*))
                     (list :hop "relay" "dtn://relay/" 4556)))
(assert-event (equal (fn-bprt-outbound-choice "dtn://bp-dest/"
                                              (list (fn-bprt-route 1 "dtn://bp-dest/" "relay"
                                                                   *rt-relay-eid* 0)))
                     (list :no-live-hop)))
(assert-event (equal (fn-bprt-outbound-choice "dtn://nobody/" (list *rt-route*))
                     (list :no-route)))

;; The operator verb and the table read back from the rows it writes.
(defconst *rt-add* (fn-bprt-admin-plan (list "bp-route" "add" "dtn://bp-dest/*" "relay" "7")))
(assert-event (equal (fn-native-admin-result-status *rt-add*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *rt-add*) :set-bp-route))
(defconst *rt-boundary-rows*
  (list (fn-cfg-row-make "relay" "path-identity" "relay.invalid" 0)
        (fn-cfg-row-make "relay" "transport-bp" "dtn://relay/" 0)
        (fn-cfg-row-make "relay" "bp-trust" "network" 0)
        (fn-cfg-row-make "relay" "bp-boundary-contact" "127.0.0.1" 4556)))
(defconst *rt-rows* (append *rt-boundary-rows* (fn-native-admin-result-value *rt-add*)))
(assert-event (equal (fn-bprt-rows-table *rt-rows* *rt-rows*)
                     (list (fn-bprt-route 7 "dtn://bp-dest/*" "relay" "dtn://relay/" 4556))))
;; A route to a name that is no BP boundary routes nothing.
(assert-event (equal (fn-bprt-rows-table (fn-native-admin-result-value *rt-add*)
                                         (fn-native-admin-result-value *rt-add*))
                     nil))
(assert-event (equal (fn-native-admin-result-kind
                      (fn-bprt-admin-plan (list "bp-route" "remove" "dtn://bp-dest/*" "relay")))
                     :remove-bp-route))
(assert-event (equal (fn-native-admin-result-status
                      (fn-bprt-admin-plan (list "bp-route" "add" "not-an-eid" "relay")))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-bprt-admin-plan (list "bp-route" "add" "dtn://bp-dest/" "")))
                     :refused))
