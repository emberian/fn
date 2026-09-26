; Teeth of books/bp-node-forward-plan.lisp: a relay holding two transit
; bundles whose destinations the route table sends to two neighbours (the
; four-node mission's X: one toward dtn7 r1, one back toward fn-a).  The
; fixture is bp-route-tests': bundles received, then dispatched by the
; :progress event under (:table TABLE).
(in-package "ACL2")
(include-book "../../books/bp-node-forward-plan")
(include-book "../../books/bp-route-step")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fp-local* (cons :dtn (fn-record-string-octets "//bp-local/")))
(defconst *fp-sender* (cons :dtn (fn-record-string-octets "//bp-sender/")))
(defconst *fp-dest* (cons :dtn (fn-record-string-octets "//bp-dest/")))
(defconst *fp-other* (cons :dtn (fn-record-string-octets "//other/x")))
(defconst *fp-config* (fn-bpn-config *fp-local* 3600000 2 32 1048576))
(defconst *fp-sender-config* (fn-bpn-config *fp-sender* 3600000 2 32 1048576))
(defconst *fp-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *fp-ingress*
  (list :cl (cons 0 1) 1 *fp-sender* '(115 101 110 100 101 114) 0))
(defun fp-receive-event (wire)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-receive-wire-event-value
   (fn-bpnf-receive-wire-event *fp-config* wire *fp-obs* *fp-ingress*)))
(defun fp-durable (answer)
  (declare (xargs :guard t :verify-guards nil))
  (let ((effect (car (fn-bpnf-answer-effects answer))))
    (fn-bpnp-step (fn-bpnf-answer-state answer)
                  (list :persist-result (fn-bpn-nth 1 effect)
                        (fn-bpn-nth 2 effect) :durable))))
(defconst *fp-raw-s0* (fn-bpnf-initial-state *fp-config* 8 1048576))
(defconst *fp-s0*
  (fn-bpnf-answer-state
   (fn-bpnp-step *fp-raw-s0*
                 (fn-bpnf-family-recover-auto-event *fp-raw-s0* nil :ready nil))))
(defconst *fp-a*
  (fn-bpb-encode (fn-bpn-send-bundle *fp-sender-config* *fp-dest* '(1 2 3 4) 7 *fp-obs*)))
(defconst *fp-b*
  (fn-bpb-encode (fn-bpn-send-bundle *fp-sender-config* *fp-other* '(5 6 7 8) 8 *fp-obs*)))
(defconst *fp-s1*
  (fn-bpnf-answer-state
   (fp-durable (fn-bpnp-step
                (fn-bpnf-answer-state
                 (fp-durable (fn-bpnp-step *fp-s0* (fp-receive-event *fp-a*))))
                (fp-receive-event *fp-b*)))))
(assert-event (equal (len (fn-bpnf-held-list *fp-s1*)) 2))

;; The route table: dtn://bp-dest/ to "relay", dtn://other/* to "relay-b".
(defconst *fp-table*
  (list (fn-bprt-route 100 "dtn://bp-dest/" "relay" "dtn://relay/" 4556)
        (fn-bprt-route 100 "dtn://other/*" "relay-b" "dtn://relay-b/" 4557)))
(defconst *fp-relay* (cons :dtn (fn-record-string-octets "//relay/")))
(defconst *fp-relay-b* (cons :dtn (fn-record-string-octets "//relay-b/")))
(assert-event (fn-bprt-tablep *fp-table*))
(assert-event (equal (fn-bpnp-host-routes *fp-table* *fp-dest*)
                     (list :table *fp-table*)))
(assert-event (equal (fn-bpnp-host-routes nil *fp-dest*)
                     (fn-bpnp-single-peer-routes *fp-dest*)))

;; fn-bpnp-table-route-peer-is-the-routed-hop: each destination its own hop.
(assert-event (equal (fn-bpnp-route-peer *fp-dest* (list :table *fp-table*)) *fp-relay*))
(assert-event (equal (fn-bpnp-route-peer *fp-other* (list :table *fp-table*)) *fp-relay-b*))
(assert-event (equal (fn-bprt-outbound-choice "dtn://other/x" *fp-table*)
                     (list :hop "relay-b" "dtn://relay-b/" 4557)))
;; Hypothesis "the route peer is non-nil": a destination no route matches.
(assert-event (null (fn-bpnp-route-peer *fp-local* (list :table *fp-table*))))
(must-fail (assert-event (equal (car (fn-bprt-outbound-choice "dtn://bp-local/" *fp-table*))
                                :hop)))
;; Hypothesis "a table": a malformed table is not the table form.
(must-fail (assert-event (fn-bpnp-table-routingp (list :table '(bad)))))
(assert-event (null (fn-bpnp-route-peer *fp-dest* (list :table '(bad)))))

;; fn-bpnp-progress-dispatch-names-the-routed-hop.  Witness: the first
;; progress event dispatches the older row (to dtn://bp-dest/) toward relay.
(make-event `(defconst *fp-progress-1* ',(fn-bpnp-progress-step *fp-s1* *fp-local* *fp-obs* (list :table *fp-table*) 1
                         (fn-bpnp-default-budgets))))
(defconst *fp-eff-1* (car (fn-bpnf-answer-effects *fp-progress-1*)))
(assert-event (equal (car *fp-eff-1*) :persist-dispatch))
(assert-event (equal (car (fn-bpnp-dispatch-apply (fn-bpn-nth 3 *fp-eff-1*)
                                                  (fn-bpnf-held-list *fp-s1*)))
                     :ready))
(assert-event (equal (fn-bpn-nth 5 (fn-bpn-nth 3 *fp-eff-1*)) *fp-relay*))
(assert-event (fn-bpp-eidp (fn-bpn-nth 5 (fn-bpn-nth 3 *fp-eff-1*))))
(assert-event
 (equal (fn-bprt-outbound-choice
         (fn-bpnp-held-dest (fn-bpnf-find-arrival (fn-bpn-nth 3 (fn-bpn-nth 3 *fp-eff-1*))
                                                  (fn-bpnf-held-list *fp-s1*)))
         *fp-table*)
        (list :hop "relay" "dtn://relay/" 4556)))
;; Hypothesis "the effect is :persist-dispatch": with an empty table the
;; event proposes no dispatch, and the rows' destinations have no :hop.
(make-event `(defconst *fp-progress-0* ',(fn-bpnp-progress-step *fp-s1* *fp-local* *fp-obs* (list :table nil) 1
                         (fn-bpnp-default-budgets))))
(must-fail (assert-event (equal (car (car (fn-bpnf-answer-effects *fp-progress-0*)))
                                :persist-dispatch)))
(must-fail (assert-event (equal (car (fn-bprt-outbound-choice "dtn://bp-dest/" nil)) :hop)))

;; Both rows dispatched and durable.
(make-event `(defconst *fp-s2* ',(fn-bpnf-answer-state (fp-durable *fp-progress-1*))))
(make-event `(defconst *fp-s3* ',(fn-bpnf-answer-state
   (fp-durable (fn-bpnp-progress-step *fp-s2* *fp-local* *fp-obs*
                                      (list :table *fp-table*) 1
                                      (fn-bpnp-default-budgets))))))
(defconst *fp-held* (fn-bpnf-held-list *fp-s3*))
(assert-event (equal (fn-bpn-nth 11 (fn-bpnf-find-arrival
                                     (fn-bpn-nth 3 (car (reverse *fp-held*))) *fp-held*))
                     *fp-relay*))

;; fn-bpnp-forward-plan-has-one-session-per-peer: two next hops, two sessions.
(defconst *fp-plan* (fn-bpnp-forward-plan *fp-held* *fp-table*))
(assert-event (equal *fp-plan*
                     (list (list *fp-relay* "relay" "dtn://relay/" 4556)
                           (list *fp-relay-b* "relay-b" "dtn://relay-b/" 4557))))
(assert-event (no-duplicatesp-equal (fn-bpnp-plan-peers *fp-plan*)))
(assert-event (null (fn-bpnp-forward-unrouted *fp-held* *fp-table*)))
(assert-event (equal (fn-bpnp-forward-unrouted *fp-held* nil)
                     (list (list "dtn://bp-dest/" :no-route)
                           (list "dtn://other/x" :no-route))))

;; fn-bpnp-forward-plan-offers-a-row-on-one-session.
(defun fp-scan (entry ordered waits)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnp-forward-scan ordered (fn-bprt-nth 0 entry) 32768 *fp-local* *fp-obs*
                        waits 1000 (fn-bpnf-epoch *fp-s3*) 3))
(defconst *fp-e1* (first *fp-plan*))
(defconst *fp-e2* (second *fp-plan*))
(defconst *fp-ordered* (reverse *fp-held*))
;; Witness: the session for e1 selects the bp-dest row; with e2 := e1 the
;; antecedent holds and so does e1 = e2.
(assert-event (equal (car (fp-scan *fp-e1* *fp-ordered* nil)) :ready))
(assert-event (member-equal *fp-e1* *fp-plan*))
(assert-event (equal (fn-bpn-nth 1 (fp-scan *fp-e1* *fp-ordered* nil))
                     (car *fp-ordered*)))
(assert-event (equal (car (fp-scan *fp-e2* *fp-ordered* nil)) :ready))
(assert-event (equal (fn-bpn-nth 1 (fp-scan *fp-e2* *fp-ordered* nil))
                     (cadr *fp-ordered*)))
;; Hypothesis "the same row": the two plan entries' sessions each select a
;; row, different ones, and the entries differ.
(must-fail (assert-event (equal (fn-bpn-nth 1 (fp-scan *fp-e1* *fp-ordered* nil))
                                (fn-bpn-nth 1 (fp-scan *fp-e2* *fp-ordered* nil)))))
(must-fail (assert-event (equal *fp-e1* *fp-e2*)))
;; Hypothesis "e2 is a plan entry": an entry with e1's peer and another
;; boundary selects the same row, and it is not e1.
(defconst *fp-e1-forged* (list *fp-relay* "relay-b" "dtn://relay-b/" 4557))
(assert-event (equal (fn-bpn-nth 1 (fp-scan *fp-e1-forged* *fp-ordered* nil))
                     (car *fp-ordered*)))
(must-fail (assert-event (member-equal *fp-e1-forged* *fp-plan*)))
(must-fail (assert-event (equal *fp-e1* *fp-e1-forged*)))
;; Hypothesis "both scans ready": e2's scan over no rows is not ready yet
;; carries e1's row in its second field (the waits it returns), and the
;; entries differ.
(assert-event (equal (fn-bpn-nth 1 (fp-scan *fp-e2* nil (car *fp-ordered*)))
                     (car *fp-ordered*)))
(must-fail (assert-event (equal (car (fp-scan *fp-e2* nil (car *fp-ordered*))) :ready)))
