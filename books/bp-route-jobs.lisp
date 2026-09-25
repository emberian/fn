; fn: routing of queued FNBS base jobs (specs/bp-node-machine.md 4.6; PRF-103).
;
; bp-routing (2026-09-25) moved the next-hop decision for HELD TRANSIT into
; ACL2 (fn-bprt-outbound-choice, consulted by the routed :session event).
; Its finding 1: the base machine's queued jobs -- A's request carrier
; (`bp-obligation request'), B's receipts (`bp-node serve' outbox) and status
; reports -- kept the TCPCL address they were queued with, from the command
; line.  This book routes them:
;
;   queue time    fn-bprt-job-route: the queued job's route is the routed
;                 hop's contact when the table names one;
;   contact time  fn-bprt-send-decision: before any octet is sent, the
;                 decision over the CURRENT table names the hop the job is
;                 offered to (the table may have changed since it was
;                 queued), or holds it (:no-route / :no-live-hop).  A held
;                 job keeps its durable row and its obligation.
;
; The contact host is loopback, as in fnn-bpnode-forward-session: a boundary
; row carries a contact PORT only.
;; The queue-time route is the job's durable route (its :queued record).
;; books/bp-node-contact-driver.lisp offers a job only when the contact-time
;; decision names that same route, and proves it over fn-bpnp-step.  Open
;; (spec 4.6): a durable re-route record, so that a job whose table changed
;; after queueing is offered on the new hop instead of held
;; (:route-changed); a contact host other than loopback.
(in-package "ACL2")
(include-book "bp-route")

(defun fn-bprt-loopback ()
  (declare (xargs :guard t))
  (fn-record-string-octets "127.0.0.1"))

; Queue time.  NODE, KEEPALIVE, SEGMENT and TRANSFER are the session
; parameters the host would have queued with; the answer is the route to
; the routed hop, or nil when the table routes DEST nowhere.
(defun fn-bprt-job-route (dest table node keepalive segment transfer)
  (declare (xargs :guard t))
  (let ((choice (fn-bprt-outbound-choice dest table)))
    (if (equal (fn-bprt-nth 0 choice) :hop)
        (list :route (fn-bprt-loopback) (fn-bprt-nth 3 choice)
              node keepalive segment transfer)
      nil)))

; Contact time.  ROUTE is the job's queued route (its session parameters
; are kept), DEST the job's destination EID text.
;   (:send ROUTE' HOP EID)  offer on ROUTE', to the boundary HOP, whose
;                           contact must announce EID;
;   (:held DECISION)        offer nothing; DECISION is :no-route or
;                           :no-live-hop.
(defun fn-bprt-send-decision (route dest table)
  (declare (xargs :guard t))
  (let ((choice (fn-bprt-outbound-choice dest table)))
    (if (equal (fn-bprt-nth 0 choice) :hop)
        (list :send
              (list :route (fn-bprt-loopback) (fn-bprt-nth 3 choice)
                    (fn-bprt-nth 3 route) (fn-bprt-nth 4 route)
                    (fn-bprt-nth 5 route) (fn-bprt-nth 6 route))
              (fn-bprt-nth 1 choice) (fn-bprt-nth 2 choice))
      (list :held (fn-bprt-nth 0 choice)))))

; The decision's own statement; the keystone over the served step is
; fn-bpnp-contact-offer-is-the-routed-hop.  A :send answer names exactly the
; boundary fn-bprt-next-hop chooses for DEST over the table's contactable
; boundaries, on that boundary's contact port: never a boundary the table
; does not route DEST to, and never the queued port.
(defthm fn-bprt-send-decision-offers-only-the-routed-hop
  (let ((d (fn-bprt-send-decision route dest table)))
    (implies (equal (car d) :send)
             (and (equal (caddr d)
                         (fn-bprt-next-hop dest table (fn-bprt-contactable table)))
                  (equal (caddr (cadr d))
                         (fn-bprt-route-port
                          (fn-bprt-hop-route dest table
                                             (fn-bprt-contactable table)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bprt-send-decision fn-bprt-outbound-choice
                         fn-bprt-nth car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e unary--) (:e equal))
                       (theory 'minimal-theory)))))

; With no matching route, nothing is sent: the job is held.
(defthm fn-bprt-send-decision-holds-without-a-route
  (implies (atom (fn-bprt-matching dest table))
           (equal (fn-bprt-send-decision route dest table)
                  '(:held :no-route)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bprt-send-decision fn-bprt-outbound-choice
                         fn-bprt-next-hop fn-bprt-nth car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e unary--) (:e equal))
                       (theory 'minimal-theory)))))
