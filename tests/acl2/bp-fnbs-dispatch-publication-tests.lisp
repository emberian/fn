(in-package "ACL2")
(include-book "../../books/bp-fnbs-dispatch-publication")
(include-book "../../books/codec-attach")
(include-book "bp-node-forwarding-teeth-tests")
(include-book "must-fail-checked")

; The live pending dispatch of the forwarding teeth fixture: the outer
; host-called step (fn-bpnp-step) issued it with a :persist-dispatch effect
; and nothing has persisted it yet -- the state bp-service holds when it
; calls fn-bpnp-dispatch-publication-authorize (fnn-bps-persist-dispatch).
(defconst *bpnpd-state* (fn-bpnf-answer-state *bpfx-new-dispatch*))
(defconst *bpnpd-epoch* (fn-bpn-nth 1 *bpfx-new-dispatch-effect*))
(defconst *bpnpd-op* (fn-bpn-nth 2 *bpfx-new-dispatch-effect*))
(defconst *bpnpd-record* (fn-bpn-nth 3 *bpfx-new-dispatch-effect*))
(make-event
 (list 'defconst '*bpnpd-operation*
       (list 'quote
             (fn-bpnp-dispatch-publication-authorize
              *bpnpd-state* *bpnpd-epoch* *bpnpd-op* *bpnpd-record* t t))))
(assert-event (fn-bpnp-dispatch-publication-operationp *bpnpd-operation*))
(assert-event (equal (fn-bpnp-dispatch-unframe
                      (fn-bpnp-dispatch-publication-frame *bpnpd-operation*))
                     *bpnpd-record*))

; KEYSTONE teeth (PRF-1016,
; fn-bpnp-dispatch-publication-authorize-admits-exactly-the-issued-pending-dispatch):
; the positive witness above with its complete antecedent by name, then
; every part of the conclusion; then a wrong operation id, a withheld lock
; and a present final name (the antecedent affirmed otherwise) answer the
; authority fault exactly.  The codec fault needs a recognized record the
; frame codec refuses; no reachable fixture produces one.
(assert-event
 (let ((issued (fn-bpnf-issued *bpnpd-state*)))
   (and (fn-bpnf-operationp issued)
        (fn-bpnf-operation-matchp issued *bpnpd-epoch* *bpnpd-op*)
        (equal (fn-bpn-nth 3 issued) :dispatch)
        (equal (fn-bpn-nth 4 issued) *bpnpd-record*)
        (equal (fn-bpn-nth 5 issued) :pending)
        (equal (fn-bpnf-epoch *bpnpd-state*) *bpnpd-epoch*)
        (equal (fn-bpnf-next-op *bpnpd-state*) (1+ *bpnpd-op*))
        (fn-bpnp-dispatch-recordp *bpnpd-record*)
        (equal (fn-bpn-nth 1 *bpnpd-record*) *bpnpd-epoch*)
        (equal (fn-bpn-nth 2 *bpnpd-record*) *bpnpd-op*)
        (not (equal (fn-bpnp-dispatch-frame *bpnpd-record*) :bad))
        (fn-bpnp-dispatch-publication-operationp *bpnpd-operation*)
        (equal (nth 1 *bpnpd-operation*) *bpnpd-epoch*)
        (equal (nth 2 *bpnpd-operation*) *bpnpd-op*)
        (equal (nth 3 *bpnpd-operation*) *bpnpd-record*)
        (equal (fn-bpnp-dispatch-publication-name *bpnpd-operation*)
               (fn-bpnf-stored-record-name *bpnpd-epoch* *bpnpd-op*))
        (equal (fn-bpnp-dispatch-publication-frame *bpnpd-operation*)
               (fn-bpnp-dispatch-frame *bpnpd-record*))
        (equal (fn-bpnp-dispatch-publication-publisher *bpnpd-operation*)
               (fn-jpub-initial t)))))
(assert-event
 (and (not (fn-bpnf-operation-matchp (fn-bpnf-issued *bpnpd-state*)
                                     *bpnpd-epoch* (1+ *bpnpd-op*)))
      (equal (fn-bpnp-dispatch-publication-authorize
              *bpnpd-state* *bpnpd-epoch* (1+ *bpnpd-op*) *bpnpd-record* t t)
             '(:fault :dispatch-authority))))
(assert-event
 (equal (fn-bpnp-dispatch-publication-authorize
         *bpnpd-state* *bpnpd-epoch* *bpnpd-op* *bpnpd-record* nil t)
        '(:fault :dispatch-authority)))
(assert-event
 (equal (fn-bpnp-dispatch-publication-authorize
         *bpnpd-state* *bpnpd-epoch* *bpnpd-op* *bpnpd-record* t nil)
        '(:fault :dispatch-authority)))
(must-fail-checked
 (assert-event
  (fn-bpnp-dispatch-publication-operationp
   (fn-bpnp-dispatch-publication-authorize
    *bpnpd-state* *bpnpd-epoch* (1+ *bpnpd-op*) *bpnpd-record* t t))))
