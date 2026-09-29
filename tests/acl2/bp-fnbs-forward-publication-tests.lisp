(in-package "ACL2")
(include-book "../../books/bp-fnbs-forward-publication")
(include-book "../../books/codec-attach")
(include-book "bp-node-forward-retry-tests")
(include-book "must-fail-checked")

; The live pending attempt of the retry fixture: the outer host-called step
; (fn-bpnp-step) reopened the session and issued the attempt; nothing has
; persisted it yet -- the state bp-service holds when it calls
; fn-bpnp-forward-publication-authorize (fnn-bps-persist-forward).
(defconst *bpnpf-state* *bpfr-pending*)
(defconst *bpnpf-issued* (fn-bpnf-issued *bpnpf-state*))
(defconst *bpnpf-epoch* (fn-bpn-nth 1 *bpnpf-issued*))
(defconst *bpnpf-op* (fn-bpn-nth 2 *bpnpf-issued*))
(defconst *bpnpf-record* (fn-bpn-nth 4 *bpnpf-issued*))
(make-event
 (list 'defconst '*bpnpf-operation*
       (list 'quote
             (fn-bpnp-forward-publication-authorize
              *bpnpf-state* *bpnpf-epoch* *bpnpf-op* *bpnpf-record* t t))))
(assert-event (fn-bpnp-forward-publication-operationp *bpnpf-operation*))
(assert-event (equal (fn-bpnp-attempt-unframe
                      (fn-bpnp-forward-publication-octets *bpnpf-operation*))
                     *bpnpf-record*))

; KEYSTONE teeth (PRF-1017,
; fn-bpnp-forward-publication-authorize-admits-exactly-the-issued-pending-forward):
; the positive witness above with its complete antecedent by name (the
; issued kind is :attempt, one of the three), then every part of the
; conclusion; then a wrong operation id, a withheld lock and a present final
; name (the antecedent affirmed otherwise) answer the authority fault
; exactly.
(assert-event
 (let ((issued (fn-bpnf-issued *bpnpf-state*)))
   (and (fn-bpnf-operationp issued)
        (fn-bpnf-operation-matchp issued *bpnpf-epoch* *bpnpf-op*)
        (equal (fn-bpn-nth 3 issued) :attempt)
        (member-equal (fn-bpn-nth 3 issued)
                      '(:attempt :forward-result :deferral))
        (equal (fn-bpn-nth 4 issued) *bpnpf-record*)
        (equal (fn-bpn-nth 5 issued) :pending)
        (equal (fn-bpnf-epoch *bpnpf-state*) *bpnpf-epoch*)
        (equal (fn-bpnf-next-op *bpnpf-state*) (1+ *bpnpf-op*))
        (equal (fn-bpn-nth 1 *bpnpf-record*) *bpnpf-epoch*)
        (equal (fn-bpn-nth 2 *bpnpf-record*) *bpnpf-op*)
        (not (equal (fn-bpnp-forward-publication-frame :attempt *bpnpf-record*)
                    :bad))
        (fn-bpnp-forward-publication-operationp *bpnpf-operation*)
        (equal (fn-bpn-nth 1 *bpnpf-operation*) *bpnpf-epoch*)
        (equal (fn-bpn-nth 2 *bpnpf-operation*) *bpnpf-op*)
        (equal (fn-bpn-nth 3 *bpnpf-operation*) *bpnpf-record*)
        (equal (fn-bpnp-forward-publication-name *bpnpf-operation*)
               (fn-bpnf-stored-record-name *bpnpf-epoch* *bpnpf-op*))
        (equal (fn-bpnp-forward-publication-octets *bpnpf-operation*)
               (fn-bpnp-forward-publication-frame :attempt *bpnpf-record*))
        (equal (fn-bpnp-forward-publication-octets *bpnpf-operation*)
               (fn-bpnp-attempt-frame *bpnpf-record*))
        (equal (fn-bpnp-forward-publication-publisher *bpnpf-operation*)
               (fn-jpub-initial t)))))
(assert-event
 (and (not (fn-bpnf-operation-matchp (fn-bpnf-issued *bpnpf-state*)
                                     *bpnpf-epoch* (1+ *bpnpf-op*)))
      (equal (fn-bpnp-forward-publication-authorize
              *bpnpf-state* *bpnpf-epoch* (1+ *bpnpf-op*) *bpnpf-record* t t)
             '(:fault :forward-authority))))
(assert-event
 (equal (fn-bpnp-forward-publication-authorize
         *bpnpf-state* *bpnpf-epoch* *bpnpf-op* *bpnpf-record* nil t)
        '(:fault :forward-authority)))
(assert-event
 (equal (fn-bpnp-forward-publication-authorize
         *bpnpf-state* *bpnpf-epoch* *bpnpf-op* *bpnpf-record* t nil)
        '(:fault :forward-authority)))
(must-fail-checked
 (assert-event
  (fn-bpnp-forward-publication-operationp
   (fn-bpnp-forward-publication-authorize
    *bpnpf-state* *bpnpf-epoch* (1+ *bpnpf-op*) *bpnpf-record* t t))))

; MUTATION witness (the codec fault): the authorization does not recognize
; the record itself, only its epoch, id and frame, so a state whose issued
; attempt carries a record with no identity octets (the attempt recognizer
; refuses it, its frame is :bad) passes every other check and answers the
; codec fault exactly -- the answer bp-service maps to :refused.  No
; reachable state issues such a record; this is the theorem's other fault
; arm, not a served case.
(defconst *bpnpf-unframable*
  (update-nth 4 nil *bpnpf-record*))
(defconst *bpnpf-mutated-state*
  (fn-bpnf-with-issued
   *bpnpf-state*
   (fn-bpnf-operation *bpnpf-epoch* *bpnpf-op* :attempt *bpnpf-unframable*
                      :pending)))
(assert-event
 (and (equal (fn-bpnp-forward-publication-frame :attempt *bpnpf-unframable*)
             :bad)
      (equal (fn-bpn-nth 1 *bpnpf-unframable*) *bpnpf-epoch*)
      (equal (fn-bpn-nth 2 *bpnpf-unframable*) *bpnpf-op*)
      (equal (fn-bpnp-forward-publication-authorize
              *bpnpf-mutated-state* *bpnpf-epoch* *bpnpf-op*
              *bpnpf-unframable* t t)
             '(:fault :forward-codec))))
