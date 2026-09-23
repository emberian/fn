; Finite A1 foundation for the future one-list BP processing machine.
; This named refinement delegates existing outbound events to fn-bpn-step.
; Reception here is a validated-bundle kernel, not a TCPCL or FNBS publisher.
(in-package "ACL2")
(include-book "bp-node-machine")
(set-verify-guards-eagerness 0)
(defconst *fn-bpnf-max-held-image* 131072)

; A partition is assigned from the admitted ingress principal before looking
; up an RFC 9171 bundle identity.  Nil is its own unauthenticated partition.
(defun fn-bpnf-ingress-principal (ingress)
  (declare (xargs :guard t))
  (if (and (true-listp ingress)
           (equal (len ingress) 6)
           (equal (car ingress) :cl))
      (fn-bpn-nth 4 ingress)
    nil))

; A kind-5 FNBS image can name only this typed TCPCL provenance.  The
; principal is the admitted configuration name, separate from peer-eid.
; Admission itself is a host boundary and is not proved by this shape check.
(defun fn-bpnf-cl-ingressp (ingress)
  (declare (xargs :guard t))
  (and (true-listp ingress) (equal (len ingress) 6)
       (equal (car ingress) :cl)
       (consp (fn-bpn-nth 1 ingress))
       (fn-bpn-machine-u64p (car (fn-bpn-nth 1 ingress)))
       (fn-bpn-machine-u64p (cdr (fn-bpn-nth 1 ingress)))
       (fn-bpn-machine-u64p (fn-bpn-nth 2 ingress))
       (fn-bpp-eidp (fn-bpn-nth 3 ingress))
       (or (null (fn-bpn-nth 4 ingress))
           (fn-bpn-machine-textp (fn-bpn-nth 4 ingress)))
       (fn-bpn-machine-u64p (fn-bpn-nth 5 ingress))))

(defun fn-bpnf-held-key (principal id)
  (declare (xargs :guard t))
  (list principal id))

; The immutable projection excludes only the three hop-local extension types.
; A later block-policy step will decide unsupported blocks before this kernel.
(defun fn-bpnf-immutable-blocks (blocks)
  (declare (xargs :guard t))
  (if (atom blocks)
      nil
    (if (and (fn-bpb-blockp (car blocks))
             (member-equal (fn-bpb-block-type (car blocks)) '(6 7 10)))
        (fn-bpnf-immutable-blocks (cdr blocks))
      (cons (car blocks) (fn-bpnf-immutable-blocks (cdr blocks))))))

(defun fn-bpnf-immutable (bundle)
  (declare (xargs :guard t))
  (if (fn-bpb-bundlep bundle)
      (list (fn-bpb-bundle-primary bundle)
            (fn-bpb-payload bundle)
            (fn-bpnf-immutable-blocks (fn-bpb-bundle-blocks bundle)))
    nil))

; The held row is intentionally explicit: bundle identity, arrival, ingress,
; submission, lineage, exact bundle/wire, anchor, dispatch, next hop,
; constraints, attempt, deletion and last token all have separate slots.
(defun fn-bpnf-held (principal id arrival ingress submission lineage bundle wire
                              anchor dispatch next-hop constraints attempt deleted token)
  (declare (xargs :guard t))
  (list :bpnf-held principal id arrival ingress submission lineage bundle wire
        anchor dispatch next-hop constraints attempt deleted token))

(defun fn-bpnf-held-principal (h) (declare (xargs :guard t)) (fn-bpn-nth 1 h))
(defun fn-bpnf-held-id (h) (declare (xargs :guard t)) (fn-bpn-nth 2 h))
(defun fn-bpnf-held-bundle (h) (declare (xargs :guard t)) (fn-bpn-nth 7 h))
(defun fn-bpnf-held-wire (h) (declare (xargs :guard t)) (fn-bpn-nth 8 h))

(defun fn-bpnf-heldp (h)
  (declare (xargs :guard t))
  (and (true-listp h) (equal (len h) 16)
       (equal (car h) :bpnf-held)
       (equal (fn-bpnf-held-principal h)
              (fn-bpnf-ingress-principal (fn-bpn-nth 4 h)))
       (natp (fn-bpn-nth 3 h))
       (fn-bpb-bundlep (fn-bpnf-held-bundle h))
       (equal (fn-bpnf-held-id h)
              (fn-bpb-bundle-id (fn-bpnf-held-bundle h)))
       (fn-cbor-octet-listp (fn-bpnf-held-wire h))
       (equal (fn-bpnf-held-wire h)
              (fn-bpb-encode (fn-bpnf-held-bundle h)))
       (natp (fn-bpn-nth 15 h))))

(defun fn-bpnf-find-held (key held)
  (declare (xargs :guard t))
  (if (atom held)
      nil
    (if (equal key (fn-bpnf-held-key (fn-bpnf-held-principal (car held))
                                      (fn-bpnf-held-id (car held))))
        (car held)
      (fn-bpnf-find-held key (cdr held)))))

(defun fn-bpnf-held-octets (held)
  (declare (xargs :guard t))
  (if (atom held)
      0
    (+ (len (fn-bpnf-held-wire (car held)))
       (fn-bpnf-held-octets (cdr held)))))

(defun fn-bpnf-receive-decision (held ingress bundle)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (let* ((principal (fn-bpnf-ingress-principal ingress))
         (id (fn-bpb-bundle-id bundle))
         (old (fn-bpnf-find-held (fn-bpnf-held-key principal id) held)))
    (cond ((not old) :fresh)
          ((equal (fn-bpnf-immutable (fn-bpnf-held-bundle old))
                  (fn-bpnf-immutable bundle)) :duplicate)
          (t :identity-conflict))))

; Authoritative submission outcomes and receipt handoffs have different keys
; and lifetimes.  Neither is inferred from the evictable correlation index.
(defun fn-bpnf-outcome (submission destination adu-id bundle-id sequence
                                  commitment expiry-evidence family result)
  (declare (xargs :guard t))
  (list :bpnf-outcome submission destination adu-id bundle-id sequence
        commitment expiry-evidence family result))

(defun fn-bpnf-outcomep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10)
       (equal (car x) :bpnf-outcome)))

(defun fn-bpnf-handoff (receipt-id trigger disposition)
  (declare (xargs :guard t))
  (list :bpnf-handoff receipt-id trigger disposition))

(defun fn-bpnf-handoffp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (equal (car x) :bpnf-handoff)
       (or (equal (fn-bpn-nth 3 x) :owed)
           (and (consp (fn-bpn-nth 3 x))
                (equal (car (fn-bpn-nth 3 x)) :handed-off)))))

; The operation id and process epoch jointly correlate every callback.
; The logical journal generation is a separate field of the record and is
; deliberately absent from this volatile callback identity.
(defun fn-bpnf-operation (epoch operation-id kind key status)
  (declare (xargs :guard t))
  (list :bpnf-operation epoch operation-id kind key status))

(defun fn-bpnf-operationp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)
       (equal (car x) :bpnf-operation)
       (natp (fn-bpn-nth 1 x)) (natp (fn-bpn-nth 2 x))
       (member-equal (fn-bpn-nth 3 x) '(:store :attempt :discard :handoff :family))
       (member-equal (fn-bpn-nth 5 x) '(:pending :uncertain))))

(defun fn-bpnf-operation-matchp (issued epoch operation-id)
  (declare (xargs :guard t))
  (and (consp issued)
       (equal (car issued) :bpnf-operation)
       (equal (fn-bpn-nth 1 issued) epoch)
       (equal (fn-bpn-nth 2 issued) operation-id)))

; A wait names an obligation and action as well as dependency versions.  A
; version change makes that action eligible for re-evaluation; it does not
; assert that the action will succeed.  This is per obligation, not per kind.
(defun fn-bpnf-wait (key action dependency versions condition)
  (declare (xargs :guard t))
  (list :bpnf-wait key action dependency versions condition))

(defun fn-bpnf-waitp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)
       (equal (car x) :bpnf-wait)
       (member-equal (fn-bpn-nth 3 x)
                     '(:route :session :fragments :credit :capacity
                       :history :after))))

(defun fn-bpnf-version-of (dependency versions)
  (declare (xargs :guard t))
  (if (atom versions)
      nil
    (if (equal dependency (fn-cbor-ag-car (car versions)))
        (fn-cbor-ag-cdr (car versions))
      (fn-bpnf-version-of dependency (cdr versions)))))

(defun fn-bpnf-wait-wakes-p (wait versions)
  (declare (xargs :guard t))
  (and (equal (fn-cbor-ag-car wait) :bpnf-wait)
       (not (equal (fn-bpn-nth 4 wait)
                   (fn-bpnf-version-of (fn-bpn-nth 3 wait) versions)))))

; The kernel state keeps the existing machine plus the new durable/volatile
; slots.  Next-op is allocated here, never supplied by a caller.  The host is
; not yet a caller: A2 must prove the FNBS publisher and replay relation
; before replacing the outbound-only host path.
(defun fn-bpnf-state (base held outcomes handoffs correlation issued waits epoch next-op)
  (declare (xargs :guard t))
  (list :bpnf-state base held outcomes handoffs correlation issued waits epoch next-op))

(defun fn-bpnf-base (st) (declare (xargs :guard t)) (fn-bpn-nth 1 st))
(defun fn-bpnf-held-list (st) (declare (xargs :guard t)) (fn-bpn-nth 2 st))
(defun fn-bpnf-outcomes (st) (declare (xargs :guard t)) (fn-bpn-nth 3 st))
(defun fn-bpnf-handoffs (st) (declare (xargs :guard t)) (fn-bpn-nth 4 st))
(defun fn-bpnf-correlation (st) (declare (xargs :guard t)) (fn-bpn-nth 5 st))
(defun fn-bpnf-issued (st) (declare (xargs :guard t)) (fn-bpn-nth 6 st))
(defun fn-bpnf-waits (st) (declare (xargs :guard t)) (fn-bpn-nth 7 st))
(defun fn-bpnf-epoch (st) (declare (xargs :guard t)) (fn-bpn-nth 8 st))
(defun fn-bpnf-next-op (st) (declare (xargs :guard t)) (fn-bpn-nth 9 st))

(defun fn-bpnf-with-issued (st issued)
  (declare (xargs :guard t))
  (fn-bpnf-state (fn-bpnf-base st) (fn-bpnf-held-list st)
                 (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                 (fn-bpnf-correlation st) issued (fn-bpnf-waits st)
                 (fn-bpnf-epoch st) (fn-bpnf-next-op st)))

(defun fn-bpnf-answer (st effects)
  (declare (xargs :guard t))
  (list :bpnf-answer st effects))
(defun fn-bpnf-answer-state (ans) (declare (xargs :guard t)) (fn-bpn-nth 1 ans))
(defun fn-bpnf-answer-effects (ans) (declare (xargs :guard t)) (fn-bpn-nth 2 ans))

; Recovery is cold-path validation of the ACL2 byte replay result.  The host
; obtains that result from fn-bpnf-replay-rows on observed FNBS name/bytes;
; the composition book binds the event argument to that exact call.
(defun fn-bpnf-recovery-heldp (held max-held max-octets)
  (declare (xargs :guard t))
  (and (natp max-held)
       (natp max-octets)
       (true-listp held)
       (<= (len held) max-held)
       (<= (fn-bpnf-held-octets held) max-octets)
       (if (atom held) t
         (and (fn-bpnf-heldp (car held))
              (fn-bpnf-recovery-heldp (cdr held) max-held max-octets)))))

(defun fn-bpnf-recover-fnbs-step (st new-epoch base-records sequence-ready replay-result)
  (declare (xargs :guard
                  (and (fn-bpn-machine-statep (fn-bpnf-base st))
                       (true-listp base-records)
                       (<= (len base-records) *fn-bpn-machine-max-records*))))
  (let ((base-answer
         (fn-bpn-restart-step (fn-bpnf-base st) base-records sequence-ready))
        (prior (fn-bpn-nth 2 replay-result)))
    (if (not (and (true-listp replay-result)
                  (equal (len replay-result) 3)
                  (equal (car replay-result) :ready)
                  (or (null prior)
                      (and (consp prior) (natp (car prior))
                           (natp (cdr prior))))
                  (fn-frame-natp new-epoch)
                  (natp (fn-bpnf-epoch st))
                  (< (fn-bpnf-epoch st) new-epoch)
                  (or (null prior) (< (car prior) new-epoch))
                  (fn-bpnf-recovery-heldp
                   (fn-bpn-nth 1 replay-result)
                   (fn-bpn-machine-state-max-jobs
                    (fn-bpn-answer-state base-answer))
                   (fn-bpn-machine-state-max-octets
                    (fn-bpn-answer-state base-answer)))
                  (equal (car (fn-bpn-answer-effects base-answer))
                         (list :restart-ready
                               (len (fn-bpn-machine-state-jobs
                                     (fn-bpn-answer-state base-answer)))))))
        (fn-bpnf-answer st (list (list :restart-fault :fnbs-or-base)))
      (fn-bpnf-answer
       (fn-bpnf-state (fn-bpn-answer-state base-answer)
                      (fn-bpn-nth 1 replay-result)
                      nil nil nil nil nil new-epoch 0)
       (list (list :restart-ready
                   (len (fn-bpn-nth 1 replay-result))))))))

(defun fn-bpnf-step (st event)
  (declare (xargs :guard
                  (and (fn-bpn-machine-statep (fn-bpnf-base st))
                       (or (not (equal (fn-cbor-ag-car event) :base))
                           (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                       (or (not (equal (fn-cbor-ag-car event) :recover-fnbs))
                           (and (true-listp (fn-bpn-nth 2 event))
                                (<= (len (fn-bpn-nth 2 event))
                                    *fn-bpn-machine-max-records*))))))
  (if (equal (fn-cbor-ag-car event) :recover-fnbs)
      (fn-bpnf-recover-fnbs-step
       st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
       (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))
    (if (equal (fn-cbor-ag-car event) :base)
      (if (fn-bpnf-issued st)
          (fn-bpnf-answer st nil)
        (let ((ans (fn-bpn-step (fn-bpnf-base st) (fn-bpn-nth 1 event))))
        (fn-bpnf-answer
         (fn-bpnf-state (fn-bpn-answer-state ans) (fn-bpnf-held-list st)
                        (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                        (fn-bpnf-correlation st) (fn-bpnf-issued st)
                        (fn-bpnf-waits st) (fn-bpnf-epoch st)
                        (fn-bpnf-next-op st))
         (fn-bpn-answer-effects ans))))
    (if (equal (fn-cbor-ag-car event) :persist-result)
        (let ((issued (fn-bpnf-issued st)))
          (if (or (equal (fn-bpn-nth 5 issued) :uncertain)
                  (not (fn-bpnf-operation-matchp issued (fn-bpn-nth 1 event) (fn-bpn-nth 2 event))))
              (fn-bpnf-answer st nil)
            (if (equal (fn-bpn-nth 3 event) :durable)
                (if (equal (fn-bpn-nth 5 issued) :pending)
                    (let ((h (fn-bpn-nth 4 issued)))
                      (fn-bpnf-answer
                       (fn-bpnf-state (fn-bpnf-base st)
                                      (cons h (fn-bpnf-held-list st))
                                      (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                                      (fn-bpnf-correlation st) nil
                                      (fn-bpnf-waits st) (fn-bpnf-epoch st)
                                      (fn-bpnf-next-op st))
                       (list (list :receive-answer (fn-bpn-nth 4 h) :stored))))
                  (fn-bpnf-answer st nil))
              (if (equal (fn-bpn-nth 3 event) :refused)
                  (fn-bpnf-answer
                   (fn-bpnf-with-issued st nil)
                   (list (list :receive-answer (fn-bpn-nth 4 (fn-bpn-nth 4 issued))
                               '(:refused :persistence))))
                (fn-bpnf-answer
                 (fn-bpnf-with-issued
                  st (fn-bpnf-operation (fn-bpn-nth 1 issued) (fn-bpn-nth 2 issued)
                                          (fn-bpn-nth 3 issued) (fn-bpn-nth 4 issued)
                                          :uncertain))
                 (list (list :receive-answer (fn-bpn-nth 4 (fn-bpn-nth 4 issued))
                             '(:uncertain :persistence))))))))
      (if (equal (fn-cbor-ag-car event) :receive-bundle)
        (let* ((bundle (fn-bpn-nth 1 event))
               (wire (fn-bpn-nth 2 event))
               (ingress (fn-bpn-nth 3 event))
               (decision (and (fn-bpnf-cl-ingressp ingress)
                              (fn-bpb-bundlep bundle)
                              (fn-cbor-octet-listp wire)
                              (equal wire (fn-bpb-encode bundle))
                              (fn-bpnf-receive-decision
                               (fn-bpnf-held-list st) ingress bundle))))
          (if (fn-bpnf-issued st)
              (fn-bpnf-answer st (list (list :receive-answer ingress
                                                '(:refused :busy))))
            (if (or (not (fn-frame-natp (fn-bpnf-epoch st)))
                    (not (fn-frame-natp (fn-bpnf-next-op st)))
                    (equal (fn-bpnf-next-op st) *fn-frame-max-nat*))
              (fn-bpnf-answer st (list (list :receive-answer ingress
                                                '(:refused :arguments))))
            (if (not decision)
                (fn-bpnf-answer st (list (list :receive-answer ingress
                                                  '(:refused :invalid-bundle))))
            (if (not (equal decision :fresh))
                (fn-bpnf-answer st (list (list :receive-answer ingress decision)))
              (if (or (> (len wire) *fn-bpnf-max-held-image*)
                      (>= (len (fn-bpnf-held-list st))
                          (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))
                      (> (+ (fn-bpnf-held-octets (fn-bpnf-held-list st))
                            (len wire))
                         (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
                  (fn-bpnf-answer st (list (list :receive-answer ingress
                                                    '(:refused :capacity))))
              (let* ((id (fn-bpb-bundle-id bundle))
                     (principal (fn-bpnf-ingress-principal ingress))
                     (arrival (len (fn-bpnf-held-list st)))
                     (h (fn-bpnf-held principal id arrival ingress nil nil bundle wire
                                      nil nil nil '(:dispatch-pending) nil nil arrival)))
                (fn-bpnf-answer
                 (fn-bpnf-state (fn-bpnf-base st)
                                (fn-bpnf-held-list st)
                                (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                                (fn-bpnf-correlation st)
                                (fn-bpnf-operation (fn-bpnf-epoch st)
                                                   (fn-bpnf-next-op st) :store h :pending)
                                (fn-bpnf-waits st) (fn-bpnf-epoch st)
                                (1+ (fn-bpnf-next-op st)))
                 (list (list :persist (fn-bpnf-epoch st)
                             (fn-bpnf-next-op st) h))))))))))
        (fn-bpnf-answer st nil))))))

; This is a precise bridge to the current host-called outbound subject.
(defthm fn-bpnf-base-step-is-fn-bpn-step
  (implies (not (fn-bpnf-issued st))
           (equal (fn-bpnf-base (fn-bpnf-answer-state
                                  (fn-bpnf-step st (list :base event))))
                  (fn-bpn-answer-state (fn-bpn-step (fn-bpnf-base st) event))))
  :hints (("Goal" :in-theory (disable fn-bpn-step)))
  :rule-classes nil)

; Reception cannot discard one principal's evidence because another
; principal holds the same bundle id or different content under that id.
(defthm fn-bpnf-other-principal-does-not-match
  (implies (not (equal (fn-bpnf-held-principal h)
                       (fn-bpnf-ingress-principal ingress)))
           (equal (fn-bpnf-receive-decision (list h) ingress bundle)
                  :fresh)))

(defthm fn-bpnf-stale-operation-cannot-match
  (implies (or (not (equal (fn-bpn-nth 1 issued) epoch))
               (not (equal (fn-bpn-nth 2 issued) operation-id)))
           (not (fn-bpnf-operation-matchp issued epoch operation-id))))

(defthm fn-bpnf-unchanged-dependency-does-not-wake
  (implies (and (equal (car wait) :bpnf-wait)
                (equal (fn-bpn-nth 4 wait)
                       (fn-bpnf-version-of (fn-bpn-nth 3 wait) versions)))
           (not (fn-bpnf-wait-wakes-p wait versions))))

(defthm fn-bpnf-receive-proposal-does-not-install-held
  (equal (fn-bpnf-held-list
          (fn-bpnf-answer-state (fn-bpnf-step st (list :receive-bundle bundle wire ingress))))
         (fn-bpnf-held-list st))
  :hints (("Goal" :in-theory (disable fn-bpn-step fn-bpb-encode
                                     fn-bpb-bundlep fn-bpb-bundle-id))))

(defthm fn-bpnf-stale-publication-does-not-install-held
  (implies (not (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op))
           (equal (fn-bpnf-held-list
                   (fn-bpnf-answer-state
                    (fn-bpnf-step st (list :persist-result epoch op :durable))))
                  (fn-bpnf-held-list st)))
  :hints (("Goal" :in-theory (disable fn-bpn-step))))

(defthm fn-bpnf-install-requires-matched-durable-publication
  (implies (not (equal (fn-bpnf-held-list
                        (fn-bpnf-answer-state
                         (fn-bpnf-step st (list :persist-result epoch op result))))
                       (fn-bpnf-held-list st)))
           (and (equal result :durable)
                (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bpn-step))))

; No ordinary callback can resolve an ambiguous publication.  Recovery will
; inspect the authoritative FNBS bytes and establish a new process epoch.
(defthm fn-bpnf-uncertain-issued-fences-every-step
  (implies (and (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
                (not (equal (car event) :recover-fnbs)))
           (equal (fn-bpnf-answer-state (fn-bpnf-step st event)) st))
  :hints (("Goal" :in-theory (disable fn-bpn-step fn-bpb-encode
                                     fn-bpb-bundlep fn-bpb-bundle-id)))
  :rule-classes nil)

; The issued publication consumes a fresh id from this state, irrespective
; of caller input.  Refusal does not decrement the frontier.
(defthm fn-bpnf-receive-proposal-consumes-next-operation-id
  (implies (equal (car (car (fn-bpnf-answer-effects
                             (fn-bpnf-step st
                                           (list :receive-bundle bundle wire ingress)))))
                  :persist)
           (and (equal (fn-bpn-nth 2 (car (fn-bpnf-answer-effects
                                     (fn-bpnf-step st
                                                   (list :receive-bundle bundle wire ingress)))))
                       (fn-bpnf-next-op st))
                (equal (fn-bpnf-next-op
                        (fn-bpnf-answer-state
                         (fn-bpnf-step st
                                       (list :receive-bundle bundle wire ingress))))
                       (1+ (fn-bpnf-next-op st)))))
  :hints (("Goal" :in-theory (disable fn-bpn-step fn-bpb-encode
                                     fn-bpb-bundlep fn-bpb-bundle-id)))
  :rule-classes nil)

(defthm fn-bpnf-next-operation-id-never-decreases
  (implies (not (equal (car event) :recover-fnbs))
           (<= (fn-bpnf-next-op st)
               (fn-bpnf-next-op
                (fn-bpnf-answer-state (fn-bpnf-step st event)))))
  :hints (("Goal" :in-theory (disable fn-bpn-step fn-bpb-encode
                                     fn-bpb-bundlep fn-bpb-bundle-id)))
  :rule-classes nil)

; Guard closure for the typed foundation helpers.  The served step remains
; open until the inherited fn-bpn-step guard and FNBS caller are verified.
(verify-guards fn-bpnf-ingress-principal)
(verify-guards fn-bpnf-cl-ingressp)
(verify-guards fn-bpnf-held-key)
(verify-guards fn-bpnf-immutable-blocks)
(verify-guards fn-bpnf-immutable)
(verify-guards fn-bpnf-held)
(verify-guards fn-bpnf-held-principal)
(verify-guards fn-bpnf-held-id)
(verify-guards fn-bpnf-held-bundle)
(verify-guards fn-bpnf-held-wire)
(verify-guards fn-bpnf-heldp)
(verify-guards fn-bpnf-find-held)
(verify-guards fn-bpnf-held-octets)
(verify-guards fn-bpnf-receive-decision)
(verify-guards fn-bpnf-outcome)
(verify-guards fn-bpnf-outcomep)
(verify-guards fn-bpnf-handoff)
(verify-guards fn-bpnf-handoffp)
(verify-guards fn-bpnf-operation)
(verify-guards fn-bpnf-operationp)
(verify-guards fn-bpnf-operation-matchp)
(verify-guards fn-bpnf-wait)
(verify-guards fn-bpnf-waitp)
(verify-guards fn-bpnf-version-of)
(verify-guards fn-bpnf-wait-wakes-p)
(verify-guards fn-bpnf-state)
(verify-guards fn-bpnf-base)
(verify-guards fn-bpnf-held-list)
(verify-guards fn-bpnf-outcomes)
(verify-guards fn-bpnf-handoffs)
(verify-guards fn-bpnf-correlation)
(verify-guards fn-bpnf-issued)
(verify-guards fn-bpnf-waits)
(verify-guards fn-bpnf-epoch)
(verify-guards fn-bpnf-next-op)
(verify-guards fn-bpnf-with-issued)
(verify-guards fn-bpnf-answer)
(verify-guards fn-bpnf-answer-state)
(verify-guards fn-bpnf-answer-effects)
