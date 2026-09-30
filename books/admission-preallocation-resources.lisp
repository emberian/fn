; Internal canonical admission charge transition over the ONE shared PRL.
; The public producer derives identity and demand from actual owner/census.
; Supplied demand or a returned old ROW is not an allocation capability.
(in-package "ACL2")
(include-book "page-read-ledger")
(include-book "index-query-resources")
(include-book "state-globals")

(local (defthm fn-apr-natural-vector-true-listp
 (implies (fn-prs-nats-p x) (true-listp x))
 :hints (("Goal" :induct (fn-prs-nats-p x)
          :in-theory (enable fn-prs-nats-p)))))
(local (defthm fn-apr-resource-vector-true-listp
 (implies (fn-prs-vectorp x) (true-listp x))
 :hints (("Goal" :in-theory (enable fn-prs-vectorp)))))

(defun fn-apr-naturals (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (null x)
  (and (consp x) (natp (car x)) (fn-apr-naturals (1- n) (cdr x)))))
; (process epoch, actual SF predecessor count, prepared sequence, txid, operation)
(defun fn-apr-identityp (x)
 (declare (xargs :guard t))
 (and (fn-apr-naturals 4 (list (fn-prl-nth 0 x) (fn-prl-nth 1 x)
                            (fn-prl-nth 2 x) (fn-prl-nth 3 x)))
      (member-eq (fn-prl-nth 4 x) '(:article :identity :retention :consumer :topic :config))
      (consp x) (consp (cdr x)) (consp (cddr x))
      (consp (cdddr x)) (consp (cddddr x)) (null (cdr (cddddr x)))))
(defun fn-apr-token (nonce identity)
 (declare (xargs :guard t))
 (list :admission-grant nonce (fn-prl-nth 0 identity) (fn-prl-nth 1 identity)
       (fn-prl-nth 2 identity) (fn-prl-nth 3 identity) (fn-prl-nth 4 identity)))
(defun fn-apr-widthp (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (null x)
  (and (consp x) (fn-apr-widthp (1- n) (cdr x)))))
(defun fn-apr-tokenp (token)
 (declare (xargs :guard t))
 (and (fn-apr-widthp 7 token) (eq (fn-prl-nth 0 token) :admission-grant)
      (natp (fn-prl-nth 1 token)) (natp (fn-prl-nth 2 token))
      (natp (fn-prl-nth 3 token)) (natp (fn-prl-nth 4 token))
      (natp (fn-prl-nth 5 token))
      (member-eq (fn-prl-nth 6 token) '(:article :identity :retention :consumer :topic :config))))
(defun fn-apr-livep (token row)
 (declare (xargs :guard t))
 (and (fn-apr-widthp 5 row) (fn-apr-tokenp token)
      (fn-apr-tokenp (fn-prl-nth 0 row))
      (equal token (fn-prl-nth 0 row))
      (member-eq (fn-prl-nth 2 row) '(:reserved :produced :promoted :uncertain))))

; Internal algebra only: CURRENT is fetched from the actual exclusive owner
; pending slot in the atomic STATE+pool wrapper, never accepted from its caller.
; Current row stores (token charged phase borrowed-base next-ready10). C includes this row
; under the joint pool+owner-slot relation; PRL bindings remain untouched.
(defun fn-apr-issue (identity demand rescue base current ledger)
 (declare (xargs :guard t))
 (if current (mv :admission-busy current ledger)
  (if (not (and (fn-apr-identityp identity) (fn-prs-vectorp demand)
                (equal (fn-prl-nth 4 demand) 1)))
   (mv :invalid-admission-census current ledger)
   (mv-let (word next charged)
    (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) rescue
                 (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                 (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
    (if (not (eq word :admitted)) (mv word current ledger)
     (mv :reserved
         (list (fn-apr-token (fn-prl-nth 2 ledger) identity) demand :reserved base nil)
         (fn-prl-build (fn-prl-nth 0 ledger) charged next
                       (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))))))))

(defun fn-apr-produced (token next-ready current)
 (declare (xargs :guard t))
 (if (not (and (fn-apr-livep token current)
                (eq (fn-prl-nth 2 current) :reserved)))
  (mv :stale current)
  (mv :produced (list token (fn-prl-nth 1 current) :produced (fn-prl-nth 3 current) next-ready))))
(defun fn-apr-uncertain (token current)
 (declare (xargs :guard t))
 (if (not (fn-apr-livep token current)) (mv :stale current)
  (if (eq (fn-prl-nth 2 current) :uncertain) (mv :uncertain current)
  (mv :uncertain (list token (fn-prl-nth 1 current) :uncertain
                      (fn-prl-nth 3 current) (fn-prl-nth 4 current))))))

; Neither cancellation nor ambiguous completion relinquishes old/new graphs.
; Settlement is permitted only after the actual owner has joined publication
; and relinquished private references. Spent nonce coordinate is never refunded.
(defun fn-apr-release (token joined current ledger)
 (declare (xargs :guard t))
 (cond ((not (fn-apr-livep token current)) (mv :stale current ledger))
       ((not (eq joined :joined)) (mv :not-joined current ledger))
       ((not (and (fn-prs-vectorp (fn-prl-nth 1 ledger))
                   (fn-prs-vectorp (fn-prl-nth 1 current))
                   (fn-prs-below (list (fn-prl-nth 0 (fn-prl-nth 1 current))
                                        (fn-prl-nth 1 (fn-prl-nth 1 current))
                                        (fn-prl-nth 2 (fn-prl-nth 1 current))
                                        (fn-prl-nth 3 (fn-prl-nth 1 current)) 0)
                                 (fn-prl-nth 1 ledger))))
        (mv :invalid-resource-state current ledger))
       (t (mv :released nil
           (fn-prl-build (fn-prl-nth 0 ledger)
              (fn-prs-release-reusable (fn-prl-nth 1 ledger) (fn-prl-nth 1 current))
              (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))))))

 ; INTERNAL only: RETAINED comes from the installed backing producer and the
; actual wrapper must fetch CURRENT. No host-supplied retained vector is a grant.
; Spent nonce is excluded; C->U transfer and row reduction happen together.
(defun fn-apr-promotablep (token retained current ledger)
 (declare (xargs :guard t))
 (and (fn-apr-livep token current)
      (eq (fn-prl-nth 2 current) :produced)
      (fn-prs-vectorp retained) (equal (fn-prl-nth 4 retained) 0)
      (fn-prs-vectorp (fn-prl-nth 1 current))
      (fn-prs-vectorp (fn-prl-nth 1 ledger))
      (fn-prs-vectorp (fn-prl-baseline ledger))
      (fn-prs-below retained (fn-prl-nth 1 current))
      (fn-prs-below retained (fn-prl-nth 1 ledger))))
(defun fn-apr-promote (token retained current ledger)
 (declare (xargs :guard t
          :guard-hints (("Goal" :in-theory
            (enable fn-apr-promotablep)))))
 (if (not (fn-apr-promotablep token retained current ledger))
  (mv :refused current ledger)
  (mv :promoted
      (list token
            (fn-prs-release-reusable (fn-prl-nth 1 current) retained)
            :promoted (fn-prl-nth 3 current) (fn-prl-nth 4 current))
      (fn-iqr-promoted-ledger ledger retained))))
(defthm fn-apr-refused-promotion-keeps-authority
 (implies (not (fn-apr-promotablep token retained current ledger))
  (and (equal (mv-nth 1 (fn-apr-promote token retained current ledger)) current)
       (equal (mv-nth 2 (fn-apr-promote token retained current ledger)) ledger))))
(defthm fn-apr-current-backing-cannot-be-promoted-twice
 (implies (equal (mv-nth 0 (fn-apr-promote token retained current ledger)) :promoted)
  (let ((next-current (mv-nth 1 (fn-apr-promote token retained current ledger)))
        (next-ledger (mv-nth 2 (fn-apr-promote token retained current ledger))))
   (and (equal (mv-nth 0 (fn-apr-promote token retained next-current next-ledger)) :refused)
        (equal (mv-nth 1 (fn-apr-promote token retained next-current next-ledger)) next-current)
        (equal (mv-nth 2 (fn-apr-promote token retained next-current next-ledger)) next-ledger))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-apr-promote fn-apr-promotablep fn-prl-nth)
       (fn-apr-livep fn-prs-vectorp fn-prs-below fn-prs-release-reusable
        fn-iqr-promoted-ledger fn-prl-baseline)))))
(in-theory (disable fn-apr-promotablep fn-apr-promote))

(defthm fn-apr-busy-preserves-shared-authority
 (implies current
  (and (equal (mv-nth 1 (fn-apr-issue identity demand rescue base current ledger)) current)
       (equal (mv-nth 2 (fn-apr-issue identity demand rescue base current ledger)) ledger))))
(defthm fn-apr-stale-callback-cannot-refund
 (implies (not (fn-apr-livep token current))
  (and (equal (mv-nth 1 (fn-apr-release token joined current ledger)) current)
       (equal (mv-nth 2 (fn-apr-release token joined current ledger)) ledger))))
(defthm fn-apr-unjoined-keeps-charge
 (implies (not (eq joined :joined))
  (equal (mv-nth 2 (fn-apr-release token joined current ledger)) ledger)))
(in-theory (disable fn-apr-identityp fn-apr-token fn-apr-livep fn-apr-issue
                    fn-apr-produced fn-apr-uncertain fn-apr-release))

; Fixed SAME decision payload held in CURRENT row NEXT slot. EVENT is borrowed
; from the actual candidate before dir-result clears it. The constructor is
; internal: the actual issuer/caller establishes its source/current relation.
(defun fn-apr-operation-packet (event checked fields status effect child sizes
                               next-ready prefix-node next-prefix-node)
 (declare (xargs :guard t))
 (list event checked fields status effect child sizes next-ready prefix-node next-prefix-node))
(defun fn-apr-operation-packetp (packet)
 (declare (xargs :guard t))
 (and (fn-apr-widthp 10 packet)
      (member-eq (fn-prl-nth 3 packet) '(:carried :unavailable))))
(defun fn-apr-current-operation-packet (current)
 (declare (xargs :guard t))
 (and (fn-apr-livep (fn-prl-nth 0 current) current)
      (member-eq (fn-prl-nth 2 current) '(:produced :promoted :uncertain))
      (fn-apr-operation-packetp (fn-prl-nth 4 current))
      (fn-prl-nth 4 current)))
(in-theory (disable fn-apr-operation-packet fn-apr-operation-packetp
                    fn-apr-current-operation-packet))

; Exact CURRENT slot-only readout. No caller row or token selects a past packet.
(defun fn-apr-owner-current (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-canonical-admission-pending state)
      (f-get-global 'fn-owner-canonical-admission-pending state)))
(defun fn-apr-owner-produced-capture (state)
 (declare (xargs :stobjs state :guard t))
 (fn-apr-current-operation-packet (fn-apr-owner-current state)))
(in-theory (disable fn-apr-owner-current fn-apr-owner-produced-capture))

; Internal phase selector: public wrapper supplies only actual core scalars,
; fetched CURRENT slot and SAME pool. This cannot authorize an allocation.
(defun fn-apr-continuation-kind (action current ledger profile-present epoch
                                count phase completion)
 (declare (xargs :guard t
  :guard-hints (("Goal" :in-theory
   (e/d (fn-apr-livep fn-apr-tokenp)
    (fn-apr-widthp fn-prs-vectorp fn-prs-below fn-prl-nth
     fn-apr-current-operation-packet))))))
 (let* ((token (fn-prl-nth 0 current))
        (charge (fn-prl-nth 1 current))
        (charged (fn-prl-nth 1 ledger))
        (packet (fn-apr-current-operation-packet current)))
  (cond
   ((not (member-eq action '(:precheck :prepare :record-dir :commit :abort :joined)))
    :invalid-continuation-action)
   ((not profile-present) :admission-profile-unavailable)
   ((null current) :admission-census-unavailable)
   ((not (fn-apr-livep token current)) :stale)
   ((not (and (natp epoch) (equal epoch (fn-prl-nth 2 token)))) :stale)
   ((eq (fn-prl-nth 2 current) :uncertain) :admission-recovery-required)
   ((not (and (fn-apr-widthp 5 (fn-prl-nth 0 ledger))
               (fn-apr-widthp 5 charged) (fn-apr-widthp 5 charge)
               (fn-prs-vectorp (fn-prl-nth 0 ledger))
               (fn-prs-vectorp charged) (fn-prs-vectorp charge)
               (fn-prs-below charge charged)))
    :invalid-resource-state)
   ((eq (fn-prl-nth 2 current) :reserved) :admission-yield)
   ((member-eq action '(:abort :joined)) :admission-join-unavailable)
   ((null packet) :admission-packet-unavailable)
   ((not (and (natp count)
               (if (eq action :commit)
                (and (eq phase :completing)
                     (equal count (+ 1 (fn-prl-nth 3 token)))
                     (equal completion
                            (cons (fn-prl-nth 4 token) (fn-prl-nth 5 token))))
                (and (equal count (fn-prl-nth 3 token))
                     (cond ((eq action :prepare) (eq phase :reserved))
                           ((eq action :record-dir) (eq phase :record-attempted))
                           (t t))))))
    :admission-phase-unavailable)
   ((not (eq (fn-prl-nth 3 packet) :carried)) :canonical-size-unavailable)
   ; Presence/shape, profile and residual C do not prove installed runtime
   ; adequacy or a bounded semantic executor. Refuse before producer mutation.
   (t :admission-executor-unavailable))))

(defthm fn-apr-continuation-never-authorizes-producer-allocation
 (member-eq (fn-apr-continuation-kind action current ledger profile-present
                                     epoch count phase completion)
  '(:invalid-continuation-action :admission-profile-unavailable
    :admission-census-unavailable :stale :admission-recovery-required
    :invalid-resource-state :admission-yield :admission-join-unavailable
    :admission-packet-unavailable :admission-phase-unavailable
    :canonical-size-unavailable :admission-executor-unavailable))
 :hints (("Goal" :in-theory
  (e/d (fn-apr-continuation-kind)
   (fn-apr-livep fn-apr-widthp fn-prs-vectorp fn-prs-below
    fn-apr-current-operation-packet fn-prl-nth)))))
