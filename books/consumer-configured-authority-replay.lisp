; Actual cfg-first recovery continuation. The caller retains the SAME parsed
; row, ORIGINALctx decision and prefix history source. This additive boundary
; is not yet admitted/guard-verified in the modern Store world. In particular
; a final history index must never be substituted for PREFIX-FILES/FN-HIST.
(in-package "ACL2")
(include-book "config-physical-replay")
(include-book "consumer-authority-carried-fold")
(include-book "consumer-account-config-commit")

; Fixed17, including the two unconsumed journal tails. These aliases and the
; prefix history belong to the actual recovery source, not native arguments
; authorizing an account. The initial/cold producer must establish all of
; their correspondence, including nonempty account and entry metadata.
(defun fn-capr-state (cn original fields cp metadata preparation publication
                        begin-count withdrawals visible verdicts cs es
                        configs events config-history)
 (declare (xargs :guard t))
 (list :configured-authority-replay cn original fields cp metadata preparation
       publication begin-count withdrawals visible verdicts cs es
       configs events config-history))

(defun fn-capr-fault (s reason)
 (declare (xargs :guard t))
 (list :fault s reason))

; Full7 E and full8 C both contain the exact original full6 prefix. Never run
; an account decision again to obtain its publication or canonical carries.
(defun fn-capr-publication (old full)
 (declare (xargs :guard t))
 (list :ok (fn-cp-nth 1 full)
       (if (fn-cp-nth 2 full) (fn-cp-nth 2 full) (fn-cp-nth 2 old))
       (if (fn-cp-nth 2 full) (fn-cp-nth 3 full) (fn-cp-nth 3 old))))

(defun fn-capr-install (s cn original fields full preparation begin-count
                          withdrawals visible verdicts cs es configs events)
 (declare (xargs :guard t))
 (list :advanced
   (fn-capr-state cn original fields (fn-cp-nth 1 full) (fn-cp-nth 4 full)
     preparation (fn-capr-publication (fn-cp-nth 7 s) full) begin-count
     withdrawals visible verdicts cs es configs events (fn-cp-nth 16 s))
   full))

; Literal C evidence remains borrowed. The actual joint decision captures its
; effective config; this descriptor requests the missing maintained pinned
; config-at projection, and is explicitly NOT a usable lookup/source token.
(defun fn-capr-config-source-required (s configured record)
 (declare (xargs :guard t))
 (let ((old (fn-cp-nth 16 s)))
  (list :typed-config-source-required
        (if (eq (fn-cp-nth 0 old) :typed-config-source-required)
            (fn-cp-nth 1 old) old)
        configured (fn-cfg-record-generation record)
        (fn-stxk-context-current-generation (fn-cp-nth 2 s))
        (fn-cfg-record-sequence record) (fn-cfg-record-txid record))))

; This is the actual ordinary physical C decision, factored additively from
; FnCPRLoop's branch. Typed C is deliberately dispatched BEFORE this gate.
(defun fn-capr-config-physical (cn record cs)
 (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil))
 (let* ((node (fn-cnode-node cn)) (txid (fn-cfg-record-txid record)))
  (cond ((not (fn-cfg-recordp record)) '(:refused :invalid-config-record))
        ((not (equal (fn-cfg-record-sequence record) cs)) '(:refused :config-sequence))
        ((not (fn-replay-advance-okp node txid)) '(:refused :config-txid))
        (t (let ((at (fn-cnode-make (fn-replay-advance-txid node txid)
                                    (fn-cnode-config cn))))
             (cond ((mbe :logic (not (fn-cnode-statep at)) :exec nil)
                    '(:refused :invalid-node))
                   ((not (mbe :logic (fn-cnode-record-acceptablep at record (fn-cnode-line-ceiling))
                              :exec (fn-cnode-carried-acceptablep at record (fn-cnode-line-ceiling))))
                    '(:refused :config-refusal))
                   (t (list :ok (fn-cnode-apply-config at record (fn-cnode-line-ceiling))))))))))

(defun fn-capr-config-step (s)
 (declare (xargs :guard (fn-cnode-statep (fn-cp-nth 1 s)) :verify-guards nil))
 (let* ((cn (fn-cp-nth 1 s)) (configs (fn-cp-nth 14 s)) (record (fn-cp-nth 0 configs))
        (cs (fn-cp-nth 12 s)) (es (fn-cp-nth 13 s))
        (cp (fn-cp-nth 4 s)) (metadata (fn-cp-nth 5 s)))
  (if (fn-cacm-recordp record)
   (let* ((prep (fn-cp-nth 6 s)) (txid (fn-cfg-record-txid record))
          (node (fn-cnode-node cn)))
    (cond ((not (equal (fn-cfg-record-sequence record) cs)) (fn-capr-fault s :config-sequence))
          ((not (equal (fn-cfg-generation (fn-cnode-config cn))
                       (fn-cfg-generation (fn-cp-nth 2 prep))))
           (fn-capr-fault s :account-config-base))
          ((not (fn-replay-advance-okp node txid)) (fn-capr-fault s :config-txid))
          (t (let ((full (fn-acj-commit cp metadata prep record (fn-cp-nth 8 s) es)))
               (if (not (eq (fn-cp-nth 0 full) :ok)) (fn-capr-fault s full)
                (fn-capr-install
                 (ec-call (update-nth 16 (fn-capr-config-source-required s (fn-cp-nth 6 full) record) s))
                 (fn-cnode-make (fn-replay-advance-txid node txid) (fn-cp-nth 6 full))
                 (fn-cp-nth 2 s) (fn-cp-nth 3 s) full nil nil
                 (fn-cp-nth 9 s) (fn-cp-nth 10 s) (fn-cp-nth 11 s)
                 (1+ (nfix cs)) es (ec-call (cdr configs)) (fn-cp-nth 15 s)))))))
   (let ((physical (fn-capr-config-physical cn record cs)))
    (if (not (eq (fn-cp-nth 0 physical) :ok)) (fn-capr-fault s physical)
     (let ((full (fn-carfc-config-step cp metadata)))
      (if (not (eq (fn-cp-nth 0 full) :ok)) (fn-capr-fault s full)
       (fn-capr-install
        (if (eq (fn-cp-nth 0 (fn-cp-nth 16 s)) :typed-config-source-required)
            (ec-call (update-nth 16 (fn-capr-config-source-required
                                    s (fn-cnode-config (fn-cp-nth 1 physical)) record) s)) s)
        (fn-cp-nth 1 physical) (fn-cp-nth 2 s) (fn-cp-nth 3 s)
        full nil nil (fn-cp-nth 9 s) (fn-cp-nth 10 s) (fn-cp-nth 11 s)
        (1+ (nfix cs)) es (ec-call (cdr configs)) (fn-cp-nth 15 s)))))))))

; PRODUCED is the retained MV6 packet of the SAME FnRISProducedStepWithEffects
; call that interns this event, not a second replay or an effects annotation.
; Its effect selects one new verdict pair; old verdict lists remain borrowed.
; PREFIX-FILES/FN-HIST must include exactly this event and preceding rows.
; Prefix storage/lookup establishment is owned by the actual SCO caller.
(defun fn-capr-event-step (s produced prefix-files fn-hist base-row-carry cep-cursor)
 (declare (xargs :stobjs fn-hist
                  :guard (fn-cnode-statep (fn-cp-nth 1 s)) :verify-guards nil))
 (let* ((cn (fn-cp-nth 1 s)) (events (fn-cp-nth 15 s)) (event (fn-cp-nth 0 events))
        (es (fn-cp-nth 13 s)) (cp (fn-cp-nth 4 s)) (metadata (fn-cp-nth 5 s))
        (checked (fn-cp-nth 0 produced)) (fields (fn-cp-nth 1 produced))
        (effect (fn-cp-nth 3 produced)) (child (fn-cp-nth 4 produced)))
  (cond ((eq (fn-cp-nth 0 (fn-cp-nth 16 s)) :typed-config-source-required)
         ; Ordinary FnCTLConfigAt cannot replay a typed marker. The actual
         ; caller must establish its pinned historical config projection,
         ; never pass this marker to a generic fold or silently omit it.
         (list :unavailable s :typed-control-config-source))
        ((not (fn-store-event-p event)) (fn-capr-fault s :invalid-event))
        ((not (equal (fn-store-event-sequence event) es)) (fn-capr-fault s :event-sequence))
        ((not (eq (fn-stxk-context-kind checked) :ok)) (fn-capr-fault s :identity))
        ((not (eq (fn-cp-nth 2 produced) :carried))
         (list :unavailable s :identity-carries))
        (t (let ((next (fn-cpr-apply-event cn event)))
         (if (mbe :logic (not (fn-cnode-statep next)) :exec (not (consp next)))
             (fn-capr-fault s :event-refusal)
          (let* ((old (fn-state-articles (fn-node-acceptance (fn-cnode-node cn))))
                 (new (fn-state-articles (fn-node-acceptance (fn-cnode-node next))))
                 (old-verdicts (fn-cp-nth 11 s))
                 (verdicts (if (eq effect :verdict)
                               (cons (fn-replay-verdict-pair child) old-verdicts) old-verdicts)))
           (mv-let (ws withdrawal-effect)
            (fn-ctl-refresh-withdrawals-effect-fx new old (fn-cp-nth 9 s) verdicts
              prefix-files fn-hist (fn-cp-nth 16 s))
            (mv-let (visible visibility-effect)
             (fn-ctl-refresh-visible-effect new old (fn-cp-nth 10 s) ws
                                            old-verdicts verdicts withdrawal-effect)
             (let* ((authorityp (fn-cae-eventp event))
                    (full (if authorityp
                              (fn-acj-stage cp metadata (fn-cp-nth 6 s) (fn-cnode-config cn)
                                            event es base-row-carry)
                            (fn-carfc-event-step cp event es visibility-effect metadata cep-cursor)))
                    (beginp (and authorityp (eq (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-begin))))
              (if (not (eq (fn-cp-nth 0 full) :ok)) (fn-capr-fault s full)
               (fn-capr-install s next checked fields full
                 (if authorityp (fn-cp-nth 6 full)
                   (if (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 full))) (fn-cp-nth 6 s) nil))
                 ; Match FnCATDPublished: persisted begin row's E sequence,
                 ; not the count after that row or an expected reservation.
                 (if beginp (nfix es)
                   (if (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 full))) (fn-cp-nth 8 s) nil))
                 ws visible verdicts (fn-cp-nth 12 s) (1+ (nfix es))
                 (fn-cp-nth 14 s) (ec-call (cdr events))))))))))))))

; Select from the actual cfg-first tails. The event descriptor does NOT
; execute the event: the actual caller must establish its prefix index and
; retain its once-produced identity packet before FnCAPREventStep. There is
; no ready flag or supplied effect list making this unavailable seam usable.
(defun fn-capr-tick (s)
 (declare (xargs :guard (fn-cnode-statep (fn-cp-nth 1 s)) :verify-guards nil))
 (let ((configs (fn-cp-nth 14 s)) (events (fn-cp-nth 15 s)))
  (cond ((fn-cpr-config-firstp configs events) (fn-capr-config-step s))
        ((consp events) (list :event s (car events)))
        ((and (null configs) (null events))
         (list :done (fn-replay-ok (fn-cp-nth 1 s)
                                 (+ (nfix (fn-cp-nth 12 s)) (nfix (fn-cp-nth 13 s)))) s))
        (t (fn-capr-fault s :improper-history)))))

(in-theory (disable fn-capr-state fn-capr-fault fn-capr-publication fn-capr-install
                    fn-capr-config-source-required
                    fn-capr-config-physical fn-capr-config-step
                    fn-capr-event-step fn-capr-tick))
