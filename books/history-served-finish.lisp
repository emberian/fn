; Completion call family over the resident history reader.
(in-package "ACL2")
(include-book "history-served-completion")
(include-book "identity-retain-carried")
(include-book "owner-parse-carried")

(defun fn-hsv-apc-completion-names-submission-p (o cfg fn-arena carry fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist)
                  :guard (fn-sn-statep (fn-own-store o))
                  :verify-guards nil))
  (let ((sub (fn-own-inflight o)) (record (fn-hist-completion-record (fn-own-store o) fn-hist)))
    (and sub
         record
         (fn-evc-recordp record)
         (let ((w (fn-row-wire-of record fn-arena)))
           (and (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
                (equal (fn-record-payload w)
                       (fn-apc-sub-stored-octets cfg sub (fn-own-node-secret o) carry))))
         t)))

(defthm fn-hsv-apc-completion-names-submission-p-is-reference
  (implies (and (fn-sn-statep (fn-own-store o)) (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-hsv-apc-completion-names-submission-p o cfg fn-arena carry fn-hist)
                  (fn-apc-completion-names-submission-p o cfg fn-arena carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-apc-completion-names-submission-p fn-hsv-apc-completion-names-submission-p
                                                        fn-hist-completion-record-is-reference)))))

(in-theory (disable fn-hsv-apc-completion-names-submission-p))

(defun fn-hsv-ccar-completion-core-enabledp (s fn-hist)
  (declare (xargs :stobjs (fn-hist) :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (let ((record (fn-hist-completion-record s fn-hist)))
         (and record
              (cond ((fn-evc-retentionp record)
                     (consp (fn-replay-apply-retention-event (fn-sn-node s) record)))
                    ((or (fn-evc-stxep record) (fn-evc-stxkp record) (fn-evc-stxap record))
                     (and (consp (fn-replay-apply-record (fn-sn-node s) record))
                          (equal (fn-stxk-context-kind (fn-replay-identity-step (fn-sn-identity-context s)
                                                                                record))
                                 :ok)))
                    ((or (fn-evc-consumerp record) (fn-evc-topicp record))
                     (consp (fn-replay-apply-record (fn-sn-node s) record)))
                    (t (and (fn-ccar-sn-record-bindsp (fn-sn-node s) record)
                            (equal (fn-hc-generation (fn-held-context record))
                                   (fn-sn-keyring-generation s)))))
              (equal (fn-sf-completion (fn-sn-files s))
                     (cons (fn-evc-sequence record) (fn-evc-txid record)))))))

(defthm fn-hsv-ccar-completion-core-enabledp-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep fn-hist s))
           (equal (fn-hsv-ccar-completion-core-enabledp s fn-hist)
                  (fn-ccar-completion-core-enabledp s)))
  :hints (("Goal"
           :in-theory
           (quote (fn-ccar-completion-core-enabledp fn-hsv-ccar-completion-core-enabledp
                                                    fn-hist-completion-record-is-reference)))))

(in-theory (disable fn-hsv-ccar-completion-core-enabledp))

(defun fn-hsv-ccar-completion-enabledp (s fn-hist)
  (declare (xargs :stobjs (fn-hist) :guard (fn-sn-statep s) :verify-guards nil))
  (and (fn-hsv-ccar-completion-core-enabledp s fn-hist)
       (let ((record (fn-hist-completion-record s fn-hist)))
         (and (eq (car (fn-ccar-cpe-projection-step (fn-sn-consumer s)
                                                    record
                                                    (fn-sn-identity-next s)))
                  :ok)
              (eq (fn-th-at 0 (fn-ccar-th-prefix-step (fn-sn-topic s) record)) :ok)))))

(defthm fn-hsv-ccar-completion-enabledp-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep fn-hist s))
           (equal (fn-hsv-ccar-completion-enabledp s fn-hist) (fn-ccar-completion-enabledp s)))
  :hints (("Goal"
           :in-theory
           (quote (fn-ccar-completion-enabledp fn-hsv-ccar-completion-enabledp
                                               fn-hist-completion-record-is-reference
                                               fn-hsv-ccar-completion-core-enabledp-is-reference)))))

(in-theory (disable fn-hsv-ccar-completion-enabledp))

(defun fn-hsv-ccar-accepted-delta (s fn-hist)
  (declare (xargs :stobjs (fn-hist) :guard (fn-sn-statep s) :verify-guards nil))
  (let ((record (fn-hist-completion-record s fn-hist)))
    (if (fn-held-p record) (fn-hc-delta (fn-held-context record)) nil)))

(defthm fn-hsv-ccar-accepted-delta-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep fn-hist s))
           (equal (fn-hsv-ccar-accepted-delta s fn-hist) (fn-ccar-accepted-delta s)))
  :hints (("Goal"
           :in-theory
           (quote (fn-ccar-accepted-delta fn-hsv-ccar-accepted-delta
                                          fn-hist-completion-record-is-reference)))))

(in-theory (disable fn-hsv-ccar-accepted-delta))

(defun fn-hsv-ccar-sn-finish-enabled (s fn-hist)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep s) (fn-hsv-ccar-completion-enabledp s fn-hist))
                  :verify-guards nil))
  (let* ((record (fn-hist-completion-record s fn-hist))
         (retentionp (fn-evc-retentionp record))
         (consumerp (fn-evc-consumerp record))
         (topicp (fn-evc-topicp record))
         (identityp (or (fn-evc-stxep record) (fn-evc-stxkp record) (fn-evc-stxap record)))
         (sequence (fn-evc-sequence record))
         (txid (fn-evc-txid record))
         (projection (fn-ccar-cpe-projection-step (fn-sn-consumer s) record (fn-sn-identity-next s)))
         (topic-projection (fn-ccar-th-prefix-step (fn-sn-topic s) record))
         (node (cond (retentionp (fn-replay-apply-retention-event (fn-sn-node s) record))
                     ((or identityp consumerp topicp)
                      (fn-replay-apply-record (fn-sn-node s) record))
                     (t (fn-node-complete (fn-sn-node s)
                                          (fn-record-txid record)
                                          (fn-record-generation record)
                                          :durable))))
         (files (fn-sf-core-completion (fn-sn-files s) sequence txid)))
    (fn-sn-with-topic (fn-sn-with-consumer (if (or retentionp consumerp topicp)
                                               (fn-sn-advance-identity-next (fn-sn-update-indexed s
                                                                                                  (fn-sf-emit-success files
                                                                                                                      sequence
                                                                                                                      txid)
                                                                                                  node
                                                                                                  (fn-sn-index s)))
                                             (if identityp
                                                 (fn-sn-finish-identity s
                                                                        (fn-sf-emit-success files
                                                                                            sequence
                                                                                            txid)
                                                                        record
                                                                        node)
                                               (fn-sn-advance-identity-next (fn-sn-update-accepted s
                                                                                                   (fn-sf-emit-success files
                                                                                                                       sequence
                                                                                                                       txid)
                                                                                                   node
                                                                                                   (fn-stx-index-add (fn-sn-index s)
                                                                                                                     (fn-hsv-ccar-accepted-delta s
                                                                                                                                                 fn-hist))
                                                                                                   (fn-record-msgid record)
                                                                                                   (fn-hc-verdict (fn-held-context record))))))
                                           (fn-cp-nth 1 projection))
                      topic-projection)))

(defthm fn-hsv-ccar-sn-finish-enabled-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep fn-hist s))
           (equal (fn-hsv-ccar-sn-finish-enabled s fn-hist) (fn-ccar-sn-finish-enabled s)))
  :hints (("Goal"
           :in-theory
           (quote (fn-ccar-sn-finish-enabled fn-hsv-ccar-sn-finish-enabled
                                             fn-hist-completion-record-is-reference
                                             fn-hsv-ccar-accepted-delta-is-reference)))))

(in-theory (disable fn-hsv-ccar-sn-finish-enabled))

(defun fn-hsv-rix-own-complete-enabled (o fn-hist)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-hsv-ccar-completion-enabledp (fn-own-store o) fn-hist))
                  :verify-guards nil))
  (let ((s (fn-own-store o)))
    (fn-own-refresh-ix (fn-own-make (fn-hsv-ccar-sn-finish-enabled s fn-hist)
                                    (fn-own-view o)
                                    (fn-own-conns o)
                                    (fn-own-next-id o)
                                    (fn-own-max-conns o)
                                    nil
                                    (fn-sl-snoc (fn-own-ledger-field o)
                                                (fn-sf-completion (fn-sn-files s)))
                                    (fn-own-clock o)
                                    (fn-own-facts o)
                                    (fn-own-config o)
                                    (fn-own-queue o)
                                    (fn-own-inflight o)
                                    (fn-own-feeds o)
                                    (fn-own-node-secret o)
                                    (fn-own-refused o))
                       fn-hist)))

(defthm fn-hsv-rix-own-complete-enabled-is-reference
  (implies (and (fn-sn-statep (fn-own-store o)) (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-hsv-rix-own-complete-enabled o fn-hist)
                  (fn-rix-own-complete-enabled o fn-hist)))
  :hints (("Goal"
           :in-theory
           (quote (fn-rix-own-complete-enabled fn-hsv-rix-own-complete-enabled
                                               fn-hsv-ccar-sn-finish-enabled-is-reference)))))

(in-theory (disable fn-hsv-rix-own-complete-enabled))

(defun fn-hsv-apc-own-finish (o cfg fn-arena fn-hist carry)
  (declare (xargs :stobjs (fn-arena fn-hist)
                  :guard (fn-sn-statep (fn-own-store o))
                  :verify-guards nil))
  (if (fn-hsv-ccar-completion-enabledp (fn-own-store o) fn-hist)
      (cons (if (fn-hsv-apc-completion-names-submission-p o cfg fn-arena carry fn-hist)
                :durable
              :fault)
            (fn-hsv-rix-own-complete-enabled o fn-hist))
    (cons :fault o)))

(defthm fn-hsv-apc-own-finish-is-reference
  (implies (and (fn-sn-statep (fn-own-store o)) (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-hsv-apc-own-finish o cfg fn-arena fn-hist carry)
                  (fn-apc-own-finish o cfg fn-arena fn-hist carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-apc-own-finish fn-hsv-apc-own-finish
                                     fn-hsv-apc-completion-names-submission-p-is-reference
                                     fn-hsv-ccar-completion-enabledp-is-reference
                                     fn-hsv-rix-own-complete-enabled-is-reference)))))

(in-theory (disable fn-hsv-apc-own-finish))

(defun fn-hsv-irc-completion-core-enabledp (s carry fn-hist)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep s) (fn-prc-carryp carry))
                  :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (let ((record (fn-hist-completion-record s fn-hist)))
         (and record
              (cond ((fn-evc-retentionp record)
                     (consp (fn-irc-apply-retention-event (fn-sn-node s) record carry)))
                    ((or (fn-evc-stxep record) (fn-evc-stxkp record) (fn-evc-stxap record))
                     (and (consp (fn-irc-apply-record (fn-sn-node s) record carry))
                          (equal (fn-stxk-context-kind (fn-replay-identity-step (fn-sn-identity-context s)
                                                                                record))
                                 :ok)))
                    ((or (fn-evc-consumerp record) (fn-evc-topicp record))
                     (consp (fn-irc-apply-record (fn-sn-node s) record carry)))
                    (t (and (fn-ccar-sn-record-bindsp (fn-sn-node s) record)
                            (equal (fn-hc-generation (fn-held-context record))
                                   (fn-sn-keyring-generation s)))))
              (equal (fn-sf-completion (fn-sn-files s))
                     (cons (fn-evc-sequence record) (fn-evc-txid record)))))))

(defthm fn-hsv-irc-completion-core-enabledp-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep fn-hist s))
           (equal (fn-hsv-irc-completion-core-enabledp s carry fn-hist)
                  (fn-irc-completion-core-enabledp s carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-irc-completion-core-enabledp fn-hsv-irc-completion-core-enabledp
                                                   fn-hist-completion-record-is-reference)))))

(in-theory (disable fn-hsv-irc-completion-core-enabledp))

(defun fn-hsv-irc-completion-enabledp (s carry fn-hist)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep s) (fn-prc-carryp carry))
                  :verify-guards nil))
  (and (fn-hsv-irc-completion-core-enabledp s carry fn-hist)
       (let ((record (fn-hist-completion-record s fn-hist)))
         (and (eq (car (fn-ccar-cpe-projection-step (fn-sn-consumer s)
                                                    record
                                                    (fn-sn-identity-next s)))
                  :ok)
              (eq (fn-th-at 0 (fn-ccar-th-prefix-step (fn-sn-topic s) record)) :ok)))))

(defthm fn-hsv-irc-completion-enabledp-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep fn-hist s))
           (equal (fn-hsv-irc-completion-enabledp s carry fn-hist)
                  (fn-irc-completion-enabledp s carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-irc-completion-enabledp fn-hsv-irc-completion-enabledp
                                              fn-hist-completion-record-is-reference
                                              fn-hsv-irc-completion-core-enabledp-is-reference)))))

(in-theory (disable fn-hsv-irc-completion-enabledp))

(defun fn-hsv-irc-sn-finish-enabled (s carry fn-hist)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep s)
                              (fn-prc-carryp carry)
                              (fn-hsv-ccar-completion-enabledp s fn-hist))
                  :verify-guards nil))
  (let* ((record (fn-hist-completion-record s fn-hist))
         (retentionp (fn-evc-retentionp record))
         (consumerp (fn-evc-consumerp record))
         (topicp (fn-evc-topicp record))
         (identityp (or (fn-evc-stxep record) (fn-evc-stxkp record) (fn-evc-stxap record)))
         (sequence (fn-evc-sequence record))
         (txid (fn-evc-txid record))
         (projection (fn-ccar-cpe-projection-step (fn-sn-consumer s) record (fn-sn-identity-next s)))
         (topic-projection (fn-ccar-th-prefix-step (fn-sn-topic s) record))
         (node (cond (retentionp (fn-irc-apply-retention-event (fn-sn-node s) record carry))
                     ((or identityp consumerp topicp)
                      (fn-irc-apply-record (fn-sn-node s) record carry))
                     (t (fn-node-complete (fn-sn-node s)
                                          (fn-record-txid record)
                                          (fn-record-generation record)
                                          :durable))))
         (files (fn-sf-core-completion (fn-sn-files s) sequence txid)))
    (fn-sn-with-topic (fn-sn-with-consumer (if (or retentionp consumerp topicp)
                                               (fn-sn-advance-identity-next (fn-sn-update-indexed s
                                                                                                  (fn-sf-emit-success files
                                                                                                                      sequence
                                                                                                                      txid)
                                                                                                  node
                                                                                                  (fn-sn-index s)))
                                             (if identityp
                                                 (fn-sn-finish-identity s
                                                                        (fn-sf-emit-success files
                                                                                            sequence
                                                                                            txid)
                                                                        record
                                                                        node)
                                               (fn-sn-advance-identity-next (fn-sn-update-accepted s
                                                                                                   (fn-sf-emit-success files
                                                                                                                       sequence
                                                                                                                       txid)
                                                                                                   node
                                                                                                   (fn-stx-index-add (fn-sn-index s)
                                                                                                                     (fn-hsv-ccar-accepted-delta s
                                                                                                                                                 fn-hist))
                                                                                                   (fn-record-msgid record)
                                                                                                   (fn-hc-verdict (fn-held-context record))))))
                                           (fn-cp-nth 1 projection))
                      topic-projection)))

(defthm fn-hsv-irc-sn-finish-enabled-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep fn-hist s))
           (equal (fn-hsv-irc-sn-finish-enabled s carry fn-hist) (fn-irc-sn-finish-enabled s carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-irc-sn-finish-enabled fn-hsv-irc-sn-finish-enabled
                                            fn-hist-completion-record-is-reference
                                            fn-hsv-ccar-accepted-delta-is-reference)))))

(in-theory (disable fn-hsv-irc-sn-finish-enabled))

(defun fn-hsv-irc-rix-own-complete-enabled (o fn-hist carry)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-prc-carryp carry)
                              (fn-hsv-ccar-completion-enabledp (fn-own-store o) fn-hist))
                  :verify-guards nil))
  (let ((s (fn-own-store o)))
    (fn-own-refresh-ix (fn-own-make (fn-hsv-irc-sn-finish-enabled s carry fn-hist)
                                    (fn-own-view o)
                                    (fn-own-conns o)
                                    (fn-own-next-id o)
                                    (fn-own-max-conns o)
                                    nil
                                    (fn-sl-snoc (fn-own-ledger-field o)
                                                (fn-sf-completion (fn-sn-files s)))
                                    (fn-own-clock o)
                                    (fn-own-facts o)
                                    (fn-own-config o)
                                    (fn-own-queue o)
                                    (fn-own-inflight o)
                                    (fn-own-feeds o)
                                    (fn-own-node-secret o)
                                    (fn-own-refused o))
                       fn-hist)))

(defthm fn-hsv-irc-rix-own-complete-enabled-is-reference
  (implies (and (fn-sn-statep (fn-own-store o)) (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-hsv-irc-rix-own-complete-enabled o fn-hist carry)
                  (fn-irc-rix-own-complete-enabled o fn-hist carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-irc-rix-own-complete-enabled fn-hsv-irc-rix-own-complete-enabled
                                                   fn-hsv-irc-sn-finish-enabled-is-reference)))))

(in-theory (disable fn-hsv-irc-rix-own-complete-enabled))

(defun fn-hsv-irc-rix-own-complete (o fn-hist carry)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep (fn-own-store o)) (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (fn-hsv-irc-completion-enabledp (fn-own-store o) carry fn-hist)
      (fn-hsv-irc-rix-own-complete-enabled o fn-hist carry)
    o))

(defthm fn-hsv-irc-rix-own-complete-is-reference
  (implies (and (fn-sn-statep (fn-own-store o)) (fn-hist-of-storep fn-hist (fn-own-store o)))
           (equal (fn-hsv-irc-rix-own-complete o fn-hist carry)
                  (fn-irc-rix-own-complete o fn-hist carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-irc-rix-own-complete fn-hsv-irc-rix-own-complete
                                           fn-hsv-irc-completion-enabledp-is-reference
                                           fn-hsv-irc-rix-own-complete-enabled-is-reference)))))

(in-theory (disable fn-hsv-irc-rix-own-complete))

(defun fn-hsv-irc-rix-ocfg-complete (oc fn-hist carry)
  (declare (xargs :stobjs (fn-hist)
                  :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let ((record (fn-ocfg-staged oc)))
    (if record
        (fn-ocfg-make (fn-ocfg-owner oc)
                      (fn-ocfg-published-config (fn-ocfg-config oc) record)
                      (fn-ocfg-pins oc)
                      nil)
      (fn-ocfg-make (fn-hsv-irc-rix-own-complete (fn-ocfg-owner oc) fn-hist carry)
                    (fn-ocfg-config oc)
                    (fn-ocfg-pins oc)
                    nil))))

(defthm fn-hsv-irc-rix-ocfg-complete-is-reference
  (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-hsv-irc-rix-ocfg-complete oc fn-hist carry)
                  (fn-irc-rix-ocfg-complete oc fn-hist carry)))
  :hints (("Goal"
           :in-theory
           (quote (fn-irc-rix-ocfg-complete fn-hsv-irc-rix-ocfg-complete
                                            fn-hsv-irc-rix-own-complete-is-reference)))))

(in-theory (disable fn-hsv-irc-rix-ocfg-complete))

; Guard verification is separate so all value refinements remain available.

(verify-guards fn-hsv-apc-completion-names-submission-p
 :hints (("Goal" :use ((:instance fn-hist-completion-record-is-store-event (s (fn-own-store o)) (hist fn-hist)))
 :in-theory (e/d (fn-evc-carried-definitions) (fn-sn-statep fn-store-event-p fn-record-p fn-hist-completion-record fn-hist-completion-record-is-reference)))))
(verify-guards fn-hsv-ccar-completion-core-enabledp
 :hints (("Goal" :use ((:instance fn-hist-completion-record-is-store-event (hist fn-hist)))
 :in-theory (e/d (fn-sn-statep fn-evc-carried-definitions)
 (fn-hist-completion-record fn-hist-completion-record-is-reference fn-sf-statep fn-node-statep fn-record-p fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-store-event-p fn-cpe-eventp fn-th-topic-eventp)))))
(defthm fn-hsv-ccar-core-finds-store-event
 (implies (fn-hsv-ccar-completion-core-enabledp s hist)
 (and (fn-sn-statep s) (fn-store-event-p (fn-hist-completion-record s hist))))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory '(fn-hsv-ccar-completion-core-enabledp fn-hist-completion-record-is-store-event))))
(verify-guards fn-hsv-ccar-completion-enabledp
 :hints (("Goal" :in-theory (union-theories '(fn-hsv-ccar-core-finds-store-event fn-ccar-cpe-projection-step-is-a-cons) (theory 'ground-zero)))))
(verify-guards fn-hsv-ccar-accepted-delta)

(defthm fn-hsv-ccar-enabled-finds-store-event
 (implies (fn-hsv-ccar-completion-enabledp s hist)
 (and (fn-sn-statep s) (fn-hsv-ccar-completion-core-enabledp s hist)
 (fn-store-event-p (fn-hist-completion-record s hist))))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory '(fn-hsv-ccar-completion-enabledp fn-hsv-ccar-core-finds-store-event))))
(verify-guards fn-hsv-ccar-sn-finish-enabled
 :hints (("Goal"
 :in-theory (e/d (fn-sn-statep fn-evc-carried-definitions fn-hsv-ccar-completion-core-enabledp fn-hsv-ccar-accepted-delta)
 (fn-sf-statep fn-node-statep fn-node-pending-matchesp fn-sf-core-completion
 fn-hist-completion-record fn-hist-completion-record-is-reference fn-hsv-ccar-completion-core-enabledp-is-reference
 fn-store-event-p fn-record-p fn-sn-record-bindsp fn-sn-identity-context fn-replay-identity-step
 fn-replay-apply-retention-event fn-replay-apply-record fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
 fn-record-record-vocabulary fn-record-shape-vocabulary)))))
(verify-guards fn-hsv-rix-own-complete-enabled)
(verify-guards fn-hsv-apc-own-finish)

(defthm fn-hsv-irc-core-is-ccar
 (implies (fn-prc-carryp carry)
  (equal (fn-hsv-irc-completion-core-enabledp s carry hist) (fn-hsv-ccar-completion-core-enabledp s hist)))
 :hints (("Goal" :in-theory '(fn-hsv-irc-completion-core-enabledp fn-hsv-ccar-completion-core-enabledp fn-irc-apply-record-is-replay-apply-record fn-irc-apply-retention-event-is-reference))))
(defthm fn-hsv-irc-enabled-is-ccar
 (implies (fn-prc-carryp carry)
  (equal (fn-hsv-irc-completion-enabledp s carry hist) (fn-hsv-ccar-completion-enabledp s hist)))
 :hints (("Goal" :in-theory '(fn-hsv-irc-completion-enabledp fn-hsv-ccar-completion-enabledp fn-hsv-irc-core-is-ccar))))
(verify-guards fn-hsv-irc-completion-core-enabledp
 :hints (("Goal" :use ((:guard-theorem fn-hsv-ccar-completion-core-enabledp))
 :in-theory (e/d (fn-sn-statep fn-evc-carried-definitions)
 (fn-hist-completion-record fn-hist-completion-record-is-reference fn-sf-statep fn-node-statep fn-prc-carryp fn-record-p fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-store-event-p fn-cpe-eventp fn-th-topic-eventp)))))
(verify-guards fn-hsv-irc-completion-enabledp
 :hints (("Goal" :use ((:guard-theorem fn-hsv-ccar-completion-enabledp))
 :in-theory (union-theories '(fn-hsv-irc-core-is-ccar) (theory 'ground-zero)))))
(verify-guards fn-hsv-irc-sn-finish-enabled
 :hints (("Goal" :use ((:guard-theorem fn-hsv-ccar-sn-finish-enabled))
 :in-theory (e/d (fn-irc-apply-record-is-replay-apply-record)
 (fn-sn-statep fn-sf-statep fn-node-statep fn-prc-carryp fn-hsv-ccar-completion-enabledp fn-hist-completion-record fn-hist-completion-record-is-reference
 fn-node-pending-matchesp fn-sf-core-completion fn-store-event-p fn-record-p fn-sn-identity-context fn-replay-identity-step fn-replay-apply-retention-event fn-replay-apply-record
 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-record-record-vocabulary fn-record-shape-vocabulary)))))
(verify-guards fn-hsv-irc-rix-own-complete-enabled)
(verify-guards fn-hsv-irc-rix-own-complete
 :hints (("Goal" :in-theory (e/d (fn-hsv-irc-enabled-is-ccar) (fn-sn-statep fn-prc-carryp fn-hsv-ccar-completion-enabledp)))))
(verify-guards fn-hsv-irc-rix-ocfg-complete)

; The total logical gate refuses a malformed Store before reading completion.
; This keeps clients whose invariant is weaker than the executable guard valid.
(defthm fn-hsv-irc-rix-ocfg-complete-is-reference-total
 (implies (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc)))
  (equal (fn-hsv-irc-rix-ocfg-complete oc hist carry)
         (fn-irc-rix-ocfg-complete oc hist carry)))
 :hints (("Goal"
  :cases ((fn-sn-statep (fn-own-store (fn-ocfg-owner oc))))
  :use ((:instance fn-hsv-irc-rix-ocfg-complete-is-reference (fn-hist hist)))
  :in-theory '(fn-hsv-irc-rix-ocfg-complete fn-irc-rix-ocfg-complete
               fn-hsv-irc-rix-own-complete fn-irc-rix-own-complete
               fn-hsv-irc-completion-enabledp fn-irc-completion-enabledp
               fn-hsv-irc-completion-core-enabledp fn-irc-completion-core-enabledp))))
