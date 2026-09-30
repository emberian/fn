; PRF-1115: complete canonical snapshot abstraction through configured open.
; Proof vocabulary only: never a live history revalidation. The physical
; writer/loader must establish the payload map before this boundary applies.
(in-package "ACL2")
(include-book "snapshot-row-remap")
(include-book "snapshot-node-alpha")
(include-book "owner-snapshot-recovery")
(local (in-theory (disable (tau-system))))

(defun fn-osa-row-alphas (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows) nil
    (cons (fn-orm-retained-alpha (car rows) fn-arena)
          (fn-osa-row-alphas (cdr rows) fn-arena))))

; Both ordinary and composite-held payloads are required. Comparing only
; fn-row-wire-of would silently omit the latter's independently held bytes.
(defun-nx fn-osa-payload-map-p (rows handles source target)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rows) t
    (and (equal (fn-orm-payload-bytes (fn-orm-row (car rows) handles) target)
                (fn-orm-payload-bytes (car rows) source))
         (fn-osa-payload-map-p
          (cdr rows) (if (fn-orm-sealsp (car rows)) (+ 1 handles) handles)
          source target))))

(defthm fn-osa-canonical-history-keeps-complete-retained-alpha
  (implies (and (fn-orm-rowsp rows) (natp handles)
                (fn-osa-payload-map-p rows handles source target))
           (equal (fn-osa-row-alphas (fn-orm-capture rows handles) target)
                  (fn-osa-row-alphas rows source)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-orm-capture rows handles)
           :in-theory (e/d (fn-orm-capture fn-orm-rowsp fn-osa-row-alphas
                            fn-osa-payload-map-p fn-orm-retained-alpha)
                           (fn-orm-row fn-orm-sealsp
                            fn-orm-payload-bytes fn-orm-projection fn-store-event-p)))))

(in-theory (disable fn-osa-row-alphas fn-osa-payload-map-p))

(defun fn-osa-store-alpha (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (list (fn-osa-node-alpha (fn-sn-node s) fn-arena)
        (fn-sn-groups s) (fn-sn-capacity s) (fn-sn-config-history s)
        (fn-sf-frontier (fn-sn-files s))
        (fn-osa-row-alphas (fn-sf-records (fn-sn-files s)) fn-arena)
        (fn-sn-identity-next s) (fn-sn-keyring-snapshots s)
        (fn-sn-keyring s) (fn-sn-keyring-generation s)
        (fn-sn-verdicts s) (fn-sn-index s) (fn-sn-event-index s)
        (fn-sn-consumer s) (fn-sn-topic s)))
(in-theory (disable fn-osa-pending-alpha fn-osa-acceptance-alpha
                    fn-osa-node-alpha fn-osa-store-alpha))

(local
 (defthm fn-osa-valid-row-dispatch-by-definition
   (implies (fn-store-event-p row)
            (and (equal (fn-orm-spinep 15 row) (fn-held-p row))
                 (equal (and (consp row) (equal (car row) :hstxa))
                        (fn-hstxa-p row))))
   :hints (("Goal" :do-not-induct t :in-theory
            (enable fn-store-event-p fn-store-retention-event-p
                    fn-held-p fn-held-shapep
                    fn-stxe-p fn-stxe-shapep fn-stxk-p fn-stxk-shapep
                    fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp
                    fn-th-local-admin-eventp fn-th-at fn-cp-nth
                    fn-stxe-internals fn-stxk-internals)))))

(local
 (defthm fn-osa-row-on-valid-input-by-definition
   (implies (fn-store-event-p row)
            (equal (fn-orm-row row handle)
                   (cond ((fn-held-p row) (fn-orm-held row handle))
                         ((fn-hstxa-p row)
                          (fn-hstxa-make (fn-hstxa-stxa row)
                                         (fn-orm-held (fn-hstxa-held row) handle)))
                         (t row))))
   :hints (("Goal" :use (fn-osa-valid-row-dispatch-by-definition)
            :in-theory (e/d (fn-orm-row)
                                   (fn-osa-valid-row-dispatch-by-definition
                                    fn-orm-spinep fn-store-event-p fn-held-p fn-hstxa-p
                                    fn-orm-held fn-hstxa-make fn-hstxa-stxa fn-hstxa-held))))))

(defthm fn-osa-remap-preserves-row-discriminants-and-coordinate
  (implies (and (fn-store-event-p row) (natp handle))
           (let ((new (fn-orm-row row handle)))
             (and (equal (fn-held-p new) (fn-held-p row))
                  (equal (fn-hstxa-p new) (fn-hstxa-p row))
                  (equal (fn-store-retention-event-p new) (fn-store-retention-event-p row))
                  (equal (fn-stxe-p new) (fn-stxe-p row))
                  (equal (fn-stxk-p new) (fn-stxk-p row))
                  (equal (fn-cpe-eventp new) (fn-cpe-eventp row))
                  (equal (fn-th-topic-eventp new) (fn-th-topic-eventp row))
                  (equal (fn-store-event-sequence new) (fn-store-event-sequence row))
                  (equal (fn-store-event-txid new) (fn-store-event-txid row))
                  (equal (fn-store-event-generation new) (fn-store-event-generation row)))))
  :hints (("Goal" :do-not-induct t :cases ((fn-held-p row) (fn-hstxa-p row))
           :use ((:instance fn-orm-held-preserves-the-held-shape)
                 (:instance fn-orm-held-preserves-the-held-shape
                            (row (fn-hstxa-held row))))
           :in-theory (e/d (fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation fn-orm-held)
                           (fn-orm-row fn-held-p fn-hstxa-p fn-store-event-p
                            fn-held-make fn-hstxa-make fn-hstxa-held fn-hstxa-stxa
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p
                            fn-cpe-eventp fn-th-topic-eventp)))))

(defthm fn-osa-remap-keeps-frozen-verdict-and-index-delta
  (implies (and (fn-store-event-p row) (natp handle))
           (and (equal (fn-sn-row-verdict-pair (fn-orm-row row handle))
                       (fn-sn-row-verdict-pair row))
                (equal (fn-sn-row-delta (fn-orm-row row handle))
                       (fn-sn-row-delta row))))
  :hints (("Goal" :do-not-induct t :cases ((fn-held-p row) (fn-hstxa-p row))
           :use (fn-osa-remap-preserves-row-discriminants-and-coordinate)
           :in-theory (e/d (fn-sn-row-verdict-pair fn-sn-row-delta fn-orm-held)
                           (fn-osa-remap-preserves-row-discriminants-and-coordinate
                            fn-orm-row fn-held-p fn-hstxa-p fn-store-event-p
                            fn-held-make fn-hstxa-make fn-hstxa-held fn-hstxa-stxa
                            fn-stxe-decode-exact fn-stxa-verdict-event fn-stmt-okp
                            fn-stmt-value fn-stxe-p fn-replay-verdict-pair
                            fn-hc-verdict fn-hc-delta)))))

(local
 (defun fn-osa-index-induct (rows handle index)
   (if (atom rows) (list handle index)
     (fn-osa-index-induct
      (cdr rows) (if (fn-orm-sealsp (car rows)) (+ 1 handle) handle)
      (fn-stx-index-add index (fn-sn-row-delta (car rows)))))))
(local
 (defun fn-osa-verdict-induct (rows handle verdicts)
   (if (atom rows) (list handle verdicts)
     (let ((pair (fn-sn-row-verdict-pair (car rows))))
       (fn-osa-verdict-induct
        (cdr rows) (if (fn-orm-sealsp (car rows)) (+ 1 handle) handle)
        (if pair (cons pair verdicts) verdicts))))))
(defthm fn-osa-canonical-history-keeps-frozen-index-fold
  (implies (and (fn-orm-rowsp rows) (natp handle))
           (equal (fn-sn-index-fold (fn-orm-capture rows handle) index)
                  (fn-sn-index-fold rows index)))
  :hints (("Goal" :induct (fn-osa-index-induct rows handle index)
           :in-theory (e/d (fn-orm-capture fn-orm-rowsp fn-sn-index-fold)
                           (fn-osa-row-on-valid-input-by-definition
                            fn-orm-row fn-orm-sealsp fn-store-event-p
                            fn-sn-row-delta fn-stx-index-add)))))
(defthm fn-osa-canonical-history-keeps-verdict-fold
  (implies (and (fn-orm-rowsp rows) (natp handle))
           (equal (fn-sn-row-verdicts-fold (fn-orm-capture rows handle) verdicts)
                  (fn-sn-row-verdicts-fold rows verdicts)))
  :hints (("Goal" :induct (fn-osa-verdict-induct rows handle verdicts)
           :in-theory (e/d (fn-orm-capture fn-orm-rowsp fn-sn-row-verdicts-fold)
                           (fn-osa-row-on-valid-input-by-definition
                            fn-orm-row fn-orm-sealsp fn-store-event-p
                            fn-sn-row-verdict-pair)))))

; Consumer replay depends on complete event metadata and journal position,
; never the relocated article payload handle.  Preserve its entire result,
; including refusal reasons, rather than projecting only successful cursors.
(defthm fn-osa-remap-keeps-consumer-projection-step
  (implies (and (fn-store-event-p row) (natp handle))
           (equal (fn-cpe-projection-step projection (fn-orm-row row handle) expected)
                  (fn-cpe-projection-step projection row expected)))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-held-p row) (fn-hstxa-p row))
           :use (fn-osa-remap-preserves-row-discriminants-and-coordinate
                 fn-orm-row-retains-the-complete-payload-independent-projection)
           :in-theory
           (e/d (fn-cpe-projection-step fn-held-is-no-wire-event
                 fn-hstxa-is-no-wire-event fn-hstxa-is-not-held)
                (fn-orm-row fn-store-event-p fn-store-event-sequence
                 fn-held-p fn-hstxa-p fn-cpe-eventp fn-cpe-operation
                 fn-cpe-projection-advance fn-cpe-projection-decision
                 fn-cp-state fn-cp-initial fn-cp-apply
                 fn-orm-held fn-hstxa-make fn-hstxa-stxa fn-hstxa-held
                 fn-osa-remap-preserves-row-discriminants-and-coordinate)))))

(local
 (defun fn-osa-consumer-induct (rows handle projection expected)
   (if (atom rows) (list handle projection expected)
     (let ((one (fn-cpe-projection-step projection (car rows) expected)))
       (fn-osa-consumer-induct
        (cdr rows) (if (fn-orm-sealsp (car rows)) (+ 1 handle) handle)
        (fn-cp-nth 1 one) (1+ (nfix expected)))))))

(defthm fn-osa-canonical-history-keeps-complete-consumer-replay
  (implies (and (fn-orm-rowsp rows) (natp handle))
           (equal (fn-cpe-projection-replay
                   projection (fn-orm-capture rows handle) expected)
                  (fn-cpe-projection-replay projection rows expected)))
  :hints (("Goal"
           :induct (fn-osa-consumer-induct rows handle projection expected)
           :in-theory
           (e/d (fn-orm-capture fn-orm-rowsp fn-cpe-projection-replay)
                (fn-osa-row-on-valid-input-by-definition
                 fn-orm-row fn-orm-sealsp fn-store-event-p
                 fn-cpe-projection-step)))))

(defthm fn-osa-remap-keeps-topic-prefix-step
  (implies (and (fn-store-event-p row) (natp handle))
           (equal (fn-th-prefix-step projection (fn-orm-row row handle))
                  (fn-th-prefix-step projection row)))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-held-p row) (fn-hstxa-p row))
           :use (fn-osa-remap-preserves-row-discriminants-and-coordinate
                 fn-orm-row-retains-the-complete-payload-independent-projection
                 (:instance fn-held-p-forward-shape (x row))
                 (:instance fn-hstxa-p-forward-shape (x row)))
           :in-theory
           (e/d (fn-th-prefix-step fn-th-local-admin-eventp fn-orm-held
                 fn-held-is-no-wire-event fn-hstxa-is-no-wire-event
                 fn-hstxa-is-not-held)
                (fn-orm-row fn-store-event-p fn-store-event-sequence
                 fn-held-p fn-hstxa-p fn-held-make fn-hstxa-make
                 fn-hstxa-held fn-hstxa-stxa fn-th-topic-eventp fn-stxk-p
                 fn-th-at fn-th-prefix-state fn-th-prefix-find-ref
                 fn-th-local-admin-commit fn-th-commit-anchor-installed-v2
                 fn-th-commit-report fn-osa-remap-preserves-row-discriminants-and-coordinate)))))

(local
 (defun fn-osa-topic-induct (rows handle projection)
   (if (atom rows) (list handle projection)
     (fn-osa-topic-induct
      (cdr rows) (if (fn-orm-sealsp (car rows)) (+ 1 handle) handle)
      (fn-th-prefix-step projection (car rows))))))

(local
 (defthm fn-osa-canonical-history-keeps-topic-prefix-loop
   (implies (and (fn-orm-rowsp rows) (natp handle))
            (equal (fn-th-prefix-loop projection (fn-orm-capture rows handle))
                   (fn-th-prefix-loop projection rows)))
   :hints (("Goal" :induct (fn-osa-topic-induct rows handle projection)
            :in-theory
            (e/d (fn-orm-capture fn-orm-rowsp fn-th-prefix-loop)
                 (fn-osa-row-on-valid-input-by-definition
                  fn-orm-row fn-orm-sealsp fn-store-event-p fn-th-prefix-step
                  fn-th-prefix-state fn-th-at))))))

(defthm fn-osa-canonical-history-keeps-complete-topic-replay
  (implies (and (fn-orm-rowsp rows) (natp handle))
           (equal (fn-th-prefix-project (fn-orm-capture rows handle))
                  (fn-th-prefix-project rows)))
  :hints (("Goal" :in-theory (enable fn-th-prefix-project))))

(defthm fn-osa-remap-keeps-identity-replay-step
  (implies (and (fn-store-event-p row) (natp handle))
           (equal (fn-replay-identity-step context (fn-orm-row row handle))
                  (fn-replay-identity-step context row)))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-held-p row) (fn-hstxa-p row))
           :use (fn-osa-remap-preserves-row-discriminants-and-coordinate
                 fn-orm-row-retains-the-complete-payload-independent-projection)
           :in-theory
           (e/d (fn-replay-identity-step fn-replay-identity-wire fn-orm-held
                 fn-hsig-article-event-carried-bindsp
                 fn-hsig-article-event-revoked-bindsp
                 fn-held-is-no-wire-event fn-hstxa-is-no-wire-event
                 fn-hstxa-is-not-held)
                (fn-orm-row fn-store-event-p fn-store-event-sequence
                 fn-held-p fn-hstxa-p fn-held-make fn-hstxa-make
                 fn-hstxa-held fn-hstxa-stxa fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-stxk-context-kind fn-stxk-context-next fn-stxk-fault
                 fn-replay-identity-advance fn-stxk-apply-snapshot
                 fn-stxk-apply-verdict fn-stxk-context fn-stxk-find
                 fn-stxa-bindsp fn-hsig-article-event-snapshot-bindsp
                 fn-osa-remap-preserves-row-discriminants-and-coordinate)))))

(local
 (defun fn-osa-identity-induct (rows handle context)
   (if (atom rows) (list handle context)
     (fn-osa-identity-induct
      (cdr rows) (if (fn-orm-sealsp (car rows)) (+ 1 handle) handle)
      (fn-replay-identity-step context (car rows))))))

(local
 (defthm fn-osa-canonical-history-keeps-identity-replay-loop
   (implies (and (fn-orm-rowsp rows) (natp handle))
            (equal (fn-replay-identity-loop (fn-orm-capture rows handle) context)
                   (fn-replay-identity-loop rows context)))
   :hints (("Goal" :induct (fn-osa-identity-induct rows handle context)
            :in-theory
            (e/d (fn-orm-capture fn-orm-rowsp fn-replay-identity-loop)
                 (fn-osa-row-on-valid-input-by-definition
                  fn-orm-row fn-orm-sealsp fn-store-event-p
                  fn-replay-identity-step fn-stxk-fault))))))

(defthm fn-osa-canonical-history-keeps-complete-identity-replay
  (implies (and (fn-orm-rowsp rows) (natp handle))
           (equal (fn-replay-identity (fn-orm-capture rows handle))
                  (fn-replay-identity rows)))
  :hints (("Goal" :in-theory (enable fn-replay-identity))))

; Actual node interpreter boundary. Symmetric alpha relations are used by
; explicit instances, not as bidirectional rewrite rules. The four runtime
; branches retain their status as well as every node abstraction field.
(local
 (defthm fn-osa-advance-keeps-full-node-alpha
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source)
                        (fn-osa-node-alpha b target)))
            (equal (fn-osa-node-alpha (fn-replay-advance-txid a txid) source)
                   (fn-osa-node-alpha (fn-replay-advance-txid b txid) target)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-osa-node-alpha fn-osa-acceptance-alpha
                             fn-osa-pending-alpha fn-replay-advance-txid)
                            (fn-node-statep fn-statep fn-node-make-state
                             fn-make-state fn-handle-bytes fn-articles-wire-of))))))
(local
 (defthm fn-osa-alpha-keeps-pending-match
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source)
                        (fn-osa-node-alpha b target)))
            (equal (fn-node-pending-matchesp a txid generation)
                   (fn-node-pending-matchesp b txid generation)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-osa-node-alpha fn-osa-acceptance-alpha
                             fn-osa-pending-alpha fn-node-pending-matchesp
                             fn-pending-matchesp)
                            (fn-handle-bytes fn-articles-wire-of))))))
(local
 (defthm fn-osa-alpha-keeps-replay-controls
   (implies (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
            (and (equal (fn-state-next-txid (fn-node-acceptance a))
                        (fn-state-next-txid (fn-node-acceptance b)))
                 (equal (fn-node-stage a) (fn-node-stage b))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-osa-node-alpha fn-osa-acceptance-alpha)
                                   (fn-osa-pending-alpha fn-articles-wire-of))))))
(local
 (defthm fn-osa-empty-node-alpha-does-not-depend-on-arena
   (equal (fn-osa-node-alpha nil source) '((nil nil nil nil nil nil) nil nil nil))
   :hints (("Goal" :in-theory (enable fn-osa-node-alpha fn-osa-acceptance-alpha
                                     fn-osa-pending-alpha fn-articles-wire-of)))))
(local
 (defthm fn-osa-remapped-held-keeps-article-inputs
   (let ((new (fn-orm-held row handle)))
     (and (equal (fn-record-txid new) (fn-record-txid row))
          (equal (fn-record-generation new) (fn-record-generation row))
          (equal (fn-record-msgid new) (fn-record-msgid row))
          (equal (fn-record-payload new) handle)
          (equal (fn-record-groups new) (fn-record-groups row))
          (equal (fn-record-obligation-id new) (fn-record-obligation-id row))
          (equal (fn-record-content-subject new) (fn-record-content-subject row))
          (equal (fn-record-release-evidence new) (fn-record-release-evidence row))
          (equal (fn-record-charge new) (fn-record-charge row))
          (equal (fn-record-stamp new) (fn-record-stamp row))))
   :hints (("Goal" :in-theory (enable fn-orm-held fn-held-internals fn-record-internals)))))
(local
 (defthm fn-osa-node-state-is-nonempty-by-definition
   (implies (fn-node-statep node) (consp node))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-node-statep fn-node-state-shapep)))))
(local
 (defthm fn-osa-held-replay-keeps-node-alpha
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
                 (fn-held-p row) (natp handle)
                 (equal (fn-handle-bytes (fn-held-payload row) source)
                        (fn-handle-bytes handle target)))
            (let ((new-a (fn-replay-apply-record a row))
                  (new-b (fn-replay-apply-record b (fn-orm-held row handle))))
              (and (equal (consp new-a) (consp new-b))
                   (equal (fn-osa-node-alpha new-a source)
                          (fn-osa-node-alpha new-b target)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-osa-alpha-keeps-replay-controls)
                  (:instance fn-osa-alpha-keeps-replay-controls
                   (a (fn-replay-advance-txid a (fn-record-txid row)))
                   (b (fn-replay-advance-txid b (fn-record-txid row))))
                  (:instance fn-osa-advance-keeps-full-node-alpha (txid (fn-held-txid row)))
                  (:instance fn-osa-prepare-keeps-full-node-alpha (a (fn-replay-advance-txid a (fn-held-txid
                    row))) (b (fn-replay-advance-txid b (fn-held-txid row))) (generation (fn-held-generation
                    row)) (msgid (fn-held-msgid row)) (p (fn-held-payload row)) (q handle) (groups
                    (fn-held-groups row)) (id (fn-held-obligation-id row)) (subject (fn-held-content-subject
                    row)) (evidence (fn-held-release-evidence row)) (charge (fn-held-charge row)) (stamp
                    (fn-held-stamp row)))
                  (:instance fn-osa-alpha-keeps-pending-match (a (fn-node-prepare (fn-replay-advance-txid a
                    (fn-held-txid row)) (fn-record-generation row) (fn-record-msgid row) (fn-record-payload
                    row) (fn-record-groups row) (fn-record-obligation-id row) (fn-record-content-subject
                    row) (fn-record-release-evidence row) (fn-record-charge row) (fn-record-stamp row))) (b
                    (fn-node-prepare (fn-replay-advance-txid b (fn-held-txid row)) (fn-record-generation
                    (fn-orm-held row handle)) (fn-record-msgid (fn-orm-held row handle)) (fn-record-payload
                    (fn-orm-held row handle)) (fn-record-groups (fn-orm-held row handle))
                    (fn-record-obligation-id (fn-orm-held row handle)) (fn-record-content-subject
                    (fn-orm-held row handle)) (fn-record-release-evidence (fn-orm-held row handle))
                    (fn-record-charge (fn-orm-held row handle)) (fn-record-stamp (fn-orm-held row handle))))
                    (txid (fn-held-txid row)) (generation (fn-held-generation row)))
                  (:instance fn-osa-complete-keeps-full-node-alpha (a (fn-node-prepare
                    (fn-replay-advance-txid a (fn-held-txid row)) (fn-record-generation row)
                    (fn-record-msgid row) (fn-record-payload row) (fn-record-groups row)
                    (fn-record-obligation-id row) (fn-record-content-subject row)
                    (fn-record-release-evidence row) (fn-record-charge row) (fn-record-stamp row))) (b
                    (fn-node-prepare (fn-replay-advance-txid b (fn-held-txid row)) (fn-record-generation
                    (fn-orm-held row handle)) (fn-record-msgid (fn-orm-held row handle)) (fn-record-payload
                    (fn-orm-held row handle)) (fn-record-groups (fn-orm-held row handle))
                    (fn-record-obligation-id (fn-orm-held row handle)) (fn-record-content-subject
                    (fn-orm-held row handle)) (fn-record-release-evidence (fn-orm-held row handle))
                    (fn-record-charge (fn-orm-held row handle)) (fn-record-stamp (fn-orm-held row handle))))
                    (txid (fn-held-txid row)) (generation (fn-held-generation row)) (status :durable))
                  (:instance fn-held-p-forward-shape (x row))
                  (:instance fn-orm-held-preserves-the-held-shape)
                  (:instance fn-osa-node-state-is-nonempty-by-definition (node (fn-node-complete
                    (fn-node-prepare (fn-replay-advance-txid a (fn-record-txid row)) (fn-record-generation
                    row) (fn-record-msgid row) (fn-record-payload row) (fn-record-groups row)
                    (fn-record-obligation-id row) (fn-record-content-subject row)
                    (fn-record-release-evidence row) (fn-record-charge row) (fn-record-stamp row))
                    (fn-record-txid row) (fn-record-generation row) :durable)))
                  (:instance fn-osa-node-state-is-nonempty-by-definition (node (fn-node-complete
                    (fn-node-prepare (fn-replay-advance-txid b (fn-record-txid row)) (fn-record-generation
                    (fn-orm-held row handle)) (fn-record-msgid (fn-orm-held row handle)) (fn-record-payload
                    (fn-orm-held row handle)) (fn-record-groups (fn-orm-held row handle))
                    (fn-record-obligation-id (fn-orm-held row handle)) (fn-record-content-subject
                    (fn-orm-held row handle)) (fn-record-release-evidence (fn-orm-held row handle))
                    (fn-record-charge (fn-orm-held row handle)) (fn-record-stamp (fn-orm-held row handle)))
                    (fn-record-txid row) (fn-record-generation row) :durable))))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(fn-replay-apply-record fn-store-event-txid
               fn-osa-empty-node-alpha-does-not-depend-on-arena
               fn-osa-remapped-held-keeps-article-inputs
               fn-osa-node-state-is-nonempty-by-definition
               fn-held-accessors-are-the-wire-accessors fn-held-p-fields
               fn-held-is-no-wire-event fn-cstp-held-kind-facts
               fn-node-prepare-preserves-state fn-node-complete-preserves-state
               fn-replay-advance-preserves-node-statep))))))
(local
 (defthm fn-osa-composite-replay-keeps-node-alpha
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
                 (fn-held-p row) (fn-stxa-p stxa) (natp handle)
                 (equal (fn-handle-bytes (fn-held-payload row) source)
                        (fn-handle-bytes handle target)))
            (let ((new-a (fn-replay-apply-record a (fn-hstxa-make stxa row)))
                  (new-b (fn-replay-apply-record b (fn-hstxa-make stxa (fn-orm-held row handle)))))
              (and (equal (consp new-a) (consp new-b))
                   (equal (fn-osa-node-alpha new-a source)
                          (fn-osa-node-alpha new-b target)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-osa-alpha-keeps-replay-controls)
                  (:instance fn-osa-alpha-keeps-replay-controls
                   (a (fn-replay-advance-txid a (fn-stxa-txid stxa)))
                   (b (fn-replay-advance-txid b (fn-stxa-txid stxa))))
                  (:instance fn-osa-advance-keeps-full-node-alpha (txid (fn-stxa-txid stxa)))
                  (:instance fn-osa-prepare-keeps-full-node-alpha (a (fn-replay-advance-txid a (fn-stxa-txid
                    stxa))) (b (fn-replay-advance-txid b (fn-stxa-txid stxa))) (generation
                    (fn-held-generation row)) (msgid (fn-held-msgid row)) (p (fn-held-payload row)) (q
                    handle) (groups (fn-held-groups row)) (id (fn-held-obligation-id row)) (subject
                    (fn-held-content-subject row)) (evidence (fn-held-release-evidence row)) (charge
                    (fn-held-charge row)) (stamp (fn-held-stamp row)))
                  (:instance fn-osa-alpha-keeps-pending-match (a (fn-node-prepare (fn-replay-advance-txid a
                    (fn-stxa-txid stxa)) (fn-record-generation row) (fn-record-msgid row) (fn-record-payload
                    row) (fn-record-groups row) (fn-record-obligation-id row) (fn-record-content-subject
                    row) (fn-record-release-evidence row) (fn-record-charge row) (fn-record-stamp row))) (b
                    (fn-node-prepare (fn-replay-advance-txid b (fn-stxa-txid stxa)) (fn-record-generation
                    (fn-orm-held row handle)) (fn-record-msgid (fn-orm-held row handle)) (fn-record-payload
                    (fn-orm-held row handle)) (fn-record-groups (fn-orm-held row handle))
                    (fn-record-obligation-id (fn-orm-held row handle)) (fn-record-content-subject
                    (fn-orm-held row handle)) (fn-record-release-evidence (fn-orm-held row handle))
                    (fn-record-charge (fn-orm-held row handle)) (fn-record-stamp (fn-orm-held row handle))))
                    (txid (fn-held-txid row)) (generation (fn-held-generation row)))
                  (:instance fn-osa-complete-keeps-full-node-alpha (a (fn-node-prepare
                    (fn-replay-advance-txid a (fn-stxa-txid stxa)) (fn-record-generation row)
                    (fn-record-msgid row) (fn-record-payload row) (fn-record-groups row)
                    (fn-record-obligation-id row) (fn-record-content-subject row)
                    (fn-record-release-evidence row) (fn-record-charge row) (fn-record-stamp row))) (b
                    (fn-node-prepare (fn-replay-advance-txid b (fn-stxa-txid stxa)) (fn-record-generation
                    (fn-orm-held row handle)) (fn-record-msgid (fn-orm-held row handle)) (fn-record-payload
                    (fn-orm-held row handle)) (fn-record-groups (fn-orm-held row handle))
                    (fn-record-obligation-id (fn-orm-held row handle)) (fn-record-content-subject
                    (fn-orm-held row handle)) (fn-record-release-evidence (fn-orm-held row handle))
                    (fn-record-charge (fn-orm-held row handle)) (fn-record-stamp (fn-orm-held row handle))))
                    (txid (fn-held-txid row)) (generation (fn-held-generation row)) (status :durable))
                  (:instance fn-held-p-forward-shape (x row))
                  (:instance fn-orm-held-preserves-the-held-shape)
                  (:instance fn-osa-node-state-is-nonempty-by-definition (node (fn-node-complete
                    (fn-node-prepare (fn-replay-advance-txid a (fn-stxa-txid stxa)) (fn-record-generation
                    row) (fn-record-msgid row) (fn-record-payload row) (fn-record-groups row)
                    (fn-record-obligation-id row) (fn-record-content-subject row)
                    (fn-record-release-evidence row) (fn-record-charge row) (fn-record-stamp row))
                    (fn-record-txid row) (fn-record-generation row) :durable)))
                  (:instance fn-osa-node-state-is-nonempty-by-definition (node (fn-node-complete
                    (fn-node-prepare (fn-replay-advance-txid b (fn-stxa-txid stxa)) (fn-record-generation
                    (fn-orm-held row handle)) (fn-record-msgid (fn-orm-held row handle)) (fn-record-payload
                    (fn-orm-held row handle)) (fn-record-groups (fn-orm-held row handle))
                    (fn-record-obligation-id (fn-orm-held row handle)) (fn-record-content-subject
                    (fn-orm-held row handle)) (fn-record-release-evidence (fn-orm-held row handle))
                    (fn-record-charge (fn-orm-held row handle)) (fn-record-stamp (fn-orm-held row handle)))
                    (fn-record-txid row) (fn-record-generation row) :durable))))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(fn-replay-apply-record fn-store-event-txid
               fn-replay-composite-held fn-hstxa-p-of-make
               fn-hstxa-accessors-of-make fn-hstxa-is-not-held
               fn-hstxa-is-no-wire-event
               fn-osa-empty-node-alpha-does-not-depend-on-arena
               fn-osa-remapped-held-keeps-article-inputs
               fn-osa-node-state-is-nonempty-by-definition
               fn-held-accessors-are-the-wire-accessors fn-held-p-fields
               fn-held-is-no-wire-event fn-cstp-held-kind-facts
               fn-node-prepare-preserves-state fn-node-complete-preserves-state
               fn-replay-advance-preserves-node-statep))))))
(local
 (defthm fn-osa-neutral-replay-keeps-node-alpha
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target)))
            (let ((new-a (fn-replay-apply-identity-neutral a event))
                  (new-b (fn-replay-apply-identity-neutral b event)))
              (and (equal (consp new-a) (consp new-b))
                   (equal (fn-osa-node-alpha new-a source)
                          (fn-osa-node-alpha new-b target)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-osa-advance-keeps-full-node-alpha
                             (txid (fn-store-event-txid event)))
                  (:instance fn-osa-alpha-keeps-replay-controls
                             (a (fn-replay-advance-txid a (fn-store-event-txid event)))
                             (b (fn-replay-advance-txid b (fn-store-event-txid event))))
                  (:instance fn-osa-advance-keeps-full-node-alpha
                             (a (fn-replay-advance-txid a (fn-store-event-txid event)))
                             (b (fn-replay-advance-txid b (fn-store-event-txid event)))
                             (txid (1+ (fn-store-event-txid event))))
                  (:instance fn-osa-node-state-is-nonempty-by-definition
                             (node (fn-replay-advance-txid
                                    (fn-replay-advance-txid a (fn-store-event-txid event))
                                    (1+ (fn-store-event-txid event)))))
                  (:instance fn-osa-node-state-is-nonempty-by-definition
                             (node (fn-replay-advance-txid
                                    (fn-replay-advance-txid b (fn-store-event-txid event))
                                    (1+ (fn-store-event-txid event))))))
            :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-replay-apply-identity-neutral
               fn-osa-empty-node-alpha-does-not-depend-on-arena
               fn-replay-advance-preserves-node-statep))))))
(local
 (defthm fn-osa-retention-replacement-keeps-alpha
   (implies (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
            (equal (fn-osa-node-alpha (fn-replay-node-with-retention a r) source)
                   (fn-osa-node-alpha (fn-replay-node-with-retention b r) target)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-replay-node-with-retention fn-osa-node-alpha)
                                   (fn-osa-acceptance-alpha))))))
(local
 (defthm fn-osa-retention-controls-by-definition
   (implies (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
            (and (equal (fn-node-retention a) (fn-node-retention b))
                 (equal (fn-node-bindings a) (fn-node-bindings b))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-osa-node-alpha) (fn-osa-acceptance-alpha))))))
(local
 (defthm fn-osa-retention-replacement-is-nrt-by-definition
   (equal (fn-replay-node-with-retention node r) (fn-nrt-node-with-retention node r))
   :hints (("Goal" :in-theory (enable fn-replay-node-with-retention fn-nrt-node-with-retention)))))
(local
 (defthm fn-osa-retention-completion-keeps-alpha
   (implies (and (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
                 (fn-node-statep (fn-replay-node-with-retention a r))
                 (fn-node-statep (fn-replay-node-with-retention b r)))
            (and (equal (consp (fn-replay-complete-retention a r event))
                        (consp (fn-replay-complete-retention b r event)))
                 (equal (fn-osa-node-alpha (fn-replay-complete-retention a r event) source)
                        (fn-osa-node-alpha (fn-replay-complete-retention b r event) target))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-osa-retention-replacement-keeps-alpha)
                  (:instance fn-osa-advance-keeps-full-node-alpha
                   (a (fn-replay-node-with-retention a r))
                   (b (fn-replay-node-with-retention b r))
                   (txid (1+ (fn-store-event-txid event))))
                  (:instance fn-osa-node-state-is-nonempty-by-definition
                   (node (fn-replay-advance-txid (fn-replay-node-with-retention a r)
                                               (1+ (fn-store-event-txid event)))))
                  (:instance fn-osa-node-state-is-nonempty-by-definition
                   (node (fn-replay-advance-txid (fn-replay-node-with-retention b r)
                                               (1+ (fn-store-event-txid event))))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-replay-complete-retention
                           fn-replay-advance-preserves-node-statep))))))
(local
 (defthm fn-osa-retention-replay-keeps-node-alpha
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
                 (fn-store-retention-event-p event))
            (let ((new-a (fn-replay-apply-retention-event a event))
                  (new-b (fn-replay-apply-retention-event b event)))
              (and (equal (consp new-a) (consp new-b))
                   (equal (fn-osa-node-alpha new-a source)
                          (fn-osa-node-alpha new-b target)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-osa-advance-keeps-full-node-alpha (txid (fn-store-event-txid event)))
                  (:instance fn-osa-alpha-keeps-replay-controls (a (fn-replay-advance-txid a
                    (fn-store-event-txid event))) (b (fn-replay-advance-txid b (fn-store-event-txid
                    event))))
                  (:instance fn-osa-retention-controls-by-definition (a (fn-replay-advance-txid a
                    (fn-store-event-txid event))) (b (fn-replay-advance-txid b (fn-store-event-txid
                    event))))
                  (:instance fn-osa-retention-completion-keeps-alpha (a (fn-replay-advance-txid a
                    (fn-store-event-txid event))) (b (fn-replay-advance-txid b (fn-store-event-txid event)))
                    (r (fn-retain-admit (fn-node-retention (fn-replay-advance-txid a (fn-store-event-txid
                    event))) (fn-store-event-obligation-id event) (fn-store-event-subject event) :forward
                    (fn-store-event-evidence event) (fn-store-event-charge event))))
                  (:instance fn-osa-retention-completion-keeps-alpha (a (fn-replay-advance-txid a
                    (fn-store-event-txid event))) (b (fn-replay-advance-txid b (fn-store-event-txid event)))
                    (r (fn-retain-release (fn-node-retention (fn-replay-advance-txid a (fn-store-event-txid
                    event))) (fn-store-event-obligation-id event) (fn-store-event-subject event) :forward
                    (fn-store-event-evidence event)))))
            :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-replay-apply-retention-event
               fn-osa-empty-node-alpha-does-not-depend-on-arena
               fn-osa-retention-replacement-is-nrt-by-definition
               fn-replay-advance-preserves-node-statep
               fn-nrt-node-admit-preserves-statep
               fn-nrt-node-release-preserves-statep))))))
(local
 (defthm fn-osa-row-bytes-is-referenced-handle-by-definition
   (equal (fn-row-bytes row fn-arena)
          (fn-handle-bytes (fn-record-payload row) fn-arena))
   :hints (("Goal" :in-theory (enable fn-row-bytes fn-handle-bytes)))))
(local
 (defthm fn-osa-valid-composite-reconstruction-by-definition
   (implies (fn-hstxa-p row)
            (equal (fn-hstxa-make (fn-hstxa-stxa row) (fn-hstxa-held row)) row))
   :hints (("Goal" :in-theory (e/d (fn-hstxa-p fn-hstxa-make fn-hstxa-stxa fn-hstxa-held)
                                   (fn-stxa-p fn-held-p))))))
(local
 (defthm fn-osa-nonarticle-row-keeps-actual-node-replay
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
                 (not (fn-held-p row)) (not (fn-hstxa-p row)))
            (let ((new-a (fn-replay-apply-record a row))
                  (new-b (fn-replay-apply-record b row)))
              (and (equal (consp new-a) (consp new-b))
                   (equal (fn-osa-node-alpha new-a source)
                          (fn-osa-node-alpha new-b target)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-osa-alpha-keeps-replay-controls)
                  (:instance fn-osa-retention-replay-keeps-node-alpha (event row))
                  (:instance fn-osa-neutral-replay-keeps-node-alpha (event row)))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-replay-apply-record
                           fn-osa-empty-node-alpha-does-not-depend-on-arena))))))
(defthm fn-osa-canonical-row-keeps-actual-node-replay
  (implies (and (fn-node-statep a) (fn-node-statep b)
                (equal (fn-osa-node-alpha a source) (fn-osa-node-alpha b target))
                (fn-store-event-p row) (natp handle)
                (equal (fn-orm-payload-bytes (fn-orm-row row handle) target)
                       (fn-orm-payload-bytes row source)))
           (let ((new-a (fn-replay-apply-record a row))
                 (new-b (fn-replay-apply-record b (fn-orm-row row handle))))
             (and (equal (consp new-a) (consp new-b))
                  (equal (fn-osa-node-alpha new-a source)
                         (fn-osa-node-alpha new-b target)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-held-p row) (fn-hstxa-p row))
           :use ((:instance fn-osa-alpha-keeps-replay-controls) (:instance
             fn-osa-held-replay-keeps-node-alpha)
                 (:instance fn-osa-composite-replay-keeps-node-alpha
                            (stxa (fn-hstxa-stxa row)) (row (fn-hstxa-held row)))
                 (:instance fn-osa-nonarticle-row-keeps-actual-node-replay))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-osa-row-on-valid-input-by-definition fn-orm-payload-bytes
              fn-osa-row-bytes-is-referenced-handle-by-definition
              fn-osa-valid-composite-reconstruction-by-definition
              fn-osa-remapped-held-keeps-article-inputs
              fn-osa-empty-node-alpha-does-not-depend-on-arena
              fn-held-is-no-wire-event fn-hstxa-is-no-wire-event
              fn-hstxa-is-not-held fn-hstxa-p-fields fn-hstxa-p-of-make
              fn-hstxa-accessors-of-make fn-held-accessors-are-the-wire-accessors
              fn-orm-held-preserves-the-held-shape fn-held-p-fields
              fn-cstp-held-kind-facts)))))
(defun fn-osa-cnode-alpha (cn fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (list (fn-osa-node-alpha (fn-cnode-node cn) fn-arena)
        (fn-cnode-config cn)))
(in-theory (disable fn-osa-cnode-alpha))
(local
 (defthm fn-osa-cnode-state-has-node-state-by-definition
   (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
   :hints (("Goal" :in-theory (enable fn-cnode-statep)))))
(local
 (defthm fn-osa-remap-keeps-configured-served-check
   (implies (and (fn-store-event-p row) (natp handle)
                 (equal (fn-cnode-config a) (fn-cnode-config b)))
            (equal (fn-cpr-event-servedp a row)
                   (fn-cpr-event-servedp b (fn-orm-row row handle))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-osa-remap-preserves-row-discriminants-and-coordinate)
            :cases ((fn-held-p row) (fn-hstxa-p row))
            :in-theory (e/d (fn-cpr-event-servedp fn-replay-composite-held fn-orm-held)
                           (fn-orm-row fn-held-p fn-hstxa-p fn-store-event-p
                            fn-cnode-selection-servedp fn-held-make fn-hstxa-make
                            fn-hstxa-held fn-hstxa-stxa))))))
(defthm fn-osa-canonical-row-keeps-actual-configured-replay
  (implies (and (fn-cnode-statep a) (fn-cnode-statep b)
                (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target))
                (fn-store-event-p row) (natp handle)
                (equal (fn-orm-payload-bytes (fn-orm-row row handle) target)
                       (fn-orm-payload-bytes row source)))
           (let ((new-a (fn-cpr-apply-event a row))
                 (new-b (fn-cpr-apply-event b (fn-orm-row row handle))))
             (and (equal (consp new-a) (consp new-b))
                  (equal (fn-osa-cnode-alpha new-a source)
                         (fn-osa-cnode-alpha new-b target)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-osa-remap-keeps-configured-served-check)
                 (:instance fn-osa-canonical-row-keeps-actual-node-replay
                            (a (fn-cnode-node a)) (b (fn-cnode-node b)))
                 (:instance fn-orm-row-retains-the-complete-payload-independent-projection)
                 (:instance fn-replay-apply-record-non-nil-is-node-state
                            (node (fn-cnode-node a)) (record row))
                 (:instance fn-replay-apply-record-non-nil-is-node-state
                            (node (fn-cnode-node b)) (record (fn-orm-row row handle))))
           :in-theory (e/d (fn-osa-cnode-alpha fn-cpr-apply-event)
                           (fn-cnode-statep fn-node-statep fn-replay-apply-record
                            fn-store-event-p fn-orm-row fn-orm-projection
                            fn-orm-payload-bytes fn-osa-node-alpha
                            fn-cpr-event-servedp)))))
(local
 (defthm fn-osa-cnode-alpha-keeps-config-check-by-definition
   (implies (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target))
            (equal (fn-cnode-record-acceptablep a record ceiling)
                   (fn-cnode-record-acceptablep b record ceiling)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-osa-cnode-alpha fn-osa-node-alpha
                                      fn-cnode-record-acceptablep)
                                     (fn-cfg-record-acceptablep fn-osa-acceptance-alpha))))))
(local
 (defthm fn-osa-config-transition-keeps-complete-alpha
   (implies (and (fn-cnode-statep a) (fn-cnode-statep b)
                 (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target)))
            (equal (fn-osa-cnode-alpha (fn-cnode-apply-config a record ceiling) source)
                   (fn-osa-cnode-alpha (fn-cnode-apply-config b record ceiling) target)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-osa-cnode-alpha-keeps-config-check-by-definition)
            :in-theory (e/d (fn-osa-cnode-alpha fn-osa-node-alpha
                             fn-osa-acceptance-alpha fn-osa-pending-alpha
                             fn-cnode-apply-config)
                            (fn-cnode-statep fn-cnode-record-acceptablep
                             fn-node-statep fn-statep fn-node-make-state
                             fn-make-state fn-retain-make-state
                             fn-articles-wire-of fn-cfg-apply-record
                             fn-cnode-extend-nexts fn-cnode-domain-of))))))
(local
 (defthm fn-osa-cnode-advance-keeps-complete-alpha
   (implies (and (fn-cnode-statep a) (fn-cnode-statep b)
                 (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target)))
            (equal (fn-osa-cnode-alpha (fn-cnode-make
                    (fn-replay-advance-txid (fn-cnode-node a) txid) (fn-cnode-config a)) source)
                   (fn-osa-cnode-alpha (fn-cnode-make
                    (fn-replay-advance-txid (fn-cnode-node b) txid) (fn-cnode-config b)) target)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-osa-advance-keeps-full-node-alpha
                         (a (fn-cnode-node a)) (b (fn-cnode-node b))))
            :in-theory (e/d (fn-osa-cnode-alpha)
                            (fn-osa-node-alpha fn-replay-advance-txid fn-cnode-statep))))))
