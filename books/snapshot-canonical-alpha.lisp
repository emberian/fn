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
