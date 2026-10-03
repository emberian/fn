; Internal exact-current request adoption. The parent fetches its pending
; receipt and persists child+pool+address ownership in one serialized call.
; No host receipt, demand vector or resource snapshot is an authority.
(in-package "ACL2")
(logic)
(include-book "index-backing-resource-driver")
(include-book "index-query-slot-issuer")
(include-book "index-reader-request")
(include-book "index-adoption-context")
(include-book "receiver-held-ticket")
(include-book "receiver-query-custody-producer")

(defun fn-ibp-adoption-eligiblep (token kind control capture context receipt scratch ledger
                                fn-ibp-query-segment fn-query-payload-grants)
 (declare (xargs :stobjs (fn-ibp-query-segment fn-query-payload-grants) :guard t))
 (and (fn-ibp-query-tokenp token)
  (let* ((slot (nth 3 token)) (nonce (nth 1 token))
         (old (fn-ibp-qs-admissionsi slot fn-ibp-query-segment))
         (payload-old (fn-qpg-rowsi slot fn-query-payload-grants))
         (demand (fn-omk-at 5 receipt))
         (claim (fn-ibp-query-resource-token token capture context))
         (payload (fn-omk-at 5 context))
         (charged (fn-prl-nth 1 ledger)))
   (and (equal (fn-omk-at 0 receipt) :index-request-receipt)
        (equal (fn-omk-at 7 receipt) :committed)
        (equal (fn-omk-at 2 receipt) nonce)
        (equal (fn-omk-at 3 receipt) (+ (* 64 (- (nth 2 token) 1)) slot))
        (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)
        (fn-prs-vectorp scratch) (equal (fn-prl-nth 4 scratch) 0)
        (fn-iqr-tokenp claim)
        (fn-qpg-tokenp payload)
        (equal (fn-omk-at 1 payload) nonce)
        (equal (fn-omk-at 2 payload) slot)
        (equal (fn-omk-at 3 payload) (nth 4 token))
        (equal (fn-omk-at 6 payload) (nth 2 token))
        (< (fn-qpg-active fn-query-payload-grants) 64)
        (equal (nth 2 token) (fn-ibp-qs-id fn-ibp-query-segment))
        (equal (nth 2 token) (fn-qpg-segment-id fn-query-payload-grants))
        (equal (fn-ibp-qs-ticketsi slot fn-ibp-query-segment) 0)
        (< (fn-ibp-qs-active fn-ibp-query-segment) 64)
        (fn-ibp-control-kindp kind control)
        (equal (fn-omk-at 1 control) nonce)
        (equal (fn-omk-at 2 control) (nth 4 token))
        (equal (fn-omk-at 1 capture) (nth 4 token))
        (not (member-eq (fn-omk-at 2 old) '(:active :cancelled)))
        (or (not (natp (fn-omk-at 3 old))) (< (fn-omk-at 3 old) nonce))
        (not (member-eq (fn-omk-at 2 payload-old) '(:active :cancelled)))
        (or (not (natp (fn-omk-at 3 payload-old))) (< (fn-omk-at 3 payload-old) nonce))
        (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                         '(0 0 0 0 0) charged)
        (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                         '(0 0 0 0 0) (fn-prs-plus charged scratch))))))

; All three child eligibility checks precede mutation. D is already charged
; by the actual pending receipt; only S is added. The refund row owns D+S,
; while the global spent identity and NEXT remain unchanged.
(defun fn-ibp-adopt-children (token kind control capture context receipt scratch ledger
                             fn-ibp-query-segment fn-query-payload-grants)
 (declare (xargs :stobjs (fn-ibp-query-segment fn-query-payload-grants) :guard t
                 :verify-guards nil))
 (mv-let (context-word owned-context)
  (fn-ibp-adoption-context token context receipt)
 (if (or (not (eq context-word :context-ready))
         (not (fn-ibp-adoption-eligiblep token kind control capture context receipt scratch ledger
                                   fn-ibp-query-segment fn-query-payload-grants)))
     (mv :refused nil ledger fn-ibp-query-segment fn-query-payload-grants)
  (let* ((slot (nth 3 token))
         (claim (fn-ibp-query-resource-token token capture context))
         (payload (fn-omk-at 5 context))
         (remaining (fn-prs-plus (fn-omk-at 5 receipt) scratch)))
   (mv-let (word fn-ibp-query-segment)
    (fn-ibp-slot-register token kind control capture owned-context fn-ibp-query-segment)
    (if (not (eq word :captured))
        (mv :recovery-required nil ledger fn-ibp-query-segment fn-query-payload-grants)
      (mv-let (word grant fn-query-payload-grants)
       (fn-qpg-acquire (nth 1 token) slot (nth 4 token)
                       (fn-omk-at 4 payload) (fn-omk-at 5 payload) claim fn-query-payload-grants)
       (if (not (eq word :acquired))
           (mv :recovery-required nil ledger fn-ibp-query-segment fn-query-payload-grants)
         (let ((fn-ibp-query-segment
                 (update-fn-ibp-qs-admissionsi slot
                   (list claim remaining :active (nth 1 token)) fn-ibp-query-segment)))
          (mv :adopted grant
           (fn-prl-build (fn-prl-nth 0 ledger) (fn-prs-plus (fn-prl-nth 1 ledger) scratch)
                         (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))
           fn-ibp-query-segment fn-query-payload-grants))))))))))
; Only eligibility's token and payload shape are needed for these calls.
; Expanding custody, funding and child mutation multiplies unrelated cases.
(verify-guards fn-ibp-adopt-children
 :hints (("Goal" :in-theory
          (e/d (fn-ibp-adoption-eligiblep fn-ibp-query-tokenp fn-qpg-tokenp)
               (fn-ibp-adoption-context fn-ibp-query-resource-token fn-prs-fundedp
                fn-prs-vectorp fn-iqr-tokenp fn-ibp-control-kindp fn-qpg-acquire
                fn-ibp-slot-register)))))

(defun fn-ibp-node-adopt-receipt (token kind control capture context receipt scratch ledger
                                 fuel address depth fn-ibp-node)
 (declare (xargs :stobjs fn-ibp-node :measure (nfix depth) :verify-guards nil
                 :guard (and (natp fuel) (natp address) (natp depth))))
 (cond
  ((<= fuel depth) (mv :yield nil ledger 0 fuel fn-ibp-node))
  ((zp depth)
   (if (not (and (zp address)
                 (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node)
                 (fn-ibp-node-children-boundp 'fn-query-payload-grants fn-ibp-node)))
       (mv :unavailable nil ledger 0 fuel fn-ibp-node)
     (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment)))
                 (fn-query-payload-grants
                   (fn-ibp-node-children-get 'fn-query-payload-grants fn-ibp-node
                                             (create-fn-query-payload-grants))))
       (status grant next-ledger fn-ibp-query-segment fn-query-payload-grants)
       (fn-ibp-adopt-children token kind control capture context receipt scratch ledger
                              fn-ibp-query-segment fn-query-payload-grants)
       (mv status grant next-ledger (if (eq status :adopted) 1 0) (- fuel 1) fn-ibp-node))))
  ((evenp address)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
       (mv :unavailable nil ledger 0 fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-left
                  (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                            (create-fn-ibp-node-left))))
      (status grant next-ledger delta remaining fn-ibp-node-left)
      (fn-ibp-node-adopt-receipt token kind control capture context receipt scratch ledger
                                (- fuel 1) (floor address 2) (- depth 1) fn-ibp-node-left)
      (mv status grant next-ledger delta remaining fn-ibp-node))))
  (t
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
       (mv :unavailable nil ledger 0 fuel fn-ibp-node)
     (stobj-let ((fn-ibp-node-right
                  (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                            (create-fn-ibp-node-right))))
      (status grant next-ledger delta remaining fn-ibp-node-right)
      (fn-ibp-node-adopt-receipt token kind control capture context receipt scratch ledger
                                (- fuel 1) (floor address 2) (- depth 1) fn-ibp-node-right)
      (mv status grant next-ledger delta remaining fn-ibp-node))))))
(verify-guards fn-ibp-node-adopt-receipt)

; Reserve S and persist D+S in the current pending receipt BEFORE the
; control/capture/context constructors. Retry reads the exact nonce marker;
; it neither repeats the charge nor manufactures a new identity.
(defun fn-ibp-reserve-capture-scratch (nonce scratch fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (marker (fn-ibp-request-capture fn-index-backing))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool)))
  (cond
   ((not (and (posp nonce) (fn-irr-receipt-committedp receipt)
              (equal (fn-omk-at 2 receipt) nonce)))
    (mv :stale fn-index-backing fn-page-read-pool))
   (marker
    (mv (if (and (eq (fn-omk-at 0 marker) :capture-scratch)
                 (equal (fn-omk-at 1 marker) nonce)) :reserved :recovery-required)
        fn-index-backing fn-page-read-pool))
   ((not (and (fn-prs-vectorp scratch) (equal (fn-prl-nth 4 scratch) 0)
               (fn-prs-vectorp (fn-omk-at 5 receipt))
               (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                               '(0 0 0 0 0) (fn-prl-nth 1 ledger))
               (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                               '(0 0 0 0 0) (fn-prs-plus (fn-prl-nth 1 ledger) scratch))))
    (mv :refused fn-index-backing fn-page-read-pool))
   (t
    (let* ((fn-page-read-pool
             (fn-owner-page-read-keep-ledger
              (fn-prl-build (fn-prl-nth 0 ledger) (fn-prs-plus (fn-prl-nth 1 ledger) scratch)
                            (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))
              fn-page-read-pool))
           (fn-index-backing
             (update-fn-ibp-request-pending
              (fn-irq-receipt-keep-demand receipt
                 (fn-prs-plus (fn-omk-at 5 receipt) scratch))
              fn-index-backing))
           (fn-index-backing
             (update-fn-ibp-request-capture (list :capture-scratch nonce scratch) fn-index-backing)))
      (mv :reserved fn-index-backing fn-page-read-pool))))))

; Parent authority: actual current committed receipt, exact allocator head,
; and existing indexed children. No caller receipt or physical address.
(defun fn-ibp-pending-range-adopt-funded
 (fuel fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
                 :guard (natp fuel) :verify-guards nil))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-irr-receipt-request receipt))
        (publication (fn-irr-request-publication request))
        (nonce (fn-omk-at 2 receipt))
        (ordinal (fn-omk-at 3 receipt))
        (generation (fn-ipub-generation publication))
        (original-generation (fn-irq-receipt-request-generation receipt))
        (ticket (fn-owner-rx-turn-custody-ticket fn-rx-provider fn-receiver-turn
                                                fn-page-read-pool))
        (depth (fn-ibp-slot-depth fn-index-backing))
        (active (fn-ibp-payload-active fn-index-backing)))
  (cond
   ((not (and (fn-irr-receipt-committedp receipt)
               (eq (fn-omk-at 0 (fn-ibp-request-capture fn-index-backing)) :capture-scratch)
               (equal (fn-omk-at 1 (fn-ibp-request-capture fn-index-backing)) nonce)))
    (mv :stale nil fuel fn-index-backing fn-page-read-pool))
   ((fn-omk-at 3 (fn-ibp-request-capture fn-index-backing))
    (mv :recovery-required
        (fn-omk-at 1 (fn-omk-at 3 (fn-ibp-request-capture fn-index-backing)))
        fuel fn-index-backing fn-page-read-pool))
   ((not (and (posp nonce) (natp ordinal) (posp generation) (posp original-generation)
               (natp (fn-ipub-arena-incarnation publication))
               (natp (fn-ipub-arena-prefix publication))))
    (mv :recovery-required nil fuel fn-index-backing fn-page-read-pool))
   ((<= fuel depth) (mv :yield nil fuel fn-index-backing fn-page-read-pool))
   (t
    (mv-let (candidate-kind candidate) (fn-irq-candidate fn-index-backing)
     (if (not (and (eq candidate-kind (fn-irq-receipt-candidate-kind receipt)) (equal candidate ordinal)))
         (mv :recovery-required nil fuel fn-index-backing fn-page-read-pool)
       (let* ((token (fn-irq-candidate-token nonce ordinal generation))
              (capture (fn-ipub-capture publication))
              (payload (list :query-payload nonce (nth 3 token) generation
                              (fn-ipub-arena-incarnation publication)
                              (fn-ipub-arena-prefix publication) (nth 2 token)))
              (original (fn-irq-candidate-token nonce ordinal original-generation)))
        (mv-let (custody-word context)
         (fn-ric-pending-reader-context ticket original payload fn-rx-provider
          fn-receiver-turn fn-index-backing fn-page-read-pool)
         (if (not (eq custody-word :captured-custody))
             (mv :unavailable-custody nil fuel fn-index-backing fn-page-read-pool)
          (let* ((claim (fn-ibp-query-resource-token token capture context))
                 (control (fn-irr-range-control receipt claim))
                 (marker (fn-ibp-request-capture fn-index-backing))
                 (fn-index-backing
                   (update-fn-ibp-request-capture
                     (list (fn-omk-at 0 marker) (fn-omk-at 1 marker)
                           (fn-omk-at 2 marker) (list :adopt-intent token))
                     fn-index-backing)))
        (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
         (status grant next-ledger delta remaining fn-ibp-node)
         (fn-ibp-node-adopt-receipt token :range control capture context receipt '(0 0 0 0 0)
           (fn-owner-page-read-ledger fn-page-read-pool) fuel (- (nth 2 token) 1) depth fn-ibp-node)
         (if (not (and (eq status :adopted) (equal delta 1) (fn-qpg-tokenp grant)))
             (if (and (member-eq status '(:yield :unavailable :refused))
                      (equal delta 0))
                 (let ((fn-index-backing
                         (update-fn-ibp-request-capture marker fn-index-backing)))
                  (mv status nil remaining fn-index-backing fn-page-read-pool))
               (let* ((fn-page-read-pool
                        (fn-owner-page-read-keep-ledger next-ledger fn-page-read-pool))
                      (fn-index-backing
                        (update-fn-ibp-request-capture
                         (list (fn-omk-at 0 marker) (fn-omk-at 1 marker)
                               (fn-omk-at 2 marker) (list :adopt-uncertain token))
                         fn-index-backing)))
                (mv :recovery-required token remaining fn-index-backing fn-page-read-pool)))
           (let* ((fn-index-backing
                    (update-fn-ibp-payload-active (+ active 1) fn-index-backing))
                  (fn-index-backing
                    (if (eq candidate-kind :fresh)
                        (update-fn-ibp-request-highwater (+ ordinal 1) fn-index-backing)
                      (update-fn-ibp-request-free
                        (cdr (fn-ibp-request-free fn-index-backing)) fn-index-backing)))
                  (fn-index-backing (update-fn-ibp-request-pending nil fn-index-backing))
                  (fn-index-backing (update-fn-ibp-request-capture nil fn-index-backing))
                  (fn-page-read-pool (fn-owner-page-read-keep-ledger next-ledger fn-page-read-pool)))
             (mv :adopted token remaining fn-index-backing fn-page-read-pool))))))))))))))
; Keep custody and receipt computations opaque: their results impose no
; additional guards here. Preserve symbolic state selectors for NTH-UPDATE-NTH;
; only the freshly constructed query token needs NTH opened on explicit conses.
(verify-guards fn-ibp-pending-range-adopt-funded
 :hints (("Goal"
          :expand ((:free (n a b) (nth n (cons a b))))
          :in-theory
          (disable fn-ibp-node-adopt-receipt fn-ibp-nodep
                   fn-ric-pending-reader-context fn-owner-rx-turn-custody-ticket
                   fn-irr-receipt-committedp fn-irq-receipt-request-generation
                   fn-ibp-query-resource-token fn-irr-range-control fn-ipub-capture
                   fn-qpg-tokenp nth nth-add1 update-nth len true-listp
                   fn-rx-providerp fn-receiver-turnp fn-page-read-poolp))))

; Internal actual producer obtains SCRATCH from the installed operation
; census. This is deliberately not a D40 vector-taking host callback.
(defun fn-ibp-pending-range-adopt
 (scratch fuel fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-index-backing fn-page-read-pool) :guard (natp fuel)))
 (if (<= fuel (fn-ibp-slot-depth fn-index-backing))
     (mv :yield nil fuel fn-index-backing fn-page-read-pool)
   (let ((nonce (fn-omk-at 2 (fn-ibp-request-pending fn-index-backing))))
    (mv-let (status fn-index-backing fn-page-read-pool)
     (fn-ibp-reserve-capture-scratch nonce scratch fn-index-backing fn-page-read-pool)
     (if (not (eq status :reserved))
         (mv status nil fuel fn-index-backing fn-page-read-pool)
       (fn-ibp-pending-range-adopt-funded fuel fn-rx-provider fn-receiver-turn
          fn-index-backing fn-page-read-pool))))))
