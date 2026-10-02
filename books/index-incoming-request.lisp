; UNHOOKED cert-roots (2026-10-02): out of the Makefile certify roots -- a Codex-era book that never certified and no image world includes: its include index-backing-request-adoption does not certify within the timeout at dev adbf57435. The code stays; its completion is queued (build/coordinator/lanedumps/cert-roots.md).
; Incoming-only producer pieces. Supplied demand is INTERNAL operation evidence,
; not a runtime receipt. Public begin must obtain actual installed issuer support.
(in-package "ACL2")
(logic)
(include-book "index-query-slot-issuer")
(include-book "index-backing-request-adoption")
(include-book "incoming-octet-holder")
(include-book "incoming-authority-freshness")

(defun fn-iiq-context-ready-p (context)
 (declare (xargs :guard t))
 (and (fn-omk-widthp context 10)
      (eq (fn-omk-at 0 context) :incoming-context)
      (fn-ioh-tokenp (fn-omk-at 1 context))
      (natp (fn-omk-at 2 context))))

(defun fn-iiq-receipt-request (receipt)
 (declare (xargs :guard t)) (fn-omk-at 6 receipt))
(defun fn-iiq-receipt-p (receipt)
 (declare (xargs :guard t))
 (and (fn-omk-widthp receipt 10)
      (eq (fn-omk-at 0 receipt) :incoming-request-receipt)
      (fn-omk-widthp (fn-iiq-receipt-request receipt) 10)
      (eq (fn-omk-at 0 (fn-iiq-receipt-request receipt)) :incoming-request)))

; Shared pending excludes reader and incoming issuers. A nonempty unrelated
; pending row is busy, never overwritten. Only admitted PRS results allocate
; request/receipt records; OLD NEXT stays recorded as the spent identity.
(defun fn-iiq-reserve-request (context publication gen-token demand
                              fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (if (fn-ibp-request-pending fn-index-backing)
     (mv :busy nil fn-index-backing fn-page-read-pool)
  (mv-let (kind ordinal) (fn-irq-candidate fn-index-backing)
   (if (not (member-eq kind '(:fresh :recycled)))
       (mv kind nil fn-index-backing fn-page-read-pool)
    (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
           (budget (fn-prl-nth 0 ledger)) (old-next (fn-prl-nth 2 ledger)))
     (if (not (and (fn-iiq-context-ready-p context)
                   (fn-ibp-generation-tokenp gen-token)
                   (posp (fn-ipub-generation publication))
                   (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
         (mv :unavailable nil fn-index-backing fn-page-read-pool)
      (mv-let (word issued charge)
       (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                     (fn-prl-nth 1 ledger) old-next (fn-prl-nth 4 budget) demand)
       (if (not (eq word :admitted))
           (mv word nil fn-index-backing fn-page-read-pool)
        (let* ((fn-page-read-pool
                 (fn-owner-page-read-keep-ledger
                   (fn-prl-build budget charge issued (fn-prl-nth 3 ledger)
                                 (fn-prl-baseline ledger)) fn-page-read-pool))
               (origin (list :incoming-index issued))
               (request (list :incoming-request (fn-omk-at 1 context)
                         (fn-omk-at 2 context) (fn-omk-at 1 (fn-omk-at 9 context))
                         (fn-omk-at 4 context) publication gen-token origin context nil))
               (receipt (list :incoming-request-receipt old-next issued ordinal
                         (list kind (fn-ipub-generation publication)) demand
                         request :reserved nil nil))
               (fn-index-backing
                 (update-fn-ibp-request-pending receipt fn-index-backing)))
         (mv :reserved issued fn-index-backing fn-page-read-pool))))))))))

; Missing actual constructor/scratch receipt is unavailable, even if a caller
; has put a runtime-shaped object in the provider field. No installer exists
; for this operation yet; this seam is not a generic shape-based activation.
(defun fn-iiq-installed-runtime-source (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t)
          (ignore fn-index-backing))
 (mv :unavailable nil nil))

; Debt/scratch marker remains incoming-specific in the SAME pending field.
; This internal operand is allowed only after the actual operation issuer.
(defun fn-iiq-reserve-scratch (nonce scratch fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (marker (fn-ibp-request-capture fn-index-backing))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool)))
  (cond
   ((not (and (fn-iiq-receipt-p receipt) (posp nonce)
              (equal nonce (fn-omk-at 2 receipt))))
    (mv :stale fn-index-backing fn-page-read-pool))
   (marker
    (mv (if (and (fn-omk-widthp marker 4)
                 (eq (fn-omk-at 0 marker) :incoming-capture-scratch)
                 (equal nonce (fn-omk-at 1 marker))) :reserved :recovery-required)
        fn-index-backing fn-page-read-pool))
   ((not (and (eq (fn-omk-at 7 receipt) :reserved)
              (fn-prs-vectorp scratch) (equal (fn-prl-nth 4 scratch) 0)
              (fn-prs-vectorp (fn-omk-at 5 receipt))
              (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                              '(0 0 0 0 0) (fn-prl-nth 1 ledger))
              (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                              '(0 0 0 0 0)
                              (fn-prs-plus (fn-prl-nth 1 ledger) scratch))))
    (mv :refused fn-index-backing fn-page-read-pool))
   (t
    (let* ((fn-page-read-pool
             (fn-owner-page-read-keep-ledger
              (fn-prl-build (fn-prl-nth 0 ledger)
                (fn-prs-plus (fn-prl-nth 1 ledger) scratch)
                (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))
              fn-page-read-pool))
           (fn-index-backing
             (update-fn-ibp-request-pending
              (list :incoming-request-receipt (fn-omk-at 1 receipt)
                    (fn-omk-at 2 receipt) (fn-omk-at 3 receipt) (fn-omk-at 4 receipt)
                    (fn-prs-plus (fn-omk-at 5 receipt) scratch)
                    (fn-omk-at 6 receipt) :ready nil nil) fn-index-backing))
           (fn-index-backing
             (update-fn-ibp-request-capture
              (list :incoming-capture-scratch nonce scratch :unretained) fn-index-backing)))
     (mv :reserved fn-index-backing fn-page-read-pool))))))

(defun fn-iiq-publication-coordinates= (x y)
 (declare (xargs :guard t))
 (and (equal (fn-ipub-generation x) (fn-ipub-generation y))
      (equal (fn-ipub-table-id x) (fn-ipub-table-id y))
      (equal (fn-ipub-row-id x) (fn-ipub-row-id y))
      (equal (fn-ipub-count x) (fn-ipub-count y))
      (equal (fn-ipub-frontier x) (fn-ipub-frontier y))
      (equal (fn-ipub-arena-incarnation x) (fn-ipub-arena-incarnation y))
      (equal (fn-ipub-arena-prefix x) (fn-ipub-arena-prefix y))))

(defun fn-iiq-reserve-or-resume (context publication gen-token demand
                                fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-iiq-receipt-request receipt)))
  (cond
   ((not receipt)
    (fn-iiq-reserve-request context publication gen-token demand fn-index-backing fn-page-read-pool))
   ((not (fn-iiq-receipt-p receipt))
    (mv :busy nil fn-index-backing fn-page-read-pool))
   ((not (and (fn-iiq-context-ready-p context)
              (fn-iaf-holder= (fn-omk-at 1 context) (fn-omk-at 1 request))
              (equal (fn-omk-at 2 context) (fn-omk-at 2 request))
              (fn-iaf-octets= 32 (fn-omk-at 1 (fn-omk-at 9 context))
                                (fn-omk-at 3 request))
              (fn-iiq-publication-coordinates= publication (fn-omk-at 5 request))
              (fn-ibp-generation-tokenp gen-token)
              (equal gen-token (fn-omk-at 6 request))
              (member-eq (fn-omk-at 7 receipt) '(:reserved :ready))
              (posp (fn-omk-at 2 receipt))))
    (mv :recapture-required nil fn-index-backing fn-page-read-pool))
   (t (mv :reserved (fn-omk-at 2 receipt) fn-index-backing fn-page-read-pool)))))

; Retain the stored actual generation exactly once. A yielded registry descent
; has not retained; :retained writes the marker in this same parent transition.
(defun fn-iiq-retain-generation (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel) :verify-guards nil))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (marker (fn-ibp-request-capture fn-index-backing))
        (token (fn-omk-at 6 (fn-iiq-receipt-request receipt))))
  (cond
   ((not (and (fn-iiq-receipt-p receipt) (eq (fn-omk-at 7 receipt) :ready)
              (fn-omk-widthp marker 4)
              (eq (fn-omk-at 0 marker) :incoming-capture-scratch)
              (equal (fn-omk-at 1 marker) (fn-omk-at 2 receipt))
              (fn-ibp-generation-tokenp token)))
    (mv :recovery-required fuel fn-index-backing))
   ((eq (fn-omk-at 3 marker) :generation-retained)
    (mv :retained fuel fn-index-backing))
   ((not (eq (fn-omk-at 3 marker) :unretained))
    (mv :recovery-required fuel fn-index-backing))
   (t
    (let ((fn-index-backing
            (update-fn-ibp-request-capture
             (list :incoming-capture-scratch (fn-omk-at 1 marker)
                   (fn-omk-at 2 marker) (list :generation-retain-intent token))
             fn-index-backing)))
    (mv-let (word publication left fn-index-backing)
     (fn-ibp-generation-reference token :retain :query nil fuel fn-index-backing)
     (let ((fn-index-backing
             (if (eq word :retained)
                 (update-fn-ibp-request-capture
                  (list :incoming-capture-scratch (fn-omk-at 1 marker)
                        (fn-omk-at 2 marker)
                        (if (fn-iiq-publication-coordinates= publication
                              (fn-omk-at 5 (fn-iiq-receipt-request receipt)))
                            :generation-retained :generation-retained-uncertain))
                  fn-index-backing)
               (update-fn-ibp-request-capture marker fn-index-backing))))
      (mv (if (and (eq word :retained)
                   (not (fn-iiq-publication-coordinates= publication
                         (fn-omk-at 5 (fn-iiq-receipt-request receipt)))))
              :recovery-required word)
          left fn-index-backing))))))))

; Compatibility projection is internal; original incoming receipt stays in
; context field4. Reader request remains a different tag. Projection supplies
; no runtime, registration, holder or generation authority.
(defun fn-iiq-adoption-receipt (receipt)
 (declare (xargs :guard t))
 (list :index-request-receipt (fn-omk-at 1 receipt) (fn-omk-at 2 receipt)
       (fn-omk-at 3 receipt) (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
       (fn-omk-at 6 receipt) :committed (fn-omk-at 8 receipt) (fn-omk-at 9 receipt)))

(defun fn-iiq-query-context (receipt payload)
 (declare (xargs :guard t))
 (let ((request (fn-iiq-receipt-request receipt)))
  (list :incoming-query-context (fn-omk-at 1 request) (fn-omk-at 2 request)
        (fn-omk-at 6 request) receipt payload (fn-omk-at 4 request)
        (fn-omk-at 7 request) receipt)))

(defun fn-iiq-query-control (receipt)
 (declare (xargs :guard t))
 (let* ((request (fn-iiq-receipt-request receipt))
        (publication (fn-omk-at 5 request))
        (msgid (fn-omk-at 4 request))
        (tag (fn-mpxt-tag msgid (fn-ipub-key publication))))
  (fn-miq-make (fn-omk-at 2 receipt) (fn-ipub-generation publication)
    (fn-ipub-key publication) (fn-ipub-count publication)
    (fn-ipub-frontier publication) (fn-ipub-pages publication) msgid tag
    (list (fn-mpx-home tag (nfix (fn-ipub-pages publication)))
          (fn-ipub-pages publication) 0) nil nil :probing)))

; Only the actual child+pool adoption permits allocator advance/pending clear.
; No range/RC adapter is called. The registered context retains original receipt.
(defun fn-iiq-attempted-token (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((marker (fn-ibp-request-capture fn-index-backing))
        (phase (fn-omk-at 3 marker)) (token (fn-omk-at 1 phase)))
  (and (eq (fn-omk-at 0 marker) :incoming-capture-scratch)
       (member-eq (fn-omk-at 0 phase) '(:adopt-intent :adopt-uncertain))
       (fn-ibp-query-tokenp token) token)))

(defun fn-iiq-adopt-pending (fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool)
                 :guard (natp fuel) :verify-guards nil))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (marker (fn-ibp-request-capture fn-index-backing))
        (request (fn-iiq-receipt-request receipt))
        (publication (fn-omk-at 5 request))
        (nonce (fn-omk-at 2 receipt)) (ordinal (fn-omk-at 3 receipt))
        (generation (fn-ipub-generation publication))
        (depth (fn-ibp-slot-depth fn-index-backing))
        (active (fn-ibp-payload-active fn-index-backing)))
  (cond
   ((fn-iiq-attempted-token fn-index-backing)
    (mv :recovery-required (fn-iiq-attempted-token fn-index-backing)
        fuel fn-index-backing fn-page-read-pool))
   ((not (and (fn-iiq-receipt-p receipt) (eq (fn-omk-at 7 receipt) :ready)
              (fn-omk-widthp marker 4)
              (eq (fn-omk-at 0 marker) :incoming-capture-scratch)
              (equal nonce (fn-omk-at 1 marker))
              (eq (fn-omk-at 3 marker) :generation-retained)
              (posp nonce) (natp ordinal) (posp generation)
              (natp (fn-ipub-arena-incarnation publication))
              (natp (fn-ipub-arena-prefix publication))))
    (mv :recovery-required nil fuel fn-index-backing fn-page-read-pool))
   ((<= fuel depth) (mv :yield nil fuel fn-index-backing fn-page-read-pool))
   (t
    (mv-let (kind candidate) (fn-irq-candidate fn-index-backing)
     (if (not (and (eq kind (fn-irq-receipt-candidate-kind receipt))
                   (equal candidate ordinal)))
         (mv :recovery-required nil fuel fn-index-backing fn-page-read-pool)
      (let* ((token (fn-irq-candidate-token nonce ordinal generation))
             (capture (fn-ipub-capture publication))
             (payload (list :query-payload nonce (nth 3 token) generation
                       (fn-ipub-arena-incarnation publication)
                       (fn-ipub-arena-prefix publication) (nth 2 token)))
             (context (fn-iiq-query-context receipt payload))
             (control (fn-iiq-query-control receipt))
             (compatibility (fn-iiq-adoption-receipt receipt))
             ; Intent is installed before any child mutation. An interrupted
             ; call retains the actual identity and cannot repeat adoption.
             (fn-index-backing
               (update-fn-ibp-request-capture
                (list :incoming-capture-scratch nonce (fn-omk-at 2 marker)
                      (list :adopt-intent token)) fn-index-backing)))
       (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
        (word grant next-ledger delta left fn-ibp-node)
        (fn-ibp-node-adopt-receipt token :mid control capture context compatibility
         '(0 0 0 0 0) (fn-owner-page-read-ledger fn-page-read-pool)
         fuel (- (nth 2 token) 1) depth fn-ibp-node)
        (if (not (and (eq word :adopted) (equal delta 1) (fn-qpg-tokenp grant)))
            (if (member-eq word '(:adopted :recovery-required))
                ; A child may already own the query. Fence retry and retain the
                ; actual attempted identity plus returned ledger; never roll back.
                (let* ((fn-index-backing
                         (update-fn-ibp-request-capture
                          (list :incoming-capture-scratch nonce (fn-omk-at 2 marker)
                                (list :adopt-uncertain token)) fn-index-backing))
                       (fn-page-read-pool
                         (fn-owner-page-read-keep-ledger next-ledger fn-page-read-pool)))
                  (mv :recovery-required token left fn-index-backing fn-page-read-pool))
              (let ((fn-index-backing
                      (update-fn-ibp-request-capture marker fn-index-backing)))
                (mv word nil left fn-index-backing fn-page-read-pool)))
          (let* ((fn-index-backing
                  (update-fn-ibp-payload-active (+ active 1) fn-index-backing))
                 (fn-index-backing
                  (if (eq kind :fresh)
                      (update-fn-ibp-request-highwater (+ ordinal 1) fn-index-backing)
                    (update-fn-ibp-request-free (cdr (fn-ibp-request-free fn-index-backing))
                                               fn-index-backing)))
                 (fn-index-backing (update-fn-ibp-request-pending nil fn-index-backing))
                 (fn-index-backing (update-fn-ibp-request-capture nil fn-index-backing))
                 (fn-page-read-pool
                  (fn-owner-page-read-keep-ledger next-ledger fn-page-read-pool)))
           (mv :captured token left fn-index-backing fn-page-read-pool)))))))))))

(verify-guards fn-iiq-retain-generation
 :hints (("Goal" :in-theory (disable fn-ibp-generation-reference fn-index-backingp))))
(verify-guards fn-iiq-adopt-pending
 :hints (("Goal" :in-theory (e/d (fn-ibp-query-tokenp fn-irq-candidate-token fn-ibp-query-token)
                                      (fn-ibp-node-adopt-receipt fn-ibp-nodep)))))

; Subject is the actual new SAMEpool reservation primitive, not reader reserve.
(defthm fn-iiq-reserved-keeps-spent-identity-and-positive-nonce
 (implies (equal (mv-nth 0 (fn-iiq-reserve-request context publication gen-token demand
                            fn-index-backing fn-page-read-pool)) :reserved)
  (let* ((next-backing (mv-nth 2 (fn-iiq-reserve-request context publication gen-token demand
                                    fn-index-backing fn-page-read-pool)))
         (next-pool (mv-nth 3 (fn-iiq-reserve-request context publication gen-token demand
                                 fn-index-backing fn-page-read-pool)))
         (receipt (fn-ibp-request-pending next-backing))
         (old-next (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool))))
   (and (equal (fn-omk-at 1 receipt) old-next)
        (equal (fn-omk-at 2 receipt) (+ 1 old-next))
        (posp (fn-omk-at 2 receipt))
        (equal (fn-prl-nth 2 (fn-owner-page-read-ledger next-pool))
               (fn-omk-at 2 receipt)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-iiq-reserve-request fn-prs-issue
  fn-owner-page-read-ledger fn-owner-page-read-keep-ledger fn-prl-build fn-prl-nth fn-omk-at))))

(defthm fn-iiq-unreserved-preserves-custody
 (implies (not (equal (mv-nth 0 (fn-iiq-reserve-request context publication gen-token demand
                                fn-index-backing fn-page-read-pool)) :reserved))
  (and (equal (mv-nth 2 (fn-iiq-reserve-request context publication gen-token demand
                         fn-index-backing fn-page-read-pool)) fn-index-backing)
       (equal (mv-nth 3 (fn-iiq-reserve-request context publication gen-token demand
                         fn-index-backing fn-page-read-pool)) fn-page-read-pool)))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-irq-candidate fn-prs-issue))))

(defthm fn-iiq-interrupted-adoption-preserves-custody
 (implies (fn-iiq-attempted-token fn-index-backing)
  (and (equal (mv-nth 0 (fn-iiq-adopt-pending fuel fn-index-backing fn-page-read-pool))
              :recovery-required)
       (equal (mv-nth 1 (fn-iiq-adopt-pending fuel fn-index-backing fn-page-read-pool))
              (fn-iiq-attempted-token fn-index-backing))
       (equal (mv-nth 3 (fn-iiq-adopt-pending fuel fn-index-backing fn-page-read-pool))
              fn-index-backing)
       (equal (mv-nth 4 (fn-iiq-adopt-pending fuel fn-index-backing fn-page-read-pool))
              fn-page-read-pool)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-iiq-adopt-pending)
                                (fn-iiq-attempted-token fn-ibp-node-adopt-receipt)))))

(defun fn-iiq-input-source= (x y)
 (declare (xargs :guard t))
 (and (eq (fn-omk-at 0 x) :incoming-input-source)
      (eq (fn-omk-at 0 y) :incoming-input-source)
      (fn-iaf-holder= (fn-omk-at 1 x) (fn-omk-at 1 y))
      (equal (fn-omk-at 1 (fn-omk-at 2 x)) (fn-omk-at 1 (fn-omk-at 2 y)))
      (equal (fn-omk-at 2 (fn-omk-at 2 x)) (fn-omk-at 2 (fn-omk-at 2 y)))
      (equal (fn-omk-at 3 x) (fn-omk-at 3 y))
      (equal (fn-omk-at 4 x) (fn-omk-at 4 y))))

; Internal reconstruction only: SOURCE is the immediately preceding actual
; producer result. An already retained source is never replaced by a resume.
(defun fn-iiq-keep-input-source (source fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-iiq-receipt-request receipt))
        (old (fn-omk-at 9 request)))
  (cond ((not (and (fn-iiq-receipt-p receipt)
                   (eq (fn-omk-at 0 source) :incoming-input-source)))
         (mv :source-unavailable fn-index-backing))
   (old (mv (if (fn-iiq-input-source= old source) :source-kept :recovery-required)
                 fn-index-backing))
   (t
    (let ((request (list (fn-omk-at 0 request) (fn-omk-at 1 request)
                  (fn-omk-at 2 request) (fn-omk-at 3 request) (fn-omk-at 4 request)
                  (fn-omk-at 5 request) (fn-omk-at 6 request) (fn-omk-at 7 request)
                  (fn-omk-at 8 request) source)))
     (let ((fn-index-backing
      (update-fn-ibp-request-pending
       (list (fn-omk-at 0 receipt) (fn-omk-at 1 receipt) (fn-omk-at 2 receipt)
             (fn-omk-at 3 receipt) (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
             request (fn-omk-at 7 receipt) (fn-omk-at 8 receipt) (fn-omk-at 9 receipt))
       fn-index-backing)))
      (mv :source-kept fn-index-backing)))))))


(defthm fn-iiq-retained-input-source-is-never-replaced
 (implies (fn-omk-at 9 (fn-iiq-receipt-request
                       (fn-ibp-request-pending fn-index-backing)))
  (equal (mv-nth 1 (fn-iiq-keep-input-source source fn-index-backing))
         fn-index-backing))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-iiq-keep-input-source)
               (fn-iiq-input-source= fn-iiq-receipt-p fn-iiq-receipt-request
                fn-ibp-request-pending fn-omk-at)))))

(defthm fn-iiq-invalid-source-retains-pending-custody
 (implies (not (eq (fn-omk-at 0 source) :incoming-input-source))
  (and (equal (mv-nth 0 (fn-iiq-keep-input-source source fn-index-backing))
              :source-unavailable)
       (equal (mv-nth 1 (fn-iiq-keep-input-source source fn-index-backing))
              fn-index-backing)))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-iiq-keep-input-source)
               (fn-iiq-input-source= fn-iiq-receipt-p fn-iiq-receipt-request
                fn-ibp-request-pending fn-omk-at)))))
