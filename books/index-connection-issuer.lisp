; INTERNAL ledger-backed connection issuance. DEMAND must be derived by the
; actual selected-runtime constructor. No supplied vector or pending marker
; alone licenses allocation, an owner open, or native activation.
(in-package "ACL2")
(include-book "index-backing-connection-pins")
(include-book "page-read-pool-state")

; Receipt8: tag, issued holder token, logical id, physical ordinal,
; candidate kind, full outstanding demand, phase, retained source pin.
(defun fn-icr-candidate (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((free (fn-ibp-connection-free fn-index-backing))
       (high (fn-ibp-connection-highwater fn-index-backing))
       (capacity (* 64 (fn-ibp-pool-capacity fn-index-backing))))
  (cond ((consp free)
         (if (and (natp (car free)) (< (car free) high) (< (car free) capacity))
             (mv :recycled (car free)) (mv :recovery-required nil)))
        (free (mv :recovery-required nil))
        ((< high capacity) (mv :fresh high))
        (t (mv :unavailable nil)))))

(defun fn-icr-keep-phase (receipt phase source)
 (declare (xargs :guard t))
 (list :connection-reservation (fn-omk-at 1 receipt) (fn-omk-at 2 receipt)
       (fn-omk-at 3 receipt) (fn-omk-at 4 receipt) (fn-omk-at 5 receipt)
       phase source))

 ; A retained intent denotes an uncertain partially executed transition.
; It must never be reported as an ordinary busy/yield that permits service
; to continue. The native caller still owes actual first-fault fencing.
(defun fn-icr-pending-status (receipt)
 (declare (xargs :guard t))
 (if (and (fn-omk-widthp receipt 8)
          (eq (fn-omk-at 0 receipt) :connection-reservation)
          (member-eq (fn-omk-at 6 receipt) '(:charged :registered :pin-owned :source-owned :abort-ready)))
     :busy :recovery-required))

(defun fn-icr-reserve (id demand fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t))
 (cond ((fn-ibp-connection-pending fn-index-backing)
        (mv (fn-icr-pending-status (fn-ibp-connection-pending fn-index-backing))
            nil fn-index-backing fn-page-read-pool))
       ((not (and (natp id) (fn-prs-vectorp demand)
                  (equal (fn-prl-nth 4 demand) 1)))
        (mv :unsupported-runtime nil fn-index-backing fn-page-read-pool))
       (t
        (mv-let (kind ordinal) (fn-icr-candidate fn-index-backing)
         (if (not (and (member-eq kind '(:fresh :recycled)) (natp ordinal)))
             (mv kind nil fn-index-backing fn-page-read-pool)
           (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
                  (budget (fn-prl-nth 0 ledger)))
            (mv-let (word issued charged)
             (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                           (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                           (fn-prl-nth 4 budget) demand)
             (if (not (eq word :admitted))
                 (mv word nil fn-index-backing fn-page-read-pool)
               ; Publish the SAME pool debit before constructing the token,
               ; receipt or physical metadata. A raw escape after this debit
               ; is an owner recovery event, never permission to retry/refund.
               (let* ((fn-page-read-pool
                       (fn-owner-page-read-keep-ledger
                         (fn-prl-build budget charged issued (fn-prl-nth 3 ledger)
                                       (fn-prl-baseline ledger)) fn-page-read-pool))
                      (token (list :connection-holder issued
                                  (+ 1 (floor ordinal 64)) (mod ordinal 64)))
                      (receipt (list :connection-reservation token id ordinal
                                     kind demand :charged nil))
                      (fn-index-backing
                       (if (eq kind :fresh)
                           (update-fn-ibp-connection-highwater (+ 1 ordinal) fn-index-backing)
                         (update-fn-ibp-connection-free
                           (let ((free (fn-ibp-connection-free fn-index-backing)))
                             (if (consp free) (cdr free) free))
                           fn-index-backing)))
                      (fn-index-backing (update-fn-ibp-connection-pending receipt fn-index-backing)))
                 (mv :reserved token fn-index-backing fn-page-read-pool))))))))))

; Register only an already constructed, admitted child. Missing physical
; capacity returns unavailable and keeps the exact receipt/charge; this path
; never runs a default-creating stobj-table getter to repair absence.
(defun fn-icr-register (token fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
  (cond ((not (and (fn-ich-tokenp token)
                   (eq (fn-omk-at 0 receipt) :connection-reservation)
                   (equal (fn-omk-at 1 receipt) token)))
         (mv :stale fuel fn-index-backing))
        ((eq (fn-omk-at 6 receipt) :registered)
         (mv :registered fuel fn-index-backing))
        ((not (eq (fn-omk-at 6 receipt) :charged))
         (mv :recovery-required fuel fn-index-backing))
        (t
         (let ((fn-index-backing
                (update-fn-ibp-connection-pending
                  (fn-icr-keep-phase receipt :register-intent nil) fn-index-backing)))
         (mv-let (word payload left fn-index-backing)
          (fn-ibp-connection-event token :reserve (fn-omk-at 2 receipt)
                                   (fn-omk-at 5 receipt) fuel fn-index-backing)
          (declare (ignore payload))
          (if (not (eq word :reserved))
              (let ((fn-index-backing
                     (update-fn-ibp-connection-pending receipt fn-index-backing)))
                (mv word left fn-index-backing))
            (let ((fn-index-backing
                   (update-fn-ibp-connection-pending
                     (fn-icr-keep-phase receipt :registered nil) fn-index-backing)))
              (mv :registered left fn-index-backing)))))))))

; KIND comes only from the actual owner's reader-view selector. In particular,
; absent D never falls back to the working publication during a batch barrier.
(defun fn-icr-selected-generation (kind fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((association (if (eq kind :d) (fn-ibp-reader-d-pin fn-index-backing)
                       (if (eq kind :current) (fn-ibp-current fn-index-backing) nil)))
        (tag (if (eq kind :d) :publication-pin :installed-publication))
        (token (fn-omk-at 1 association)))
  (if (and (member-eq kind '(:d :current))
           (eq (fn-omk-at 0 association) tag) (fn-ibp-generation-tokenp token))
      token nil)))

; A raw interruption at pin-intent is uncertain; it must not retry retain.
; A definite refusal restores registered. Success first records pin-owned,
; then attaches it to the child. A retry of pin-owned only retries attach.
(defun fn-icr-capture (token kind fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((receipt (fn-ibp-connection-pending fn-index-backing))
        (phase (fn-omk-at 6 receipt))
        (needed (* 2 (+ 1 (fn-ibp-slot-depth fn-index-backing)))))
  (cond
   ((not (and (fn-ich-tokenp token) (equal (fn-omk-at 1 receipt) token)
              (eq (fn-omk-at 0 receipt) :connection-reservation)))
    (mv :stale nil fuel fn-index-backing))
   ((eq phase :source-owned) (mv :captured (fn-omk-at 7 receipt) fuel fn-index-backing))
   ((not (member-eq phase '(:registered :pin-owned)))
    (mv :recovery-required nil fuel fn-index-backing))
   ((< fuel needed) (mv :yield nil fuel fn-index-backing))
   (t
    (mv-let (word pin left fn-index-backing)
     (if (eq phase :pin-owned)
         (mv :retained (fn-omk-at 7 receipt) fuel fn-index-backing)
       (let ((generation (fn-icr-selected-generation kind fn-index-backing)))
        (if (not generation) (mv :unavailable nil fuel fn-index-backing)
         (let ((fn-index-backing
                (update-fn-ibp-connection-pending
                  (fn-icr-keep-phase receipt :pin-intent generation) fn-index-backing)))
          (mv-let (retained pub remaining fn-index-backing)
           (fn-ibp-generation-reference generation :retain :pin nil fuel fn-index-backing)
           (if (not (eq retained :retained))
               (let ((fn-index-backing
                      (update-fn-ibp-connection-pending receipt fn-index-backing)))
                 (mv retained nil remaining fn-index-backing))
             (let* ((pin (list :publication-pin generation pub))
                    (fn-index-backing
                     (update-fn-ibp-connection-pending
                       (fn-icr-keep-phase receipt :pin-owned pin) fn-index-backing)))
               (mv :retained pin remaining fn-index-backing))))))))
     (if (not (eq word :retained)) (mv word nil left fn-index-backing)
       (mv-let (attached payload remaining fn-index-backing)
        (fn-ibp-connection-event token :attach (fn-omk-at 2 receipt) pin
                                 (nfix left) fn-index-backing)
        (declare (ignore payload))
        (if (not (eq attached :attached))
            (mv :recovery-required nil remaining fn-index-backing)
          (let ((fn-index-backing
                 (update-fn-ibp-connection-pending
                   (fn-icr-keep-phase receipt :source-owned pin) fn-index-backing)))
            (mv :captured pin remaining fn-index-backing))))))))))

; INTERNAL finish after the SAME actual owner open/repin has accepted ID.
; This does not accept a host Boolean as evidence of that transition. Its
; composed caller must bind the returned token to that accepted connection.
(defun fn-icr-finish-open (id token fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
  (if (not (and (fn-ich-tokenp token)
                (eq (fn-omk-at 0 receipt) :connection-reservation)
                (equal (fn-omk-at 1 receipt) token)
                (equal (fn-omk-at 2 receipt) id)
                (eq (fn-omk-at 6 receipt) :source-owned)))
      (mv :stale fuel fn-index-backing)
    (mv-let (word row left) (fn-ibp-connection-read token fuel fn-index-backing)
     (if (not (and (eq word :present)
                   (equal (fn-omk-at 2 row) id)
                   (eq (fn-omk-at 4 row) :live)
                   (equal (fn-omk-at 3 row) (fn-omk-at 7 receipt))))
         (mv (if (eq word :yield) :yield :recovery-required) left fn-index-backing)
       (let ((fn-index-backing (update-fn-ibp-connection-pending nil fn-index-backing)))
        (mv :opened left fn-index-backing)))))))

; Settling is a serialized transaction spanning registry, pool and free list.
; Its intent retains the actual grant and source before either is removed.
; A raw escape anywhere after intent fences the service: repeating settlement
; is forbidden because the reusable debit or the generation drop may already
; have happened. The process-local nonce is never refunded. Permanent slot /
; free-list metadata must be covered by the installed runtime baseline.
(local
 (defthm fn-icr-natural-list-is-true-list
  (implies (fn-prs-nats-p x) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-prs-nats-p)))))
(defun fn-icr-settle (token fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard (natp fuel)
  :guard-hints (("Goal" :in-theory
   (e/d (fn-prs-vectorp)
        (fn-ibp-connection-read fn-ibp-connection-release fn-ich-row-release-ready
         fn-owner-page-read-ledger))))))
 (cond
  ((and (fn-ibp-connection-pending fn-index-backing)
        (not (and (equal (fn-omk-at 1 (fn-ibp-connection-pending fn-index-backing)) token)
                  (eq (fn-omk-at 6 (fn-ibp-connection-pending fn-index-backing)) :abort-ready))))
   (mv (fn-icr-pending-status (fn-ibp-connection-pending fn-index-backing))
       fuel fn-index-backing fn-page-read-pool))
  ((not (fn-ich-tokenp token))
   (mv :stale fuel fn-index-backing fn-page-read-pool))
  ((< fuel (* 4 (+ 1 (fn-ibp-slot-depth fn-index-backing))))
   (mv :yield fuel fn-index-backing fn-page-read-pool))
  (t
   (mv-let (word row left) (fn-ibp-connection-read token fuel fn-index-backing)
    (if (not (eq word :present)) (mv word left fn-index-backing fn-page-read-pool)
     (mv-let (ready pin grant) (fn-ich-row-release-ready row)
      (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
             (charged (fn-prl-nth 1 ledger))
             (ordinal (+ (* 64 (- (fn-omk-at 2 token) 1)) (fn-omk-at 3 token))))
       (cond
        ((not (eq ready :ready)) (mv ready left fn-index-backing fn-page-read-pool))
        ((not (and (fn-prs-vectorp grant) (fn-prs-vectorp charged)
                    (fn-prs-below grant charged)
                    (< ordinal (fn-ibp-connection-highwater fn-index-backing))))
         (mv :recovery-required left fn-index-backing fn-page-read-pool))
        (t
         (let ((fn-index-backing
                (update-fn-ibp-connection-pending
                 (list :connection-reservation token (fn-omk-at 2 row) ordinal
                       :retiring grant :settle-intent pin) fn-index-backing)))
          (mv-let (released actual-grant remaining fn-index-backing)
           (fn-ibp-connection-release token (nfix left) fn-index-backing)
           (if (not (and (eq released :released) (equal actual-grant grant)))
               (mv :recovery-required remaining fn-index-backing fn-page-read-pool)
             (let* ((fn-page-read-pool
                     (fn-owner-page-read-keep-ledger
                      (fn-prl-build (fn-prl-nth 0 ledger)
                        (fn-prs-release-reusable charged grant) (fn-prl-nth 2 ledger)
                        (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)) fn-page-read-pool))
                    (fn-index-backing
                     (update-fn-ibp-connection-free
                      (cons ordinal (fn-ibp-connection-free fn-index-backing)) fn-index-backing))
                    (fn-index-backing
                     (update-fn-ibp-connection-pending nil fn-index-backing)))
              (mv :released remaining fn-index-backing fn-page-read-pool))))))))))))))

; Definite pre-open refusal cancels only this owned reservation. Registered
; rows go through the SAME close/alias/generation settlement as live ones.
; An uncertain register/retain/settle intent is never cancellation authority.
(defun fn-icr-abort (token fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard (natp fuel)
  :guard-hints (("Goal" :in-theory
    (e/d (fn-prs-vectorp)
         (fn-ibp-connection-event fn-icr-settle fn-owner-page-read-ledger))))))
 (let* ((receipt (fn-ibp-connection-pending fn-index-backing))
        (phase (fn-omk-at 6 receipt))
        (grant (fn-omk-at 5 receipt))
        (ordinal (fn-omk-at 3 receipt))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool))
        (charged (fn-prl-nth 1 ledger)))
  (cond
   ((not (and (fn-omk-widthp receipt 8) (fn-ich-tokenp token)
               (eq (fn-omk-at 0 receipt) :connection-reservation)
               (equal (fn-omk-at 1 receipt) token)))
    (mv :stale fuel fn-index-backing fn-page-read-pool))
   ((eq phase :abort-ready) (fn-icr-settle token fuel fn-index-backing fn-page-read-pool))
   ((not (member-eq phase '(:charged :registered :source-owned)))
    (mv :recovery-required fuel fn-index-backing fn-page-read-pool))
   ((eq phase :charged)
    (if (not (and (fn-prs-vectorp grant) (fn-prs-vectorp charged)
                   (fn-prs-below grant charged) (natp ordinal)
                   (< ordinal (fn-ibp-connection-highwater fn-index-backing))))
        (mv :recovery-required fuel fn-index-backing fn-page-read-pool)
      (let* ((fn-index-backing
              (update-fn-ibp-connection-pending
               (fn-icr-keep-phase receipt :settle-intent nil) fn-index-backing))
             (fn-page-read-pool
              (fn-owner-page-read-keep-ledger
               (fn-prl-build (fn-prl-nth 0 ledger) (fn-prs-release-reusable charged grant)
                             (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger)
                             (fn-prl-nth 4 ledger)) fn-page-read-pool))
             (fn-index-backing
              (update-fn-ibp-connection-free
               (cons ordinal (fn-ibp-connection-free fn-index-backing)) fn-index-backing))
             (fn-index-backing (update-fn-ibp-connection-pending nil fn-index-backing)))
       (mv :released fuel fn-index-backing fn-page-read-pool))))
   ((< fuel (* 5 (+ 1 (fn-ibp-slot-depth fn-index-backing))))
    (mv :yield fuel fn-index-backing fn-page-read-pool))
   (t
    (let ((fn-index-backing
           (update-fn-ibp-connection-pending
            (fn-icr-keep-phase receipt :abort-intent (fn-omk-at 7 receipt)) fn-index-backing)))
     (mv-let (closed payload left fn-index-backing)
      (fn-ibp-connection-event token :close (fn-omk-at 2 receipt) nil fuel fn-index-backing)
      (declare (ignore payload))
      (if (not (eq closed :closing))
          (mv :recovery-required left fn-index-backing fn-page-read-pool)
        (let ((fn-index-backing
               (update-fn-ibp-connection-pending
                (fn-icr-keep-phase receipt :abort-ready (fn-omk-at 7 receipt)) fn-index-backing)))
         (fn-icr-settle token (nfix left) fn-index-backing fn-page-read-pool)))))))))
