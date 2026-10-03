; Actual host-called retention carry transitions.
; The owner installer is one global put (W9's obligation view is parked:
; books/owner-obligation-state.lisp). Raw owner dispatch stays disabled.
(in-package "ACL2")
(include-book "owner-state-accessors")
(include-book "owner-retain-state")
(include-book "owner-obligation-state")
(include-book "identity-retain-carried")

; The installers' effects and frames are books/owner-carrier.lisp's.

; Proof-only carried entry-state invariant. Never called by native serving
; code or used as an executable guard: it names the maintained relation.
(defun fn-owner-retain-statep (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st :guard t :verify-guards nil))
  (and (fn-owner-boundp fn-owner-st)
       (fn-lgoc-invariantp (fn-owner-ocfg fn-owner-st))
       (fn-prc-carryp (fn-owner-retain-carry fn-owner-st))))

(defthm fn-owner-retain-statep-implies-entry-guard
  (implies (fn-owner-retain-statep fn-owner-st)
           (and (fn-owner-boundp fn-owner-st)
                (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg fn-owner-st)))
                (fn-prc-carryp (fn-owner-retain-carry fn-owner-st))))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep fn-sbud-oc-store
                               fn-lgoc-invariant-statep))))

(defun fn-owner-prepare-identity (event fn-arena fn-owner-st state)
  (declare (xargs :stobjs (fn-arena fn-owner-st state) :guard (and (fn-owner-boundp fn-owner-st)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg fn-owner-st)))
                              (fn-prc-carryp (fn-owner-retain-carry fn-owner-st)))
                  :guard-hints (("Goal" :in-theory (enable fn-sn-statep fn-sbud-oc-store fn-arena-count-is-len)))))
  (let ((s (fn-owner-store fn-owner-st)))
    (if (not (or (fn-stxk-p event) (fn-stxa-p event)))
        (mv nil :invalid fn-owner-st state)
      ;; fn-oiis-prepare-identity (books/owner-identity-served.lisp): the
      ;; owner's identity prepare over the ROW the intern makes of EVENT at
      ;; the arena's count (signed-post: fn-oii-identity-row, KEYSTONE
      ;; fn-oii-ocfg-prepare-identity-is-intern-then-step), when the row's
      ;; article groups are served (prepare-served's test over the row --
      ;; over the wire event it answered t for every composite; KEYSTONE
      ;; fn-oiis-prepare-identity-preserves-invariant), and the owner
      ;; unchanged otherwise.
      ;; fn-pout-prepare-identity (books/owner-prepare-outcome.lisp) answers
      ;; its word (KEYSTONE fn-pout-prepare-identity-answers-the-store-change).
      ;; served-costs-4 (Q5b): the prepare the host calls is
      ;; fn-irc-pout-prepare-identity (books/identity-retain-carried.lisp)
      ;; with the carried obligation-id trie brought to the Store node's
      ;; ledger, as the article prepare above: the gate's record application
      ;; answers the retention admission from the trie instead of scanning
      ;; every pin and release (KEYSTONE
      ;; fn-irc-pout-prepare-identity-of-refresh-is-pout: its word and owner
      ;; are fn-pout-prepare-identity's for every carry the host holds).
      (let ((carry (fn-prc-refresh (fn-owner-retain-carry fn-owner-st)
                                   (fn-node-retention (fn-sn-node s)))))
      (mv-let (word next)
        (fn-irc-pout-prepare-identity (fn-owner-ocfg fn-owner-st) event
                                      (fn-arena-count fn-arena) carry)
      (let* ((row (fn-oii-identity-row event (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                       (fn-arena-count fn-arena)))
             (fn-owner-st (fn-owner-retain-carry-put carry fn-owner-st))
             (fn-owner-st (fn-owner-install-ocfg next fn-owner-st)))
        (cond ((not (equal word :prepared)) (mv nil word fn-owner-st state))
              ((fn-oii-identity-sealsp event)
               ; The catalog (signed-post's red, catalog-columns): the article
               ; this event serves and its held row -- the row itself for a
               ; plain record, the held row inside the composite for a signed
               ; one -- kept for the catalog's prepare after the host's seal
               ; (fn-owner-cat-prepare-sealed), completed by
               ; fn-owner-finish-identity (T4 then T2, as a POST).
               (let ((state (f-put-global
                             'fn-owner-cat-candidate
                             (if (fn-hstxa-p row)
                                 (cons (fn-replay-composite-record event) (fn-hstxa-held row))
                               (cons event row))
                             state)))
                 (mv nil (list :seal (fn-oii-identity-payload event)) fn-owner-st state)))
              (t (mv nil :prepared fn-owner-st state)))))))))

(defthm fn-owner-prepare-identity-preserves-retain-carry
  (implies (fn-prc-carryp (fn-owner-retain-carry fn-owner-st))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 2 (fn-owner-prepare-identity event fn-arena fn-owner-st state)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-prepare-identity mv-nth nth endp zp car-cons cdr-cons
              (:executable-counterpart zp)
              (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-install-ocfg
              fn-prc-carryp-of-refresh)
            (theory 'minimal-theory)))))

(defthm fn-owner-prepare-identity-preserves-retain-state
  (implies (fn-owner-retain-statep fn-owner-st)
           (fn-owner-retain-statep
            (mv-nth 2 (fn-owner-prepare-identity event fn-arena fn-owner-st state))))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-statep fn-owner-prepare-identity
             fn-pout-prepare-identity mv-nth nth endp zp car-cons cdr-cons
             fn-owner-bound-of-retain-carry-put
             fn-owner-bound-of-install-ocfg 
             fn-owner-ocfg-of-retain-carry-put fn-owner-ocfg-of-install-ocfg
             fn-owner-retain-carry-of-put
             fn-owner-retain-carry-of-install-ocfg
             fn-prc-carryp-of-refresh
             fn-irc-pout-prepare-identity-of-refresh-is-pout
             fn-oiis-prepare-identity-preserves-invariant))))

(defun fn-owner-finish-synced (fn-hist fn-owner-st state)
  (declare (xargs :stobjs (fn-hist fn-owner-st state) :guard (and (fn-owner-boundp fn-owner-st)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg fn-owner-st)))
                              (fn-prc-carryp (fn-owner-retain-carry fn-owner-st)))
                  :guard-hints (("Goal" :in-theory (e/d (fn-sbud-oc-store) (boundp-global))))))
  (let* ((before (fn-owner-core fn-owner-st))
         (before-files (fn-sn-files (fn-own-store before)))
         ;; served-costs-4 (Q5b): the completion the host calls is
         ;; fn-irc-rix-ocfg-complete (books/identity-retain-carried.lisp),
         ;; its gate and finish applying an identity, consumer or topic
         ;; record through the carried obligation-id trie brought to the
         ;; Store node's ledger (boundary fn-irc-rix-ocfg-complete-is-rix,
         ;; then derived composition
         ;; fn-irc-rix-ocfg-complete-of-refresh-is-ocfg-step-complete-by-definition).
         (carry (fn-prc-refresh (fn-owner-retain-carry fn-owner-st)
                                (fn-node-retention
                                 (fn-sn-node (fn-own-store before)))))
         (fn-owner-st (fn-owner-retain-carry-put carry fn-owner-st))
         (fn-owner-st (fn-owner-install-ocfg
                 (fn-irc-rix-ocfg-complete (fn-owner-ocfg fn-owner-st) fn-hist carry)
                 fn-owner-st))
         (after (fn-owner-core fn-owner-st))
         (after-files (fn-sn-files (fn-own-store after))))
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (fn-own-ledger-count after)
                    (1+ (fn-own-ledger-count before))))
        (mv nil :durable fn-owner-st state)
      (mv nil :fault fn-owner-st state))))

(defthm fn-owner-finish-synced-preserves-retain-carry
  (implies (fn-prc-carryp (fn-owner-retain-carry fn-owner-st))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 2 (fn-owner-finish-synced fn-hist fn-owner-st state)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-finish-synced mv-nth nth endp zp car-cons cdr-cons
              (:executable-counterpart zp)
              (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-install-ocfg
              fn-prc-carryp-of-refresh)
            (theory 'minimal-theory)))))

(in-theory (disable fn-owner-retain-statep fn-owner-prepare-identity fn-owner-finish-synced))
