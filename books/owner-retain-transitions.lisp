; Actual host-called retention carry transitions.
; The owner installer is one global put (W9's obligation view is parked:
; books/owner-obligation-state.lisp). Raw owner dispatch stays disabled.
(in-package "ACL2")
(include-book "owner-state-accessors")
(include-book "owner-retain-state")
(include-book "owner-obligation-state")
(include-book "identity-retain-carried")

(defthm fn-owner-retain-carry-of-install-ocfg
  (equal (fn-owner-retain-carry (fn-owner-install-ocfg oc state))
         (fn-owner-retain-carry state))
  :hints (("Goal" :in-theory (e/d (fn-owner-install-ocfg)
                                  (put-global)))))

; Entry guards read the owner after the carry global changes.  These
; exact frame/availability facts avoid reopening the whole state writer.
(defthm fn-owner-ocfg-of-retain-carry-put
  (equal (fn-owner-ocfg (fn-owner-retain-carry-put carry state))
         (fn-owner-ocfg state))
  :hints (("Goal" :in-theory (enable fn-owner-ocfg
                                    fn-owner-retain-carry-put))))

(defthm fn-owner-bound-of-retain-carry-put
  (equal (boundp-global 'fn-owner (fn-owner-retain-carry-put carry state))
         (boundp-global 'fn-owner state))
  :hints (("Goal" :in-theory (enable fn-owner-retain-carry-put))))

(defthm fn-owner-bound-of-install-ocfg
  (boundp-global 'fn-owner (fn-owner-install-ocfg oc state))
  :hints (("Goal" :in-theory (enable fn-owner-install-ocfg))))

(defthm fn-owner-ocfg-of-install-ocfg
  (equal (fn-owner-ocfg (fn-owner-install-ocfg oc state)) oc)
  :hints (("Goal" :in-theory (enable fn-owner-ocfg))))

(defthm fn-owner-ocfg-of-other-global-put
  (implies (not (equal key 'fn-owner))
           (equal (fn-owner-ocfg (f-put-global key value state))
                  (fn-owner-ocfg state)))
  :hints (("Goal" :in-theory (enable fn-owner-ocfg))))

(defthm fn-owner-bound-of-other-global-put
  (implies (not (equal key 'fn-owner))
           (equal (boundp-global 'fn-owner (f-put-global key value state))
                  (boundp-global 'fn-owner state))))

; Proof-only carried entry-state invariant. Never called by native serving
; code or used as an executable guard: it names the maintained relation.
(defun fn-owner-retain-statep (state)
  (declare (xargs :stobjs state :guard t :verify-guards nil))
  (and (boundp-global 'fn-owner state)
       (fn-lgoc-invariantp (fn-owner-ocfg state))
       (fn-prc-carryp (fn-owner-retain-carry state))))

(defthm fn-owner-retain-statep-implies-entry-guard
  (implies (fn-owner-retain-statep state)
           (and (boundp-global 'fn-owner state)
                (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                (fn-prc-carryp (fn-owner-retain-carry state))))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep fn-sbud-oc-store
                               fn-lgoc-invariant-statep))))

(defun fn-owner-prepare-identity (event fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                              (fn-prc-carryp (fn-owner-retain-carry state)))
                  :guard-hints (("Goal" :in-theory (enable fn-sn-statep fn-sbud-oc-store fn-arena-count-is-len)))))
  (let ((s (fn-owner-store state)))
    (if (not (or (fn-stxk-p event) (fn-stxa-p event)))
        (value :invalid)
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
      (let ((carry (fn-prc-refresh (fn-owner-retain-carry state)
                                   (fn-node-retention (fn-sn-node s)))))
      (mv-let (word next)
        (fn-irc-pout-prepare-identity (fn-owner-ocfg state) event
                                      (fn-arena-count fn-arena) carry)
      (let* ((row (fn-oii-identity-row event (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                       (fn-arena-count fn-arena)))
             (state (fn-owner-retain-carry-put carry state))
             (state (fn-owner-install-ocfg next state)))
        (cond ((not (equal word :prepared)) (value word))
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
                 (value (list :seal (fn-oii-identity-payload event)))))
              (t (value :prepared)))))))))

(defthm fn-owner-prepare-identity-preserves-retain-carry
  (implies (fn-prc-carryp (fn-owner-retain-carry state))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 2 (fn-owner-prepare-identity event fn-arena state)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-prepare-identity mv-nth nth endp zp car-cons cdr-cons
              (:executable-counterpart zp)
              (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-other-global-put
              fn-owner-retain-carry-of-install-ocfg
              fn-prc-carryp-of-refresh)
            (theory 'minimal-theory)))))

(defthm fn-owner-prepare-identity-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep
            (mv-nth 2 (fn-owner-prepare-identity event fn-arena state))))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-statep fn-owner-prepare-identity
             fn-pout-prepare-identity mv-nth nth endp zp car-cons cdr-cons
             fn-owner-bound-of-retain-carry-put
             fn-owner-bound-of-install-ocfg fn-owner-bound-of-other-global-put
             fn-owner-ocfg-of-retain-carry-put fn-owner-ocfg-of-install-ocfg
             fn-owner-ocfg-of-other-global-put
             fn-owner-retain-carry-of-put
             fn-owner-retain-carry-of-other-global-put
             fn-owner-retain-carry-of-install-ocfg
             fn-prc-carryp-of-refresh
             fn-irc-pout-prepare-identity-of-refresh-is-pout
             fn-oiis-prepare-identity-preserves-invariant))))

(defun fn-owner-finish-synced (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                              (fn-prc-carryp (fn-owner-retain-carry state)))
                  :guard-hints (("Goal" :in-theory (e/d (fn-sbud-oc-store) (boundp-global))))))
  (let* ((before (fn-owner-core state))
         (before-files (fn-sn-files (fn-own-store before)))
         ;; served-costs-4 (Q5b): the completion the host calls is
         ;; fn-irc-rix-ocfg-complete (books/identity-retain-carried.lisp),
         ;; its gate and finish applying an identity, consumer or topic
         ;; record through the carried obligation-id trie brought to the
         ;; Store node's ledger (boundary fn-irc-rix-ocfg-complete-is-rix,
         ;; then derived composition
         ;; fn-irc-rix-ocfg-complete-of-refresh-is-ocfg-step-complete-by-definition).
         (carry (fn-prc-refresh (fn-owner-retain-carry state)
                                (fn-node-retention
                                 (fn-sn-node (fn-own-store before)))))
         (state (fn-owner-retain-carry-put carry state))
         (state (fn-owner-install-ocfg
                 (fn-irc-rix-ocfg-complete (fn-owner-ocfg state) fn-hist carry)
                 state))
         (after (fn-owner-core state))
         (after-files (fn-sn-files (fn-own-store after))))
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (fn-own-ledger-count after)
                    (1+ (fn-own-ledger-count before))))
        (value :durable)
      (value :fault))))

(defthm fn-owner-finish-synced-preserves-retain-carry
  (implies (fn-prc-carryp (fn-owner-retain-carry state))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 2 (fn-owner-finish-synced fn-hist state)))))
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
