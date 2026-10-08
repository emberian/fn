; Actual cold owner initialization and atomic reclaim installation.
; The cold entry carries the recovered Store and node-secret key domains.
; These are proved at producers before any raw owner dispatch is considered.
(in-package "ACL2")
(include-book "owner-report-capture")
(include-book "owner-retain-transitions")
(include-book "owner-reclaim-carry")
(include-book "store-checkpoint-arena-writer")
(include-book "store-genesis")
(include-book "feed-connection-invariants")
(include-book "owner-number-bound")
(include-book "served-catalog-owner-keyed")
(include-book "owner-canonical-state")
(include-book "owner-authority-proposal-state")
(include-book "owner-connection-state")
(include-book "owner-publication-transitions")
; The "Theory" warning check costs about 20 ms on every :in-theory hint in this world.
(local (set-inhibit-warnings "Theory"))

; Their declared guards are t; proof is against the exact imported bodies.
(verify-guards fn-orcp-swapped-owner)
(verify-guards fn-orcp-swapped-ocfg)







; Structural entry premise for the exact producer native binds as REBUILT.
; These are definitional guard bridges, not cited carry keystones and not
; permission to dispatch an arbitrary host-constructed REBUILT value raw.
(defthm fn-owner-orcp-rebuild-returns-true-list-by-definition
  (true-listp (fn-owner-orcp-rebuild rows configs frontier max-conns))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:type-prescription fn-owner-orcp-rebuild))))))

(defthm fn-owner-retain-statep-implies-reclaim-entry-guard-by-definition
  (implies (fn-owner-retain-statep state)
           (and (true-listp (fn-owner-orcp-rebuild rows configs frontier max-conns))
                (boundp-global 'fn-owner state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep
                  fn-owner-orcp-rebuild-returns-true-list-by-definition))))

(defun fn-owner-orcp-swap (rebuilt state)
  (declare (xargs :stobjs state :guard (and (true-listp rebuilt) (boundp-global 'fn-owner state))
                  :guard-hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-orcp-swap-base) (:definition fn-orcp-swapped-ocfg)
                              (:definition fn-orcp-swapped-owner)
                              (:definition fn-owner-authority-proposal-clear)
                              (:definition fn-scka-strip-base) (:definition fn-sco-at)
                              (:definition fn-sco-consumer) (:definition fn-sco-cpr)
                              (:definition fn-sco-identity) (:definition fn-sco-make)
                              (:definition fn-sco-records) (:definition fn-sco-topic)
                              (:definition global-table) (:definition not) (:definition nth)
                              (:definition put-global) (:definition state-p)
                              (:definition true-listp) (:definition update-global-table)
                              (:executable-counterpart cons) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-ocfg-config)
                              (:executable-counterpart fn-ocfg-owner)
                              (:executable-counterpart fn-own-store)
                              (:executable-counterpart fn-own-view)
                              (:executable-counterpart fn-sbud-used)
                              (:executable-counterpart fn-scka-strip-base)
                              (:executable-counterpart nfix) (:executable-counterpart nth)
                              (:executable-counterpart zp)
                              (:forward-chaining state-p-implies-and-forward-to-state-p1)
                              (:rewrite fn-ocfg-owner-of-fn-ocfg-make)
                              (:rewrite fn-ocl-set-conns-keeps-owner-control)
                              (:rewrite fn-own-store-of-fn-own-make)
                              (:rewrite fn-owner-canonical-reset-preserves-state-p1-by-definition)
                              (:rewrite fn-owner-installed-state-p1)
                              (:rewrite fn-owner-retain-carry-put-preserves-state-p1)
                              (:rewrite fn-pcar-records-count-is-sbud-used)
                              (:rewrite fn-sg-state-p1-of-put-global) (:rewrite nth-update-nth)
                              (:rewrite state-p-implies-and-forward-to-state-p1)
                              (:type-prescription boundp-global) (:type-prescription state-p)
                              (:type-prescription state-p1)))))))
  (let* ((e (nth 0 rebuilt))
         (oc (nth 1 rebuilt))
         (next (fn-orcp-swapped-ocfg (fn-owner-ocfg state) oc))
         (swapped (fn-ocfg-owner next))
         (state (f-put-global 'fn-owner-identity-grant nil state))
         (state (fn-owner-authority-proposal-clear state))
         (state (fn-owner-canonical-reset state))
         (state (fn-owner-install-ocfg next state))
         (count (fn-sf-records-count (fn-sn-files (fn-own-store swapped))))
         (state (fn-owner-retain-carry-put (nth 2 rebuilt) state))
         (state (f-put-global 'fn-owner-record-octets (nth 3 rebuilt) state))
         (state (f-put-global 'fn-owner-record-debt (nth 4 rebuilt) state))
         (state (f-put-global 'fn-owner-carried-usage (nth 5 rebuilt) state))
         ; The rebuilt base has no canonical H0. Reset durable/attempted to
         ; COUNT and release the slot; pending/requested/serial survive.
         (state (fn-ost-install-publication
                 (fn-opub-reclaim-install (fn-ost-publication state)
                                         (fn-scka-strip-base e) count) state))
         (state (fn-owner-put-credits (fn-orcp-release (fn-owner-credits state)) state)))
    (value count)))

(defthm fn-owner-orcp-swap-installs-retain-carry
  (equal (fn-owner-retain-carry (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (nth 2 rebuilt))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-orcp-swap fn-owner-put-credits fn-ost-install-publication mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-other-global-put)
            (theory 'minimal-theory)))))

(defthm fn-owner-orcp-swap-preserves-retain-carry-by-definition
  (implies (fn-prc-carryp (nth 2 rebuilt))
           (fn-prc-carryp (fn-owner-retain-carry
                          (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))))
  :hints (("Goal" :in-theory '(fn-owner-orcp-swap-installs-retain-carry))))

(local
 (defthm fn-orr-put-association
   (equal (assoc-equal key (nth 2 (put-global name value state)))
          (if (equal key name) (cons name value)
            (assoc-equal key (nth 2 state))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition global-table) (:definition put-global)
                              (:definition update-global-table) (:executable-counterpart equal)
                              (:executable-counterpart nfix) (:rewrite assoc-add-pair)
                              (:rewrite nth-update-nth)))))))

(local
 (defthm fn-orr-put-state-p1
   (implies (and (state-p1 state) (symbolp name)
                 (not (equal name 'current-acl2-world))
                 (not (equal name 'timer-alist))
                 (not (equal name 'print-base)))
            (state-p1 (put-global name value state)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition global-table) (:definition not)
                              (:definition put-global) (:definition update-global-table)
                              (:rewrite fn-sg-state-p1-of-put-global)
                              (:type-prescription state-p1)))))))

(local
 (defthm fn-orr-installed-open-ocfg
   (equal (fn-owner-ocfg (fn-owner-install-open-ocfg oc state)) oc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-owner-install-ocfg)
                              (:definition fn-owner-install-open-ocfg)
                              (:definition fn-owner-ocfg) (:definition get-global)
                              (:definition global-table) (:definition put-global)
                              (:definition update-global-table) (:executable-counterpart equal)
                              (:executable-counterpart nfix) (:rewrite assoc-add-pair)
                              (:rewrite cdr-cons) (:rewrite nth-update-nth)))))))

(local
 (defthm fn-orr-open-owner-association
   (equal (assoc-equal 'fn-owner (nth 2 (fn-owner-install-open-ocfg oc state)))
          (cons 'fn-owner oc))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-owner-install-ocfg)
                              (:definition fn-owner-install-open-ocfg)
                              (:definition global-table) (:definition put-global)
                              (:definition update-global-table) (:executable-counterpart equal)
                              (:executable-counterpart nfix) (:rewrite assoc-add-pair)
                              (:rewrite nth-update-nth)))))))

(local
 (defthm fn-orr-open-other-association
   (implies (not (equal key 'fn-owner))
            (equal (assoc-equal key (nth 2 (fn-owner-install-open-ocfg oc state)))
                   (assoc-equal key (nth 2 state))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-owner-install-ocfg)
                              (:definition fn-owner-install-open-ocfg)
                              (:definition global-table) (:definition not)
                              (:definition put-global) (:definition update-global-table)
                              (:executable-counterpart equal) (:executable-counterpart nfix)
                              (:rewrite assoc-add-pair) (:rewrite nth-update-nth)))))))

; The recovered Store carries typed event rows; the cold loader consumes
; those rows directly without reconstructing their representation.
(local
 (defthm fn-orr-record-listp-implies-values
   (implies (fn-sf-record-listp rows sequence lower frontier)
            (fn-sf-record-valuesp rows))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-sf-record-listp)
                              (:definition fn-sf-record-valuesp) (:executable-counterpart consp)
                              (:executable-counterpart fn-sf-record-valuesp)
                              (:forward-chaining fn-cfgc-record-list-is-true-list)
                              (:induction fn-sf-record-listp) (:induction fn-sf-record-valuesp)
                              (:type-prescription fn-sf-record-listp)
                              (:type-prescription fn-sf-record-valuesp)
                              (:type-prescription fn-store-event-p)))))))

(defun fn-owner-install-extended (oc extended key fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state)
                  :guard (or (equal oc :fault)
                             (not (fn-onb-open-okp (fn-ocfg-owner oc)))
                             (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                                  (fn-mpxt-keyp key)
                                  (equal (len key) *fn-mpxt-key-octets*)))
                  :guard-hints
                  (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition boundp-global) (:definition boundp-global1)
                              (:definition fn-onb-open-okp) (:definition fn-orc-job)
                              (:definition fn-orc-writer-enter)
                              (:definition fn-owner-authority-proposal-clear)
                              (:definition fn-scka-strip-base) (:definition fn-sco-at)
                              (:definition fn-sco-consumer) (:definition fn-sco-cpr)
                              (:definition fn-sco-identity) (:definition fn-sco-make)
                              (:definition fn-sco-records) (:definition fn-sco-topic)
                              (:definition fn-sf-record-phasep) (:definition fn-sf-statep)
                              (:definition fn-sn-statep) (:definition get-global)
                              (:definition global-table) (:definition member-equal)
                              (:definition natp) (:definition not) (:definition state-p)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart cons) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-fc-table-initial-state)
                              (:executable-counterpart if) (:executable-counterpart len)
                              (:executable-counterpart tau-system)
                              (:executable-counterpart true-listp)
                              (:forward-chaining fn-cfgc-record-list-is-true-list)
                              (:forward-chaining state-p-implies-and-forward-to-state-p1)
                              (:rewrite fn-gen-verdict-salt-is-32-bits)
                              (:rewrite fn-hist-p-is-true-listp)
                              (:rewrite fn-orr-installed-open-ocfg)
                              (:rewrite fn-orr-open-other-association)
                              (:rewrite fn-orr-open-owner-association)
                              (:rewrite fn-orr-put-association) (:rewrite fn-orr-put-state-p1)
                              (:rewrite fn-orr-record-listp-implies-values)
                              (:rewrite fn-owner-core-is-configured-owner-by-definition)
                              (:rewrite fn-owner-open-state-p1)
                              (:rewrite fn-owner-retain-carry-put-frames-global-association)
                              (:rewrite fn-owner-retain-carry-put-preserves-state-p1)
                              (:rewrite fn-sca-held-rowsp-of-record-values)
                              (:rewrite state-p-implies-and-forward-to-state-p1)
                              (:type-prescription fn-fc-table-initial-state)
                              (:type-prescription fn-mpxt-keyp)
                              (:type-prescription fn-sf-record-listp)
                              (:type-prescription state-p) (:type-prescription state-p1)))))))
  (cond
   ((equal oc :fault)
    (mv nil :fault fn-arena fn-cat fn-hist state))
   ; THE OPEN's number bound (books/owner-number-bound.lisp fn-onb-open-okp,
   ; KEYSTONE fn-onb-boundp-when-open-okp): a recovered owner whose
   ; watermarks pass RFC 3977 section 6's bound is a damaged Store, refused
   ; by name before anything is installed.  O(groups); the served path then
   ; carries the bound (fn-onb-boundp), never revalidating it.
   ((not (fn-onb-open-okp (fn-ocfg-owner oc)))
    (mv nil :article-numbers-damaged fn-arena fn-cat fn-hist state))
   (t
      (let* ((state (f-put-global 'fn-owner-identity-grant nil state))
         (state (fn-owner-authority-proposal-clear state))
         ; Cold reset occurs before physical recovery under lifecycle exclusion.
         ; Preserve the epoch captured by the issued recovery source.
             (state (fn-owner-install-open-ocfg oc state))
             ; PRF-289: the carried obligation-id trie for the ledger the
             ; owner opens with (books/post-retain-carried.lisp
             ; fn-prc-refresh of nil; fn-prc-carryp-of-refresh), so the
             ; first POST's refresh is a delta, not a build.
             (state (fn-owner-retain-carry-put
                     (fn-prc-refresh nil (fn-node-retention
                                          (fn-sn-node
                                           (fn-own-store (fn-owner-core state)))))
                     state))
             ; Rebuilt exclusively by successful FNFD scans after
             ; authoritative store recovery.  It is a carried
             ; incremental fold, never a whole-journal rescan on a
             ; served event.
             (state (f-put-global 'fn-owner-feed-intents nil state))
             (state (f-put-global 'fn-owner-feed-pending 0 state))
             ; The persisted profile is handed back by
             ; fn-owner-install-profile after every recovery; until
             ; then the budget is 0 and every publication is
             ; :unaffordable (books/store-budget.lisp).
             (state (f-put-global 'fn-owner-store-profile nil state))
             ; PRF-284: its carried verdict with it (fn-pvc-carryp-when-atom).
             (state (f-put-global 'fn-owner-profile-carry nil state))
             ; Socket-only reply framers are recreated after
             ; authoritative recovery; their durable counterpart is
             ; the FNFD replay above, not this retained input.
             (state (f-put-global 'fn-owner-feed-inputs
                                  (fn-fc-table-initial-state) state))
             ; Preserve the capture serial exactly as the old installer did.
             ; Install the stripped base; all other eight fields become nil.
             (state (fn-ost-install-publication
                     (fn-opub-install (fn-ost-publication state)
                                      (fn-scka-strip-base extended)) state))
             ; The pending PreparedCommit of the catalog (fn-owner-prepare-buffer).
             (state (f-put-global 'fn-owner-cat-pending nil state))
             ; E (step 8): the catalog of the installed store's history, from
             ; empty (books/served-catalog-owner.lisp fn-sca-load-held-rows).
             (store (fn-own-store (fn-ocfg-owner oc))))
        ; The records flip: the store's history is its ROWS, interned into
        ; the arena by the open; the catalog commits those rows and reads no
        ; byte and seals nothing (fn-sca-load-held-rows).
        ; THE SWITCH: under the ring's key (fn-sca-load-held-rows-keyed-is-
        ; load-held-rows: the same catalog, the table keyed).
        (let* ((state (fn-orc-writer-enter state))
               (fn-cat (fn-sca-load-held-rows-keyed key
                                                   (fn-sf-records (fn-sn-files store))
                                                   (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                                                   fn-arena fn-cat)))
          (let (; Stage 2b: the history stobj IS the installed store's history
              ; (KEYSTONE fn-hist-load-is-the-history,
              ; books/history-columns.lisp): R is established here, at every
              ; install, and the budget readers below sync it forward
              ; (fn-hist-sync-after-run-is-the-history).  The salt is the
              ; store's recorded one (format 10: the genesis the open read,
              ; books/store-genesis.lisp fn-gen-verdict-salt, 32 bits by
              ; fn-gen-verdict-salt-is-32-bits); it keys only the Message-ID
              ; buckets, which no reader here consults yet.
                (fn-hist (fn-hist-load (fn-sf-records (fn-sn-files store))
                                       (fn-gen-verdict-salt
                                        (and (boundp-global 'fn-store-genesis state)
                                             (f-get-global 'fn-store-genesis state)))
                                       fn-hist)))
            (let ((state (fn-orc-writer-leave state)))
              (mv nil :recovering fn-arena fn-cat fn-hist state))))))))

; The report writer's bracket (fn-orc-writer-enter/-leave, b9efc2afe) puts
; only the report globals: the owner, its binding and the retain carry
; pass through it.
(local
 (defthm fn-orr-writer-enter-frame
   (and (equal (fn-owner-retain-carry (fn-orc-writer-enter state))
               (fn-owner-retain-carry state))
        (equal (fn-owner-ocfg (fn-orc-writer-enter state)) (fn-owner-ocfg state))
        (equal (boundp-global 'fn-owner (fn-orc-writer-enter state))
               (boundp-global 'fn-owner state)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-orc-writer-enter) (:definition not)
                              (:rewrite fn-owner-bound-of-other-global-put)
                              (:rewrite fn-owner-ocfg-of-other-global-put)
                              (:rewrite fn-owner-retain-carry-of-other-global-put)))))))

(local
 (defthm fn-orr-writer-leave-frame
   (and (equal (fn-owner-retain-carry (fn-orc-writer-leave state))
               (fn-owner-retain-carry state))
        (equal (fn-owner-ocfg (fn-orc-writer-leave state)) (fn-owner-ocfg state))
        (equal (boundp-global 'fn-owner (fn-orc-writer-leave state))
               (boundp-global 'fn-owner state)))
   :hints (("Goal" :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(fn-orc-writer-leave fn-owner-retain-carry-of-other-global-put
               fn-owner-ocfg-of-other-global-put fn-owner-bound-of-other-global-put))))))

(defthm fn-owner-install-extended-establishes-retain-carry
  (implies (and (not (equal oc :fault))
                (fn-onb-open-okp (fn-ocfg-owner oc)))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 5 (fn-owner-install-extended
                        oc extended key fn-arena fn-cat fn-hist state)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-install-extended fn-ost-install-publication mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-other-global-put
              fn-orr-writer-enter-frame fn-orr-writer-leave-frame
              fn-prc-carryp-of-refresh (:executable-counterpart fn-prc-carryp))
            (theory 'minimal-theory)))))

(defthm fn-owner-install-extended-establishes-retain-state
  (implies (and (fn-onb-open-okp (fn-ocfg-owner oc))
                (fn-lgoc-invariantp oc))
           (fn-owner-retain-statep
            (mv-nth 5 (fn-owner-install-extended
                        oc extended key fn-arena fn-cat fn-hist state))))
  :hints (("Goal" :cases ((equal oc :fault)) :in-theory
           (union-theories
            '((:executable-counterpart fn-lgoc-invariantp)
              fn-owner-install-extended fn-ost-install-publication fn-owner-retain-statep
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-bound-of-other-global-put
              fn-owner-bound-of-retain-carry-put fn-owner-open-owner-bound
              fn-owner-ocfg-of-other-global-put
              fn-owner-ocfg-of-retain-carry-put fn-orr-installed-open-ocfg
              fn-owner-retain-carry-of-put
              fn-owner-retain-carry-of-other-global-put
              fn-orr-writer-enter-frame fn-orr-writer-leave-frame
              fn-prc-carryp-of-refresh (:executable-counterpart fn-prc-carryp))
            (theory 'minimal-theory)))))

; The exact recovery and key producers discharge the cold entry's literal
; guard. This implication is a guard bridge, not a separate keystone.
(defthm fn-owner-recovery-producers-imply-install-guard-by-definition
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns))
        (key (fn-mpxt-key-of-entry entry)))
    (or (equal oc :fault)
        (not (fn-onb-open-okp (fn-ocfg-owner oc)))
        (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
             (fn-mpxt-keyp key)
             (equal (len key) *fn-mpxt-key-octets*))))
  :rule-classes nil
  :hints (("Goal" :use (fn-ock-recover-installs-ocl-relation)
           :in-theory '(fn-ccar-ocl-relation-carries-sn-statep
                        fn-mpxt-key-of-entry-is-a-key))))

(in-theory (disable fn-owner-credit-reserve fn-owner-credits fn-owner-put-credits
                    fn-owner-orcp-swap fn-owner-install-extended))
