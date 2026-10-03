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
(include-book "owner-reclaim-pass")
(include-book "owner-number-bound")
(include-book "served-catalog-owner-keyed")
(include-book "heap-store-figure")
(include-book "owner-canonical-state")
(include-book "owner-authority-proposal-state")
(include-book "owner-connection-state")

; Their declared guards are t; proof is against the exact imported bodies.
(verify-guards fn-orcp-swapped-owner)
(verify-guards fn-orcp-swapped-ocfg)







; Structural entry premise for the exact producer native binds as REBUILT.
; These are definitional guard bridges, not cited carry keystones and not
; permission to dispatch an arbitrary host-constructed REBUILT value raw.
(defthm fn-owner-orcp-rebuild-returns-true-list-by-definition
  (true-listp (fn-owner-orcp-rebuild rows configs frontier max-conns))
  :hints (("Goal" :in-theory (enable fn-owner-orcp-rebuild))))

(defthm fn-owner-retain-statep-implies-reclaim-entry-guard-by-definition
  (implies (fn-owner-retain-statep fn-owner-st)
           (and (true-listp (fn-owner-orcp-rebuild rows configs frontier max-conns))
                (fn-owner-boundp fn-owner-st)))
  :hints (("Goal" :in-theory '(fn-owner-retain-statep
                  fn-owner-orcp-rebuild-returns-true-list-by-definition))))

(defun fn-owner-orcp-swap (rebuilt fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :guard (and (true-listp rebuilt) (fn-owner-boundp fn-owner-st))
                  :guard-hints (("Goal" :in-theory (disable boundp-global)))))
  (let* ((e (nth 0 rebuilt))
         (oc (nth 1 rebuilt))
         (next (fn-orcp-swapped-ocfg (fn-owner-ocfg fn-owner-st) oc))
         (swapped (fn-ocfg-owner next))
         (state (f-put-global 'fn-owner-identity-grant nil state))
         (state (fn-owner-authority-proposal-clear state))
         (state (fn-owner-canonical-reset state))
         (fn-owner-st (fn-owner-install-ocfg next fn-owner-st))
         (count (fn-sf-records-count (fn-sn-files (fn-own-store swapped))))
         (fn-owner-st (fn-owner-retain-carry-put (nth 2 rebuilt) fn-owner-st))
         (state (f-put-global 'fn-owner-record-octets (nth 3 rebuilt) state))
         (state (f-put-global 'fn-owner-record-debt (nth 4 rebuilt) state))
         (state (f-put-global 'fn-owner-carried-usage (nth 5 rebuilt) state))
         (state (f-put-global 'fn-owner-sco-base (fn-scka-strip-base e) state))
         ; No H0: the next publication is the whole capture of the canonical
         ; rows (fn-owner-sco-prepare's nil branch), the checkpoint an open
         ; of this history publishes.  The open notes the arena's count
         ; because its rows ARE canonical (interned from the emptied or the
         ; checkpoint's canonical arena); the rebuilt E's rows keep their
         ; live handles, so E is not the canonical capture the incremental
         ; path's base must be (fn-scka-next-checkpoint-is-capture) and no
         ; count makes it one.  The whole walk is the publication's own cost
         ; (fnn-checkpoint-walk walks every record either way).
         (state (f-put-global 'fn-owner-sco-base-payloads nil state))
         (state (f-put-global 'fn-owner-sco-durable count state))
         (state (f-put-global 'fn-owner-sco-attempted count state))
         (state (f-put-global 'fn-owner-sco-deferred nil state))
         (state (f-put-global 'fn-owner-sco-inflight nil state))
         (state (f-put-global 'fn-owner-orc-pass nil state))
         (state (fn-owner-put-credits (fn-orcp-release (fn-owner-credits state)) state)))
    (mv nil count fn-owner-st state)))

(defthm fn-owner-orcp-swap-installs-retain-carry
  (equal (fn-owner-retain-carry (mv-nth 2 (fn-owner-orcp-swap rebuilt fn-owner-st state)))
         (nth 2 rebuilt))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-orcp-swap fn-owner-put-credits mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              )
            (theory 'minimal-theory)))))

(defthm fn-owner-orcp-swap-preserves-retain-carry-by-definition
  (implies (fn-prc-carryp (nth 2 rebuilt))
           (fn-prc-carryp (fn-owner-retain-carry
                          (mv-nth 2 (fn-owner-orcp-swap rebuilt fn-owner-st state)))))
  :hints (("Goal" :in-theory '(fn-owner-orcp-swap-installs-retain-carry))))

(local
 (defthm fn-orr-put-association
   (equal (assoc-equal key (nth 2 (put-global name value state)))
          (if (equal key name) (cons name value)
            (assoc-equal key (nth 2 state))))
   :hints (("Goal" :in-theory (enable put-global)))))

(local
 (defthm fn-orr-put-state-p1
   (implies (and (state-p1 state) (symbolp name)
                 (not (equal name 'current-acl2-world))
                 (not (equal name 'timer-alist))
                 (not (equal name 'print-base)))
            (state-p1 (put-global name value state)))
   :hints (("Goal" :in-theory (enable put-global)))))




; The recovered Store carries typed event rows; the cold loader consumes
; those rows directly without reconstructing their representation.
(local
 (defthm fn-orr-record-listp-implies-values
   (implies (fn-sf-record-listp rows sequence lower frontier)
            (fn-sf-record-valuesp rows))
   :hints (("Goal" :in-theory (enable fn-sf-record-listp fn-sf-record-valuesp)))))

(defun fn-owner-install-extended (oc extended key fn-arena fn-cat fn-hist fn-owner-st state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist fn-owner-st state)
                  :guard (or (equal oc :fault)
                             (not (fn-onb-open-okp (fn-ocfg-owner oc)))
                             (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                                  (fn-mpxt-keyp key)
                                  (equal (len key) *fn-mpxt-key-octets*)))
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-sn-statep fn-sf-statep)
                         (put-global fn-sf-phasep fn-owner-install-open-ocfg
                          fn-owner-retain-carry-put fn-prc-refresh
                          fn-gen-verdict-salt))))))
  (cond
   ((equal oc :fault)
    (mv nil :fault fn-arena fn-cat fn-hist fn-owner-st state))
   ; THE OPEN's number bound (books/owner-number-bound.lisp fn-onb-open-okp,
   ; KEYSTONE fn-onb-boundp-when-open-okp): a recovered owner whose
   ; watermarks pass RFC 3977 section 6's bound is a damaged Store, refused
   ; by name before anything is installed.  O(groups); the served path then
   ; carries the bound (fn-onb-boundp), never revalidating it.
   ((not (fn-onb-open-okp (fn-ocfg-owner oc)))
    (mv nil :article-numbers-damaged fn-arena fn-cat fn-hist fn-owner-st state))
   (t
      (let* ((state (f-put-global 'fn-owner-identity-grant nil state))
         (state (fn-owner-authority-proposal-clear state))
         ; Cold reset occurs before physical recovery under lifecycle exclusion.
         ; Preserve the epoch captured by the issued recovery source.
             (fn-owner-st (fn-owner-install-open-ocfg oc fn-owner-st))
             ; PRF-289: the carried obligation-id trie for the ledger the
             ; owner opens with (books/post-retain-carried.lisp
             ; fn-prc-refresh of nil; fn-prc-carryp-of-refresh), so the
             ; first POST's refresh is a delta, not a build.
             (fn-owner-st (fn-owner-retain-carry-put
                     (fn-prc-refresh nil (fn-node-retention
                                          (fn-sn-node
                                           (fn-own-store (fn-owner-core fn-owner-st)))))
                     fn-owner-st))
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
             ; The owner's checkpoint state: the capture it extends at its
             ; next publication, the newest durable checkpoint's S (set by
             ; fn-owner-sco-note-durable), and the count of the last attempt.
             ; (kept stripped of its event index, rebuilt at the next
             ; publication: fn-scka-restore-base-of-strip-of-capture)
             (state (f-put-global 'fn-owner-sco-base (fn-scka-strip-base extended) state))
             ; The base's canonical payload count (the arena's count at the
             ; open: fn-owner-sco-note-base-payloads), nil until noted.
             (state (f-put-global 'fn-owner-sco-base-payloads nil state))
             (state (f-put-global 'fn-owner-sco-durable nil state))
             (state (f-put-global 'fn-owner-sco-attempted nil state))
             ; PKT-492: the publication the owner deferred by name, or nil.
             (state (f-put-global 'fn-owner-sco-deferred nil state))
             ; PKT-583 (b): the count the publication in flight captured, or
             ; nil; and the one coalesced request observed while it ran.
             (state (f-put-global 'fn-owner-sco-inflight nil state))
             (state (f-put-global 'fn-owner-sco-pending nil state))
             ; PKT-868: an operator's standing compaction request
             ; (fn-owner-sco-request), cleared by the capture it causes.
             (state (f-put-global 'fn-owner-sco-requested nil state))
             ; Q16: no reclaim pass in flight (fn-owner-orc-pass).
             (state (f-put-global 'fn-owner-orc-pass nil state))
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
              (mv nil :recovering fn-arena fn-cat fn-hist fn-owner-st state))))))))

; The report writer's bracket (fn-orc-writer-enter/-leave, b9efc2afe) puts
; only report globals of STATE; the owner's carrier passes through it by the
; stobj discipline (it takes no FN-OWNER-ST).


(defthm fn-owner-install-extended-establishes-retain-carry
  (implies (and (not (equal oc :fault))
                (fn-onb-open-okp (fn-ocfg-owner oc)))
           (fn-prc-carryp
            (fn-owner-retain-carry
             (mv-nth 5 (fn-owner-install-extended
                        oc extended key fn-arena fn-cat fn-hist fn-owner-st state)))))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-install-extended mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-retain-carry-of-put
              fn-prc-carryp-of-refresh (:executable-counterpart fn-prc-carryp))
            (theory 'minimal-theory)))))

(defthm fn-owner-install-extended-establishes-retain-state
  (implies (and (fn-onb-open-okp (fn-ocfg-owner oc))
                (fn-lgoc-invariantp oc))
           (fn-owner-retain-statep
            (mv-nth 5 (fn-owner-install-extended
                        oc extended key fn-arena fn-cat fn-hist fn-owner-st state))))
  :hints (("Goal" :cases ((equal oc :fault)) :in-theory
           (union-theories
            '((:executable-counterpart fn-lgoc-invariantp)
              fn-owner-install-extended fn-owner-retain-statep
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              fn-owner-bound-of-retain-carry-put fn-owner-open-owner-bound
              fn-owner-ocfg-of-retain-carry-put fn-owner-open-ocfg-effect
              fn-owner-retain-carry-of-put
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
