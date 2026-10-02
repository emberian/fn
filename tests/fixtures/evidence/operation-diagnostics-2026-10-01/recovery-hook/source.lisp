(defun fn-owner-install-extended (oc extended key fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state)
                  :guard (or (equal oc :fault)
                             (not (fn-onb-open-okp (fn-ocfg-owner oc)))
                             (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                                  (fn-mpxt-keyp key)
                                  (equal (len key) *fn-mpxt-key-octets*)))
                  :guard-hints
                  (("Goal" :in-theory
                    (e/d (fn-sn-statep fn-sf-statep fn-rov-oc-ledger)
                         (put-global fn-sf-phasep fn-owner-install-open-ocfg
                          fn-owner-retain-carry-put fn-prc-refresh
                          fn-gen-verdict-salt))))))
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
              (mv nil :recovering fn-arena fn-cat fn-hist state))))))))
