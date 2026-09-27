; Experimental owner bridge: :program wrappers over the proved fn-own machine.
;
; tools/run_owner.py drives one owner per store through these entry points.
; Every wrapper is one proved owner transition: fn-own-step, fn-opc-prepare,
; or fn-own-read (the served port: one
; socket read is one fn-served-step over the connection's pinned archive,
; fn-own-read-is-served-step-on-pinned-prefix) or one fn-own-open, over the
; global `fn-owner`; the host never rebuilds owner, store, wire or session
; state itself.  The wire framing state lives inside the owner's connection
; record, so there is no per-connection host state at all.  Marshaling
; reuses host/store-host.lisp (decimal octets in, symbols and naturals out);
; the reply stream and the close verdict are the book's two projections of an
; effect list (fn-served-reply-octets, fn-served-closingp), installed in the
; globals `fn-owner-output` and `fn-owner-closep`.
; The served POST path: a read that injected an article leaves its
; submission queued inside the owner (fn-own-read); fn-owner-take is the
; writer step (fn-own-take-submission) and exposes the submission in flight
; (its connection, Message-ID, octets and groups, all produced by
; books/injection.lisp); the host carries it through the same store events
; tools/run_store.py `post' reports and feeds the word it observed to
; fn-owner-outcome (fn-own-outcome), which renders the 240 or 441 for that
; connection alone.  The submission flag is the third projection of an
; effect list, `fn-owner-submittedp' (fn-served-submission).  The host never
; writes a reply octet.
(in-package "ACL2")
; books/owner-fault includes books/owner and adds the host-fault transition
; `fn-own-fault'.  The host needs it: `fn-owner-fault' below is the only way
; tools/run_owner.py can abandon ONE connection, and before it existed an
; exception in the serve loop ended the process for every connection.
(include-book "../books/owner-config")
; P3 owner open and publication (fn-ock-).
(include-book "../books/owner-checkpoint-open")
; The publication through the octet buffer, decided before it is encoded
; (fn-ock-publication-stream, fn-ock-capture-budget, fn-ock-publication-blockedp;
; PKT-492, PKT-315).
(include-book "../books/owner-checkpoint-pipeline")
; D25: the duplicate-versus-conflict decision keys on the poster's bytes.
(include-book "../books/poster-bytes")
(include-book "../books/config-owner-live")
(include-book "../books/config-owner-publish")
; PRF-274: the live completion from the owner's carried node (fn-oclc-publish).
(include-book "../books/config-owner-carried")
(include-book "../books/config-owner-live-authorize")
(include-book "../books/owner-tls-prefix")
(include-book "../books/owner-config-observe")
(include-book "../books/owner-served-carried")
(include-book "../books/owner-commit-carried")
(include-book "../books/owner-refresh-indexed")
(include-book "../books/owner-bound-commit")
(include-book "../books/owner-log-reopen")
(include-book "../books/owner-prepare-carried")
; PRF-191: a POST's Message-ID tests through the owner's view trie
; (fn-pidx-existing-action, fn-pidx-sbud-prepare).
(include-book "../books/post-identity-index")
; The retention admission of a POST through a carried obligation-id trie
; (fn-prc-refresh, fn-prc-sbud-prepare; fn-owner-prepare-buffer).
(include-book "../books/post-retain-carried")
;; lane prepare-served: the served decision inside the prepares the host calls
;; (fn-psrv-prepare, fn-psrv-refusal-kind, fn-psrv-prepare-identity,
;; fn-psrv-prepare-topic) and the configuration un-stage (fn-psrv-unstage).
(include-book "../books/owner-prepare-served")
; Stage 2b (lane history-columns-2): the store's history as the column stobj
; fn-hist (books/history-columns.lisp), loaded at every install and synced
; before each carried budget read (books/history-columns-store.lisp).
(include-book "../books/history-columns-store")
; PRF-180: the per-POST caches (their EXTEND specifications).
(include-book "../books/store-carried-folds")
(include-book "../books/owner-log-route")
(include-book "../books/owner-advance-carried")
(include-book "../books/owner-intent-carried")
; The POST's article parsed once at take (fn-apc-; fn-owner-parse-carry).
(include-book "../books/owner-parse-carried")
(include-book "../books/owner-identity-intern")
(include-book "../books/owner-identity-served")
;; host-decisions-2 (packet A): every owner prepare, the reservation refusal,
;; the known abort, :begin and :declare-group answer their own word
;; (fn-pout-); the host relays it.
(include-book "../books/owner-prepare-outcome")
(include-book "../books/owner-commit-ocl")
(include-book "../books/owner-served-invariants")
(include-book "../books/owner-feed-port")
; Step 8 (catalog slice): the served read over the catalog and the catalog at
; the owner's entries (books/served-catalog-chain, books/served-catalog-owner).
(include-book "../books/served-catalog-owner")
(include-book "../books/owner-prepare-correspondence")
; The transaction budget: `fn-owner-prepare' installs `fn-sbud-prepare'.
(include-book "../books/owner-store-budget")
(include-book "../books/store-budget-article")
; PKT-169: the maintenance reservation (the served gates below).
(include-book "../books/store-maintenance-reserve")
(include-book "../books/store-capacity-vector")
; PRF-284: the profile's admission decided once at open and carried
; (fn-pvc-make; fn-pvc-article-budget-carried, fn-pvc-verdict-carried,
; fn-pvc-post-boundary-carried).
(include-book "../books/store-profile-carried")
(include-book "../books/checkpoint-auxiliary")
(include-book "../books/feed-wire-input")
(include-book "../books/feed-connection")
(include-book "../books/feed-connection-invariants")
; The injecting agent (the path-identity policy, fn-oag-post-config) and the
; service log lines (fn-olog-*): both ACL2's, read here and nowhere computed.
(include-book "../books/owner-agent")
(include-book "../books/owner-log")
; PKT-657, PKT-575: the moderation and withdrawal verbs' decision.
(include-book "../books/moderation-verbs")
(include-book "../books/owner-results")
; The served article bound installed with the profile (PKT-103).
(include-book "../books/owner-served-bound")
(include-book "../books/topic-history-local-proposals")
;; This file names what it calls, so every loader gets the same world: the
;; native images (host/native/build.lisp) and the Python owner bridge
;; (tools/bridge_image.py OWNER_FORMS), which boots from this file alone.
;; fn-owner-io calls fn-rcon-ocfg-io; fn-owner-prepare-buffer reads the
;; fn-octets buffer and calls fn-pidx-existing-action, whose comparison is
;; books/store-reclaim-buffer's fn-rclb-same-articlep (D13, STO-014).
(include-book "../books/records-concrete-owner")
(include-book "../books/octets-stobj")
(include-book "../books/store-reclaim-buffer")
; HST-023 (PRF-248): the served step's typed result and render plan.
(include-book "../books/served-plan")
; The FNFD feed trailer.  `tools/run_owner.py' used to run its own
; `hashlib.sha256' over the protected prefix of every feed frame; the owner's
; ACL2 session does not load `host/store-host.lisp', so the one owner has to
; be a book both sessions include.  See books/frame-trailer.lisp.
(include-book "../books/feed-journal")
(include-book "../books/peer-pull")
(include-book "../books/peer-pull-session")
; PRF-325: catching up from a peer (the XFNCATCHUP requester).
(include-book "../books/peer-catchup")
(include-book "../books/consumer-owner-local")
(include-book "../books/consumer-bound")
(include-book "../books/consumer-wait")
;; PKT-710: the page and the wait step over it.
(include-book "../books/consumer-withdrawal")
(include-book "../books/acceptance-payload-ref")
(include-book "../books/owner-feed-article")
(include-book "../books/hybrid-lifecycle")
(include-book "../books/peer-authored-accept")
(include-book "../books/key-statements")
; Lane ack-before-barrier: a statement's commit is fenced before its cut and
; its executor (fn-oab-fence-before-change).
(include-book "../books/owner-ack-after-barrier")
(include-book "../books/login-binding")
(include-book "../books/login-binding-live")
; PRF-161: the limits of a public reader port (fn-exp-).
(include-book "../books/public-exposure")
; fn-exp-observe-effects: the observation without building the reply.
(include-book "../books/public-exposure-reply")
; PKT-605 (PRF-223): the connection budget the run installs and every live
; reconfiguration keeps (fn-owner-connection-budget, fn-owner-reconfigure-deltas).
(include-book "../books/connection-budget")
; PRF-192: the served reply as a range of the octet buffer (fn-served-reply-to-buffer;
; since HST-023 the host renders the step's plan off the mutex instead).
(include-book "../books/served-reply-buffer")
(include-book "../books/owner-open-carried")
; PKT-828: a reader quantum during a batch's barrier runs at the reader view
; (fn-owner-at-reader-view, fn-ocfg-with-view; fn-ocv-capture); the span read
; there, the working view put back, is fn-orr-read-span, whose keystone
; fn-orr-read-span-at-a-captured-view-restores-the-owner restates the relation
; after it (books/owner-reader-read.lisp).
(include-book "../books/owner-reader-view")
; Lane time-model (PRF-311): the barrier's deadline and the shed POST;
; lane time-model-2: the decision journal (books/owner-time-journal.lisp,
; PRF-322) and the 440 at the POST command (books/owner-time-admission.lisp,
; PRF-323).
(include-book "../books/owner-time-journal")
(include-book "../books/owner-time-admission")
(include-book "../books/owner-reader-read")
; PRF-099: the opaque-carriage budget and the refusal classes.
(include-book "../books/peer-carriage")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-node-host.lisp (and host/store-host.lisp under it) defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-node-host.lisp" :ld-error-action :error)

; The posting configuration: the groups served at the live configuration
; generation, the node's own <path-identity> from the ONE slot that holds it
; (the configuration policy `path-identity', which `fn-peer-local-identity'
; and `fn-store-prov-post' also read), and the store's payload bound.  ACL2
; derives all of it (books/owner-agent.lisp fn-oag-post-config, whose agent
; is the path-identity by fn-oag-post-config-agent-is-the-path-identity);
; this wrapper only supplies the payload bound: the record codec's payload
; field (`*fn-record-max-payload*', books/records-shape), which bounds every
; profile's (`fn-sbud-payload-bound-within-record-codec').  The wire limit is
; fixed before the profile is handed over; the POST boundary applies the
; profile's own bound (`fn-owner-post-boundary').
(defun fn-owner-post-config (cfg)
  (declare (xargs :mode :program))
  (fn-oag-post-config cfg *fn-record-max-payload*))

(defun fn-owner-ocfg (state)
  ; Internal, single-valued accessor for host wrappers.
  (declare (xargs :stobjs state :mode :program))
  (f-get-global 'fn-owner state))

(defun fn-owner-ocfg-state (state)
  ; External ACL2 bridge accessor.  `value' is intentionally only at this
  ; boundary; host functions use fn-owner-ocfg above as a single value.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-ocfg state)))

; `fn-owner' has one canonical value: the configured owner.  These are the
; only host accessors for its raw owner component.  A wrapper that changes
; connection membership must use fn-owner-step's fn-ocfg transition; a core
; operation which preserves membership may use fn-owner-replace-core.
(defun fn-owner-core (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-ocfg-owner (f-get-global 'fn-owner state)))

;; A live owner's administrative publication (PKT-837): the authorization
;; from the owner's carried state, books/config-owner-live-authorize.lisp
;; fn-olau-authorize -- the candidate is the one record applied to the
;; carried node and configuration, no Store record read and no history
;; replayed.  Under the owner's invariant, at :ready, with the observed
;; configuration history the carried one and the record at the frontier, it
;; EQUALS fn-cvec-native-admin-authorize over the carried rows and frontier,
;; the replaying decision it replaced (KEYSTONE
;; fn-olau-authorize-is-the-replayed-authorization).  Called from
;; host/native/admin.lisp fnn-admin-authorize-owner, after
;; fn-owner-reconfigure-authorizedp (PRF-287) answered for the staged record.
(defun fn-owner-cfg-native-admin-authorize
    (config-octet-records record-octets lock-owned observed-name-octets profile state)
  (declare (xargs :stobjs state :mode :program
                  :guard (and (fn-cbor-octet-listp record-octets)
                              (fn-octet-list-listp config-octet-records)
                              (fn-octet-list-listp observed-name-octets))))
  (let* ((config-records (fn-store-cfg-decode-records config-octet-records))
         (parsed (fn-cfg-decode-exact record-octets))
         (names (fn-store-octet-lists->strings observed-name-octets)))
    (value
     (if (or (equal config-records :bad) (null config-records)
             (equal names :bad) (not (fn-record-parse-okp parsed)))
         (fn-native-admin-publication-result :refused :decode nil nil nil)
       (fn-olau-authorize (fn-owner-ocfg state) config-records
                          (fn-record-parse-value parsed) lock-owned names profile)))))

(defun fn-owner-clock-observation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-clock (fn-owner-core state))))

(defun fn-owner-stamp-status (state)
  ; The native submission boundary asks ACL2 whether this owner's current
  ; observation can become a schema-1 stamp.  An accepted observation may
  ; still have no wall or exceed the record's uint32 seconds bound.
  (declare (xargs :stobjs state :mode :program))
  (value (if (natp (fn-record-stamp-of-observation
                    (fn-own-clock (fn-owner-core state))))
             :usable :clock-unusable)))

(defun fn-owner-config (state)
  ; The one live configuration.  No host global shadows this value: every
  ; caller reads the generation replayed into and published by fn-ocfg.
  (declare (xargs :stobjs state :mode :program))
  (fn-ocfg-config (fn-owner-ocfg state)))

;; The injection configuration the owner has installed (fn-own-config): the
;; one served POST and control submission read, whose bound is the store
;; profile's A with its header limits (`fn-owner-posting-configure',
;; `fn-owner-served-post-bound').  host/native/hybrid-control.lisp
;; `fnn-hybrid-control-author' injects the signed carrier under it, so a
;; carrier past A is the injection's :oversize, answered
;; ARTICLE-EXCEEDS-PROFILE-BOUND (books/native-hybrid-control.lisp
;; fn-nhc-author-refusal), as for `operator post'.  Before 2026-09-27 this
;; was `fn-owner-post-config' at the codec's payload bound, so the carrier
;; passed injection and the owner's admission refused it with no name
;; (PKT-codex-003's native case).
(defun fn-owner-live-post-config (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-config (fn-owner-core state))))

(defun fn-owner-install-ocfg (oc state)
  (declare (xargs :stobjs state :mode :program))
  (f-put-global 'fn-owner oc state))

(defun fn-owner-replace-core (owner state)
  (declare (xargs :stobjs state :mode :program))
  (let ((oc (f-get-global 'fn-owner state)))
    (fn-owner-install-ocfg (fn-ocfg-with-owner oc owner) state)))

(defun fn-owner-state (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-core state)))

;; SEC-006 (PRF-210): the node's key ring the native host read from
;; STORE/keys/ (host/native/owner.lisp fnn-owner-load-node-secret: the
;; current entry, then each retained older epoch), installed into the
;; configured owner after the open and after every recovery.  ACL2 decides
;; whether the entries are a ring (fn-ns-ringp: every entry well formed,
;; epochs strictly decreasing); the owner then carries it through every step.
(defun fn-owner-install-node-secret (ring state)
  (declare (xargs :stobjs state :mode :program))
  (if (fn-ns-ringp ring)
      (let ((state (fn-owner-replace-core
                    (fn-own-with-node-secret (fn-owner-core state) ring)
                    state)))
        (value :installed))
    (value :refused)))

(defun fn-owner-node-secret-width (state)
  (declare (xargs :stobjs state :mode :program))
  (value *fn-ns-secret-octets*))

; The served read's install (fn-owner-chunk, the bridge's list read): every
; projection `fn-owner-install-effects' makes EXCEPT the reply octets, which
; are never built as a list here: `fn-owner-output' is NIL and the reply is
; the effects' (the native host renders the step's plan off the mutex,
; fn-owner-chunk-span and books/served-plan.lisp, HST-023; before it the
; octet buffer of PRF-192, books/served-reply-buffer.lisp).
(defun fn-owner-install-served-effects (effects state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-effects effects state))
         (state (f-put-global 'fn-owner-output nil state))
         (state (f-put-global 'fn-owner-closep (fn-served-closingp effects) state))
         ; RFC 4642 section 2.2.2: the host owes a TLS handshake.  The book
         ; decided it (fn-auth-starttls, books/nntp-auth.lisp); this reads
         ; its answer off the effect list, exactly as the close is read.
         (state (f-put-global 'fn-owner-starttlsp
                              (if (fn-served-starttlsp effects) t nil) state))
         (state (f-put-global 'fn-owner-submittedp
                              (if (fn-served-submission effects) t nil) state)))
    state))

(defun fn-owner-install-effects (effects state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (fn-owner-install-served-effects effects state)))
    (f-put-global 'fn-owner-output (fn-served-reply-octets effects) state)))


;; The process root (P3 owner open, books/owner-checkpoint-open.lisp).  Both
;; paths extend a checkpoint over the records after it (`fn-sco-extend') and
;; install from the extended value with `fn-ock-recover-extended'
;; (fn-owner-recover-extended below).  From a verified checkpoint
;; (fn-owner-recover-from-checkpoint) the records are the suffix after S; on
;; a full replay (fn-owner-recover-rows) the checkpoint is the capture of the
;; empty prefix and the records are the whole history.  The keystone
;; fn-owner-recover-from-checkpoint-equals-full-recover says both install the
;; owner of the full open, the composition
;; fn-orec-recover-installs-ocl-relation is stated over, and
;; fn-ock-recover-installs-ocl-relation carries its two premises of the
;; carried served keystones to what is installed here.  The extended value is
;; the capture of the whole history; the owner keeps it as the base of its
;; next publication (`fn-owner-sco-base').
(defun fn-owner-install-extended (oc extended fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program))
  (if (equal oc :fault)
        (mv nil :fault fn-arena fn-cat fn-hist state)
      (let* ((state (fn-owner-install-ocfg oc state))
             ; PRF-289: the carried obligation-id trie for the ledger the
             ; owner opens with (books/post-retain-carried.lisp
             ; fn-prc-refresh of nil; fn-prc-carryp-of-refresh), so the
             ; first POST's refresh is a delta, not a build.
             (state (f-put-global
                     'fn-owner-retain-carry
                     (fn-prc-refresh nil (fn-node-retention
                                          (fn-sn-node
                                           (fn-own-store (fn-owner-core state)))))
                     state))
             ; Rebuilt exclusively by successful FNFD scans after
             ; authoritative store recovery.  It is a carried
             ; incremental fold, never a whole-journal rescan on a
             ; served event.
             (state (f-put-global 'fn-owner-feed-intents nil state))
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
             ; The pending PreparedCommit of the catalog (fn-owner-prepare-buffer).
             (state (f-put-global 'fn-owner-cat-pending nil state))
             ; E (step 8): the catalog of the installed store's history, from
             ; empty (books/served-catalog-owner.lisp fn-sca-load-held-rows).
             (store (fn-own-store (fn-ocfg-owner oc))))
        ; The records flip: the store's history is its ROWS, interned into
        ; the arena by the open; the catalog commits those rows and reads no
        ; byte and seals nothing (fn-sca-load-held-rows).
        (let ((fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files store))
                                             (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                                             fn-arena fn-cat)))
          (let (; Stage 2b: the history stobj IS the installed store's history
              ; (KEYSTONE fn-hist-load-is-the-history,
              ; books/history-columns.lisp): R is established here, at every
              ; install, and the budget readers below sync it forward
              ; (fn-hist-sync-after-run-is-the-history).  The salt keys only
              ; the Message-ID buckets, which no reader here consults yet.
                (fn-hist (fn-hist-load (fn-sf-records (fn-sn-files store)) 0 fn-hist)))
            (mv nil :recovering fn-arena fn-cat fn-hist state))))))

(defun fn-owner-recover-extended (extended config-records frontier max-conns fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program))
  (fn-owner-install-extended
   (fn-ock-recover-extended extended config-records frontier max-conns)
   extended fn-arena fn-cat fn-hist state))

; The owner from the Store open this process just ran
; (fn-store-sn-open-extended, host/store-node-host.lisp): its extended
; checkpoint E and (fn-sco-store-open E ...) = (REPLAYED OPENED), kept in the
; global `fn-store-sco-open'.  fn-ock-install over that pair is
; fn-ock-recover-extended of E (fn-ock-install-of-store-open-by-definition),
; so the keystone fn-owner-recover-from-checkpoint-equals-full-recover and
; fn-ock-recover-installs-ocl-relation hold of what is installed here, on
; both paths, with no second extension or finalization.
(defun fn-owner-recover-from-store-open (max-conns fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program))
  (let ((opened (and (boundp-global 'fn-store-sco-open state)
                     (f-get-global 'fn-store-sco-open state))))
    (if (not (and (consp opened) (consp (cdr opened)) (consp (cddr opened))))
        (mv nil :fault fn-arena fn-cat fn-hist state)
      (let ((state (f-put-global 'fn-store-sco-open nil state)))
        (fn-owner-install-extended
         (fn-ock-install (cadr opened) (caddr opened) max-conns)
         (car opened) fn-arena fn-cat fn-hist state)))))

; The two recoveries below are the Python bridge's (tools/run_owner.py), whose
; served path is fn-owner-chunk over the view's lists and reads no catalog:
; the catalog the install loads is a local one, dropped; the arena is the
; live one the open interned into (the native owner recovers through
; fn-owner-recover-from-store-open over the live stobjs).
(defun fn-owner-recover-extended-arena (extended config-records frontier max-conns fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  (with-local-stobj fn-cat
    (mv-let (erp val fn-arena fn-cat fn-hist state)
      (fn-owner-recover-extended extended config-records frontier max-conns
                                 fn-arena fn-cat fn-hist state)
      (mv erp val fn-arena fn-hist state))))

;; The records flip: both opens intern the decoded journal into the arena
;; first, so the extended capture is over ROWS.  The bridge (tools/run_owner.py
;; recover) decodes with fn-store-sn-recover-records, empties the arena and
;; interns with the guard-verified fn-intern-events at top level, then calls
;; this entry over the rows and the live arena (the install reads it; the
;; catalog it loads is a local one, fn-owner-recover-extended-arena).  The
;; native owner installs from the Store open instead
;; (fn-owner-recover-from-store-open).  (mv nil KEYWORD fn-arena state).
(defun fn-owner-recover-rows (rows frontier config-octet-records max-conns fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  (let ((config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal rows :bad) (equal config-records :bad))
        (mv nil :fault fn-arena fn-hist state)
      (fn-owner-recover-extended-arena
       (fn-rii-sco-extend (fn-sco-capture config-records nil) config-records rows)
       config-records frontier max-conns fn-arena fn-hist state))))

; The open from the checkpoint the Store open loaded (`fn-store-sco-checkpoint',
; host/store-node-host.lisp) over the ROWS of the records after it, which the
; caller interned ON TOP of the loaded arena (fn-intern-events records nil 0:
; host/native/io.lisp fnn-recover-suffix-rows); the entry reads no arena.
; books/store-checkpoint-arena.lisp fn-scka-recover-from-checkpoint-is-full-
; recover: the extension is the full recover's.  (mv nil KEYWORD fn-arena state).
(defun fn-owner-recover-from-checkpoint (rows frontier config-octet-records max-conns fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  (let ((checkpoint (fn-store-sco-current state))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (null checkpoint) (equal rows :bad) (equal config-records :bad))
        (mv nil :fault fn-arena fn-hist state)
      (fn-owner-recover-extended-arena
       (fn-rii-sco-extend checkpoint config-records rows)
       config-records frontier max-conns fn-arena fn-hist state))))

(defun fn-owner-store (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-own-store (fn-owner-core state)))

; The Store's persisted profile, carried from open.  VALUES is what
; `fn-bs-config-decode' returned for the store's metadata file (the host
; decoded nothing: host/native/io.lisp `fnn-metadata-config-decode' asked
; ACL2); anything that is not one of the named profiles is refused and the
; budget stays 0.  The profile is never changed while the owner runs:
; books/store-budget.lisp says why it is fixed at init.
; The served article bound is installed here too, on every run path
; (books/owner-served-bound.lisp fn-osb-install-serves-the-profile-bound): the
; developer `owner run' never reaches fn-owner-posting-configure, and served
; its connections with the codec ceiling recovery installed.
(defun fn-owner-install-profile (values state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (verdict next)
    (fn-osb-install (fn-owner-core state) values)
    (if (equal verdict :installed)
        (let* ((state (fn-owner-replace-core next state))
               (state (f-put-global 'fn-owner-store-profile values state))
               ; PRF-284: the profile's admission, decided once here
               ; (fn-pvc-carryp-of-make); see fn-owner-profile-carry.
               (state (f-put-global 'fn-owner-profile-carry
                                    (fn-pvc-make values) state))
               ; PRF-180: the committed record octets, the completion debt
               ; and the carried usage are folded once here, over the Store
               ; this open replayed (valid caches: fn-sbud-full-cache-is-valid,
               ; fn-cvec-full-debt-cache-is-valid, fn-pcb-full-cache-is-valid);
               ; every later query advances them from the history
               ; stobj (fn-owner-record-octets, fn-owner-record-debt,
               ; fn-owner-carried-usage).
               (s (fn-owner-store state))
               (records (fn-sf-records (fn-sn-files s)))
               ; the count: fn-sf-records-count-is-used-by-definition
               (count (fn-sf-records-count (fn-sn-files s)))
               (state (f-put-global 'fn-owner-record-octets
                                    (cons count (fn-sbud-bytes-used s))
                                    state))
               (state (f-put-global 'fn-owner-record-debt
                                    (cons count (fn-cvec-record-debt records))
                                    state))
               (state (f-put-global 'fn-owner-carried-usage
                                    (cons count (fn-pcb-tally-records records nil))
                                    state)))
          (value :installed))
      (value :refused))))

(defun fn-owner-store-profile (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-store-profile state)
      (f-get-global 'fn-owner-store-profile state)
    nil))

; The carried verdict of the profile (books/store-profile-carried.lisp).
; Its writers are fn-owner-install-profile (fn-pvc-make of the profile it
; installs, fn-pvc-carryp-of-make) and the recovery reset (nil,
; fn-pvc-carryp-when-atom), so it always satisfies fn-pvc-carryp; the
; recognizer names no owner state, so no owner step can falsify it.  A
; reader uses the verdict only for the profile the carry names (the same
; object as fn-owner-store-profile's, so the EQUAL is an EQ).
(defun fn-owner-profile-carry (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-profile-carry state)
      (f-get-global 'fn-owner-profile-carry state)
    nil))

; The carried profile's article bound A and group bound G, for the control
; socket's read bound (host/native/control.lisp `fnn-control-start').  Both
; are 0 before a profile is installed, and the read bound is then the
; command-frame bound: no article is accepted without a profile anyway.
(defun fn-owner-control-profile-bounds (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((profile (fn-owner-store-profile state)))
    (value (list (nfix (fn-sbud-payload-bound profile))
                 (nfix (fn-sbud-group-bound profile))))))

; The served posting bound: the profile's article octets and its header
; limits (fields 15 to 17, PRF-230), read from the opened profile; the host
; computes nothing (ACL2's `fn-inj-post-bound', read back by
; `fn-inj-make-config-full').  A store with no admitted profile keeps the
; codec ceiling and the default header limits, as before.
(defun fn-owner-served-post-bound (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((profile (fn-owner-store-profile state))
         (bound (fn-sbud-payload-bound profile)))
    (if (and (posp bound) (fn-bs-profile-admittedp profile))
        (fn-inj-post-bound bound (fn-bs-profile-header-limits profile))
      (if (posp bound) bound *fn-record-max-payload*))))


;; The owner's publication (books/owner-checkpoint-open.lisp).  These read
;; the owner and write only the four fn-owner-sco-* globals: the served
;; owner `fn-owner' is never written here.

(defun fn-owner-sco-global (name state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global name state) (f-get-global name state) nil))

; The committed record count: the snoc-list's carried count, which is
; `fn-sbud-used' by definition (books/history-columns-store.lisp
; fn-sf-records-count-is-used-by-definition), not a len of the history and
; not a read of the store node's event index.
(defun fn-owner-sco-count (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-sf-records-count (fn-sn-files (fn-own-store (fn-owner-core state)))))

; The newest durable checkpoint the Store open verified: its S, or NIL.
(defun fn-owner-sco-note-durable (sequence state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-sco-durable (and (natp sequence) sequence)
                             state)))
    (value :noted)))

; The base's canonical payload count after the Store open: the arena's
; count the host read (host/native/owner.lisp fnn-owner-recover-core).  Both
; opens intern at the canonical handles from the emptied arena (the full
; recover) or from the checkpoint's canonical arena (fn-scka-load), so the
; arena holds exactly the canonical payloads of the opened history, which is
; the base's (fn-scka-next-checkpoint-is-capture's H0).
(defun fn-owner-sco-note-base-payloads (count state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-sco-base-payloads (and (natp count) count) state)))
    (value :noted)))

; The publication the owner deferred by name, (:deferred REASON ESTIMATE
; BUDGET) as fn-ock-publication-stream answered it, or nil; the status
; report carries it (host/native-live-status-host.lisp).
(defun fn-owner-sco-deferred (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-owner-sco-global 'fn-owner-sco-deferred state))

; The checkpoint budget the publication is decided against: the profile's
; (fn-ock-capture-budget, books/owner-checkpoint-pipeline.lisp), or, on a
; developer image only, the natural the host read from
; FN_NATIVE_CHECKPOINT_BUDGET_TEST (host/native/io.lisp
; fnn-checkpoint-budget-test-override; nil otherwise), so the due path and
; the publication see one budget.
(defun fn-owner-sco-budget (override profile)
  (declare (xargs :mode :program))
  (if (natp override) override (fn-ock-capture-budget profile)))

;; :due, :idle, :blocked or :inflight, by fn-ock-publication-next
;; (books/owner-checkpoint-open.lisp, PKT-583 (b)): the rule
;; fn-ock-publication-duep under the profile's K at the newest committed
;; frontier, never while a deferred publication is blocked
;; (fn-ock-publication-blockedp, books/owner-checkpoint-pipeline.lisp: the
;; checkpoint budget is still below the estimate the deferral named; PKT-492),
;; and never while one is in flight: a due observation then is the ONE
;; coalesced request, recorded here (fn-owner-sco-pending) and answered
;; :inflight, so the host starts nothing; a decision made with nothing in
;; flight clears the request (it was decided from the newest frontier).
;; FREE: the free octets of the store's filesystem the host observed by
;; statvfs (or nil); a space deferral stays blocked while the space is still
;; below the estimate it named (fn-ock-publication-blockedp, both reasons).
(defun fn-owner-sco-due (override free state)
  (declare (xargs :stobjs state :mode :program))
  (let ((profile (fn-owner-store-profile state)))
    (if (not profile)
        (value :idle)
      (let ((next (fn-ock-publication-next
                   (fn-owner-sco-global 'fn-owner-sco-durable state)
                   (fn-owner-sco-count state)
                   (fn-bs-profile-max-open-suffix profile)
                   (fn-owner-sco-global 'fn-owner-sco-attempted state)
                   (fn-owner-sco-global 'fn-owner-sco-inflight state)
                   (fn-ock-publication-blockedp
                    (fn-owner-sco-deferred state)
                    (fn-owner-sco-budget override profile)
                    (fn-ockp-space free)))))
        (cond ((eq next :coalesce)
               (let ((state (f-put-global 'fn-owner-sco-pending t state)))
                 (value :inflight)))
              ((eq next :inflight) (value :inflight))
              (t (let ((state (f-put-global 'fn-owner-sco-pending nil state)))
                   (value next))))))))

; The one coalesced request, for the status report: t while a due
; observation waits for the publication in flight to finish.
(defun fn-owner-sco-pending (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-owner-sco-global 'fn-owner-sco-pending state))

; The publication in three steps (checkpoint-cost): the capture under the
; owner mutex, the encoding outside it, the result back under it.
;
; fn-owner-sco-capture (under the mutex): the values the publication reads,
; (BASE CONFIGS RECORDS SEGMENT COUNT SUFFIX BUDGET), and the attempt is
; recorded at COUNT.  They are ACL2 values; a later commit makes new ones and
; changes none of these.  BUDGET is the checkpoint budget (fn-owner-sco-budget:
; the profile's, the file bound the open refuses a checkpoint past).
; The capture is O(1) under the mutex: the base, the configuration
; history and the record list are handed by pointer (a later commit makes
; new ones); FRONTIER is the store's frontier txid at the capture (the F
; row), FREE the free octets the host observed, REVISION the writer's
; source revision (a string the host read; the F row carries it).
(defun fn-owner-sco-capture (override free revision state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((st (fn-own-store (fn-owner-core state)))
         (records (fn-sf-records (fn-sn-files st)))
         ; (len records), the snoc-list's carried count:
         ; fn-sf-records-count-is-used-by-definition.
         (count (fn-sf-records-count (fn-sn-files st)))
         (durable (fn-owner-sco-global 'fn-owner-sco-durable state))
         (profile (fn-owner-store-profile state))
         (state (f-put-global 'fn-owner-sco-attempted count state))
         ; the publication in flight, bound to the count it captures
         (state (f-put-global 'fn-owner-sco-inflight count state)))
    (value (list (fn-owner-sco-global 'fn-owner-sco-base state)
                 (fn-sn-config-history st)
                 records
                 (fn-bs-profile-max-record-octets profile)
                 count
                 (- count (if (natp durable) durable 0))
                 (fn-owner-sco-budget override profile)
                 (fn-sf-frontier (fn-sn-files st))
                 free
                 revision
                 (fn-owner-sco-global 'fn-owner-sco-base-payloads state)))))

; Off the mutex, over the values captured above and the live arena, READ
; only (host/native/owner.lisp fnn-owner-publish-captured): NEXT, the capture
; of the captured rows' canonical rows (books/store-checkpoint-arena-writer.lisp
; fn-scka-next-checkpoint: BASE extended over the canonical rows of the rows
; after it, handles from H0; KEYSTONE fn-scka-next-checkpoint-is-capture;
; the whole capture when no H0 was noted), then the setup of the arena run
; from WALKED, the host's bounded fn-scka-srcs-n calls over RECORDS (ROWS'
; LACC SACC: each canonical payload's length and source, reversed;
; fn-scka-srcs-n-compose, fn-scka-srcs-n-complete), by fn-scka-lens-setup,
; and of the file (fn-scka-publication-setup: the
; decision by name over the whole file's octets before anything is
; allocated).  LOG is the record log's position at the capture's S (a
; format-9 owner rotated the log there; NIL otherwise): the F row carries it.
; (list SETUP NEXT N ARUN), N the canonical payload count (the
; next base's H0), ARUN (N COUNT STATE0) for fnn-checkpoint-write-steps.
; The arena is read at handles below the count the capture saw: the owner
; thread only appends to it (a seal never moves a sealed payload's bytes),
; so what is read is what was sealed before the capture.
(defun fn-owner-sco-prepare (base h0 configs records frontier revision log seg budget free
                                  walked fn-arena)
  (declare (xargs :stobjs fn-arena :mode :program))
  (let* ((next0 (and base (natp h0) (<= (len (fn-sco-records base)) (len records))
                     (fn-scka-next-checkpoint (fn-scka-restore-base base) h0 configs records
                                              fn-arena)))
         (next (if (or (null next0) (equal next0 :bad))
                   (let ((canon (fn-scka-canon-rows records fn-arena 0)))
                     (if (equal canon :bad) :bad (fn-sco-capture configs canon)))
                 next0)))
    (if (or (equal next :bad) (not (and (consp walked) (atom (nth 0 walked)))))
        (list (list :unencodable nil nil nil nil 0 0) nil 0 nil)
      (let* ((ws (fn-scka-lens-setup (reverse (nth 1 walked)) seg))
             (setup (fn-scka-publication-setup next frontier revision log seg budget free
                                               (nth 3 ws))))
        (list setup next (nth 0 ws)
              (list (nth 0 ws) (nth 2 ws)
                    (fn-scka-initial-state (reverse (nth 2 walked)) (nth 1 ws) 0)))))))

; Outside the mutex, the host calls `fn-ock-next-checkpoint' (NEXT, the
; capture of the captured history: fn-ock-next-checkpoint-is-the-capture),
; then `fn-ockp-setup' (books/owner-checkpoint-pipeline.lisp: the tables of
; NEXT, the estimate, the decision by name before any allocation) and loops
; on `fn-ockp-step' over the publication buffer, writing each step's
; frames.  None of them reads or writes a global.

; fn-owner-sco-publication-done (under the mutex): NEXT becomes the base,
; whether or not the write succeeded (it is the capture of a prefix of the
; owner's history either way), on a durable write its S is the newest
; durable checkpoint, and a deferred VERDICT is carried (for the due path
; and the status report) until a later verdict replaces it.  Answers S, or
; :none.
(defun fn-owner-sco-publication-done (next payloads durablep verdict state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-sco-base (fn-scka-strip-base next) state))
         ; NEXT's canonical payload count, the next publication's H0
         (state (f-put-global 'fn-owner-sco-base-payloads (and (natp payloads) payloads)
                              state))
         ; nothing in flight; the durable S below is NEXT's sequence, the
         ; count the capture was handed (fn-ock-finish-binds-the-captured-
         ; prefix), never the count now
         (state (f-put-global 'fn-owner-sco-inflight nil state))
         (state (if durablep
                    (f-put-global 'fn-owner-sco-durable (fn-sco-sequence next) state)
                  state))
         (state (f-put-global 'fn-owner-sco-deferred
                              (if (and (consp verdict) (eq (car verdict) :deferred))
                                  verdict
                                nil)
                              state)))
    (value (if durablep (fn-sco-sequence next) :none))))

; The served POST bound (D27): the carried Store profile's payload bound
; (`fn-sbud-payload-bound', books/store-budget-naming, which never exceeds the
; record codec's payload ceiling: `fn-sbud-payload-bound-within-record-codec'),
; so the wire reads at most what the operator's profile admits.  Before a
; profile is installed (recovery, where nothing is served and the budget is 0)
; it is the codec ceiling `*fn-record-max-payload*'.
;
; Native operator startup supplies the one posting-policy bit after recovery
; and after `fn-owner-install-profile'.  Preserve the agent, served groups,
; reader listing (PRF-195) and closed groups (PRF-196) ACL2 already installed
; and set the served bound from the profile; this
; changes the same fn-own-config value read by served POST and control.
(defun fn-owner-posting-configure (allow state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (cfg (fn-own-config owner))
         (next (fn-inj-make-config-full (and allow t)
                                        (fn-inj-config-agent cfg)
                                        (fn-inj-config-groups cfg)
                                        (fn-owner-served-post-bound state)
                                        (fn-inj-config-listing cfg)
                                        ;; O2: keep the closed groups.
                                        (fn-inj-config-closed cfg))))
    (if (not (fn-inj-configp next))
        (value :refused)
      (let ((state (fn-owner-replace-core (fn-own-configure owner next) state)))
        (value :configured)))))

; The committed record octets of the carried Store, from the carried
; (K . SUM) of the first K records advanced over the records committed since
; through the history stobj fn-hist (stage 2b, books/history-columns-store.lisp):
; first `fn-hist-sync' appends the rows committed since the last sync (R is
; established at install by fn-hist-load-is-the-history and preserved by
; fn-hist-sync-after-run-is-the-history), then `fn-hist-bytes-carried' reads
; one row per record committed since the last query, never a walk of the
; history (fn-hist-bytes-carried-is-bytes-extend: under R it is
; `fn-sbud-bytes-extend', which is `fn-sbud-bytes-used' for a valid cache,
; fn-sbud-bytes-used-is-kernel-sum).  The cache is the fold at open
; (`fn-owner-install-profile') and stays valid while committed records only
; grow (`fn-sbud-octets-cache-valid-after-commit'); the count stored with it
; is the stobj's (fn-hist-count-is-used).
(defun fn-owner-record-octets (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let* ((s (fn-owner-store state))
         (fn-hist (fn-hist-sync (fn-sn-files s) fn-hist))
         (cache (if (boundp-global 'fn-owner-record-octets state)
                    (f-get-global 'fn-owner-record-octets state)
                  nil))
         (bytes (fn-hist-bytes-carried cache s fn-hist))
         (state (f-put-global 'fn-owner-record-octets
                              (cons (fn-hist-count fn-hist) bytes) state)))
    (mv bytes fn-hist state)))

; The completion debt of the carried Store (the open forward undertakings,
; each owing a release record), carried as (K . DEBT) and advanced over the
; records committed since through the synced history stobj
; (`fn-hist-debt-carried', fn-hist-debt-carried-is-debt-extend under R; the
; extension is `fn-cvec-record-debt' when the cache is valid,
; fn-cvec-debt-extend-is-the-record-debt), reset with the octets when a
; profile is installed at open.
(defun fn-owner-record-debt (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let* ((s (fn-owner-store state))
         (fn-hist (fn-hist-sync (fn-sn-files s) fn-hist))
         (cache (if (boundp-global 'fn-owner-record-debt state)
                    (f-get-global 'fn-owner-record-debt state)
                  nil))
         (debt (fn-hist-debt-carried cache s fn-hist))
         (state (f-put-global 'fn-owner-record-debt
                              (cons (fn-hist-count fn-hist) debt) state)))
    (mv debt fn-hist state)))

; The owner's verdict on one more record of KIND: the carried profile's count
; and history gates against the Store it carries, and the capacity vector
; (books/store-capacity-vector.lisp `fn-cvec-verdict-at': a release
; discharges a debt or consumes the maintenance release, every other kind
; keeps room for every open undertaking's release, its own included, and the
; maintenance release, `fn-cvec-admission-keeps-the-vector').
(defun fn-owner-publication-verdict (kind fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (mv-let (bytes fn-hist state) (fn-owner-record-octets fn-hist state)
    (mv-let (debt fn-hist state) (fn-owner-record-debt fn-hist state)
      (let ((s (fn-owner-store state)))
        ; the count: fn-sf-records-count-is-used-by-definition.
        ; PRF-284: fn-pvc-verdict-carried-is-cvec-verdict-at.
        (mv nil (fn-pvc-verdict-carried (fn-owner-profile-carry state)
                                       (fn-owner-store-profile state) kind
                                       (fn-sf-records-count (fn-sn-files s)) bytes debt)
               fn-hist state)))))

; The identity preflight's verdict on one ACL2-constructed EVENT (lane
; bp-retention-leftovers).  Its kind is the WIRE event's
; (`fn-wire-event-kind'; the row reading `fn-store-event-kind' answered NIL
; for a wire composite, so the preflight charged a composite nothing); an
; accepted-statement composite is charged its figure, the kind's ceiling
; plus 320 per group its article is filed in
; (`fn-pvc-statement-verdict-carried-is-cvec-statement-verdict-at',
; `fn-oii-publication-group-count-is-the-rows'); any other kind as before.
(defun fn-owner-identity-publication-verdict (event fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let ((kind (fn-wire-event-kind event)))
    (if (not (equal kind :accepted-statement))
        (fn-owner-publication-verdict kind fn-hist state)
      (mv-let (bytes fn-hist state) (fn-owner-record-octets fn-hist state)
        (mv-let (debt fn-hist state) (fn-owner-record-debt fn-hist state)
          (let ((s (fn-owner-store state)))
            (mv nil (fn-pvc-statement-verdict-carried
                     (fn-owner-profile-carry state)
                     (fn-owner-store-profile state)
                     (fn-sf-records-count (fn-sn-files s)) bytes
                     (fn-oii-publication-group-count event) debt)
                fn-hist state)))))))

; The carried profile as the operator reads it (field names and values).
(defun fn-owner-profile-report (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bs-profile-report (fn-owner-store-profile state))))

(defun fn-owner-node (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-sn-node (fn-owner-store state)))

(defun fn-owner-step (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((state (fn-owner-install-ocfg
                (fn-ocfg-step (fn-owner-ocfg state) event fn-arena) state)))
    state))

; The live control path is deliberately small for this packet: a configured
; client asks to create or retire one group.  ACL2 constructs the delta
; (`fn-ocl-request-deltas', books/config-owner-publish.lisp), checks the
; pinned generation and staged/clock/reservation conditions, and produces the
; exact record that the host persists.  Python carries only the kind/name
; request and the resulting octets.

(defun fn-owner-reconfigure-deltas-admitted (id deltas fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let* ((oc (fn-owner-ocfg state))
         (reason (fn-ocfg-reconfig-refusal oc id deltas))
         (state (fn-owner-step (list :reconfigure id deltas) fn-arena state))
         (staged (fn-ocfg-staged (fn-owner-ocfg state))))
    ; A ConfigResult (books/owner-results.lisp): :staged with exactly one
    ; encoded configuration record, or :refused with ACL2's named reason
    ; (fn-ores-config-staged-result-by-definition).
    (value (fn-ores-config-staged-result staged reason))))

;; PKT-605 (PRF-223): the bound the run installed (fn-owner-connection-budget)
;; is kept by every live reconfiguration: a delta list whose configuration
;; holds more connections than the machine does is refused by name,
;; :connections-exceed-memory, before the owner stages anything
;; (books/connection-budget.lisp fn-cbud-deltas-refusal-keeps-the-capacity-held).
;; Every live path reaches this function (native-admin, peer-invite, auth).
(defun fn-owner-connection-bound (state)
  (declare (xargs :stobjs state :mode :program))
  (and (boundp-global 'fn-owner-connection-bound state)
       (f-get-global 'fn-owner-connection-bound state)))

(defun fn-owner-reconfigure-deltas (id deltas fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let* ((oc (fn-owner-ocfg state))
         (memory (fn-cbud-deltas-refusal
                  (fn-cfg-value (fn-ocfg-config oc))
                  (+ 1 (fn-cfg-generation (fn-ocfg-config oc)))
                  (fn-own-clock (fn-ocfg-owner oc))
                  deltas (fn-owner-connection-bound state))))
    ;; The refusal is the staging step's result value (PRF-208,
    ;; adapter-retirement: books/owner-results.lisp fn-ores-config-refused),
    ;; which every live caller's recognizer accepts.
    (if memory
        (value (fn-ores-config-refused memory))
      (fn-owner-reconfigure-deltas-admitted id deltas fn-arena state))))

(defun fn-owner-connection-budget (machine dynamic core threads stack nursery profile
                                           tlsp state)
  ; Once per run, after recovery and before listen (host/native/mux.lisp
  ; fnn-mux-budget-install, from fnn-owner-run).  MACHINE, DYNAMIC (the
  ; dynamic space this process has), CORE, THREADS and STACK are the host's
  ; observations; NURSERY its collection trigger;
  ; PROFILE the store's; TLSP whether a TLS context is loaded.  The capacity
  ; is the live configuration's.
  (declare (xargs :stobjs state :mode :program))
  (let* ((capacity (fn-exp-connections-capacity (fn-cfg-value (fn-owner-config state))))
         (article (fn-bs-profile-max-article-octets profile))
         (hneed (fn-heap-figure-octets profile core nursery))
         (d (fn-cbud-run-decide capacity machine dynamic hneed core threads stack
                                 article tlsp))
         (state (f-put-global 'fn-owner-connection-bound
                              (and (equal (car d) :hold) (fn-cbud-held-bound d))
                              state))
         (state (f-put-global 'fn-owner-connection-budget-line
                              (fn-record-string-octets
                               (if (equal (car d) :hold)
                                   (fn-cbud-hold-line d article tlsp)
                                 (fn-cbud-run-refusal-line d article tlsp machine dynamic
                                                           hneed core threads stack)))
                              state)))
    (value (car d))))

(defun fn-owner-reconfigure (id kind name-octets fn-arena state)
  ; Answers a ConfigResult: :staged with exactly one encoded configuration
  ; record, or :refused with the named ACL2 refusal reason.  No state is
  ; published until fn-owner-reconfigure-complete follows a durable write.
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((name (if (fn-pfld-group-name-requestp name-octets)
                  (fn-store-octets->string name-octets) :bad)))
    (if (equal name :bad)
        (value (fn-ores-config-refused :group-name))
      (let ((deltas (fn-ocl-request-deltas kind name)))
        (if (null deltas)
            (value (fn-ores-config-refused :delta-kind))
          (fn-owner-reconfigure-deltas id deltas fn-arena state))))))

(defun fn-owner-reconfigure-complete (generation state)
  ; This is called only after Store.write_config_record has named the record
  ; durable. An uncertain write has no call here and forces recovery.  The
  ; whole completion is ACL2's `fn-oclc-publish' (books/config-owner-carried):
  ; the refusal, the Store domain/capacity and carried physical history in one
  ; owner transition, the posting configuration of the published generation,
  ; and the verdict.  On :refused and :recovery-required its owner is the one
  ; installed now, so the host installs it unconditionally and decides nothing.
  ; It applies the one record to the owner's carried node and configuration
  ; instead of replaying the whole history three times (PKT-827: 2.9 s at
  ; 1,000 articles, past 10 s at 10,000); under the owner's invariant it is
  ; `fn-ocl-publish' (fn-oclc-publish-is-publish, PRF-274), which carries the
  ; invariant to the next completion (fn-oclc-publish-carries-ocl-relation).
  (declare (xargs :stobjs state :mode :program))
  (mv-let (verdict next)
    (fn-oclc-publish (fn-owner-ocfg state) generation
                     (fn-owner-served-post-bound state))
    (let ((state (fn-owner-install-ocfg next state)))
      (value verdict))))

;; PKT-827 (b), PRF-287: the live request's authorization from the owner's
;; carried state, asked after staging and before publication
;; (host/native/admin.lisp fnn-owner-live-reconfigure-locked).  ACL2's
;; fn-oclc-live-authorizep: the staged record applies to the carried node and
;; configuration; an authorized record's completion is :durable
;; (fn-oclc-live-authorizep-is-durable-completion) and under the owner's
;; invariant the history reopens to the state it installs
;; (fn-oclc-authorized-record-reopens).  It reads no record.
(defun fn-owner-reconfigure-authorizedp (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-oclc-live-authorizep (fn-owner-ocfg state))))

;; lane prepare-served: a live request refused BEFORE its record was written
;; (the authorization above, the candidate open, or the immutable publisher's
;; :refused; host/native/admin.lisp fnn-owner-live-reconfigure-locked) drops
;; the staged record, ACL2's fn-psrv-unstage (KEYSTONE
;; fn-psrv-unstage-preserves-invariant).  Before it the staged record stayed:
;; the configuration lock held and :begin/:take refused every POST until a
;; restart.  Answers :unstaged, or :none when nothing was staged.
(defun fn-owner-reconfigure-unstage (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-ocfg state))
         (state (fn-owner-install-ocfg (fn-psrv-unstage before) state)))
    (value (if (fn-ocfg-staged before) :unstaged :none))))

(defun fn-owner-config-generation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-generation (fn-owner-config state))))

(defun fn-owner-config-served (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-cnode-served-of (fn-owner-config state)))))

; -----------------------------------------------------------------------------
; The transaction path: the same observations run_store.py reports, each one
; a (:store ...) owner event.

;; The call is fn-rcon-ocfg-io (books/records-concrete-owner.lisp), equal to
;; fn-ocfg-step of (:store (:io operation result)) for every configured owner
;; (fn-rcon-ocfg-io-is-ocfg-step, no hypothesis): its :record-directory arm
;; pairs the staged record's sequence and transaction id through the
;; concrete record dispatchers instead of fn-record-p's octet lists.
;; On a format-9 store the member's reservation and its place in the log are
;; the two composite steps of books/owner-log-route.lisp (fn-olr-ocfg-reserve,
;; fn-olr-ocfg-order: the file route's success sequences, by definition).
(defun fn-owner-io (operation result state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((oc (fn-owner-ocfg state))
         (state (fn-owner-install-ocfg
                 (case operation
                   (:log-reserve (fn-olr-ocfg-reserve oc))
                   (:log-order (fn-olr-ocfg-order oc))
                   (t (fn-rcon-ocfg-io oc operation result)))
                 state)))
    (value (fn-sf-phase (fn-sn-files (fn-owner-store state))))))

; The parse carry fn-owner-take wrote (books/owner-parse-carried.lisp): each
; reader below is its reference under fn-apc-p, whatever octets it is given.
(defun fn-owner-parse-carry (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-parse-carry state)
      (f-get-global 'fn-owner-parse-carry state)
    nil))

;; Lane commit-onto-log: the owner as it is now, a value (the commit quantum
;; keeps it before each member's outcome, and renders from it only when the
;; batch's barrier fails).
(defun fn-owner-snapshot (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-core state)))

;; The reply a member's connection gets for the word :uncertain, rendered
;; from OWNER, the owner before the member's outcome was fed: the effects of
;; the served outcome (fn-acar-own-outcome, as fn-owner-outcome feeds it) or
;; of the transit outcome (fn-own-transit-outcome, as fn-owner-transit-outcome
;; feeds it) for that word, as fn-owner-install-effects renders them.  No
;; state changes: the batch failed and the owner stops.
(defun fn-owner-uncertain-reply-of (owner id transitp kind reason)
  (declare (xargs :mode :program))
  (fn-served-reply-octets
   (car (if transitp
            (fn-own-transit-outcome owner id kind reason :uncertain)
          (fn-acar-own-outcome owner id :uncertain)))))

;; The operator's bounds on one log batch, from the live configuration.
(defun fn-owner-log-bounds (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-olr-bounds (fn-owner-config state))))

;; Lane time-model (PRF-311): the barrier's deadline from the live
;; configuration, the `barrier-deadline-ms' limit row read like the batch
;; bounds (books/owner-log-route.lisp fn-olr-bmax), ACL2's default when the
;; row is absent (books/owner-time-model.lisp fn-otm-deadline-of-limit).
(defun fn-owner-barrier-deadline (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-otm-deadline-of-limit
          (fn-cfg-limit (fn-cfg-value (fn-owner-config state)) "barrier-deadline-ms"))))

;; Lane time-model-2: the three disk rows, (D H C) as the operator set them
;; (`policy set barrier-deadline-ms|barrier-stall-ms|clock-event-ms N'); the
;; barrier's :issue event normalizes them (fn-otm-limits: defaults for
;; absent rows, H at least D).
(defun fn-owner-barrier-limits (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((v (fn-cfg-value (fn-owner-config state))))
    (value (fn-otm-limits (list (fn-cfg-limit v "barrier-deadline-ms")
                                (fn-cfg-limit v "barrier-stall-ms")
                                (fn-cfg-limit v "clock-event-ms"))))))

;; Whether the oldest queued submission is a served POST's (not a control
;; submission, not a peer transit): the only kind a slow disk sheds.
(defun fn-owner-queue-head-served-p (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((q (fn-own-queue (fn-owner-core state))))
    (value (and (consp q)
                (not (fn-own-transit-subp (car q)))
                (not (fn-own-control-submissionp (car q)))
                t))))

;; The carried obligation-id trie (books/post-retain-carried.lisp): the
;; global's writers are fn-owner-install-extended (every recovery: the
;; refresh of nil, so the first POST pays no build), fn-owner-prepare-buffer
;; and fn-owner-prepare, which store fn-prc-refresh of the value read here;
;; so it always satisfies fn-prc-carryp (fn-prc-carryp-of-refresh; nil by
;; fn-prc-carryp-when-atom).  The recognizer names no owner state, so no
;; owner step between two POSTs can falsify it.
(defun fn-owner-retain-carry (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-retain-carry state)
      (f-get-global 'fn-owner-retain-carry state)
    nil))

; THE OWNER'S POST ENTRY (records-flip).  The duplicate test is the Store's
; entry over the arena (fn-store-existing-action, KEYSTONE
; fn-store-existing-action-is-the-verdict-over-alpha); the budget is sized on
; the WIRE record the POST builds (its journal frame); the record staged is
; the ROW fn-intern-row-at interns at the arena's count under the Store's
; keyring and generation (books/store-intern.lisp; fn-cat-intern-list-is-row-
; at-count), and the payload is sealed into the arena exactly when the Store
; changed, as fn-store-prepare-interned does (its KEYSTONES
; -refusal-keeps-the-arena and -acceptance-seals-one-payload are about that
; shape; the owner's prepare is fn-pcar-sbud-prepare over the row in place of
; fn-sn-prepare).  (mv nil KEYWORD fn-arena state).
(defun fn-owner-prepare (msgid-octets payload group-codes id-octets
                          subject-octets evidence-octets charge fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    ; The fields' checks are ACL2's (books/post-fields.lisp
    ; fn-pfld-article-inputsp): the Message-ID grammar, the codec's payload
    ; ceiling, the resolved groups, the record's metadata domain, the charge.
    (if (or (not (fn-octet-listp payload))
            (not (fn-pfld-article-inputsp msgid-octets (len payload) groups
                                          id-octets subject-octets
                                          evidence-octets charge)))
        (mv nil :invalid fn-arena fn-hist state)
      ; A name in the domain but not served at the live generation (a retired
      ; group) is refused by the prepare itself (fn-psrv-prepare, lane
      ; prepare-served): the host makes no served test of its own.
      (let* ((msgid (fn-store-octets->string msgid-octets))
             (existing (fn-store-existing-action msgid payload groups s fn-arena)))
        (if existing
            (mv nil existing fn-arena fn-hist state)
          (mv-let (bytes fn-hist state) (fn-owner-record-octets fn-hist state)
          (mv-let (debt fn-hist state) (fn-owner-record-debt fn-hist state)
          (let* ((record (fn-sn-article-record
                          s (fn-own-clock (fn-owner-core state))
                          msgid payload groups
                          (fn-store-octets->string id-octets)
                          (fn-store-octets->string subject-octets)
                          (fn-store-octets->string evidence-octets)
                          charge))
                 ; fn-opc-prepare is equal to the former fn-ocfg-step event
                 ; under fn-own-relation, established by observed recovery
                 ; and preserved by every live owner transition.
                 ; The budget gate is part of the prepare: at or over the
                 ; carried profile's budget fn-sbud-prepare is the identity
                 ; (fn-sbud-prepare-refuses-at-budget) and the word is
                 ; :unaffordable; below it, it is fn-opc-prepare.
                 ; The call is fn-pcar-sbud-prepare
                 ; (books/owner-prepare-carried.lisp), equal to
                 ; fn-sbud-prepare with no hypothesis
                 ; (fn-pcar-sbud-prepare-is-sbud-prepare): its candidate
                 ; test reads the last record's txid instead of folding
                 ; every record's through fn-record-p.
                 ; Packet 1: the history gate at the article's own figure
                 ; (books/store-budget-article.lisp), and PRF-138: 0 unless
                 ; the capacity vector (a release per open undertaking and
                 ; the maintenance release) still holds after the article
                 ; (books/store-capacity-vector.lisp
                 ; `fn-cvec-prepare-keeps-the-vector').
                 ; PRF-284: fn-pvc-article-budget-carried-is-cvec-
                 ; article-budget-for (the carry satisfies fn-pvc-carryp).
                 (budget (fn-pvc-article-budget-carried
                          (fn-owner-profile-carry state)
                          (fn-owner-store-profile state)
                          (fn-sf-records-count (fn-sn-files s))
                          bytes record debt))
                 (before (fn-owner-ocfg state))
                 (row (if (equal record :clock-unusable)
                          nil
                        ; fn-apc-intern-row-at-is-reference: the row's
                        ; held context reads the take's parse.
                        (fn-apc-intern-row-at record (fn-sn-keyring s)
                                              (fn-sn-keyring-generation s)
                                              (fn-arena-count fn-arena)
                                              (fn-owner-parse-carry state))))
                 (carry (fn-prc-refresh (fn-owner-retain-carry state)
                                        (fn-node-retention (fn-sn-node s))))
                 ; fn-pout-prepare-article (books/owner-prepare-outcome.lisp):
                 ; fn-psrv-prepare (the served test, then fn-prc-sbud-prepare,
                 ; as the buffer entry below) and its word, :prepared when it
                 ; staged the row, else fn-psrv-refusal-kind (KEYSTONE
                 ; fn-pout-prepare-article-answers-the-store-change).
                 (outcome (if (equal record :clock-unusable)
                              nil
                            (mv-let (word next)
                              (fn-pout-prepare-article before row budget carry)
                              ; Lane membership-budget: an :unaffordable
                              ; that the membership charge alone caused is
                              ; :memberships (books/store-capacity-vector.lisp
                              ; KEYSTONE fn-cvec-article-refusal-word-names-
                              ; the-memberships), over the same count, octets,
                              ; record and debt the budget was decided from.
                              (cons (fn-cvec-article-refusal-word
                                     word (fn-owner-store-profile state)
                                     (fn-sbud-count s) bytes record debt)
                                    next))))
                 (state (if (equal record :clock-unusable)
                            state
                          (let ((state (f-put-global 'fn-owner-retain-carry
                                                     carry state)))
                            (fn-owner-install-ocfg (cdr outcome) state)))))
            (if (equal record :clock-unusable)
                (mv nil :clock-unusable fn-arena fn-hist state)
              (if (not (equal (car outcome) :prepared))
                (mv nil (car outcome) fn-arena fn-hist state)
              ; The entry reads the arena only (no invariant-risk: it runs
              ; compiled, no callee re-checks its guard); it names the payload
              ; and the host seals it with one fn-arena-seal-list call
              ; (tools/run_owner.py prepare), exactly when ACL2 answered
              ; :prepared.
              (mv nil (list :seal payload) fn-arena fn-hist state)))))))))))

; Step 8 (catalog slice) after the records flip: the host sealed the POST's
; payload (host/native/owner.lisp fnn-owner-attempt, after
; fn-owner-prepare-buffer answered :seal-buffer); the catalog's pending row is
; the store's row, which names that sealed handle (books/served-catalog-owner.lisp
; fn-cat-prepare-sealed, KEYSTONE fn-cat-prepare-sealed-names-the-sealed-handle):
; one seal per POST.  A row that does not name the newest handle is refused
; by name (:not-sealed), never prepared.
(defun fn-owner-cat-prepare-sealed (fn-arena fn-cat state)
  (declare (xargs :stobjs (fn-arena fn-cat state) :mode :program))
  (let ((cand (and (boundp-global 'fn-owner-cat-candidate state)
                   (f-get-global 'fn-owner-cat-candidate state))))
    (if (not (consp cand))
        (value :fault)
      (let* ((pending (fn-cat-prepare-sealed (car cand) (cdr cand) nil nil nil fn-arena fn-cat))
             (state (f-put-global 'fn-owner-cat-candidate nil state)))
        (if (fn-pc-p pending)
            (let ((state (f-put-global 'fn-owner-cat-pending pending state)))
              (value :prepared))
          (value (if (consp pending) (car pending) :fault)))))))

; fn-pout-refuse-reservation (books/owner-prepare-outcome.lisp): :refused
; exactly when the Store's gate fn-sn-refuse-reservation-enabledp holds, else
; :fault (KEYSTONE fn-pout-refuse-reservation-answers-the-host-test: the word
; the before/after comparison this entry used to make).
(defun fn-owner-refuse-reservation (fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (mv-let (word next)
    (fn-pout-refuse-reservation (fn-owner-ocfg state) fn-arena)
    (let ((state (fn-owner-install-ocfg next state)))
      (value word))))

; fn-owner-prepare with the payload in the octet buffer (books/octets-stobj.lisp;
; host/native/owner.lisp fnn-owner-attempt).  Three things differ from the
; list entry above, each by a theorem of books/poster-bytes-buffer.lisp:
; the fn-octet-listp test is discharged by the buffer's recognizer
; (fn-pbb-buffer-is-octet-listp); the length is the fill count
; (fn-octets-len); the existing-article test reads the buffer by index
; (fn-pbb-same-articlep-is-pb-same-articlep).  The record's payload is
; the buffer's list (fn-octets-list), consed once here: it is the store
; record's own field, held for the record's life, until wave C gives the
; owner state a concrete representation.  Everything after the record is
; the same prepare (fn-pcar-sbud-prepare) on the same record.
; The records flip: as fn-owner-prepare above, with the duplicate test
; fn-pidx-existing-action over the arena (KEYSTONE
; fn-pidx-existing-action-is-store-existing-action) and the payload sealed
; from the buffer (fn-arena-seal-buffer: no list is retained; the wire
; record's list payload lives only for the facts, the context and the budget).

(defun fn-owner-prepare-buffer (msgid-octets group-codes id-octets
                                 subject-octets evidence-octets charge
                                 fn-octets fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-octets fn-arena fn-hist state) :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    ; books/post-fields.lisp fn-pfld-article-inputsp, over the buffer's fill.
    (if (not (fn-pfld-article-inputsp msgid-octets (fn-octets-len fn-octets)
                                      groups id-octets subject-octets
                                      evidence-octets charge))
        (mv nil :invalid fn-arena fn-hist state)
      ; A retired group (in the domain, not served at the live generation)
      ; is refused by the prepare below (fn-psrv-prepare, lane
      ; prepare-served): the host makes no served test of its own.
      (let* ((msgid (fn-store-octets->string msgid-octets))
             ; PRF-191: the held article through the view trie
             ; (books/post-identity-index.lisp
             ; fn-pidx-existing-action-is-store-existing-action).
             (existing (fn-pidx-existing-action msgid fn-octets groups
                                                (fn-owner-core state) fn-arena)))
        (if existing
            (mv nil existing fn-arena fn-hist state)
          (mv-let (bytes fn-hist state) (fn-owner-record-octets fn-hist state)
          (mv-let (debt fn-hist state) (fn-owner-record-debt fn-hist state)
          (let* ((record (fn-sn-article-record
                          s (fn-own-clock (fn-owner-core state))
                          msgid (fn-octets-list fn-octets) groups
                          (fn-store-octets->string id-octets)
                          (fn-store-octets->string subject-octets)
                          (fn-store-octets->string evidence-octets)
                          charge))
                 ; Packet 1: the history gate at the article's own figure
                 ; (books/store-budget-article.lisp), and PRF-138: 0 unless
                 ; the capacity vector (a release per open undertaking and
                 ; the maintenance release) still holds after the article
                 ; (books/store-capacity-vector.lisp
                 ; `fn-cvec-prepare-keeps-the-vector').
                 ; PRF-284: fn-pvc-article-budget-carried-is-cvec-
                 ; article-budget-for (the carry satisfies fn-pvc-carryp).
                 (budget (fn-pvc-article-budget-carried
                          (fn-owner-profile-carry state)
                          (fn-owner-store-profile state)
                          (fn-sf-records-count (fn-sn-files s))
                          bytes record debt))
                 (before (fn-owner-ocfg state))
                 (row (if (equal record :clock-unusable)
                          nil
                        ; fn-apc-intern-row-at-is-reference: the row's
                        ; held context reads the take's parse.
                        (fn-apc-intern-row-at record (fn-sn-keyring s)
                                              (fn-sn-keyring-generation s)
                                              (fn-arena-count fn-arena)
                                              (fn-owner-parse-carry state))))
                 ; The carried obligation-id trie, brought to the Store
                 ; node's ledger (a commit puts one id, a release none).
                 (carry (fn-prc-refresh (fn-owner-retain-carry state)
                                        (fn-node-retention (fn-sn-node s))))
                 ; fn-pout-prepare-article (books/owner-prepare-outcome.lisp)
                 ; runs fn-psrv-prepare (lane prepare-served): the served test
                 ; is the prepare's own, then fn-prc-sbud-prepare (KEYSTONE
                 ; fn-psrv-prepare-preserves-invariant), equal to PRF-191's
                 ; fn-pidx-sbud-prepare under fn-prc-carryp
                 ; (fn-prc-sbud-prepare-is-pidx-sbud-prepare), so to
                 ; fn-pcar-sbud-prepare over the owner's carried view
                 ; (fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare): the
                 ; duplicate test reads the view trie and the retention
                 ; admission the carried id trie, decided once.  Its word is
                 ; :prepared when the row was staged, else
                 ; fn-psrv-refusal-kind (KEYSTONE
                 ; fn-pout-prepare-article-answers-the-store-change); the host
                 ; relays it.
                 (outcome (if (equal record :clock-unusable)
                              nil
                            (mv-let (word next)
                              (fn-pout-prepare-article before row budget carry)
                              ; Lane membership-budget: an :unaffordable
                              ; that the membership charge alone caused is
                              ; :memberships (books/store-capacity-vector.lisp
                              ; KEYSTONE fn-cvec-article-refusal-word-names-
                              ; the-memberships), over the same count, octets,
                              ; record and debt the budget was decided from.
                              (cons (fn-cvec-article-refusal-word
                                     word (fn-owner-store-profile state)
                                     (fn-sbud-count s) bytes record debt)
                                    next))))
                 (state (if (equal record :clock-unusable)
                            state
                          (let ((state (f-put-global 'fn-owner-retain-carry
                                                     carry state)))
                            (fn-owner-install-ocfg (cdr outcome) state)))))
            (if (equal record :clock-unusable)
                (mv nil :clock-unusable fn-arena fn-hist state)
              (if (not (equal (car outcome) :prepared))
                (mv nil (car outcome) fn-arena fn-hist state)
              ; Reads the arena and the buffer only (no invariant-risk; see
              ; fn-owner-prepare): :seal-buffer tells the host to seal the
              ; buffer's payload with one fn-arena-seal-buffer call
              ; (host/native/owner.lisp fnn-owner-attempt), exactly when ACL2
              ; answered :prepared.
              ; Step 8 (catalog slice, one seal per POST): the store's row, which
              ; names the handle the host's seal creates, is kept for the
              ; catalog's prepare after that seal (fn-owner-cat-prepare-sealed;
              ; books/served-catalog-owner.lisp fn-cat-prepare-sealed).
              (let ((state (f-put-global 'fn-owner-cat-candidate (cons record row) state)))
                (mv nil :seal-buffer fn-arena fn-hist state))))))))))))

(defun fn-owner-prepare-retention
  (kind id-octets subject-octets evidence-octets charge fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program
                  :guard (and (fn-cbor-octet-listp id-octets)
                              (fn-cbor-octet-listp subject-octets)
                              (fn-cbor-octet-listp evidence-octets))))
  (let* ((s (fn-owner-store state))
         (node (fn-sn-node s)))
    ; books/post-fields.lisp fn-pfld-retention-inputsp.
    (if (not (fn-pfld-retention-inputsp kind id-octets subject-octets
                                        evidence-octets charge))
        (value :invalid)
      (let* ((txid (fn-state-next-txid (fn-node-acceptance node)))
             (event (fn-store-retention-event-make
                     kind (fn-sn-identity-next s) txid txid
                     (fn-store-octets->string id-octets)
                     (fn-store-octets->string subject-octets)
                     (fn-store-octets->string evidence-octets) charge)))
        ; fn-pout-prepare-retention: (:store (:prepare-retention E)) and its
        ; word (KEYSTONE fn-pout-prepare-retention-answers-the-store-change).
        (mv-let (word next)
          (fn-pout-prepare-retention (fn-owner-ocfg state) event fn-arena)
          (let ((state (fn-owner-install-ocfg next state)))
            (value word)))))))

; The caller supplies an ACL2-constructed kind-3 or kind-4 event.  This
; boundary deliberately accepts no separate profile, key, article, or verdict
; fields that host code could recombine differently.
;; The owner's identity entry (lane signed-post, PRF-292).  Since the records
;; flip the Store retains a composite as a ROW (fn-hstxa-p); the event ACL2
;; built is the wire composite, so the entry stages the row the intern would
;; make at the arena's count (books/owner-identity-intern.lisp
;; fn-oii-ocfg-prepare-identity, KEYSTONE
;; fn-oii-ocfg-prepare-identity-is-intern-then-step) and, when the Store took
;; it and the intern seals (fn-oii-identity-sealsp), answers (:seal PAYLOAD):
;; the host seals exactly those octets (fn-oii-seal-is-the-intern-arena), so
;; a refused composite's bytes are never retained.  A keyring snapshot
;; (fn-stxk-p) interns to itself and seals nothing.
;; fn-ccar-ocfg-prepare-identity (books/owner-commit-carried.lisp) is
;; fn-ocfg-step of this event on every owner fn-own-relation admits
;; (fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation, PRF-144):
;; it stages without replaying the appended history, whose replay the
;; maintained store relation carries, and its candidate test reads the
;; history's last record, not every record (PRF-193,
;; fn-ccar-sn-prepare-identity-stages-the-next-event-above-the-last-record).
;; Guard-verified under fn-sn-statep of the store, which fn-ocl-relation
;; carries.
(defun fn-owner-prepare-identity (event fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
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
      (mv-let (word next)
        (fn-pout-prepare-identity (fn-owner-ocfg state) event (fn-arena-count fn-arena))
      (let* ((row (fn-oii-identity-row event (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                       (fn-arena-count fn-arena)))
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
              (t (value :prepared))))))))

; The consumer proposal is constructed by ACL2.  The host carries this exact
; bounded event into Store; it does not rebuild the scope, epoch or cursor.
(defun fn-owner-prepare-consumer (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (if (not (fn-cpe-eventp event))
      (value :invalid)
    ; fn-pout-prepare-consumer: (:store (:prepare-consumer E)) and its word
    ; (KEYSTONE fn-pout-prepare-consumer-answers-the-store-change).
    (mv-let (word next)
      (fn-pout-prepare-consumer (fn-owner-ocfg state) event fn-arena)
      (let ((state (fn-owner-install-ocfg next state)))
        (value word)))))

; ACL2 constructs the exact topic event before this host boundary. Store's
; carried historical projection decides whether it may be staged.
(defun fn-owner-prepare-topic (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program)
           (ignorable fn-arena))
  (if (not (fn-th-topic-eventp event))
      (value :invalid)
    ; fn-psrv-prepare-topic (lane prepare-served): (:store (:prepare-topic
    ; E)) when the consumer projection accepts E, which its completion
    ; needs (fn-psrv-prepare-topic-is-ocfg-step-when-admitted,
    ; fn-psrv-prepare-topic-preserves-invariant); fn-pout-prepare-topic
    ; answers its word (KEYSTONE
    ; fn-pout-prepare-topic-answers-the-store-change).
    (mv-let (word next)
      (fn-pout-prepare-topic (fn-owner-ocfg state) event)
      (let ((state (fn-owner-install-ocfg next state)))
        (value word)))))

; This is the one owner-side proposal read. ACL2 selects an exact earlier T10
; event and snapshot from the carried topic projection; neither the control
; peer nor host may supply an external verified/source verdict.
(defun fn-owner-topic-propose (operation source-sequence observed-uid
                                         entropy-id quota state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (projection (fn-sn-topic s))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (value
     (fn-th-local-propose operation projection txid source-sequence
                          observed-uid entropy-id quota))))

; The local-control socket binds its one OS owner to fn-col's fixed principal.
; These ACL2 calls alone choose the operation, current cursor scope and Store
; coordinates.  No request may provide qver, view, principal or event bytes.
(defun fn-owner-consumer-local-bootstrap (history incarnation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-bootstrap (fn-owner-core state) history incarnation)))

;; The consumer count is the carried Store profile's field 9 (D27, PRF-167),
;; read by ACL2 (host/store-host.lisp `fn-store-profile-max-consumers'); before
;; a profile is installed it reads 0 and every registration is refused.
(defun fn-owner-consumer-local-register (consumer group state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-register (fn-owner-core state)
                          (fn-store-profile-max-consumers
                           (fn-owner-store-profile state))
                          consumer group)))

; PRF-234: the plain ack is today's for an unbound consumer and refused
; (:bound) for a consumer the configuration binds to an account
; (books/consumer-bound.lisp fn-cbind-plain-ack-of-an-unbound-consumer-is-
; the-consumer-ack).
(defun fn-owner-consumer-local-ack (cursor-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp cursor-octets)))
  (value (fn-cbind-plain-ack (fn-owner-ocfg state) cursor-octets)))

(defun fn-owner-consumer-local-position (consumer state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-position (fn-owner-core state) consumer)))

(defun fn-owner-consumer-local-status (consumer state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-status (fn-owner-core state) consumer)))

(defun fn-owner-consumer-local-poll (consumer fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  ;; PKT-254: ACL2 encodes the selected event and refuses a report the
  ;; poll reply cannot carry by name (books/consumer-owner-local.lisp
  ;; fn-col-poll-report; fn-col-poll-report-fits-or-refuses-by-name,
  ;; books/consumer-owner-local-progress.lisp).  The legacy record's encoder
  ;; is fn-rcon-record-encode-impl (fn-rcon-record-encode-impl-is-record-
  ;; encode-impl, books/records-codec-concrete, no hypothesis).
  ;; PRF-234: fn-cbind-plain-poll is fn-col-poll-report for an unbound
  ;; consumer and refuses (:bound) a bound one (books/consumer-bound.lisp
  ;; fn-cbind-plain-poll-of-an-unbound-consumer-is-the-consumer-poll).
  ;; The records flip: a selected article is a held row, whose report reads
  ;; its bytes through the live arena (fn-cbind-plain-poll-over,
  ;; fn-cbind-plain-poll-over-of-an-unbound-consumer-is-the-consumer-poll).
  ;; PKT-710: the page is that answer with the view's withdrawals in it
  ;; (books/consumer-withdrawal.lisp fn-cwd-page; the answer itself while
  ;; nothing is withdrawn, fn-cwd-page-without-withdrawals-is-the-answer).
  (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (mv nil (fn-cwd-page (fn-ocfg-owner (fn-owner-ocfg state)) consumer
                         (fn-cbind-plain-poll-over (fn-owner-ocfg state) consumer
                                                   fn-arena fn-hist)
                         fn-hist)
        fn-hist state)))

(defun fn-owner-consumer-local-unregister (consumer state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-unregister (fn-owner-core state) consumer)))

(defun fn-owner-checkpoint-clone-phase (marker-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp marker-octets)))
  (value (fn-cpa-clone-phase-of-octets
          (fn-owner-store state) marker-octets)))

; fn-pout-known-abort (books/owner-prepare-outcome.lisp): :aborted exactly
; when the Store's gate fn-sn-known-abort-enabledp holds, else :fault
; (KEYSTONE fn-pout-known-abort-answers-the-host-test).
(defun fn-owner-known-abort (fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (mv-let (word next)
    (fn-pout-known-abort (fn-owner-ocfg state) fn-arena)
    (let ((state (fn-owner-install-ocfg next state)))
      (value word))))

(defun fn-owner-pending-octets (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((record (fn-sf-record-candidate
                 (fn-sn-files (fn-owner-store state)))))
    ; fn-rcon-store-event-encode-is-store-event-encode: the encoder's
    ; dispatch, with the concrete record recognizer (books/records-concrete),
    ; over ALPHA of the staged row (books/store-intern.lisp fn-row-wire-of).
    (value (if record (fn-rcon-store-event-encode (fn-row-wire-of record fn-arena)) nil))))

; The staged record's sequence, the one the host names its transaction file
; from (host/native/owner.lisp fnn-owner-publish-prepared); the host holds no
; count of its own.  It is the committed count
; (books/store-budget-naming.lisp `fn-sbud-pending-sequence-is-used').
(defun fn-owner-pending-sequence (state)
  (declare (xargs :stobjs state :mode :program))
  ; fn-rcon-sbud-pending-sequence-is-sbud-pending-sequence (books/records-concrete).
  (value (fn-rcon-sbud-pending-sequence (fn-owner-store state))))

; The POST admission boundary over the profile the owner was handed at open
; (`fn-owner-install-profile'); without one the payload bound is 0.
(defun fn-owner-post-boundary (msgid-octets payload-length group-count charge
                                            state)
  (declare (xargs :stobjs state :mode :program
                  :guard (and (fn-cbor-octet-listp msgid-octets)
                              (natp payload-length))))
  ; PRF-284: fn-pvc-post-boundary-carried-is-sbud-post-boundary.
  (value (fn-pvc-post-boundary-carried (fn-owner-profile-carry state)
                                       (fn-owner-store-profile state)
                                       msgid-octets payload-length
                                       group-count charge)))

; Completion is the owner's (:complete) event: fn-sn-finish consumed once,
; its pair appended to the ledger once (fn-own-completion-consumed-once).
;; post-alloc-2: the call is fn-rix-ocfg-complete (books/owner-refresh-indexed.lisp),
;; equal to fn-ccar-ocfg-complete under fn-ceis-indexedp of the owner's Store
;; (fn-rix-ocfg-complete-is-ccar-ocfg-complete; every owner the host holds has
;; it, fn-osi-live-owner-store-is-indexed): the refresh reads the new article's
;; row and the count from the Store's event index.
;; The call was fn-ccar-ocfg-complete (books/owner-commit-carried.lisp), equal
;; to fn-ocfg-step of (:complete) for every configured owner, no hypothesis
;; (fn-ccar-ocfg-complete-is-ocfg-step-complete).  It is guard-verified under
;; fn-sn-statep of the store, which fn-ocl-relation carries
;; (fn-ccar-ocl-relation-carries-sn-statep); the unverified fn-ocfg-step
;; evaluated that guard over the whole store on every completion, and its
;; fn-sn-finish searched the whole history and re-recognized the record for
;; every field it read.  The signed POST's composite, keyring snapshots,
;; retention, consumer and topic events complete here.
(defun fn-owner-finish-synced (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let* ((before (fn-owner-core state))
         (before-files (fn-sn-files (fn-own-store before)))
         (state (fn-owner-install-ocfg
                 (fn-rix-ocfg-complete (fn-owner-ocfg state) fn-hist) state))
         (after (fn-owner-core state))
         (after-files (fn-sn-files (fn-own-store after))))
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (fn-own-ledger-count after)
                    (1+ (fn-own-ledger-count before))))
        (value :durable)
      (value :fault))))

; The completion over the history stobj refreshed against the owner's Store
; (R at the read: fn-hist-refresh-is-the-history; the finish keeps the
; history, fn-ceis-finish-keeps-records), so fn-rix-ocfg-complete is
; fn-ccar-ocfg-complete (fn-rix-ocfg-complete-is-ccar-ocfg-complete).
(defun fn-owner-finish (fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (mv-let (erp val state) (fn-owner-finish-synced fn-hist state)
      (mv erp val fn-hist state))))

; The article completion of the submission in flight (served POST, control
; post): the word is fn-own-finish's (books/owner-served-invariants.lisp),
; :durable only when fn-sn-finish consumed an enabled completion whose record
; carries this submission's Message-ID and the octets fn-owner-take staged for
; it (fn-own-sub-stored-octets under the live configuration: for transit, the
; Path-updated fn-peer-relayed-octets), and the owner installed is its
; (fn-own-complete o).  That is the subject of
; fn-own-240-follows-consumed-completion, so the host no longer decides the
; word by comparing phases.  With no config record staged, fn-ocfg-step's
; (:complete) is exactly fn-ocfg-with-owner of fn-own-complete
; (books/owner-config.lisp fn-ocfg-complete); a staged record means this is
; not an article completion at all, and the answer is :fault with nothing
; changed.  Retention, identity and config completions still use
; fn-owner-finish above: they have no article submission to name.
;; post-alloc-2: the call is fn-rix-own-finish (books/owner-refresh-indexed.lisp),
;; equal to fn-ccar-own-finish under fn-ceis-indexedp of the owner's Store
;; (fn-rix-own-finish-is-ccar-own-finish; fn-osi-live-owner-store-is-indexed).
;; fn-ccar-own-finish (books/owner-commit-carried.lisp) is equal
;; to fn-own-finish for every owner and configuration
;; (fn-ccar-own-finish-is-own-finish) under the same guard, fn-sn-statep of
;; the store, which the owner relation carries from open.  It finds the
;; completion record at its sequence position instead of searching the
;; whole history through fn-record-p, ten times per commit.  Since
;; books/records-concrete.lisp the record recognizer it executes is
;; fn-rcon-record-p (fn-rcon-record-p-is-record-p: equal to fn-record-p on
;; every input), which reads the record's strings in place instead of
;; building their octet lists.
; The records flip (flip-L8) and step 8 (catalog slice): the submission is
; named through ALPHA of the completing row, read through the arena
; (fn-ccar-own-finish takes it); then T4-then-T2 over the catalog
; (books/served-catalog-owner.lisp fn-sca-finish).
(defun fn-owner-finish-submission-synced (fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program))
  (let ((oc (fn-owner-ocfg state)))
    (if (fn-ocfg-staged oc)
        (mv nil :fault fn-cat state)
      ; The completion the store is consuming, read before the finish: its
      ; (sequence . txid) pair (fn-sf-completion).  The pending row's token is
      ; (txid . expected) of the record it prepared, so a completion of any
      ; other record is a stale token.
      (let* ((completion (fn-sf-completion
                          (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
             ; fn-apc-own-finish-is-own-finish (books/owner-parse-carried.lisp):
             ; fn-ccar-own-finish with the stored octets' Cancel-Lock fields
             ; read from the take's parse and the completion's refresh over the
             ; Store's event index (post-alloc-2).
             (result (fn-apc-own-finish (fn-ocfg-owner oc) (fn-ocfg-config oc)
                                        fn-arena fn-hist (fn-owner-parse-carry state)))
             (state (fn-owner-replace-core (cdr result) state))
             (pending (f-get-global 'fn-owner-cat-pending state)))
        (if (not (and (equal (car result) :durable) pending (consp completion)))
            (mv nil (car result) fn-cat state)
          ; T4 then T2: the article's withdrawal targets the refreshed view no
          ; longer shows, withdrawn at the count with this row as the cause,
          ; THEN the row completed by the completing record's token -- hidden
          ; when the view no longer shows its Message-ID (R1).
          (let ((view (fn-own-view (cdr result))))
            (mv-let (word pending2 fn-cat)
              (fn-sca-finish (cons (nfix (cdr completion)) (fn-pc-expected pending))
                             pending (fn-own-view-index view)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view))
                             fn-cat)
              (let ((state (f-put-global 'fn-owner-cat-pending pending2 state)))
                (if (or (equal (car word) :stale-token) (equal (car word) :expected-mismatch))
                    ; the catalog refused the completion the store made durable:
                    ; a recovery event, never a silent divergence (the catalog
                    ; is rebuilt from the store's rows at the next open).
                    (mv nil :fault fn-cat state)
                  (mv nil (car result) fn-cat state))))))))))

; The POST's completion over the history stobj refreshed against the owner's
; Store (R at the read), so fn-apc-own-finish is fn-own-finish
; (fn-apc-own-finish-is-own-finish).
(defun fn-owner-finish-submission (fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program))
  (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (mv-let (erp val fn-cat state)
      (fn-owner-finish-submission-synced fn-arena fn-cat fn-hist state)
      (mv erp val fn-cat fn-hist state))))

;; The completion of an identity event that carried an article (a signed
;; composite: signed-post), with the catalog's T4 then T2 over the pending
;; row fn-owner-cat-prepare-sealed prepared after the host's seal, exactly as
;; fn-owner-finish-submission completes a POST (books/served-catalog-owner.lisp
;; fn-sca-finish; its R keystone fn-sca-ocl-relation-of-finish is stated over
;; the article the history's rows serve, fn-cat-history-articles, which
;; reads a composite row's held article).  Without a pending row it is
;; fn-owner-finish.  (mv nil WORD fn-cat state).
(defun fn-owner-finish-identity (fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state) :mode :program)
           (ignorable fn-arena))
  (let ((completion (fn-sf-completion (fn-sn-files (fn-owner-store state)))))
    (mv-let (erp word fn-hist state)
      (fn-owner-finish fn-hist state)
      (declare (ignore erp))
      (let ((pending (f-get-global 'fn-owner-cat-pending state)))
        (if (not (and (equal word :durable) pending (consp completion)))
            (mv nil word fn-cat fn-hist state)
          (let ((view (fn-own-view (fn-owner-core state))))
            (mv-let (cword pending2 fn-cat)
              (fn-sca-finish (cons (nfix (cdr completion)) (fn-pc-expected pending))
                             pending (fn-own-view-index view)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view))
                             fn-cat)
              (let ((state (f-put-global 'fn-owner-cat-pending pending2 state)))
                (if (or (equal (car cword) :stale-token) (equal (car cword) :expected-mismatch))
                    (mv nil :fault fn-cat fn-hist state)
                  (mv nil word fn-cat fn-hist state))))))))))

; fn-pout-begin (books/owner-prepare-outcome.lisp): :begun exactly when the
; begin's gate fn-pout-begin-admitsp holds (KEYSTONE
; fn-pout-begin-answers-the-host-test, for the natural connection
; identifiers the host passes).
(defun fn-owner-begin (id fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (mv-let (word next)
    (fn-pout-begin (fn-owner-ocfg state) id fn-arena)
    (let ((state (fn-owner-install-ocfg next state)))
      (value word))))

; The writer step: fn-own-take-submission moves the oldest queued submission
; into the durable path when nothing is in flight, no transaction is pending
; and the store is :ready.  The submission in flight is exposed to the host
; through four globals read off the injection decision; the host passes them
; back through fn-owner-prepare exactly as the CLI passes its own.
(defun fn-owner-take (fn-arena state)
  ; One SubmissionTaken (books/owner-results.lisp fn-ores-take-result; its
  ; fields are what the seven fn-owner-submit-* globals held,
  ; fn-ores-take-result-by-definition).  The octets are fn-own-sub-stored-
  ; octets of the live configuration: a transit article is stored, served
  ; and fed on as fn-peer-relayed-octets makes it (its Path updated with this
  ; node's identity, its Xref removed; RFC 5537 3.6/3.7,
  ; books/path-update.lisp); fn-owner-transit-decide stages the same function
  ; of the same octets in fn-owner-transit-payload, which the native drain
  ; compares with these before the store attempt, and
  ; fn-owner-finish-submission compares the completed record with the same
  ; function of the same configuration.
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let* ((before (fn-owner-core state))
         (state (fn-owner-step (list :take) fn-arena state))
         (after (fn-owner-core state))
         (sub (fn-own-inflight after)))
    (if (or (equal after before) (null sub))
        (value *fn-ores-take-idle*)
      ; The submission's intent identity, digested once here and carried to
      ; the intent and the resolution (books/owner-intent-carried.lisp).  It
      ; stays ACL2's own state: this is the only writer of the global and
      ; only fn-owner-intent-carry reads it, so its value always satisfies
      ; fn-icar-carryp (fn-icar-carryp-of-carry-of; nil before the first
      ; take).  The host never sees it as an input.
      ; The article is parsed once here too (books/owner-parse-carried.lisp):
      ; fn-apc-take answers the stored octets and the parse carry, and the
      ; carry is written to 'fn-owner-parse-carry, whose only writer this is
      ; and whose only reader is fn-owner-parse-carry; its value satisfies
      ; fn-apc-p (fn-apc-p-of-take; nil before the first take).  The intent
      ; carry is fn-icar-carry-of's value with its Path read from the parse
      ; carry, and the SubmissionTaken's INTENT field is that same object
      ; (fn-apc-take-is-take-result: the three calls are fn-ores-take-result
      ; of fn-own-sub-stored-octets, and the intent is fn-icar-carry-of).
      ; A served POST under a login gets its RFC 8315 Cancel-Lock in the
      ; stored octets (SEC-006, PRF-210): the owner's node secret.
      (let* ((tk (fn-apc-take (fn-owner-config state) sub
                              (fn-own-node-secret after)))
             (intent (fn-apc-icar-carry-of sub (cdr tk)))
             (state (f-put-global 'fn-owner-submit-intent intent state))
             (state (f-put-global 'fn-owner-parse-carry (cdr tk) state)))
        (value (fn-apc-take-result sub (car tk) intent))))))

; The hybrid-signed author path and the BP application path submit an
; already-authored article object whose octets a signature or a journal
; binds.  This is one owner event, not a call around the owner to the store
; bridge: ACL2 checks the boundary, preserves the supplied octets exactly and
; queues the same submission record fn-own-take-submission consumes for
; served POST.
(defun fn-owner-control-submit (msgid-octets group-octets payload fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program
                  :guard (and (fn-cbor-octet-listp msgid-octets)
                              (fn-octet-list-listp group-octets))))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-control-submit-result owner msgid-octets
                                                group-octets payload))
         ; A refused submission keeps the decision's reason (a header
         ; limit's name, PRF-230) for the delivery's refusal line.
         (state (if (equal result :refused)
                    (f-put-global
                     'fn-owner-app-refusal-reason
                     (fn-inj-decision-reason
                      (fn-own-control-decision (fn-own-config owner)
                                               msgid-octets group-octets
                                               payload))
                     state)
                  state))
         (state (fn-owner-step (list :control-submit msgid-octets
                                     group-octets payload)
                               fn-arena state)))
    (value result)))

(defun fn-owner-bp-transit-submit
    (peer msgid-octets payload id subject fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let* ((owner (fn-owner-core state))
         (cfg (fn-owner-config state))
         (result (fn-own-bp-transit-submit-result
                  owner cfg peer msgid-octets payload id subject))
         ; A refused submission keeps the transfer decision's reason for
         ; the delivery's refusal line (fn-owner-bp-request-refusal-line).
         (state (if (equal result :refused)
                    (f-put-global
                     'fn-owner-app-refusal-reason
                     (fn-peer-decision-reason
                      (fn-peer-decide-transfer-under
                       (fn-sn-node (fn-own-store owner)) cfg peer msgid-octets
                       payload (fn-own-clock owner) id subject
                       (fn-own-config-header-limits (fn-own-config owner))))
                     state)
                  state))
         (state (fn-owner-step
                 (list :bp-transit-submit cfg peer msgid-octets payload
                       id subject) fn-arena state)))
    (value result)))

(defun fn-owner-bp-transit-raw (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((sub (fn-own-inflight (fn-owner-core state))))
    (value (and (fn-own-bp-transit-submissionp sub)
                (fn-peer-submission-octets (fn-own-sub-decision sub))))))

; `fn operator CONFIG post': the operator is a posting agent and this node
; its injecting agent (RFC 5537 section 3.5).  books/owner.lisp
; fn-own-operator-submit injects the payload under the owner's posting
; configuration and the owner's current clock reading, refuses without one
; (D10-a), and resubmits the stored article when the same octets were
; already injected (fn-own-operator-retry-resubmits-the-stored-injection).
; The injected octets are what fn-owner-take then leaves in
; fn-owner-submit-octets; the host stores those, never the payload it read.
;; PKT-657, PKT-575: the owner's decision on a moderation or withdrawal
;; request (books/moderation-verbs.lisp `fn-mvb-plan'): (:refused REASON),
;; (:submit MSGID GROUPS OCTETS) or (:withdraw ARGV MSGID GROUPS OCTETS).  It
;; reads the owner and the configuration it carries and changes nothing; the
;; host runs the named steps (host/native/control.lisp
;; fnn-owner-moderation-serialized) through the live administration and
;; the operator submission, each deciding again.
;; The held envelope's octets are read through the payload arena (only READ:
;; the host seals; flip-L6-2's rule): its payload position is a handle since
;; the records flip (lane matrix-reds: approve answered envelope-malformed).
(defun fn-owner-moderation-plan (op login id reason fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-mvb-plan op login id reason (fn-owner-ocfg state) fn-arena)))

; After the records flip the node holds the stored article's HANDLE; the
; retry arm reads the octets under it through the arena
; (books/owner-served-invariants.lisp fn-own-operator-stored-octets,
; keystone fn-own-operator-retry-at-the-entry-is-the-stored-injection), and
; the submit, its refusal line and the event carry them (flip-L8-2).
(defun fn-owner-operator-submit (msgid-octets group-octets payload fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let* ((owner (fn-owner-core state))
         (stored (fn-own-operator-stored-octets owner msgid-octets fn-arena))
         (result (fn-own-operator-submit-result owner msgid-octets
                                                 group-octets payload stored))
         ; The refusal's service-log line, NIL unless RESULT is :refused
         ; (fn-olog-control-refusal-line-says-refused-iff-submit-refused).
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-control-refusal-line
                               owner msgid-octets group-octets payload stored)
                              state))
         (state (fn-owner-step (list :operator-submit msgid-octets
                                     group-octets payload stored)
                               fn-arena state)))
    (value result)))

; Why the owner refused the operator's article: the injection decision's
; reason under the owner's current configuration and clock (the decision
; `fn-owner-operator-submit' just refused), NIL when that decision injects.
; The native control path maps it to the control word
; (`fn-native-control-refusal-status'), so an article past the profile's A
; reaches the operator as `article-exceeds-profile-bound', not a bare refusal.
(defun fn-owner-operator-refusal-reason (msgid-octets group-octets payload fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program
                  :guard (and (fn-cbor-octet-listp msgid-octets)
                              (fn-cbor-octet-listp payload)
                              (fn-octet-list-listp group-octets))))
  (let ((decision (fn-own-operator-decision-of
                   (fn-owner-core state) msgid-octets group-octets payload
                   (fn-own-operator-stored-octets (fn-owner-core state) msgid-octets
                                                  fn-arena))))
    (value (if (fn-inj-injectedp decision)
               nil
             (fn-inj-decision-reason decision)))))

; -----------------------------------------------------------------------------
; The AUTHINFO policy (RFC 4643), set once at start-up and pinned per
; connection.
;
; It is defined HERE, above the transit port, because `fn-owner-open-peer'
; now reads it: a peer connection carries the operator's policy exactly as a
; reader connection does.
;
; The host reads the operator's credential file and passes the FIELDS; ACL2
; builds the record, the verifier and the configuration.  Nothing here
; derives a digest, compares a secret or decides a permission: the rows are
; transport (AGENTS.md's one-owner rule).  A row is
; (name-octets principal-octets salt-octets digest-octets postingp).

(defun fn-owner-auth-cred-of (row)
  (declare (xargs :mode :program))
  (fn-auth-make-cred (nth 0 row) (nth 1 row)
                     (fn-authsec-verifier (nth 2 row) (nth 3 row))
                     (and (nth 4 row) t)))

(defun fn-owner-auth-creds-of (rows)
  (declare (xargs :mode :program))
  (if (consp rows)
      (cons (fn-owner-auth-cred-of (car rows))
            (fn-owner-auth-creds-of (cdr rows)))
    nil))

(defun fn-owner-set-auth (requiredp protected-onlyp tls-availablep rows state)
  (declare (xargs :stobjs state :mode :program))
  (let ((acfg (fn-auth-make-config (and requiredp t) (and protected-onlyp t)
                                   (and tls-availablep t)
                                   (fn-owner-auth-creds-of rows))))
    (if (not (fn-auth-configp acfg))
        (value :rejected)
      (let ((state (f-put-global 'fn-owner-auth acfg state)))
        (value :ok)))))

(defun fn-owner-auth (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-auth state)
      (f-get-global 'fn-owner-auth state)
    (fn-auth-open-config)))

; PRF-234 (CNS-006): a consumer bound to an account.  ACL2 decides the
; binding, the credential (the account's own, against the credential table
; AUTHINFO reads), the account's read rule and the answer, from the latest
; configuration (books/consumer-bound.lisp fn-cbind-poll / fn-cbind-ack;
; keystones fn-cbind-poll-delivers-only-readable-events,
; fn-cbind-poll-is-the-consumer-poll-or-a-refusal,
; fn-cbind-ack-is-the-consumer-ack-or-a-refusal).  The host carries the
; decoded consumer id or cursor and the password octets; it compares
; nothing.
(defun fn-owner-consumer-local-bound-poll (consumer secret fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  ;; Over the live arena (records flip): fn-cbind-poll-over-delivers-only-
  ;; readable-events, fn-cbind-poll-over-is-the-consumer-poll-or-a-refusal.
  ;; PKT-710: with the withdrawals in it (a refusal of the gate is served
  ;; unchanged, fn-cwd-page-of-a-refusal).
  (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (mv nil (fn-cwd-page (fn-ocfg-owner (fn-owner-ocfg state)) consumer
                         (fn-cbind-poll-over (fn-owner-ocfg state) (fn-owner-auth state)
                                             consumer secret fn-arena fn-hist)
                         fn-hist)
        fn-hist state)))

;; PRF-252: one step of a consumer wait (books/consumer-wait.lisp
;; fn-cwait-step-is-the-poll-or-a-sleep-on-an-empty-page): the poll a
;; `poll' (SECRET nil) or `bound-poll' request answers now, or (:sleep MS)
;; when that is an empty page before the deadline.  The admission of one
;; more waiter.  host/native/owner.lisp fnn-owner-consumer-local-wait calls
;; both under the owner mutex.
(defun fn-owner-consumer-local-wait-step (consumer secret elapsed seconds fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  ;; Over the live arena (records flip), and PKT-710: a wait answers the
  ;; page (fn-cwd-wait-step-over-is-the-page-or-a-sleep-on-an-empty-page),
  ;; so a withdrawal wakes it as an article does.
  (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (mv nil (fn-cwd-wait-step-over (fn-owner-ocfg state) (fn-owner-auth state)
                                   consumer secret elapsed seconds fn-arena fn-hist)
        fn-hist state)))

(defun fn-owner-consumer-local-wait-admit (waiters state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cwait-admit waiters)))

(defun fn-owner-consumer-local-bound-ack (cursor-octets secret state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp cursor-octets)))
  (value (fn-cbind-ack (fn-owner-ocfg state) (fn-owner-auth state)
                       cursor-octets secret)))

; Install a complete ACL2-built authentication configuration.  The native
; auth profile parser calls this after owner recovery and before the listener
; opens.  Raw Lisp cannot rebuild a credential row or change one policy bit.
(defun fn-owner-set-auth-config (acfg state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-auth-configp acfg))
      (value :rejected)
    (let ((state (f-put-global 'fn-owner-auth acfg state)))
      (value :ok))))

; -----------------------------------------------------------------------------
; The transit port (specs/peering.md 2.2).
;
; Accept: the host resolves the connecting address to a configured peer name
; with fn-owner-peer-for-address (the record's auth slot decides, not the
; client) and opens the connection with fn-own-open-peer, which pins the
; node, the live configuration AND the operator's AUTHINFO policy into the
; session.  A reader opens with fn-owner-open as before, on the same
; listener, under the same policy: `fn-served-peer-and-reader-open-under-
; the-same-policy' (books/served.lisp) is the statement of that.

(defun fn-owner-peer-name-for (rows address)
  ; The first configured peer whose auth slot is this source address.
  (declare (xargs :mode :program))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-b (car rows)) "auth-source-address")
               (equal (fn-cfg-row-c (car rows)) address))
          (fn-cfg-row-a (car rows))
        (fn-owner-peer-name-for (cdr rows) address))
    nil))

(defun fn-owner-peer-for-address (address-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((address (fn-store-octets->string address-octets)))
    (if (equal address :bad)
        (value nil)
      (let ((name (fn-owner-peer-name-for
                   (fn-cfg-peers (fn-cfg-value (fn-owner-config state)))
                   address)))
        (value (if name (fn-record-string-octets name) nil))))))

; The native socket boundary supplies a family tag and the kernel's fixed-width
; address octets.  ACL2 owns their textual projection because the configured
; source-address is a semantic peer-identity decision, not a raw-host string
; formatting choice.  Numeric IPv4 is rendered canonically here; the current
; IPv6 profile admits only ::1, so every other IPv6 shape remains an explicit
; non-match until its textual policy is added in ACL2.
(defun fn-owner-ipv4-address-octets (address)
  (declare (xargs :mode :program))
  (if (consp address)
      (if (and (natp (car address)) (<= (car address) 255))
          (append (fn-nntp-decimal (car address))
                  (if (consp (cdr address)) '(46) nil)
                  (fn-owner-ipv4-address-octets (cdr address)))
        nil)
    nil))

(defun fn-owner-peer-for-socket-address (family address state)
  (declare (xargs :stobjs state :mode :program))
  (cond ((and (equal family :inet)
              (true-listp address) (equal (len address) 4)
              (fn-cbor-octet-listp address))
         (fn-owner-peer-for-address (fn-owner-ipv4-address-octets address) state))
        ((and (equal family :inet6)
              (equal address '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)))
         (fn-owner-peer-for-address (fn-record-string-octets "::1") state))
        (t (value nil))))

(defun fn-owner-open-peer (peer-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((before (fn-owner-core state))
             (id (fn-own-next-id before))
             ; The owner's AUTHINFO policy, the same value fn-owner-open
             ; pins into a reader.  A peer connection was opened with no
             ; policy at all, and the owner resolves a connection to a peer
             ; by source address alone (fn-owner-peer-name-for below), so on
             ; a box where a configured peer is on loopback that was every
             ; client: the operator's credential reached nothing.
             (opened (fn-ocfg-open-peer (fn-owner-ocfg state) peer
                                        (fn-owner-auth state)))
             (state (fn-owner-install-ocfg (cdr opened) state))
             (state (fn-owner-install-effects (car opened) state))
             (state (f-put-global 'fn-owner-log-line
                                  (fn-olog-connection-line
                                   (fn-owner-core state) id peer-octets)
                                  state)))
        (if (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))
            (value id)
          (value nil))))))

; The transfer decision for the transit submission in flight, over the LIVE
; node and the live configuration (RFC 4644 2.4.2: the offer was advisory).
; Every check of specs/peering.md 2.2 is in fn-peer-decide-transfer; this
; wrapper only reads its answer and the memberships fn-peer-injection-arguments
; derives, and leaves them where the bridge can read them.  The obligation id
; and the subject are the host's digests, as for POST (fn-frame-digest is
; constrained and unattached).
(defun fn-owner-transit-decide (id-octets subject-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (and (fn-cbor-octet-listp id-octets)
                              (fn-cbor-octet-listp subject-octets))))
  (let* ((owner (fn-owner-core state))
         (sub (fn-own-inflight owner)))
    (if (not (fn-own-transit-subp sub))
        (value :not-transit)
      (let* ((decision (fn-own-sub-decision sub))
             (node (fn-sn-node (fn-own-store owner)))
             (cfg (fn-owner-config state))
             (peer (fn-peer-submission-peer decision))
             (msgid (fn-peer-submission-msgid decision))
             (octets (fn-peer-submission-octets decision))
             (id (fn-store-octets->string id-octets))
             (subject (fn-store-octets->string subject-octets)))
        (if (or (equal id :bad) (equal subject :bad))
            (value :not-transit)
          ; PRF-230/PKT-660: under the opened profile's header limits, the
          ; owner's injection configuration's, exactly as a POST.
          (let* ((d (fn-peer-decide-transfer-under
                     node cfg peer msgid octets (fn-own-clock owner) id subject
                     (fn-own-config-header-limits (fn-own-config owner))))
                 (args (fn-peer-injection-arguments node cfg peer msgid octets
                                                    0 id subject
                                                    (fn-own-clock owner)))
                 (state (f-put-global 'fn-owner-transit-kind
                                      (fn-peer-decision-kind d) state))
                 (state (f-put-global 'fn-owner-transit-reason
                                      (fn-peer-decision-reason d) state))
                 ; (nth 3 args) is fn-peer-scope-groups' answer: the list
                 ; fn-peer-injection-arguments hands fn-node-prepare as the
                 ; memberships (generation, msgid, octets, GROUPS, id,
                 ; subject, evidence, charge).  The generation passed here is
                 ; 0 because no element read from this list depends on it.
                 ;
                 ; It answers with STRINGS ("Strings, as fn-node-prepare
                 ; takes", books/peer-inbound.lisp fn-peer-scope-groups, which
                 ; ends in `fn-record-octets-string') where the POST path's
                 ; `fn-inj-decision-groups' answers with OCTETS -- its
                 ; elements are `fn-cbor-octet-listp' by
                 ; `fn-inj-group-namesp' -- and the host reads ONE global for
                 ; both.  Reading a string as an octet list raised
                 ; `unexpected ACL2 octet-list result' inside `Owner.drain',
                 ; which did not catch, so the OWNER PROCESS DIED on the
                 ; first article a peer transferred: the second half of the
                 ; w10/v0-matrix board ASK, and the death that took 22
                 ; transit rows, the feed rows and the crash rows of the
                 ; matrix with it.  The conversion is ACL2's own and happens
                 ; here, where the global is written, so the two paths agree
                 ; on a representation without Python choosing one.
                 ;
                 ; `w11/twonode-feed' and `w11/owner-survival' diagnosed and
                 ; fixed this independently on the same evening, and the two
                 ; fixes differed only in which of two identical helpers they
                 ; called.  The duplicate is folded into ACL2:
                 ; `fn-oag-group-octets' (books/owner-agent.lisp) is the one.
                 (state (f-put-global 'fn-owner-transit-groups
                                      (if (equal (fn-peer-decision-kind d) :want)
                                          (fn-oag-group-octets (nth 3 args))
                                        nil)
                                      state))
                 (state (f-put-global 'fn-owner-transit-evidence
                                      (fn-record-string-octets
                                       (fn-peer-evidence peer cfg))
                                      state))
                 ; D23: the delivering boundary's carried-source list, the
                 ; one fn-owner-peer-carrier-plan hands fn-pa-current-plan
                 ; for this transit attempt (books/peer-authored-accept).
                 (state (f-put-global 'fn-owner-transit-carried
                                      (fn-pa-peer-carried-sources
                                       peer (fn-cfg-peers (fn-cfg-value cfg)))
                                      state))
                 ; PRF-099: the same boundary's opaque-carriage budget
                 ; (books/peer-carriage-rows.lisp fn-pcb-peer-budget), read
                 ; from the same configuration as its carried list.
                 (state (f-put-global 'fn-owner-transit-budget
                                      (fn-pcb-peer-budget
                                       peer (fn-cfg-peers (fn-cfg-value cfg)))
                                      state))
                 ; (nth 2 args) is the payload fn-node-prepare is given:
                 ; fn-peer-relayed-octets of the received octets
                 ; (fn-peer-injection-arguments-stages-the-relayed-octets).
                 ; fn-owner-take left the same function of the same octets in
                 ; fn-owner-submit-octets; the native drain compares the two.
                 (state (f-put-global 'fn-owner-transit-payload
                                      (if (equal (fn-peer-decision-kind d) :want)
                                          (nth 2 args)
                                        nil)
                                      state)))
            (value (fn-peer-decision-kind d))))))))

; The transit reply.  `kind' and `reason' are the decision this image just
; made; `word' is the store's observed outcome (:durable, :refused,
; :uncertain), ignored unless the decision was :want.
;; The feed step's result is ONE value, a FeedPublication
;; (books/owner-results.lisp fn-ores-feed-publication-p): the step's word,
;; the peer its effect names, the sealed frame plan -- one (PEER . FRAME)
;; pair per FNFD record, in append order, each frame sealed with the
;; constrained trailer over its protected prefix (A-CRYPTO) -- the
;; completion token, and the rendered outbound command with its status.
;; The native host appends each pair's frame to that peer's journal BEFORE
;; it writes the command (host/native/owner.lisp fnn-owner-feed-flush); it
;; fetches nothing by index and splits no name list.  The header, the field
;; encoding, the seal and every bound stay ACL2's
;; (fn-ores-feed-port-publication-by-definition; the plan IS the by-index
;; fetch it replaced: fn-ores-sealed-plan-is-indexed-fetch).

(defun fn-owner-feed-word-publication (word command log-line)
  ; A step with no journal records: a connection-phase command (MODE,
  ; AUTHINFO, STARTTLS), a bare word, or a refusal.
  (declare (xargs :mode :program))
  (fn-ores-feed-publication word nil nil nil command :ok log-line))

; The only host projection of a bounded feed step.  The ACL2 subject has
; already selected the next table, journal records and effects together.  A
; refusal publishes no records and no command and deliberately does not
; replace the owner's core, so queued delivery intent remains available for
; recovery.  Answers (mv STATUS PUBLICATION STATE).
(defun fn-owner-feed-install-port-result (owner result word-of log-line state)
  (declare (xargs :stobjs state :mode :program))
  (if (equal (fn-own-feed-port-status result) :accepted)
      (let ((state (fn-owner-replace-core
                    (fn-own-with-feeds owner
                                       (fn-own-feed-port-table result)) state)))
        (mv :accepted
            (fn-ores-feed-port-publication
             (cdr (assoc-eq :accepted word-of))
             (fn-own-feed-port-records result)
             (fn-own-feed-port-effects result) nil log-line)
            state))
    (mv :refused
        (fn-ores-feed-port-publication (cdr (assoc-eq :refused word-of))
                                       nil nil nil log-line)
        state)))

; Project the durable intent before the store is allowed to begin.  The host
; supplies values ACL2 itself produced (provenance, configuration generation
; and next transaction id); this function derives the exact object identity,
; acceptance-time targets and queue-capacity verdict from the in-flight owner
; submission.  No owner state moves until the frames have reached their
; per-peer journals.
;; The call is fn-icar-submission-intent (books/owner-intent-carried.lisp),
;; which returns (result . records) and equals
;; (cons fn-own-submission-intent-result fn-own-submission-intent-records)
;; under fn-icar-carryp of the carry fn-owner-take installed
;; (fn-icar-submission-intent-is-reference): the identity is the one digested
;; at take, not three new digests of the payload.
(defun fn-owner-intent-carry (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-submit-intent state)
      (f-get-global 'fn-owner-submit-intent state)
    nil))

(defun fn-owner-submission-intent (evidence generation txid state)
  ; The FeedPublication is fn-ores-submission-intent-publication's
  ; (books/owner-results.lisp; well-formed by
  ; fn-ores-submission-intent-publication-is-well-formed): the token is the
  ; in-flight id, a connection number or the control id.
  ; (fn-ores-submission-intent-publication-unfolds: these two calls are it.)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         ; fn-apc-submission-intent-is-reference: under the two carries
         ; fn-owner-take wrote, the reference's result and records.
         (intent (fn-apc-submission-intent owner (fn-owner-intent-carry state)
                                           (fn-owner-parse-carry state)
                                           evidence generation txid))
         (state (f-put-global 'fn-owner-shared-resolution-id nil state)))
    (value (fn-ores-intent-publication intent (fn-ores-inflight-token owner)))))

; Project commit/abort while the same submission is still in flight.  The
; caller durably appends these records before invoking fn-owner-outcome (or
; its control/transit counterpart), so the in-memory feed can never get ahead
; of the obligation journal.  Uncertain produces no resolution record.
;; The call is fn-icar-submission-resolution-records, equal to
;; fn-own-submission-resolution-records under the same carry
;; (fn-icar-submission-resolution-records-is-reference).
(defun fn-owner-submission-resolution (word evidence generation txid state)
  ; fn-ores-submission-resolution-publication (books/owner-results.lisp;
  ; fn-ores-submission-resolution-publication-is-well-formed).
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (state (f-put-global 'fn-owner-shared-resolution-id
                              (fn-ores-inflight-token owner) state)))
    ; fn-apc-submission-resolution-publication-is-reference.
    (value (fn-apc-submission-resolution-publication
            owner (fn-owner-intent-carry state) (fn-owner-parse-carry state)
            word evidence generation txid))))

; Startup calls this only after the store's authoritative recovery completed.
; The scanner accumulated exact unresolved intent values in the global.  One
; call projects one commit/abort frame; replaying that frame removes the exact
; key.  A partial binding is :uncertain and must fence startup.
; The record for the first unresolved intent, or nil (none, or unbound).
(defun fn-owner-feed-reconcile-record (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((values (car (f-get-global 'fn-owner-feed-intents state))))
    (and values
         (fn-own-feed-intent-reconcile-record
          (fn-sn-node (fn-own-store (fn-owner-core state))) values))))

(defun fn-owner-feed-reconcile-next (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((values (car (f-get-global 'fn-owner-feed-intents state))))
    (if (null values)
        (value (fn-owner-feed-word-publication :done nil nil))
      (let ((record (fn-owner-feed-reconcile-record state)))
        (if (null record)
            (value (fn-owner-feed-word-publication :uncertain nil nil))
          (value (fn-ores-feed-port-publication
                  (fn-feed-journal-kind record) (list record) nil nil nil)))))))

; Applies the record fn-owner-feed-reconcile-next published: the same
; function of the same intents and the same owner (the host only appended
; frames in between), so no result crosses a mailbox.
(defun fn-owner-feed-reconcile-apply (fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((record (fn-owner-feed-reconcile-record state)))
    (if (or (null record)
            (not (member-equal (fn-feed-journal-kind record)
                               '(:feed-commit :feed-abort))))
        (value :invalid)
      (let* ((peer (fn-record-octets-string
                    (fn-feed-record-peer (fn-feed-journal-values record))))
             (state (fn-owner-step (list :feed-replay peer (list record)) fn-arena state))
             (state (f-put-global
                     'fn-owner-feed-intents
                     (fn-own-feed-intent-apply
                      (f-get-global 'fn-owner-feed-intents state)
                      (fn-feed-journal-kind record)
                      (fn-feed-journal-values record))
                     state)))
        (value :ok)))))

(defun fn-owner-feed-journal-peer-validp (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (fn-feed-namep peer-octets) t nil)))

(defun fn-owner-feed-journal-begin (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-feed-safe-offset 0 state)))
    (value :ok)))

(defun fn-owner-feed-journal-prefix-size (state)
  (declare (xargs :stobjs state :mode :program))
  (value *fn-feed-journal-prefix-size*))

(defun fn-owner-feed-journal-offset (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-feed-safe-offset state)))

; A transit transfer that became durable owes the feed journal the same
; `(:feed-enqueue ...)` records a POST does: a relayed article is fed
; onward (RFC 5537 sec. 3.6) and the entry must survive the process that
; accepted it.  Read before the outcome moves the owner, as for POST.
(defun fn-owner-transit-outcome (id kind reason word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-transit-outcome owner id kind reason word))
         (state (fn-owner-replace-core (cdr result) state))
         (state (fn-owner-install-effects (car result) state)))
    (value :fed)))

; The service-log line for the transit outcome about to be fed, read off the
; owner BEFORE fn-owner-transit-outcome moves it (books/owner-log.lisp
; fn-olog-transit-line), with the same id, kind, reason and word.  DETAIL is
; the ingress refusal the host relays (host/native/owner.lisp
; fnn-owner-transit-refused), a log field only.
; VERDICT (PKT-473) is the accepted arm's fn-pcb-transit-verdict
; (fn-owner-transit-verdict below), or nil.
(defun fn-owner-transit-log-line (id kind reason word detail verdict state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-log-line
                             (fn-olog-transit-line (fn-owner-core state)
                                                   id kind reason word detail
                                                   verdict)
                             state)))
    (value :ok)))

(defun fn-owner-transit-kind (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-transit-kind state)))

(defun fn-owner-transit-reason (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-transit-reason state)))

(defun fn-owner-transit-evidence (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-transit-evidence state)))

; The word the host observed for the submission in flight (:durable,
; :refused, :uncertain or anything else) is fed back as one owner event;
; fn-own-outcome renders the reply (240 only when a completion was consumed
; after the take, fn-own-durable-reply-names-a-durable-record) for that
; connection and installs it in fn-owner-output.
; The FNFD records a durable acceptance owes the feed journal are the
; submission resolution's (fn-owner-submission-resolution, journaled by the
; host before this outcome); this wrapper used to also compute
; fn-own-outcome-journal-records and leave them in a global that neither
; host read (every flush follows a fresh publication), so it no longer
; computes them (adapter retirement; PKT in the lane record).
(defun fn-owner-outcome (id word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         ; The service log line, read before the event consumes the
         ; submission in flight (books/owner-log.lisp).
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-served-post-line owner id word) state))
         ; fn-acar-own-outcome (books/owner-advance-carried.lisp) is
         ; fn-own-outcome under fn-ocl-relation
         ; (fn-acar-own-outcome-is-reference-under-ocl-relation), which the
         ; commit before it keeps (fn-ocmt-post-commit-preserves-ocl-relation):
         ; the re-pin tests the rebuilt session at the node the held session
         ; already carries instead of re-running fn-node-statep on it, and
         ; opens the reader session with fn-acar-nntp-projectionp, which
         ; omits the fn-statep of the whole view archive that
         ; fn-ocl-view-historyp carries (fn-acar-view-historyp-carries-view-statep).
         ; post-alloc-2: fn-apc-own-outcome, equal to fn-acar-own-outcome
         ; under the intent and parse carries fn-owner-take wrote
         ; (fn-apc-own-outcome-is-acar-own-outcome): the durable article's
         ; feed targets from the carried Path and parse, not a reparse.
         (result (fn-apc-own-outcome owner id word (fn-owner-intent-carry state)
                                     (fn-owner-parse-carry state)))
         (state (fn-owner-replace-core (cdr result) state))
         (state (fn-owner-install-effects (car result) state))
         (state (f-put-global 'fn-owner-shared-resolution-id nil state)))
    (value :fed)))

;; A served POST shed while the disk is slow (books/owner-time-model.lisp
;; fn-otm-admit-post answered :shed): the submission in flight gets
;; fn-own-outcome's :refused outcome -- nothing durable, no pin moved, the
;; feeds unchanged, the owner's own refusal log line -- and its reply is
;; ACL2's try-later line for the disk (fn-otm-shed-reply over the gate's
;; value S, at its recorded time): RFC 3977 section 6.3.1's 441,
;; with the reason in place of the generic refusal text.
(defun fn-owner-shed-outcome (id s state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (erp val state) (fn-owner-outcome id :refused state)
    (declare (ignore val))
    (if erp
        (mv erp nil state)
      (let ((state (f-put-global 'fn-owner-output (fn-otm-shed-reply s) state)))
        (value :shed)))))

; The control result is projected before the event consumes the in-flight
; submission.  The state transition uses fn-own-outcome-completion and
; fn-own-feed-durable exactly as the served outcome; only wire rendering and
; connection re-pinning are absent because the control request has no NNTP
; connection.
(defun fn-owner-control-outcome (word fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-control-outcome-result owner word))
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-control-post-line owner word) state))
         (state (fn-owner-step (list :control-outcome word) fn-arena state)))
    (value result)))

(defun fn-owner-bp-transit-outcome (word fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-bp-transit-outcome-result owner word))
         (state (fn-owner-step (list :bp-transit-outcome word) fn-arena state)))
    (value result)))

; The allocation domain the owner's live node carries (every name ever
; created): the store bridge's fn-store-cfg-domain reads the global
; fn-store-sn, which the owner never sets (its store lives in fn-owner), so
; the owner answers the same question from its own node.
(defun fn-owner-domain (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))

(defun fn-owner-group-codes (name-octets state)
  ; Resolve submitted names against the owner's current allocation domain.
  ; The separate Store bridge's replayed global does not follow live owner
  ; reconfiguration.  This is the same ACL2 resolver as fn-store-group-codes.
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-octet-list-listp name-octets)))
  (let ((names (fn-store-octet-lists->strings name-octets)))
    (value (if (equal names :bad) :bad
             (fn-store-codes-from-groups
              names (fn-state-groups
                     (fn-node-acceptance (fn-owner-node state))))))))

(defun fn-owner-next-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-state-next-txid (fn-node-acceptance (fn-owner-node state)))))

(defun fn-owner-next-store-coordinates (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (value (list (fn-sn-identity-next s) txid txid))))

(defun fn-owner-keyring-snapshot (generation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-stxk-find generation
                       (fn-sn-keyring-snapshots (fn-owner-store state)))))

(defun fn-owner-hybrid-snapshots (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sn-keyring-snapshots (fn-owner-store state))))

(defun fn-owner-hybrid-current-enrollment (generation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-hl-current-enrollment
          generation (fn-sn-keyring-snapshots (fn-owner-store state)))))

; TRANSITP is the host's path: t only for the NNTP transit attempt, whose
; delivering boundary fn-owner-transit-decide just read; served POST, bound
; submissions and BP transit pass nil, the D02 decision unchanged
; (fn-pa-current-plan-without-carried-list-never-carries).
(defun fn-owner-transit-carried-list (transitp state)
  (declare (xargs :stobjs state :mode :program))
  (if (and transitp (boundp-global 'fn-owner-transit-carried state))
      (f-get-global 'fn-owner-transit-carried state)
    nil))

;; PKT-221: the credential file's login bindings (BINDINGS, read by
;; host/native-auth-host.lisp fn-native-auth-host-load-bindings from the file
;; the profile accepted) against the owner's live configuration
;; (books/login-binding-live.lisp fn-lb-sync-plan): (:ok RECORDS), each a
;; delta list host/native/auth.lisp fnn-native-auth-publish-bindings stages
;; with fn-owner-reconfigure-deltas and publishes in order, or (:refused R).
(defun fn-owner-login-bindings-plan (bindings state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-lb-sync-plan bindings (fn-cfg-value (fn-ocfg-config (fn-owner-ocfg state))))))

;; The posting policy's gate for the served submission in flight
;; (books/login-binding-live.lisp fn-lb-ocfg-gate: the policy of the owner's
;; LIVE configuration, the login-binding table the submission's connection
;; pinned when it opened), called by host/native/owner.lisp
;; fnn-owner-attempt-served before the transit attempt.  The table is rows of
;; the configuration (PKT-221), published at start and on `principal bind'
;; through the live reconfiguration; there is no binding global.  The
;; verdict's service-log line is left in fn-owner-login-log-line (nil: no
;; login).
(defun fn-owner-login-gate (received state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((verdict (fn-lb-ocfg-gate (fn-owner-ocfg state) received))
         (state (f-put-global 'fn-owner-login-log-line
                              (fn-lb-verdict-line verdict) state)))
    (value verdict)))

(defun fn-owner-peer-carrier-plan (received transitp state)
  (declare (xargs :stobjs state :mode :program))
  ; fn-apc-current-plan-is-reference (books/owner-parse-carried.lisp).
  (value (fn-apc-current-plan
          received (fn-sn-keyring-snapshots (fn-owner-store state))
          (fn-owner-transit-carried-list transitp state)
          (and transitp t) (fn-owner-parse-carry state))))

;; C1 (control messages): the filing step every ingress takes first,
;; books/peer-authored-accept.lisp fn-pa-filing-plan over the received
;; octets, the ingress's group names and the owner's allocation domain (the
;; table fn-owner-group-codes resolves against).  (:file GROUPS) or
;; (:refused REASON); the host uses GROUPS in place of its own.
(defun fn-owner-control-filing (received group-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-octet-list-listp group-octets)))
  ; fn-apc-filing-plan-is-reference (books/owner-parse-carried.lisp).
  (value (fn-apc-filing-plan
          received group-octets
          (fn-state-groups (fn-node-acceptance (fn-owner-node state)))
          (fn-owner-parse-carry state))))

;; PKT-101: whether a SIGHUP asks for a reopen of `[log] path'
;; (books/owner-log-reopen.lisp fn-olr-decide, KEYSTONE
;; fn-olr-reopen-iff-requested), and on :reopen the line the reopened file
;; starts with, left in `fn-owner-log-line' for host/native/owner.lisp
;; fnn-owner-maybe-reopen-log.
(defun fn-owner-log-reopen (configured handled requested state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((decision (fn-olr-decide configured handled requested))
         (state (f-put-global 'fn-owner-log-line
                              (if (equal (car decision) :reopen)
                                  (fn-olr-line requested
                                               (fn-own-clock (fn-owner-core state)))
                                nil)
                              state)))
    (value decision)))

;; PKT-069: the gate host/native/owner.lisp fnn-owner-complete-bound-submission
;; asks before it calls a commit callback (books/owner-bound-commit.lisp
;; fn-obc-commit-gate; KEYSTONE fn-obc-commit-only-after-filing).
(defun fn-owner-bound-commit-gate (received group-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-octet-list-listp group-octets)))
  (value (fn-obc-commit-gate
          received group-octets
          (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))

(defun fn-owner-peer-carrier-form (received state)
  (declare (xargs :stobjs state :mode :program))
  ; fn-apc-carrier-form-is-reference (books/owner-parse-carried.lisp).
  (value (fn-apc-carrier-form received (fn-owner-parse-carry state))))

(defun fn-owner-served-carried-word (word detail state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pa-served-word word detail)))

; The served POST's word (PKT-473, PRF-184): fn-pa-served-post-word names a
; durable composite whose key change the Store refused.  Called by
; host/native/owner.lisp fnn-owner-attempt-served only.
(defun fn-owner-served-post-word (word detail state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pa-served-post-word word detail)))

; PRF-099: the carried usage of the boundary whose release evidence is
; EVIDENCE (a string), from the owner's (K . TALLY) cache over the committed
; records, advanced over the records committed since through the synced
; history stobj (`fn-hist-usage-carried', which under R is
; books/peer-carriage.lisp's fn-pcb-usage-extend,
; fn-hist-usage-carried-is-usage-extend, so fn-pcb-extended-cache-is-valid
; keeps the stored cache valid).  Reset at open (fn-owner-install-profile).
(defun fn-owner-carried-usage (evidence fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let* ((s (fn-owner-store state))
         (fn-hist (fn-hist-sync (fn-sn-files s) fn-hist))
         (cache (if (boundp-global 'fn-owner-carried-usage state)
                    (f-get-global 'fn-owner-carried-usage state)
                  nil))
         (tally (fn-hist-usage-carried cache s fn-hist))
         (state (f-put-global 'fn-owner-carried-usage
                              (cons (fn-hist-count fn-hist) tally) state)))
    (mv (fn-pcb-tally-get evidence tally) fn-hist state)))

; D23 and PRF-099: the carried arm's kind-4 event, for the NNTP transit
; attempt only, gated by the delivering boundary's opaque-carriage budget
; over its carried usage (books/peer-carriage.lisp fn-pcb-carried-event):
; the event, (:refused REASON) naming the exhausted bound, or nil.  No
; primitive observation is taken or claimed.
(defun fn-owner-peer-carried-relay-event
    (coordinates msgid received group-codes obligation subject evidence charge
                 fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes
                  (fn-state-groups (fn-node-acceptance (fn-sn-node s)))))
         (evidence-string (fn-store-octets->string evidence)))
    (mv-let (usage fn-hist state) (fn-owner-carried-usage evidence-string fn-hist state)
      (mv nil
       (if (equal groups :bad) nil
         (fn-pcb-carried-event
          (first coordinates) (second coordinates) (third coordinates)
          (fn-store-octets->string msgid) received groups
          (fn-store-octets->string obligation)
          (fn-store-octets->string subject)
          evidence-string charge
          (fn-sn-keyring-snapshots s)
          (fn-owner-transit-carried-list t state)
          (fn-own-clock (fn-owner-core state))
          (if (boundp-global 'fn-owner-transit-budget state)
              (f-get-global 'fn-owner-transit-budget state)
            nil)
          usage))
       fn-hist state))))

; PRF-099: the refusal class of a present carrier on transit
; (books/peer-carriage.lisp fn-pcb-refusal-class): :no-local-binding,
; :unsupported-profile, :signature-failed or :malformed, or nil.  ED and ML
; are the host's two primitive outcomes (nil when not observed).
; PKT-240: through the seven-class verdict, whose refusal arm is
; fn-pcb-refusal-class on every input
; (fn-pcb-admission-verdict-refusal-arms-are-the-refusal-class).
(defun fn-owner-transit-refusal-class (received transitp ed ml state)
  (declare (xargs :stobjs state :mode :program))
  ;; PKT-433 (d): (CLASS VERDICT) (fn-pcb-transit-refusal-detail), or nil.
  ;; fn-apc-transit-refusal-detail-is-reference (books/owner-parse-carried).
  (value (fn-apc-transit-refusal-detail
          received (fn-sn-keyring-snapshots (fn-owner-store state))
          (fn-owner-transit-carried-list transitp state) ed ml
          (fn-owner-parse-carry state))))

; PKT-473 (PRF-184): an accepted transit arm's verdict
; (books/peer-carriage.lisp fn-pcb-transit-verdict) under the same keyring
; snapshots and carried list as fn-owner-peer-carrier-plan, read before the
; kind-4 commit.
(defun fn-owner-transit-verdict (received transitp ed ml state)
  (declare (xargs :stobjs state :mode :program))
  ; fn-apc-transit-verdict-is-reference (books/owner-parse-carried.lisp).
  (value (fn-apc-transit-verdict
          received (fn-sn-keyring-snapshots (fn-owner-store state))
          (fn-owner-transit-carried-list transitp state)
          (and transitp t) ed ml (fn-owner-parse-carry state))))

(defun fn-owner-peer-carried-event
    (coordinates msgid received group-codes obligation subject evidence charge
                 observed-ml-key ed-observation ml-observation state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes
                  (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (value
     (if (equal groups :bad) nil
       (fn-pa-authorized-event
        (first coordinates) (second coordinates) (third coordinates)
        (fn-store-octets->string msgid) received groups
        (fn-store-octets->string obligation)
        (fn-store-octets->string subject)
        (fn-store-octets->string evidence) charge
        (fn-sn-keyring-snapshots s)
        observed-ml-key ed-observation ml-observation
        ;; Read the owner clock directly: fn-owner-clock-observation is an
        ;; error triple, and ACL2 refuses it where one value is required
        ;; (the 9c344d1d image build, native-build-production.log:8292).
        (fn-own-clock (fn-owner-core state)))))))

;; PRF-098: the revoked arm's kind-4 event (fn-pa-revoked-event), for the
;; NNTP transit attempt only, with both primitive observations the host made
;; over the carrier's keys (the keys this node once enrolled for the
;; principal).
(defun fn-owner-peer-revoked-event
    (coordinates msgid received group-codes obligation subject evidence charge
                 observed-ml-key ed-observation ml-observation state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes
                  (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (value
     (if (equal groups :bad) nil
       (fn-pa-revoked-event
        (first coordinates) (second coordinates) (third coordinates)
        (fn-store-octets->string msgid) received groups
        (fn-store-octets->string obligation)
        (fn-store-octets->string subject)
        (fn-store-octets->string evidence) charge
        (fn-sn-keyring-snapshots s)
        observed-ml-key ed-observation ml-observation
        (fn-own-clock (fn-owner-core state)))))))

;; PRF-098: the key-statement executor (books/key-statements.lisp), run by
;; the owner after it committed a kind-4 statement composite EVENT.  The
;; request names the primitive observation the host must make (the PoP's
;; D09 subject), or nil; the plan and event are ACL2's.  ROWS are the live
;; configuration's authorities rows (C2).
(defun fn-owner-key-statement-request (event state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-pop-request event)))

;; Lane ack-before-barrier (books/owner-ack-after-barrier.lisp): whether the
;; committed kind-4 composite EVENT carries a key statement, whose commit the
;; owner fences before its crash cut and its executor run
;; (host/native/owner.lisp fnn-owner-statement-committed).  KEYSTONE
;; fn-oab-plan-only-after-the-fence: the executor decides only such events.
(defun fn-owner-statement-fence (event state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-oab-fence-before-change event)))

;; The grants a statement is decided under (books/key-statements.lisp
;; fn-ks-statement-rows): at acceptance the live configuration's; at open
;; (AT-OPEN, the newest-record recovery) the configuration in force at the
;; statement's own txid, the fold of the Store's configuration journal
;; (fn-ks-recover-recorded; PRF-124, PRF-140).  The reopen is recorded by
;; definition: there is no policy switch.
(defun fn-owner-key-statement-rows (event at-open state)
  (declare (xargs :stobjs state :mode :program))
  (fn-ks-statement-rows event at-open
                        (fn-cfg-authorities (fn-cfg-value (fn-owner-config state)))
                        (fn-sn-config-history (fn-owner-store state))))

(defun fn-owner-key-statement-plan
    (event observed-ml-key ed-observation ml-observation at-open state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-plan event (fn-sn-keyring-snapshots (fn-owner-store state))
                     (fn-owner-key-statement-rows event at-open state)
                     observed-ml-key ed-observation ml-observation)))

(defun fn-owner-key-statement-event
    (event observed-ml-key ed-observation ml-observation coordinates at-open
           state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-execute event (fn-sn-keyring-snapshots (fn-owner-store state))
                        (fn-owner-key-statement-rows event at-open state)
                        observed-ml-key ed-observation ml-observation
                        (first coordinates) (second coordinates)
                        (third coordinates))))

(defun fn-owner-key-statement-log-line (plan outcome at-open state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-log-line plan outcome at-open)))

;; PRF-098, the crash cut: the open's recovery (books/key-statements.lisp
;; fn-ks-recover) executes the newest Store record when it is a statement.
;; OCTETS are that record as the open read it; the answer is the decoded
;; event for fnn-owner-key-statement, or nil.
(defun fn-owner-key-statement-pending (octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (let ((records (fn-store-decode-records (list octets))))
    (value (if (and (consp records) (null (cdr records)))
               (fn-ks-pending (car records))
             nil))))

;; PRF-166 (PKT-325): `keys redecide MSGID' (books/key-statements.lisp
;; fn-ks-find-statement, fn-ks-redecide-plan, fn-ks-redecide-event).  The
;; stored statement MSGID (octets) names among the Store's records, or nil;
;; its plan and kind-3 event under the Store's keyring now and the live
;; configuration's grants -- the configuration in force at the redecide's own
;; txid (fn-ks-redecide-decides-under-the-configuration-at-its-own-txid).
;; Called by host/native/keys.lisp fnn-keys-owner-redecide under the owner
;; mutex; the host observes, commits and logs.
(defun fn-owner-key-statement-redecide-find (msgid state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-find-statement
          (fn-store-octets->string msgid)
          (fn-sf-records (fn-sn-files (fn-owner-store state))))))

(defun fn-owner-key-statement-redecide-plan
    (event observed-ml-key ed-observation ml-observation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-redecide-plan event
                              (fn-sn-keyring-snapshots (fn-owner-store state))
                              (fn-owner-key-statement-rows event nil state)
                              observed-ml-key ed-observation ml-observation)))

(defun fn-owner-key-statement-redecide-event
    (event observed-ml-key ed-observation ml-observation coordinates state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-redecide-event event
                               (fn-sn-keyring-snapshots (fn-owner-store state))
                               (fn-owner-key-statement-rows event nil state)
                               observed-ml-key ed-observation ml-observation
                               (first coordinates) (second coordinates)
                               (third coordinates))))

(defun fn-owner-key-statement-redecide-log-line (plan outcome state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-redecide-log-line plan outcome)))

;; D27: the signed composite against the profile the owner was handed at
;; open (books/store-budget-naming.lisp fn-sbud-signed-event-boundary):
;; :ok, :event (no composite formed) or :signed-record (past its R).
(defun fn-owner-signed-event-boundary (event state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sbud-signed-event-boundary (fn-owner-store-profile state) event)))

(defun fn-owner-article-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-state-articles (fn-node-acceptance (fn-owner-node state))))))

; The local-post provenance from the owner's canonical live configuration.
; The native service cannot call fn-store-prov-post: that wrapper reads the
; standalone store bridge's shadow configuration and would stay stale after
; an owner reconfiguration.  This is the same ACL2 construction over the
; configuration that owns the acceptance decision.
(defun fn-owner-prov-post (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((cfg (fn-owner-config state))
         (identity (fn-cfg-policy (fn-cfg-value cfg) "path-identity"))
         (principal (if (and (stringp identity) (not (equal identity "")))
                        identity
                      "local"))
         (p (fn-prov-make-post principal (fn-cfg-generation cfg))))
    (value (fn-record-string-octets
            (if (fn-prov-durablep p) (fn-prov-wire p) (fn-prov-render p))))))

(defun fn-owner-existing-action (msgid-octets payload group-codes fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((groups (fn-store-groups-from-codes
                 group-codes
                 (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))
    (if (or (not (fn-pfld-lookup-inputsp msgid-octets groups))
            (not (fn-octet-listp payload)))
        (value :absent)
      ; fn-store-existing-action-is-the-verdict-over-alpha.
      (let ((action (fn-store-existing-action
                     (fn-store-octets->string msgid-octets) payload groups
                     (fn-owner-store state) fn-arena)))
        (value (if action action :absent))))))

; The same question with the submitted payload in the octet buffer
; (books/octets-stobj.lisp): host/native/owner.lisp fnn-owner-attempt fills
; the buffer once from the byte vector the owner handed back and asks this
; and fn-owner-prepare-buffer over it, so the payload is not consed into a
; list for either.  The decision is fn-pidx-existing-action
; (books/post-identity-index.lisp), equal to the Store's entry
; fn-store-existing-action (fn-pidx-existing-action-is-store-existing-action),
; which is the tombstone-aware fn-rcl-action-over over ALPHA of the Store's
; articles (fn-store-existing-action-is-the-verdict-over-alpha), itself
; fn-pb-action-over wherever the held payload is not a tombstone
; (fn-rcl-action-over-is-pb-without-a-tombstone);
; the list entry's fn-octet-listp test is the buffer's recognizer
; (fn-pbb-buffer-is-octet-listp).
(defun fn-owner-existing-action-buffer (msgid-octets group-codes fn-octets fn-arena state)
  (declare (xargs :stobjs (fn-octets fn-arena state) :mode :program))
  (let ((groups (fn-store-groups-from-codes
                 group-codes
                 (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))
    (if (not (fn-pfld-lookup-inputsp msgid-octets groups))
        (value :absent)
      ; PRF-191: D25's buffer verdict through the view trie
      ; (fn-pidx-existing-action-is-store-existing-action).
      (let ((action (fn-pidx-existing-action
                     (fn-store-octets->string msgid-octets) fn-octets groups
                     (fn-owner-core state) fn-arena)))
        (value (if action action :absent))))))

; The subject identity of the payload in the octet buffer is
; books/sha256-buffer.lisp fn-shb-subject-id-bounded, which host/native/io.lisp
; fnn-subject-id-buffer calls directly: a guard-verified entry, so no :program
; wrapper here reaches the digest's local stobj updaters (qual-e747dbcc A4).

; -----------------------------------------------------------------------------
; Connections

(defun fn-owner-version (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-view-version (fn-own-view (fn-owner-core state)))))

(defun fn-owner-conn-version (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))))
    (value (if conn (fn-own-conn-version conn) nil))))

(defun fn-owner-connection-versions (conns)
  (declare (xargs :mode :program))
  (if (consp conns)
      (cons (fn-own-conn-id (car conns))
            (cons (fn-own-conn-version (car conns))
                  (fn-owner-connection-versions (cdr conns))))
    nil))

(defun fn-owner-connections (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-connection-versions
          (fn-own-conns (fn-owner-core state)))))

; The host's re-entry after the TLS handshake (RFC 4642 section 2.2.2).  It
; is a wire event, not octets: no client input produces it, and
; fn-auth-step is the only thing that reads it.
(defun fn-owner-tls-established (id fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((owner (fn-owner-core state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-ocfg-read-step (fn-owner-ocfg state)
                                        id (list :tls-established) fn-arena))
             (state (fn-owner-install-ocfg (cdr result) state))
             (state (fn-owner-install-effects (car result) state)))
        (value :ok)))))

; Open pins the committed view and opens one served connection over it
; (fn-own-open); the greeting is the effect list it returns.  A refused open
; (bound reached) installs no connection and returns NIL so the host closes
; the socket without a reply.
; PKT-828 (books/owner-reader-view.lisp).  The reader views the committer
; captured: nil (none held: readers read the working view), (D) or (D N).
(defun fn-owner-reader-views (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-reader-views state)
      (f-get-global 'fn-owner-reader-views state)
    nil))

; The committer's capture at EVENT (:start before a START's drain, :next
; before a START-NEXT's, :unnext when that START-NEXT took nobody, :complete
; after a COMPLETE's replies, :drop when a START took nobody or the owner
; stops): fn-ocv-capture of the owner's working view.  Answers whether a
; capture is held after it.
(defun fn-owner-reader-views-capture (event state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((views (fn-ocv-capture (fn-owner-reader-views state) event
                                (fn-own-view (fn-owner-core state))))
         (state (f-put-global 'fn-owner-reader-views views state)))
    (value (if (consp views) t nil))))

; A reader entry at the reader view: while a capture is held the entry runs
; on the owner with the reader view in place of the working view
; (fn-ocfg-at-reader-view; fn-ocl-relation-of-a-view-captured-before-appends:
; a related owner, whose reads are the served machine's over at most the
; records the Store held at the capture), and the working view is put back
; after it (fn-ocfg-with-view).  Only the view is exchanged: the connections,
; the queue a POST joins and every other field are the entry's.
(defun fn-owner-at-reader-view (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((views (fn-owner-reader-views state)))
    (if (consp views)
        (fn-owner-install-ocfg (fn-ocfg-at-reader-view (fn-owner-ocfg state) views)
                               state)
      state)))

(defun fn-owner-at-working-view (working state)
  (declare (xargs :stobjs state :mode :program))
  (if (consp (fn-owner-reader-views state))
      (fn-owner-install-ocfg (fn-ocfg-with-view (fn-owner-ocfg state) working) state)
    state))

(defun fn-owner-open-at (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-core state))
         (id (fn-own-next-id before))
         ; fn-ocar-ocfg-open (books/owner-open-carried.lisp) is fn-ocfg-open
         ; under the configured owner's relation
         ; (fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation): the greeting
         ; takes the view archive's fn-statep, the store node's
         ; fn-node-statep and the configuration's fn-cfgp from the relation
         ; instead of evaluating them per connection (PKT-455 (1)).
         (opened (fn-ocar-ocfg-open (fn-owner-ocfg state)
                                    (fn-owner-auth state)))
         (state (fn-owner-install-ocfg (cdr opened) state))
         (state (fn-owner-install-effects (car opened) state))
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-connection-line (fn-owner-core state)
                                                       id nil)
                              state)))
    (if (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))
        (value id)
      (value nil))))

(defun fn-owner-open (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((working (fn-own-view (fn-owner-core state)))
         (state (fn-owner-at-reader-view state)))
    (mv-let (erp val state)
      (fn-owner-open-at state)
      (let ((state (fn-owner-at-working-view working state)))
        (mv erp val state)))))


; One observed socket region is one ACL2 prefix transition.  Its effects and
; configured-owner state equal fn-ocfg-read over the prefix it consumed
; (fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix); fn-owner-consumed names the exact
; physical prefix.  The prefix ends early after a STARTTLS 382, a closed wire,
; or (PKT-600, PRF-213) the octet that completed a submission: the host then
; commits and answers it and feeds the rest of the region as the next read.  The native adapter leaves any suffix for the TLS record
; layer instead of parsing STARTTLS in raw Lisp.
; The call is fn-scar-ocfg-read-tls-prefix (books/owner-served-carried.lisp),
; which equals fn-ocfg-read-tls-prefix under the configured owner's relation
; (fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation): it takes the
; store node's fn-node-statep from that relation instead of re-evaluating it,
; O(N^2) in the archive, four times per read.  It also passes the owner
; view's Message-ID trie to the peer step, so an IHAVE/CHECK duplicate test is
; one trie lookup instead of a scan of the node's articles and bindings
; (books/peer-offer-indexed.lisp, fn-pix-history-hasp-is-peer-history-hasp);
; the trie premise fn-scar-view-indexedp is carried by every owner transition
; (books/owner-offer-indexed.lisp).  A peer session's events run
; fn-pgc-peer-arm (books/peer-guard-carried.lisp, D24), whose guard names no
; node recognizer, so no peer event evaluates fn-node-statep either
; (fn-pgc-peer-arm-is-peer-step-pinned).
;; -----------------------------------------------------------------------------
;; PRF-161: the limits of a public reader port (books/public-exposure.lisp).
;;
;; The exposure state lives in `fn-owner-exposure', beside the configured
;; owner, and only fn-exp- functions change it.  The limits are read from the
;; LIVE configuration at every call (fn-exp-limits), so a `policy set' the
;; owner published is in force for the next accept and the next step; no
;; connection is closed by it (fn-exp-limits-never-drop-a-connection).  The
;; host passes the kernel's source address, the connection id and nothing it
;; computed; the clock is the owner's current observation, which the host
;; advanced just before (fnn-owner-advance-clock).

(defun fn-owner-exposure-state (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-exposure state)
      (f-get-global 'fn-owner-exposure state)
    (fn-exp-initial)))

(defun fn-owner-exposure-publicp (state)
  (declare (xargs :stobjs state :mode :program))
  (and (boundp-global 'fn-owner-exposure-public state)
       (f-get-global 'fn-owner-exposure-public state)))

(defun fn-owner-exposure-now (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-clock-monotonic (fn-own-clock (fn-owner-core state))))

(defun fn-owner-exposure-limits (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-exp-limits (fn-cfg-value (fn-owner-config state))
                 (fn-own-max-conns (fn-owner-core state))
                 (fn-owner-exposure-publicp state)
                 (fn-auth-config-requiredp (fn-owner-auth state))))

;; The octets one served step may read (books/connection-budget.lisp
;; fn-cbud-step-read-octets): 512 under a step rate, 4 KiB without one.
;; host/native/owner.lisp fnn-owner-refresh-read-octets reads it under the
;; owner mutex after the exposure install and after every served step, so a
;; live change of the rate reaches the next read.
(defun fn-owner-read-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cbud-step-read-octets (fn-owner-exposure-limits state))))

;; Once per run, after recovery and before listen: the listener the owner is
;; about to bind (FAMILY, ADDRESS-LIST as ACL2 projected them) decides the
;; defaults of every absent row.
;; NNT-041: several listeners.  The node is public when any listener is
;; (fn-exp-address-publicp decides each).
(defun fn-owner-exposure-projections-publicp (projections)
  (declare (xargs :mode :program))
  (and (consp projections)
       (or (fn-exp-address-publicp (car (car projections)) (cadr (car projections)))
           (fn-owner-exposure-projections-publicp (cdr projections)))))

(defun fn-owner-exposure-install-set (projections state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((publicp (fn-owner-exposure-projections-publicp projections))
         (state (f-put-global 'fn-owner-exposure (fn-exp-initial) state))
         (state (f-put-global 'fn-owner-exposure-close nil state))
         (state (f-put-global 'fn-owner-exposure-public publicp state)))
    (value (if publicp :public :loopback))))

(defun fn-owner-exposure-install (family address state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-exposure (fn-exp-initial) state))
         (state (f-put-global 'fn-owner-exposure-close nil state))
         (state (f-put-global 'fn-owner-exposure-public
                              (fn-exp-address-publicp family address) state)))
    (value (if (fn-exp-address-publicp family address) :public :loopback))))

;; The accept.  PEER-OCTETS is fn-owner-peer-for-socket-address's answer.
;; The result is the new connection id, or NIL; `fn-owner-output' holds the
;; greeting, or the 400 a refused connection is sent before it is closed
;; (`fn-owner-closep' is then T).
(defun fn-owner-exposure-open (family address peer-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let* ((peer (and peer-octets (fn-store-octets->string peer-octets)))
         (peer (if (equal peer :bad) nil peer))
         (before (fn-owner-core state))
         (id (fn-own-next-id before))
         ; fn-ocar-exp-open is fn-exp-open under the configured owner's
         ; relation (fn-ocar-exp-open-is-exp-open-under-ocl-relation,
         ; books/owner-open-carried.lisp): its reader arm opens through
         ; fn-ocar-ocfg-open, which evaluates no whole-state recognizer.
         (r (fn-ocar-exp-open (fn-owner-ocfg state) (fn-owner-exposure-state state)
                         (fn-owner-exposure-limits state) (fn-owner-auth state)
                         peer (cons family address)
                         (fn-owner-exposure-now state)))
         (state (fn-owner-install-ocfg (fn-exp-open-ocfg r) state))
         (state (f-put-global 'fn-owner-exposure (fn-exp-open-state r) state)))
    (if (fn-exp-open-id r)
        (let* ((state (fn-owner-install-effects (fn-exp-open-effects r) state))
               (state (f-put-global 'fn-owner-log-line
                                    (fn-olog-connection-line
                                     (fn-owner-core state) id
                                     (and peer peer-octets))
                                    state)))
          (value (fn-exp-open-id r)))
      (let* ((state (f-put-global 'fn-owner-effects nil state))
             (state (f-put-global 'fn-owner-output
                                  (fn-exp-open-refusal r) state))
             (state (f-put-global 'fn-owner-closep
                                  (and (fn-exp-open-refusal r) t) state))
             (state (f-put-global 'fn-owner-starttlsp nil state))
             (state (f-put-global 'fn-owner-submittedp nil state)))
        (value nil)))))

;; Before a served step: :proceed, or the milliseconds to wait.
(defun fn-owner-exposure-charge (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((r (fn-exp-charge (fn-owner-exposure-state state)
                           (fn-owner-exposure-limits state) id
                           (fn-owner-exposure-now state)))
         (state (f-put-global 'fn-owner-exposure (cdr r) state)))
    (value (if (equal (car r) :proceed) :proceed (cadr (car r))))))

;; After a served step (fn-owner-chunk below): `fn-owner-exposure-close'
;; holds the 400 the host appends before it closes, or NIL.  The step's
;; EFFECTS go in, not its reply octets: fn-exp-observe-effects is
;; fn-exp-observe of (fn-served-reply-octets effects)
;; (fn-exp-observe-effects-unfolds) and scans the effects in constant stack
;; without building that list (books/public-exposure-reply.lisp; PKT-481).
(defun fn-owner-exposure-observe (id effects consumed state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((conn (fn-own-find-conn id (fn-own-conns (fn-owner-core state))))
         (subject (and conn (fn-auth-session-subject (fn-own-conn-session conn))))
         (r (fn-exp-observe-effects (fn-owner-exposure-state state)
                                    (fn-owner-exposure-limits state) id
                                    (fn-owner-exposure-now state)
                                    effects consumed subject
                                    (and (fn-served-submission effects) t)))
         (state (f-put-global 'fn-owner-exposure (cdr r) state))
         (state (f-put-global 'fn-owner-exposure-close
                              (if (consp (car r)) (cadr (car r)) nil) state)))
    state))

;; On a receive timeout: :keep or :close (RFC 3977 3.1: close, send nothing).
(defun fn-owner-exposure-idle (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((r (fn-exp-idle (fn-owner-exposure-state state)
                         (fn-owner-exposure-limits state) id
                         (fn-owner-exposure-now state)))
         (state (f-put-global 'fn-owner-exposure (cdr r) state)))
    (value (car r))))

(defun fn-owner-exposure-release (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-exposure
                             (fn-exp-release (fn-owner-exposure-state state) id)
                             state)))
    (value :released)))

;; The lines `health' appends (host/native-live-status-host.lisp).
;; PRF-211: the capacity and the count, the last line of `status'.
(defun fn-owner-exposure-capacity (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-exp-capacity-line (fn-owner-exposure-limits state)
                        (len (fn-own-conns (fn-owner-core state)))))

(defun fn-owner-exposure-health (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-exp-health-lines (fn-owner-exposure-state state)
                       (fn-owner-exposure-limits state)
                       (len (fn-own-conns (fn-owner-core state)))
                       (fn-owner-exposure-now state)))

(defun fn-owner-chunk (id octets fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((owner (fn-owner-core state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-scar-ocfg-read-tls-prefix
                      (fn-owner-ocfg state) id octets fn-arena))
             (state (fn-owner-install-ocfg
                     (fn-own-tls-result-owner result) state))
             (state (fn-owner-install-served-effects
                     (fn-own-tls-result-effects result) state))
             (state (f-put-global 'fn-owner-consumed
                                  (fn-own-tls-result-consumed result) state))
             ; PRF-161: progress, failed logins and submissions of this step.
             (state (fn-owner-exposure-observe
                     id (fn-own-tls-result-effects result)
                     (fn-own-tls-result-consumed result) state))
             ; One line per 441 the effects send (books/owner-log.lisp
             ; fn-olog-served-refusal-lines-one-per-441).
             (state (f-put-global 'fn-owner-refusal-lines
                                  (fn-olog-served-refusal-lines
                                   (fn-owner-core state) id
                                   (fn-own-tls-result-effects result))
                                  state)))
        (value :ok)))))

; Step 8 (catalog slice): the read runs books/served-catalog-chain.lisp
; fn-scr-ocfg-read-span, the same chain with the catalog carried to the
; retrieval arms (fn-scr-ocfg-read-span-is-reference-under-ocl-relation);
; the paragraph below describes the carried read it equals.
; The same read over a range of the octet buffer (books/served-span.lisp;
; REP-012, PRF-181): host/native/owner.lisp fnn-owner-handle-chunk fills the
; buffer from the socket's byte vector and calls this with [start, end), so
; no octet of a read is ever a cons cell.  fn-scar-ocfg-read-span is
; fn-scar-ocfg-read-tls-prefix over (fn-oct-slice-list start end fn-octets)
; (fn-scar-ocfg-read-span-is-reference-under-ocl-relation).
;
; HST-023 (PRF-248; adapter-retirement-2's ServedStep, PKT-616 (b)): the
; result is ONE typed value, `fn-splan-step-make' of the step's effects, its
; close, STARTTLS and submission projections (fn-served-closingp,
; fn-served-starttlsp, fn-served-submission: what fn-owner-install-effects
; put in six globals), the consumed prefix, the refusal log lines and the
; exposure close.  No reply octets are built or rendered here: the effects
; are the render plan (books/served-plan.lisp), which the host renders into
; the connection's own buffer after the mutex is released.  The owner and
; exposure states are installed exactly as fn-owner-chunk installs them.
(defun fn-owner-chunk-span-at (id start end admit replies fn-octets fn-arena fn-cat state)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat state) :mode :program))
  (let ((owner (fn-owner-core state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (if (not (and (natp start) (natp end) (<= start end)
                    (<= end (fn-octets-len fn-octets))))
          (value :bad-range)
        ;; PKT-828: at the reader view while the committer holds a capture,
        ;; the working view put back after it (books/owner-reader-read.lisp
        ;; fn-orr-read-span; with no capture it is fn-scr-ocfg-read-span).
        ;; Lane time-model-2 (PRF-323): ADMIT is the disk's write admission
        ;; at this read's recorded time; while it sheds, the read runs with
        ;; posting not permitted, so a POST command is answered 440 before
        ;; its article (books/owner-time-admission.lisp fn-otm-read-span;
        ;; admitted it is fn-orr-read-span, fn-otm-read-span-when-admitted-
        ;; unfolds).  REPLIES is ACL2's pair of lines naming the disk's
        ;; reason (fn-otm-shed-replies), passed through unread.
        (let* ((result (fn-otm-read-span
                        (fn-owner-ocfg state) (fn-owner-reader-views state)
                        id start end admit replies fn-octets fn-arena fn-cat))
               (effects (fn-own-tls-result-effects result))
               (consumed (fn-own-tls-result-consumed result))
               (state (fn-owner-install-ocfg
                       (fn-own-tls-result-owner result) state))
               ; PRF-161: progress, failed logins and submissions of this step.
               (state (fn-owner-exposure-observe id effects consumed state)))
          (value (fn-splan-step-make
                  effects
                  (fn-served-closingp effects)
                  (fn-served-starttlsp effects)
                  (fn-served-submission effects)
                  consumed
                  ; One line per 441 the effects send (books/owner-log.lisp
                  ; fn-olog-served-refusal-lines-one-per-441).
                  (fn-olog-served-refusal-lines (fn-owner-core state) id effects)
                  (f-get-global 'fn-owner-exposure-close state))))))))

(defun fn-owner-chunk-span (id start end admit replies fn-octets fn-arena fn-cat state)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat state) :mode :program))
  (fn-owner-chunk-span-at id start end admit replies fn-octets fn-arena fn-cat state))

(defun fn-owner-close (id fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((state (fn-owner-step (list :close id) fn-arena state)))
    (value :closed)))

; The host-fault boundary (books/owner-fault.lisp).
;
; tools/run_owner.py calls this when it has caught an exception it did not
; expect while serving connection `id': the model decides the reply line, the
; close and everything that happens to the owner (`fn-own-fault'), and the
; host's only remaining decision is that it will not use that socket again.
; The result is installed through the same `fn-owner-install-effects' every
; other entry uses, so the host reads the reply out of `fn-owner-output' and
; the close out of `fn-owner-closep' exactly as it does for a served read.
;
; `:faulted' is answered when there was a connection to answer, `:unknown'
; when there was not; the owner has forgotten `id' either way.  The host
; reports the two differently because a fault naming no connection is a host
; defect and not a served event.
(defun fn-owner-fault (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (knownp (if (fn-own-find-conn id (fn-own-conns owner)) t nil))
         (result (fn-ocfg-fault (fn-owner-ocfg state) id))
         (state (fn-owner-install-ocfg (cdr result) state))
         (state (fn-owner-install-effects (car result) state)))
    (value (if knownp :faulted :unknown))))

(defun fn-owner-advance (id fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((state (fn-owner-step (list :advance id) fn-arena state)))
    (fn-owner-conn-version id state)))

; -----------------------------------------------------------------------------
; Clock observations and group facts

; The word is fn-own-observe-outcome's (books/owner.lisp; decision D10-a).
; This used to compare the owner before and after the event and answer
; :rejected whenever nothing moved, which spelled an ADMITTED reading equal
; to the one already held exactly like a contradicted clock, and put the
; decision in the host.  Nothing here judges a reading.
(defun fn-owner-observe (monotonic wall wall-error has-wall state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((obs (fn-clock-observation monotonic wall wall-error has-wall))
         (outcome (fn-own-observe-outcome (fn-owner-core state) obs))
         ; fn-ocfg-observe, not fn-owner-step: it is fn-ocfg-step's
         ; (:observe obs) arm (fn-ocfg-step-observe-is-fn-ocfg-observe,
         ; books/owner-config-observe.lisp) with guard t, so the reading the
         ; host takes before every socket read no longer evaluates the
         ; whole-store guard of the unverified fn-ocfg-step.
         (state (fn-owner-install-ocfg
                 (fn-ocfg-observe (fn-owner-ocfg state) obs) state)))
    (value outcome)))

(defun fn-owner-declare-group (name-octets fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (if (not (fn-pfld-group-name-requestp name-octets))
      (value :invalid)
    ; fn-pout-declare-group (books/owner-prepare-outcome.lisp): :declared
    ; exactly when its gate holds (KEYSTONE
    ; fn-pout-declare-group-answers-the-host-test).
    (mv-let (word next)
      (fn-pout-declare-group (fn-owner-ocfg state)
                             (fn-store-octets->string name-octets) fn-arena)
      (let ((state (fn-owner-install-ocfg next state)))
        (value word)))))

(defun fn-owner-group-facts (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-replay-facts (fn-own-facts (fn-owner-core state)))))

; -----------------------------------------------------------------------------
; The outbound feed (books/owner-feed.lisp; specs/peering.md 3, milestone 3)
;
; One outbound client connection per configured peer with work.  Every
; decision is the book's: which peers an article is offered to
; (fn-own-feed-targets), when an offer may go out (fn-feed-selection inside
; fn-feed-tick-step), what the offer line is (fn-feed-offer-line), what a
; reply code means (fn-feed-observe) and what the journal record for each is
; (fn-own-feed-*-record).  This file frames octets and moves them; it names
; no code, no wildmat, no Message-ID and no FNFD field.
;
; The order is "durable before the effect": every entry point below returns
; one FeedPublication (books/owner-results.lisp) whose sealed frame plan the
; host appends to <journal>/feed/<peer>.fnfd and fsyncs BEFORE it writes the
; publication's command bytes.

(defun fn-owner-feed-configure (fn-arena state)
  ; Rebuild the feed table from the live configuration: at open and after
  ; every :set-peer / :remove-peer delta.
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  ; Answers the peer names, a list of strings (the native host checks
  ; string-listp once and splits nothing).
  (let ((state (fn-owner-step (list :feeds (fn-owner-config state)) fn-arena state)))
    (value (fn-own-feed-names (fn-own-feeds (fn-owner-core state))))))

(defun fn-owner-feed-peers (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-feed-names (fn-own-feeds (fn-owner-core state)))))

(defun fn-owner-feed-record (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        nil
      (fn-own-feed-record-of peer (fn-own-feeds (fn-owner-core state))))))

; Where to dial: the peer record's transport row, read by ACL2.  The host
; does not parse the configuration.
(defun fn-owner-feed-host (peer-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (consp transport) (equal (car transport) :nntp))
               (fn-record-string-octets
                (if (equal (len transport) 5) (caddr transport)
                  (fn-cfg-ag-car (fn-cfg-ag-cdr transport))))
             nil))))

(defun fn-owner-feed-port (peer-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (consp transport) (equal (car transport) :nntp))
               (nfix (if (equal (len transport) 5) (cadddr transport)
                       (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr transport)))))
             0))))

(defun fn-owner-feed-security (peer-octets state)
  "ACL2-owned outbound security tuple; old records are clear by definition."
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (equal (car transport) :nntp) (equal (len transport) 5))
               (car (cddddr transport))
             '(:clear)))))

(defun fn-owner-feed-auth-policy (peer-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (value (fn-cfg-peer-outbound-auth
          (fn-owner-feed-record peer-octets state))))

(defun fn-owner-feed-profile-decode (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-fap-decode octets))

(defun fn-owner-feed-profile-max-octets ()
  (declare (xargs :mode :program))
  *fn-fap-max-octets*)

(defun fn-owner-feed-streamingp (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (fn-cfg-peer-streamingp (fn-owner-feed-record peer-octets state))
             t
           nil)))

; How long the host must wait between dial attempts for this peer: the peer
; record's own outbound backoff.  Read here so the NUMBER stays ACL2's; the
; host only measures the interval with the clock it already owns.
;
; Without it the host dialled on queue length alone, and the feed machine's
; backoff does not gate a dial (it gates `fn-feed-selection`, which needs a
; connection first).  A peer that was down therefore drew a fresh TCP
; connection about five times a second for as long as one entry stayed
; queued: 9,479 refused connections in one two-node gate run, all of them in
; the window where one node was restarting.
(defun fn-owner-feed-backoff-ms (peer-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let ((record (fn-owner-feed-record peer-octets state)))
    (value (if (and record (natp (fn-cfg-peer-backoff record)))
               (fn-cfg-peer-backoff record)
             0))))

; Is there an entry this feed could OFFER if it had a connection: a
; `:queued` one, which is what `fn-feed-selection` picks.  Queue length is
; not that question -- an entry in flight is in the queue -- and answering
; the wrong one is what made a peer that lost a reply a denial of service:
; the entry stayed `:sent`, the host re-dialled on queue length alone every
; few seconds, each dial took a connection on the peer that the peer did not
; release, and the peer reached its `--max-connections` bound and began
; refusing EVERY client at accept.  Measured on two-node gate `a5c6792`:
; seven tap sessions, `MODE STREAM` and nothing else in each, and node B
; closing the harness's reader probes for the next 90 s.
;
; This does not resolve the in-flight entry -- only a restart does today,
; and the packet that fixes it is in the lane handoff.  It stops the host
; opening a socket it has nothing to send on.
(defun fn-owner-feed-stopped (state)
  "The owner process's feed stop table (peer . reason), nil before any stop."
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-feed-stopped state)
      (f-get-global 'fn-owner-feed-stopped state)
    nil))

(defun fn-owner-feed-has-queued (peer-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      ;; A peer the owner stopped (it refused MODE STREAM, books/
      ;; feed-connection.lisp) is not dialled, whatever it has queued.
      (value (fn-fc-dial-allowedp
              (fn-feed-head-queued
               (fn-feed-queue
                (fn-own-feed-find peer (fn-own-feeds
                                        (fn-owner-core state)))))
              peer
              (fn-owner-feed-stopped state))))))

(defun fn-owner-feed-queue-length (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value 0)
      (value (len (fn-feed-queue
                   (fn-own-feed-find peer (fn-own-feeds
                                           (fn-owner-core state)))))))))

; A raw TCP descriptor starts in the ACL2 connection phase below.  Only a
; successful greeting (and configured MODE STREAM exchange) makes this feed
; live for selection.  FORM is ACL2's (`fn-fc-connection-form' of the ready
; connection state): :ihave after a 500/501 to MODE STREAM (PRF-207), so the
; feed offers this connection IHAVE; nil otherwise.
(defun fn-owner-feed-connect (peer-octets conn form fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (or (equal peer :bad) (not (natp conn)))
        (value nil)
      (let ((state (fn-owner-step (list :feed-conn peer conn form) fn-arena state)))
        (value :ok)))))

(defun fn-owner-feed-dial-open (peer-octets conn user pass allow-clear state)
  "Install greeting/MODE state without treating a TCP socket as a feed.

FN-OWNER-RECOVER installs the carried table invariant, and this is its only
constructor thereafter.  It deliberately does not rescan every peer/framer on
a dial: the selected peer entry is the owner-feed boundary being opened."
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp peer-octets)))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (or (equal peer :bad) (not (natp conn)))
        (value :invalid)
      (let* ((inputs (f-get-global 'fn-owner-feed-inputs state))
             (entry (fn-own-feed-entry-of peer
                                          (fn-own-feeds (fn-owner-core state)))))
        (if (null entry)
            (value :fault)
          (let* ((streamingp (fn-cfg-peer-streamingp
                               (fn-own-feed-entry-record entry)))
                 (transport (fn-cfg-peer-transport (fn-own-feed-entry-record entry)))
                 (security (if (equal (len transport) 5)
                               (let ((s (car (cddddr transport))))
                                 (if (equal s '(:clear)) :clear (cadr s)))
                             :clear))
                 (state (f-put-global
                         'fn-owner-feed-inputs
                         (fn-fc-table-put
                          peer
                          (if user
                              (fn-fc-initial-auth-state streamingp conn security
                                                        user pass allow-clear)
                            (fn-fc-initial-state streamingp conn security))
                          inputs)
                         state)))
            (value (if (equal security :implicit) :await-tls :await-greeting))))))))

(defun fn-owner-feed-tls-established (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((peer (fn-store-octets->string peer-octets))
         (inputs (f-get-global 'fn-owner-feed-inputs state))
         (step (and (not (equal peer :bad))
                    (fn-fc-after-tls (fn-fc-table-lookup peer inputs)))))
    (if (null step) (value (fn-owner-feed-word-publication :invalid nil nil))
      (let ((state (f-put-global 'fn-owner-feed-inputs
                                 (fn-fc-table-put peer (fn-fc-next-state step) inputs) state)))
        (value
         (case (fn-fc-kind step)
           (:mode (fn-owner-feed-word-publication :mode (fn-fc-mode-command) nil))
           (:auth-user
            (fn-owner-feed-word-publication
             :auth-user (fn-fc-auth-user-command (fn-fc-next-state step)) nil))
           (:ready (fn-owner-feed-word-publication :ready nil nil))
           (:need-input (fn-owner-feed-word-publication :need-input nil nil))
           (otherwise (fn-owner-feed-word-publication :invalid nil nil))))))))

(defun fn-owner-feed-read-limit ()
  "ACL2-owned upper bound for one native feed socket-read observation."
  (declare (xargs :mode :program))
  *fn-feed-wire-input-max-chunk-octets*)

; The raw socket layer enforces this one TCP completion deadline after DNS has
; produced an address.  It is deliberately a local ACL2 policy rather than a
; feed-service literal: a caller cannot silently widen an unavailable peer's
; attempt window.  DNS remains a separate host availability boundary.
(defconst *fn-owner-feed-connect-timeout-seconds* 10)

(defun fn-owner-feed-connect-timeout ()
  "ACL2-owned TCP completion deadline for one outbound peer dial."
  (declare (xargs :mode :program))
  *fn-owner-feed-connect-timeout-seconds*)

; One tick for one peer: the records first, then the bytes.
(defun fn-owner-feed-tick (peer-octets monotonic state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value (fn-owner-feed-word-publication nil nil nil))
      (let* ((owner (fn-owner-core state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (result (fn-own-feed-port-tick-peer
                      peer (fn-own-feeds owner) obs)))
        (mv-let (status publication state)
          (fn-owner-feed-install-port-result
           owner result
           (list (cons :accepted (if (fn-own-feed-port-effects result) :offer :idle))
                 (cons :refused :refused))
           nil state)
          (declare (ignore status))
          ;; fn-ofa-publication-command-words-have-octets: an :offer
          ;; reaches the host only with octets (books/owner-feed-article).
          (value (fn-ofa-publication publication)))))))

; One reply line from one peer.  The article of a 335/238 is the row's bytes
; read through the arena (books/owner-feed-article.lisp fn-ofa-feed-article,
; fn-ofa-feed-article-is-the-feed-article-over-alpha), never its handle.
(defun fn-owner-feed-octets (peer-octets line monotonic fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value (fn-owner-feed-word-publication nil nil nil))
      (let* ((owner (fn-owner-core state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (entry (fn-own-feed-entry-of peer (fn-own-feeds owner)))
             (feed (fn-own-feed-entry-feed entry))
             (msgid (fn-own-feed-inflight-msgid (fn-feed-queue feed)))
             (response (fn-own-feed-parse-response line msgid)))
        (if (null response)
            (value (fn-ores-feed-port-publication :quiet nil nil nil nil))
          (let ((result (fn-own-feed-port-observe-peer
                         peer (fn-own-feeds owner) response
                         ; The record's bytes by Message-ID: its handle
                         ; through the history stobj (R holds: the entry
                         ; fn-owner-feed-reply-chunk refreshed it)
                         ; (fn-apr-feed-article-is-own-feed-article,
                         ; books/acceptance-payload-ref.lisp) read through
                         ; the arena (fn-ofa-feed-article-is-the-feed-
                         ; article-over-alpha).  Since the records flip the
                         ; row holds a handle; handing it to the port sent
                         ; an empty command (lane feed-fault).
                         (fn-ofa-feed-article owner msgid fn-arena fn-hist) obs)))
            ; The sender's one line for this reply (nil for a 335/238),
            ; books/owner-log.lisp fn-olog-feed-reply-line, is the
            ; publication's log line.
            (mv-let (status publication state)
              (fn-owner-feed-install-port-result
               owner result
               (list (cons :accepted (if (fn-own-feed-port-effects result) :send :quiet))
                     (cons :refused :refused))
               (fn-olog-feed-reply-line owner peer response) state)
              (declare (ignore status))
              ;; fn-ofa-publication-command-words-have-octets: a :send
              ;; reaches the host only with octets; otherwise :unsendable,
              ;; its line naming the renderer's reason.
              (value (fn-ofa-publication publication)))))))))

(defun fn-owner-feed-connection-result-kind (step)
  "Map only a connection-phase refusal away from the feed-port outcome tag.

The feed port's :REFUSED means an ACL2 transition may have produced a fresh
FNFD record batch.  A greeting or MODE rejection produces no such batch, so
it is :CONNECTION-REFUSED and the raw adapter must close this peer without
flushing the previous peer's pending projection."
  (if (equal (fn-fc-kind step) :refused) :connection-refused (fn-fc-kind step)))

(defun fn-owner-feed-reply-chunk-synced (peer-octets octets monotonic fn-arena fn-hist state)
  "Consume one ACL2 connection/reply event; nil drains retained input.

Greeting and MODE replies stay inside fn-fc.  A normal feed reply reaches the
existing port only after fn-fc has made this connection ready."
  (declare (xargs :stobjs (state fn-arena fn-hist) :mode :program
                  :guard (and (fn-cbor-octet-listp octets)
                              (fn-cbor-octet-listp peer-octets))))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (or (equal peer :bad) (not (fn-wire-octet-listp octets)))
        (value (fn-owner-feed-word-publication :invalid nil nil))
      (let* ((inputs (f-get-global 'fn-owner-feed-inputs state))
             (input (fn-fc-table-lookup peer inputs)))
        ;; The table invariant is carried from recovery through only
        ;; put/remove.  This served path validates the selected connection,
        ;; never every peer's retained buffer.
        (if (not (fn-fc-statep input))
            (value (fn-owner-feed-word-publication :invalid nil nil))
          (let* ((step (fn-fc-step input octets))
                 (stop (fn-fc-streaming-refusal-p input step))
                 (kind (if stop :streaming-refused
                         (fn-owner-feed-connection-result-kind step)))
                 (stopped (fn-fc-stopped-put peer *fn-fc-stop-mode-stream-refused*
                                             (fn-owner-feed-stopped state)))
                 (state (if stop
                            (f-put-global 'fn-owner-feed-stopped stopped state)
                          state))
                 ; The stop's one line is the publication's log line.
                 (stop-line (and stop (fn-fc-stop-log-line peer)))
                 ;; PRF-207: a 500/501 to MODE STREAM goes on in IHAVE; the
                 ;; one line says so (no stop is recorded): the :ready
                 ;; publication's log line.
                 (fallback-line (and (fn-fc-ihave-fallback-p input step)
                                     (fn-fc-fallback-log-line peer)))
                 (state (f-put-global
                         'fn-owner-feed-inputs
                         (fn-fc-table-put peer (fn-fc-next-state step) inputs)
                         state)))
            (case kind
                  (:mode
                   (let ((command (fn-fc-mode-command)))
                     (value (if (null command) (fn-owner-feed-word-publication :fault nil nil)
                              (fn-owner-feed-word-publication :mode command nil)))))
                  (:auth-user
                   (let ((command (fn-fc-auth-user-command (fn-fc-next-state step))))
                     (value (if (null command) (fn-owner-feed-word-publication :fault nil nil)
                              (fn-owner-feed-word-publication :auth-user command nil)))))
                  (:auth-pass
                   (let ((command (fn-fc-auth-pass-command (fn-fc-next-state step))))
                     (value (if (null command) (fn-owner-feed-word-publication :fault nil nil)
                              (fn-owner-feed-word-publication :auth-pass command nil)))))
                  (:starttls
                   (let ((command (fn-fc-starttls-command)))
                     (value (if (null command) (fn-owner-feed-word-publication :fault nil nil)
                              (fn-owner-feed-word-publication :starttls command nil)))))
                  (:tls (value (fn-owner-feed-word-publication :tls nil nil)))
                  (:ready
                   (mv-let (erp word state)
                     (fn-owner-feed-connect peer-octets
                                            (fn-fc-conn (fn-fc-next-state step))
                                            (fn-fc-connection-form
                                             (fn-fc-next-state step))
                                            fn-arena state)
                     (if erp (mv erp word state)
                       (value (fn-owner-feed-word-publication (if (equal word :ok) :ready :fault) nil
                                                                (and (equal word :ok) fallback-line))))))
                  (:reply
                   (fn-owner-feed-octets peer-octets (fn-fc-line step)
                                         monotonic fn-arena fn-hist state))
                  (:streaming-refused
                   (value (fn-owner-feed-word-publication :streaming-refused nil stop-line)))
                  (:need-input
                   (value (fn-owner-feed-word-publication kind nil nil)))
                  ;; friend-path-2: a refused, closed or unreadable
                  ;; connection names why (books/peer-pull-session.lisp
                  ;; fn-peer-feed-failure-line): the publication's log line.
                  ((:connection-refused :closed :invalid)
                   (value (fn-owner-feed-word-publication
                           kind nil (fn-peer-feed-failure-line peer input step octets))))
                  (otherwise (value (fn-owner-feed-word-publication :fault nil nil))))))))))

; The feed reply entry: the history stobj refreshed against the owner's Store
; first (host/store-node-host.lisp fn-host-hist-sync; R by
; fn-hist-refresh-is-the-history), then the reply read through it.
(defun fn-owner-feed-reply-chunk (peer-octets octets monotonic fn-arena fn-hist state)
  (declare (xargs :stobjs (state fn-arena fn-hist) :mode :program
                  :guard (and (fn-cbor-octet-listp octets)
                              (fn-cbor-octet-listp peer-octets))))
  (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (mv-let (erp val state)
      (fn-owner-feed-reply-chunk-synced peer-octets octets monotonic fn-arena fn-hist state)
      (mv erp val fn-hist state))))


; The connection to ONE peer is gone.  The host reports the event and the
; time it happened; ACL2 decides what it means.  `fn-own-feed-lost-records'
; is read off the state BEFORE it moves and `fn-own-feed-lost' moves it, so
; the frame the host then appends is the one the transition authorized.
; There are no bytes: a lost connection emits no command, which is why the
; effects argument is nil.
;
; Before this entry point existed the host told the owner only
; `(:feed-conn peer nil)' and the in-flight entry stayed :sent until the
; PROCESS restarted -- the blocker in front of K5's restart-by-offer
; (planning/lanes/HANDOFF-w11-twonode-feed.md).  The requeue decision is
; `fn-feed-lost''s; the host decides only when to hand the model the event.
(defun fn-owner-feed-lost (peer-octets monotonic state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value (fn-owner-feed-word-publication nil nil nil))
      (let* ((inputs (f-get-global 'fn-owner-feed-inputs state))
             (owner (fn-owner-core state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (result (fn-own-feed-port-lost-peer
                      peer (fn-own-feeds owner) obs)))
        ;; Removal is the other carried-table transition; a lost peer has no
        ;; reason to revalidate unrelated live connections or suffixes.
        (mv-let (status publication state)
          (fn-owner-feed-install-port-result
           owner result '((:accepted . :ok) (:refused . :refused)) nil state)
          (declare (ignore status))
          (let ((state (f-put-global 'fn-owner-feed-inputs
                                     (fn-fc-table-remove peer inputs)
                                     state)))
            (value publication)))))))

; (The by-index readers fn-owner-feed-record-peers, fn-owner-feed-frames,
; fn-owner-feed-sealed-frame, fn-owner-feed-command and
; fn-owner-feed-command-status were retired with their globals: each feed
; step returns its FeedPublication, books/owner-results.lisp.)

; One bounded read from the physical journal. The scanner owns acceptance,
; the exact safe offset and the entry fed to the existing replay transition.
(defun fn-owner-feed-journal-scan (peer-octets prefix frame fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program
                  :guard (and (fn-cbor-octet-listp frame)
                              (fn-cbor-octet-listp peer-octets))))
  (let* ((peer (fn-store-octets->string peer-octets))
         (result (fn-feed-journal-scan peer-octets prefix frame
                   (f-get-global 'fn-owner-feed-safe-offset state))))
    (if (equal peer :bad)
        (value :invalid)
      (if (equal (car result) :next)
          (let* ((entry (nth 2 result))
                 (state (fn-owner-step
                         (list :feed-replay peer (list entry)) fn-arena state))
                 (state (f-put-global
                         'fn-owner-feed-intents
                         (fn-own-feed-intent-apply
                          (f-get-global 'fn-owner-feed-intents state)
                          (fn-feed-journal-kind entry)
                          (fn-feed-journal-values entry))
                         state))
                 (state (f-put-global 'fn-owner-feed-safe-offset
                                      (nth 1 result) state)))
            (value :next))
        (value (car result))))))

; The fence a process death owes every feed: one (:feed-restart peer) record
; per peer, durable, then fn-feed-restart on each.  fn-own-reopen does the
; restart; this is the record side and the entry point a recovering host
; calls once, after the replay and before any command.
(defun fn-owner-feed-restart (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (table (fn-own-feeds owner))
         (result (fn-own-feed-port-restart-fold
                  (fn-own-feed-names table) table table)))
    (mv-let (status publication state)
      (fn-owner-feed-install-port-result
       owner result '((:accepted . :restarted) (:refused . :refused)) nil state)
      (declare (ignore status))
      (value publication))))

; -----------------------------------------------------------------------------
; The NEWNEWS pull feed (PRF-100, books/peer-pull.lisp).  The pulled peers of
; the one live configuration, read by ACL2; host/native/pull-service.lisp
; drives each round through the pure fn-pull-* functions.
(defun fn-owner-pull-plans (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pull-plans (fn-cfg-peers (fn-cfg-value (fn-owner-config state))))))

; PRF-325: the peers this node catches up from (books/peer-catchup.lisp
; `fn-cu-plans'); host/native/pull-service.lisp drives each round.
(defun fn-owner-catchup-plans (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cu-plans (fn-cfg-peers (fn-cfg-value (fn-owner-config state))))))
