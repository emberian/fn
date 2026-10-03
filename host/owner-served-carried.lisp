; owner-served-carried.lisp -- the owner's carried relation over the host
; writers that are proved, relied on under a NAMED assumption for the rest
; (lane post-guard-off, 2026-10-03; ember: "we can just not have that guard").
;
; WHY.  Every owner entry on the POST path had the guard
; (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))), and the executable
; counterpart evaluates it on every call: a walk of the whole record log,
; the success keyset and the node (COST-GATE, image set 45e05c7fd: 92 ms and
; 11.8 MB per fn-owner-io call at 1000 articles, two calls per POST, linear
; in the store; about 9 s per call extrapolated to 100k).  The guard cannot
; be narrowed: every fn-sf step is (if (mbe :logic (fn-sf-statep s) :exec t)
; STEP s), which forces fn-sf-statep into every guard above it
; (planning/design/sf-statep-idiom-2026-10-03.md).  D40's raw dispatch is the
; way to skip it -- the guard-verified definition runs where its guard holds
; -- and needs a carried invariant that implies the guard and that every
; writer of the carried state preserves.
;
; WHAT IS PROVED.  fn-owner-retain-statep (books/owner-retain-transitions.lisp)
; implies each such guard (fn-owner-retain-statep-implies-entry-guard); it is
; established at the recovery install under A-RECOVERED-OPEN (the pilot row
; fn-owner-retain-carried, books/owner-retain-carried.lisp, whose open this
; row repeats verbatim and def-carried re-checks); and it is preserved by the
; thirteen writers listed as :transitions below: STAGE-5B's tier A
; (host/owner-retain-host.lisp, frozen at f98e1ff1b) and the pilot's three
; prepares.  def-carried generates each NAME-FN-carries statement from the
; world and proves it from the named theorem.
;
; WHAT IS TEMPORARILY TRUSTED AT NATIVE DISPATCH: A-OWNER-INVARIANT-CARRIED (specs/failures.md).  The carried
; state is the whole ACL2 state, so every host-called entry that returns
; state is a writer of it, and def-carried's completeness demands a
; preservation theorem for each.  The ones not yet proved are the :incomplete
; owed list below: the escape names them one by one, so a writer added later
; is refused at image build until it is proved or owed here, and a proved one
; must leave the list.  Most of them never write 'fn-owner or
; 'fn-owner-retain-carry (the only globals the relation reads), but
; most of them are :program and can carry no theorem at all; the
; carrier move (STAGE-5B, lane/stage-5b-carrier: the owner's state in its
; own stobj, so only its writers return it) is the principled replacement.
; The stable identifier is runtime trust, not a formal logical assumption.
; No encapsulate or whole-host invariant theorem is introduced for it.
; Each owed writer is a ledger item (planning/repair, category proof-owed).
;
; WHAT USES IT.  The entries host/interfaces.lisp declares
; `:raw-with (:carried fn-owner-served-carried :assuming
; A-OWNER-INVARIANT-CARRIED)'; books/definterface.lisp refuses that
; annotation unless the entry is a listed transition here and the assumption
; is the one this row names, and host/native/io.lisp prints each such entry
; at image build.  The developer selector FN_NATIVE_DISPATCH_COUNTERPART=1
; keeps the counterpart path (the whole guard evaluated) for comparison.
;
; Loaded by host/native/build.lisp after every ACL2-mode host file (the owed
; writers are defined by then) and before host/interfaces.lisp.

(in-package "ACL2")
(include-book "../books/definterface") ; def-carried, with the :incomplete escape
(include-book "../books/owner-retain-carried") ; the pilot row and its open

(def-carried fn-owner-served-carried
  :invariant fn-owner-retain-statep
  ; the pilot's open, verbatim (books/owner-retain-carried.lisp)
  :established ((fn-owner-install-extended
                 fn-owner-install-extended-establishes-when-recovering
                 :ok (equal (mv-nth 1 _) :recovering)
                 :hyps ((or (equal oc :fault) (fn-lgoc-invariantp oc)))
                 :produced ((fn-ock-recover-extended
                             fn-owner-recover-extended-produces-invariant
                             :assuming ((fn-assume-capture-extensionp extended configs)))
                            (fn-ock-install
                             fn-owner-store-open-install-produces-invariant
                             :assuming ((fn-assume-store-open-pairp replayed opened))))
                 :witness ((fn-owner-retain-witness-oc) nil (make-list 32 :initial-element 0)
                           (create-fn-arena$a) (create-fn-cat$a) (create-fn-hist$a)
                           (fn-owner-retain-witness-state))))
  :transitions (; the pilot's (books/owner-retain-carried.lisp)
                (fn-owner-prepare-identity fn-owner-prepare-identity-preserves-retain-state)
                (fn-owner-prepare-consumer fn-owner-prepare-consumer-preserves-retain-state)
                (fn-owner-prepare-topic fn-owner-prepare-topic-preserves-retain-state)
                ; STAGE-5B tier A (host/owner-retain-host.lisp)
                (fn-owner-io fn-owner-io-preserves-retain-state)
                (fn-owner-take fn-owner-take-preserves-retain-state)
                (fn-owner-control-submit fn-owner-control-submit-preserves-retain-state)
                (fn-owner-prepare-retention fn-owner-prepare-retention-preserves-retain-state)
                (fn-owner-install-effects fn-owner-install-effects-preserves-retain-state)
                (fn-owner-close fn-owner-close-preserves-retain-state)
                (fn-owner-fault fn-owner-fault-preserves-retain-state)
                (fn-owner-open-peer fn-owner-open-peer-preserves-retain-state)
                (fn-owner-install-node-secret fn-owner-install-node-secret-preserves-retain-state)
                (fn-owner-apply-limit-profile fn-owner-apply-limit-profile-preserves-retain-state))
  :concludes ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard)
              (fn-prc-carryp fn-owner-retain-statep-implies-entry-guard))
  :incomplete (A-OWNER-INVARIANT-CARRIED
               ; every other state-returning host writer, by name: the
               ; fn-interfaces entries, and the owner entries the raw host
               ; reaches through fnn-owner-result and its wrappers, which
               ; the host reading does not list (tools/raw_dispatch_rule.py's
               ; undeclared names); regenerate from the refusal, which
               ; names every unlisted and every stale entry
               (
                fn-acct-host-owner-redeem-log-line
                fn-acct-host-owner-redeem-stage
                fn-acct-host-owner-redeem-waitingp
                fn-acct-host-owner-redeem-word fn-bprj-apply
                fn-bprj-config-status fn-bprj-install
                fn-bprj-pending-receipt-resolution fn-bprj-preflight
                fn-bprj-preview-receipt fn-bprj-receipt-adu
                fn-bprj-request-action fn-bprj-request-bound-generation
                fn-bprj-request-bound-inbound-id
                fn-bprj-request-planned-result fn-bprj-request-receipt-id
                fn-bprj-request-result fn-bprj-request-transit-context-record
                fn-bprj-request-transit-intent-record fn-bprj-request-work-id
                fn-bprj-reset fn-bprj-valid-config fn-hl-host-store-history
                fn-native-admin-host-apply
                fn-native-admin-host-owner-reconfigure
                fn-native-admin-host-query-report fn-owner-account-outcome
                fn-owner-app-bind-receipt-store
                fn-owner-app-current-generation fn-owner-app-plan
                fn-owner-app-record fn-owner-app-refusal-log
                fn-owner-app-submit fn-owner-app-unbind-receipt-store
                fn-owner-barrier-limits fn-owner-bound-commit-gate
                fn-owner-bp-receipt-gatep fn-owner-bp-receipt-release-detail
                fn-owner-bp-receipt-release-record
                fn-owner-bp-receipt-signature-plan fn-owner-bp-release-line
                fn-owner-bp-request-refusal-line fn-owner-bp-request-trustedp
                fn-owner-bp-route-table fn-owner-bp-source-decision-line
                fn-owner-bp-tcpcl-ingress fn-owner-bp-transit-outcome
                fn-owner-bp-transit-raw fn-owner-bplc-begin
                fn-owner-bplc-recover fn-owner-bplc-turn-plan
                fn-owner-cat-may-seal fn-owner-cat-prepare-sealed
                fn-owner-catchup-plans
                fn-owner-cfg-native-admin-authorize-carried
                fn-owner-cfg-next-name fn-owner-checkpoint-clone-phase
                fn-owner-chunk-span fn-owner-clock-observation
                fn-owner-compress-min-octets fn-owner-compress-owed
                fn-owner-config-generation fn-owner-config-served
                fn-owner-connection-budget fn-owner-consumer-local-ack
                fn-owner-consumer-local-bootstrap
                fn-owner-consumer-local-bound-ack
                fn-owner-consumer-local-bound-poll
                fn-owner-consumer-local-poll fn-owner-consumer-local-position
                fn-owner-consumer-local-register
                fn-owner-consumer-local-status
                fn-owner-consumer-local-unregister
                fn-owner-consumer-local-wait-admit
                fn-owner-consumer-local-wait-step
                fn-owner-consumer-publication-verdict fn-owner-control-filing
                fn-owner-control-filing-buffer fn-owner-control-outcome
                fn-owner-control-profile-bounds fn-owner-control-reason
                fn-owner-credits-batch-done fn-owner-credits-seal
                fn-owner-credits-settle fn-owner-credits-stop fn-owner-domain
                fn-owner-existing-action fn-owner-existing-action-buffer
                fn-owner-exposure-charge fn-owner-exposure-idle
                fn-owner-exposure-install-set fn-owner-exposure-open
                fn-owner-exposure-progress fn-owner-exposure-release
                fn-owner-feed-auth-policy fn-owner-feed-backoff-ms
                fn-owner-feed-configure fn-owner-feed-dial-open
                fn-owner-feed-has-queued fn-owner-feed-host
                fn-owner-feed-journal-begin fn-owner-feed-journal-offset
                fn-owner-feed-journal-prefix-size fn-owner-feed-journal-scan
                fn-owner-feed-lost fn-owner-feed-peers fn-owner-feed-port
                fn-owner-feed-reconcile-apply fn-owner-feed-reconcile-next
                fn-owner-feed-reply-chunk fn-owner-feed-restart
                fn-owner-feed-security fn-owner-feed-tick
                fn-owner-feed-tls-established fn-owner-finish
                fn-owner-finish-identity fn-owner-finish-submission
                fn-owner-group-codes fn-owner-handshake-admit
                fn-owner-handshake-done fn-owner-handshake-leave
                fn-owner-hybrid-current-enrollment fn-owner-hybrid-snapshots
                fn-owner-identity-publication-verdict
                fn-owner-identity-reservation fn-owner-install-profile
                fn-owner-key-statement-event fn-owner-key-statement-log-line
                fn-owner-key-statement-pending fn-owner-key-statement-plan
                fn-owner-key-statement-redecide-event
                fn-owner-key-statement-redecide-find
                fn-owner-key-statement-redecide-log-line
                fn-owner-key-statement-redecide-plan
                fn-owner-key-statement-request fn-owner-known-abort
                fn-owner-limit-carried fn-owner-limit-decided
                fn-owner-limit-use fn-owner-live-post-config
                fn-owner-log-bounds fn-owner-log-reopen
                fn-owner-login-bindings-plan fn-owner-login-gate-buffer
                fn-owner-moderation-plan fn-owner-next-store-coordinates
                fn-owner-next-txid fn-owner-observe fn-owner-oex-capture
                fn-owner-open fn-owner-operator-refusal-reason
                fn-owner-operator-submit fn-owner-orc-capture
                fn-owner-orc-finish fn-owner-orc-instant-stage
                fn-owner-orc-request fn-owner-orcp-capture
                fn-owner-orcp-finish fn-owner-orcp-key fn-owner-orcp-salt
                fn-owner-orcp-swap fn-owner-orcp-swap-word fn-owner-outcome
                fn-owner-payload-view-acquire fn-owner-payload-view-live-p
                fn-owner-payload-view-owned-p fn-owner-payload-view-release
                fn-owner-payload-view-reset fn-owner-peer-carried-event
                fn-owner-peer-carried-relay-event
                fn-owner-peer-carrier-form-buffer fn-owner-peer-carrier-plan
                fn-owner-peer-for-socket-address fn-owner-peer-revoked-event
                fn-owner-pending-octets fn-owner-pending-sequence
                fn-owner-post-boundary fn-owner-posting-configure
                fn-owner-prepare-buffer fn-owner-prov-post
                fn-owner-proxy-begin fn-owner-proxy-handover
                fn-owner-proxy-step fn-owner-proxy-timeout-line
                fn-owner-publication-verdict fn-owner-pull-plans
                fn-owner-queue-head-served-p fn-owner-read-octets
                fn-owner-reader-views-capture fn-owner-reconfigure-authorizedp
                fn-owner-reconfigure-complete fn-owner-reconfigure-deltas
                fn-owner-reconfigure-unstage fn-owner-recover-from-store-open
                fn-owner-refuse-reservation fn-owner-remote-ingress
                fn-owner-remote-operation-preflight
                fn-owner-resource-unavailable-line-at
                fn-owner-retire-intake-refused fn-owner-retire-report
                fn-owner-retire-step
                fn-owner-runtime-operation-binding-install-internal
                fn-owner-sasl-context fn-owner-sco-capture fn-owner-sco-due
                fn-owner-sco-note-base-payloads fn-owner-sco-note-durable
                fn-owner-sco-publication-done fn-owner-sco-request
                fn-owner-served-carried-word fn-owner-served-post-word
                fn-owner-set-auth-config fn-owner-shed-outcome
                fn-owner-signed-event-boundary fn-owner-snapshot
                fn-owner-space-need fn-owner-stamp-status
                fn-owner-statement-fence fn-owner-submission-intent
                fn-owner-submission-resolution fn-owner-tls-established
                fn-owner-topic-propose fn-owner-transit-decide
                fn-owner-transit-evidence fn-owner-transit-log-line
                fn-owner-transit-outcome fn-owner-transit-reason
                fn-owner-transit-refusal-class fn-owner-transit-verdict
                fn-owner-transit-verdict-buffer fn-owner-unavailable-line-at
                fn-owner-workflow-apply-record
                fn-owner-workflow-forward-pinnedp
                fn-owner-workflow-install-replay
                fn-owner-workflow-pending-waivers
                fn-owner-workflow-preflight-record
                fn-owner-workflow-request-plan fn-owner-workflow-reset
                fn-owner-workflow-store-release
                fn-owner-workflow-store-undertake
                fn-owner-workflow-store-waive
                fn-owner-workflow-sync-store-node
                fn-pinv-host-owner-invitations fn-pinv-host-owner-peers
                fn-pinv-host-owner-reconfigure
                fn-pinv-host-owner-reconfigure-deltas fn-reader-chunk
                fn-reader-model-octets fn-reader-observe-clock
                fn-reader-outcome fn-reader-reset fn-reader-set-posting
                fn-reader-use-seed fn-reader-use-store fn-store-cfg-domain
                fn-store-cfg-generation fn-store-cfg-last-octets
                fn-store-cfg-last-reason
                fn-store-cfg-native-admin-authorize-carried
                fn-store-cfg-served fn-store-checkpoint-clone-phase
                fn-store-checkpoint-rollover-proposal
                fn-store-compress-min-octets fn-store-genesis-ident
                fn-store-genesis-install fn-store-lim-use
                fn-store-log-reclaim-decide-recorded
                fn-store-log-reclaim-decide-stream fn-store-open-refusal-text
                fn-store-open-stop-text fn-store-prov-for-msgid
                fn-store-prov-post fn-store-reclaim-context
                fn-store-reclaim-context-recorded fn-store-reclaim-ctx-classes
                fn-store-reclaim-instant-record fn-store-sco-clear
                fn-store-sco-decode fn-store-sco-decode-finish
                fn-store-sco-image-open fn-store-sco-last-record-octets
                fn-store-sco-log-position fn-store-sco-note-checkpoint-digest
                fn-store-sco-pass-begin fn-store-sco-pass-step
                fn-store-sco-prefix-octets-range fn-store-sco-publish-next
                fn-store-sco-publish-setup-of
                fn-store-sco-want-checkpoint-digest fn-store-sn-article-count
                fn-store-sn-article-verdict-word fn-store-sn-existing-action
                fn-store-sn-finish fn-store-sn-group-next fn-store-sn-headroom
                fn-store-sn-io fn-store-sn-known-abort fn-store-sn-lookup
                fn-store-sn-lookup-foundp fn-store-sn-next-txid
                fn-store-sn-pending-octets fn-store-sn-pending-sequence
                fn-store-sn-pin-count fn-store-sn-prepare
                fn-store-sn-recover-from-checkpoint fn-store-sn-recover-rows
                fn-store-sn-refuse-reservation
                fn-store-sn-replay-digest-report fn-store-sn-reserved
                fn-store-sn-reset fn-store-sn-staging-observation-limit
                fn-store-sn-sweep-round fn-store-statement-replay-seed
                fn-web-host-reset fn-web-host-step fn-workflow-apply-record
                fn-workflow-carry-apply fn-workflow-carry-install
                fn-workflow-carry-preflight fn-workflow-carry-record
                fn-workflow-carry-report fn-workflow-enqueue-record
                fn-workflow-fencedp fn-workflow-install-replay
                fn-workflow-ion-attempt-plan
                fn-workflow-ion-observation-record fn-workflow-ion-request-adu
                fn-workflow-ion-route-record fn-workflow-ion-status
                fn-workflow-preflight-record fn-workflow-receipt-record
                fn-workflow-recovery-plan fn-workflow-release-record
                fn-workflow-request-plan fn-workflow-reset
                fn-workflow-take-submit fn-workflow-undertake-record
                fn-workflow-work-status))
  :trace nil)
