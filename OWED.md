# OWED: the proof-debt ledger of cut/breaking

Ledger, not gate (CUT-LEAD-20261016 §5). Every theorem or book deleted or
broken on this branch gets a row: the claim it carried, where it lived, and
the replacement path (or "none: the code it was about is gone"). ACL2
certification runs for information. A book that no longer certifies and is
not on the survivors list is deleted, not repaired; a survivor book that
breaks gets a one-line hint repair when that is cheap, else a red row here
and the work continues. The 5.4 series picks this ledger up.

## Top-level theorems: teeth owed to 5.4 as must-fail books inside ACL2

Ember (2026-10-17): we only need to demonstrate that our top-level theorems
are not vacuous; the rest fall from use via that. On this branch the
citation, ledger and register apparatus is deleted (last tree below), so
non-vacuity is owed once, here, at the top: for each theorem named in this
section 5.4 writes a must-fail book inside ACL2 (`must-fail-checked`: the
hypothesis negated or the witness broken, the conclusion refused) and a
satisfiable-premise witness. A lemma that turns out vacuous is an ugly
argument, not a hole in the ledger. The names are the book's own `defthm`
names; the files are those of the surviving tree at the M1-d commit.

### (a) specs/node-functionality.md: 106 theorem names it cites, and its numbered claims

Numbered claims (each is a theorem or a family owed as one): 1.3 the transition-relation projections; 2.2 the refinement statement R against F_node; 3.1 totality (no guard violation on the served path); 3.2 work per step bounded by configuration and input length; 3.3 retained memory bounded by configuration; 3.4 the only failures are the three typed refusals; 3.5 the reply stream is F_node's; 3.6 connection isolation under interleaving; 5.2 steps M1 to M10 of the chaining plan.

Names: `fn-allocate-at-watermark`, `fn-bp-effect-for-pending-attempt-unfolds`, `fn-bp-fenced-complete-is-no-op`, `fn-bp-observe-transport-never-moves-status-backward`, `fn-bp-stale-transport-is-no-op`, `fn-bp-step-preserves-state`, `fn-bp-step-submit-requires-matching-durable-attempt-completion`, `fn-bp-trace-preserves-node`, `fn-bp-transport-trace-preserves-receipt`, `fn-bp-unchecked-receipt-is-no-op`, `fn-bpc-decode-refuses-overlong-input`, `fn-bpf-cell-of-uncovered-is-gap`, `fn-bpf-out-of-bounds-input-allocates-nothing`, `fn-bpp-decode-of-encode`, `fn-bpp-encode-is-injective`, `fn-bpr-live-receipt-regenerated-after-restart`, `fn-bpr-live-state-is-replay-of-journal`, `fn-bprl-authorized-receipt-evidence-matches-required`, `fn-bprl-no-receipt-no-release-no-peer-reliance`, `fn-bprl-release-preserves-archive-pin`, `fn-bprl-release-removes-the-forward-pin`, `fn-bprl-undertake-pins-the-forwarding-obligation`, `fn-bprv-evolving-invariant-survives-observed-reopen`, `fn-bprv-evolving-output-is-history-grounded`, `fn-bprv-evolving-output-is-node-grounded-when-idle`, `fn-bprv-replayed-receipt-is-grounded`, `fn-clock-expired-and-live-cannot-both-be-sound`, `fn-clock-expired-requires-every-admissible-clock-to-agree`, `fn-clock-no-wall-and-no-age-is-uncertain`, `fn-clock-zero-creation-time-without-age-is-uncertain`, `fn-duplicate-accepted-prepare-is-no-op`, `fn-exchange-admitted-ingest-retains-conflicting-evidence`, `fn-exchange-ingest-refusal-is-no-op`, `fn-exchange-invalid-batch-refuses-atomically`, `fn-exchange-merge-commutative-member`, `fn-exchange-merge-idempotent`, `fn-exchange-unauthorized-batch-refuses-atomically`, `fn-exchange-unknown-schema-batch-refuses-atomically`, `fn-fenced-completion-is-no-op`, `fn-fenced-prepare-is-no-op`, `fn-frame-decode-refuses-oversize-before-validation`, `fn-install-preserves-state`, `fn-nntp-archive-free-step-ignores-the-archive`, `fn-nntp-block-scan-start-without-a-dot`, `fn-nntp-closed-step-has-no-effects`, `fn-nntp-finite-trace-preserves-consistent-session`, `fn-nntp-group-on-empty-group-invalidates-the-cursor`, `fn-nntp-group-selects-the-first-available-article`, `fn-nntp-next-or-last-moves-only-to-an-available-article`, `fn-nntp-opened-finite-trace-is-consistent`, `fn-nntp-replyp-of-block`, `fn-nntp-step-effects-well-formed`, `fn-nntp-step-preserves-carried-projection`, `fn-nntp-step-preserves-consistent-session`, `fn-node-capacity-refusal-is-no-op`, `fn-node-install-stage-preserves-state`, `fn-node-malformed-step-is-no-op`, `fn-node-stale-completion-is-no-op`, `fn-node-step-preserves-state`, `fn-own-durable-outcome-repins-the-poster`, `fn-own-durable-reply-names-a-durable-record`, `fn-own-outcome-touches-only-its-connection`, `fn-own-pinned-prefix-survives-any-trace`, `fn-own-read-is-served-step-on-pinned-prefix-after-any-trace`, `fn-own-read-touches-only-its-connection`, `fn-own-reader-sees-pinned-prefix-replay-after-any-trace`, `fn-prepare-allocates-fresh-monotone-txid`, `fn-relay-accept-preserves-invp`, `fn-relay-archived-receipt-needs-no-undertaking-by-definition`, `fn-relay-crash-recover-never-yields-a-promise-alone`, `fn-relay-forwarding-receipt-has-durable-onward-obligation`, `fn-relay-forwarding-without-undertaking-is-refused-by-definition`, `fn-relay-sender-step-preserves-invp`, `fn-retain-accounting-within-capacity`, `fn-retain-admission-refusal-is-no-op`, `fn-retain-known-obligation-id-is-not-reused`, `fn-retain-release-preserves-independent-pin`, `fn-retain-wrong-evidence-does-not-release`, `fn-served-step-effects-are-typed`, `fn-served-step-partition-independence`, `fn-served-step-preserves-connp`, `fn-sn-actual-durable-completion-installs-record`, `fn-sn-finish-disabled-is-no-op`, `fn-sn-known-abort-disabled-is-no-op`, `fn-sn-new-success-requires-actual-matching-durable-node-completion`, `fn-sn-open-observed-invalid-history-refuses`, `fn-sn-refuse-reservation-disabled-is-no-op`, `fn-snt-acknowledged-history-retained-through-mixed-trace`, `fn-snt-admissible-crash-image-is-recoverable`, `fn-snt-mixed-trace-preserves-live-history-relation`, `fn-snt-ready-or-recovered-node-is-exact-replay`, `fn-snt-step-preserves-relation`, `fn-snt-unknown-io-is-no-op`, `fn-stale-completion-is-no-op`, `fn-unknown-or-duplicate-group-prepare-is-no-op`, `fn-watermark-does-not-conflict`, `fn-wire-begin-article-refusal-keeps-state`, `fn-wire-drive-is-feed-proper`, `fn-wire-drive-partition-independence`, `fn-wire-drive-preserves-statep`, `fn-wire-feed-byte-retained-input-is-bounded`, `fn-wire-feed-closed-noop`, `fn-wire-feed-proper-append`, `fn-wire-next-closed-noop`, `fn-wire-next-strictly-consumes`, `fn-wire-next-unconsumed-is-suffix`

### (b) the survivors' keystones, by family (CUT-LEAD-20261016 §3)

The KEYSTONE-marked theorems of the deleted proofs registry (read at 40015b3f8:planning/proofs.json) that are still `defthm`s in a surviving book, grouped by the family of the book that defines them. A keystone defined in a book of another family of the survivor tree (catalog, payload, owner, config, consumer and the like, 342 names) is not repeated: it is readable from the registry's last tree.

**wire grammar and command surface** (57 theorems)

- `books/article-buffer.lisp`: `fn-ars-parse-under-is-article-parse-under`
- `books/article.lisp`: `fn-article-parse-lines-acc-is-parse-lines`
- `books/group-access-cache.lisp`: `fn-gacc-prepare-keeps-okp`, `fn-gacc-view-of-prepare`
- `books/list-available-reference.lisp`: `fn-lst-active-command-is-av-list-active`, `fn-lst-counts-command-is-av-list-counts`
- `books/nntp-article-pass.lisp`: `fn-nntp-response-block-rev-is-the-block`
- `books/nntp-compress-dict.lisp`: `fn-zdn-body-round-trip`, `fn-zdn-choose-complete`, `fn-zdn-choose-stored-only-shared`
- `books/nntp-help.lisp`: `fn-auth-step-pinned-answers-500-to-a-keyword-help-does-not-list`
- `books/nntp-responses.lisp`: `fn-nntp-article-response-is-of-bytes`
- `books/nntp-zarticle.lisp`: `fn-zar-decide-complete`, `fn-zar-decide-stored-denotes`
- `books/protocol-codes.lisp`: `fn-proto-command-pinned-replies-are-in-the-row`
- `books/protocol-dispatch.lisp`: `fn-proto-command-pinned-is-command-pinned`
- `books/protocol-framing.lisp`: `fn-proto-command-pinned-offers-only-article-framing`
- `books/response-plan-pins.lisp`: `fn-rpin-acquire-holds-the-captured-generation`, `fn-rpin-step-preserves-funded-ownership`
- `books/served-catalog-chain.lisp`: `fn-scr-prepare-access-keeps-okp`, `fn-scr-scan-span-is-feed-span`
- `books/served-catalog-join-entry.lisp`: `fn-scj-joinp-at-full-open`, `fn-scj-joinp-at-idle-current-owner`, `fn-scj-joinp-at-recover`, `fn-scj-joinp-of-load`
- `books/served-catalog-join-finish.lisp`: `fn-scj-finish-keeps-rows-invp`, `fn-scj-joinp-at-host-finish`
- `books/served-catalog-join-number.lisp`: `fn-scj-acc-rowsp-of-install`
- `books/served-catalog-join-open.lisp`: `fn-scj-acc-rowsp-at-idle-related-owner`, `fn-scj-acc-rowsp-of-cpr-loop`, `fn-scj-row-equation-of-acc-rowsp`
- `books/served-catalog-join-read.lisp`: `fn-scj-ocfg-read-span-is-reference-under-invp`
- `books/served-catalog-join-step.lisp`: `fn-scj-join-of-finish-lists`
- `books/served-catalog-join.lisp`: `fn-scj-joinp-of-article-finish`
- `books/served-catalog.lisp`: `fn-nntp-list-active-cat-is-list-command`, `fn-nntp-next-or-last-cat-is-next-or-last`, `fn-nntp-over-range-ovw-expands-to-over-range-cat`, `fn-nntp-over-range-ovw-expands-to-over-range-served-cat`, `fn-nntp-verdict-hdr-response-cat-is-archive`, `fn-scat-available-article-is-available`, `fn-scat-next-number-is-next-number`, `fn-scat-previous-number-is-last-number`, `fn-scat-range-numbers-is-group-range-numbers`
- `books/served-columns.lisp`: `fn-nntp-xref-reply-col-is-xref-reply`, `fn-scol-facts-are-the-bytes-facts`, `fn-scol-hdr-content-is-bytes`, `fn-scol-overview-of-is-bytes`, `fn-scol-tombstonep-is-bytes`
- `books/served-plan-cursor.lisp`: `fn-splan-cw-drain-is-the-expanded-reply`
- `books/served-query-plan.lisp`: `fn-qplan-cw-drain-is-a-prefix`
- `books/served-scan.lisp`: `fn-scar-scan-span-is-feed-counted`
- `books/served-span.lisp`: `fn-scar-feed-span-is-feed-counted`, `fn-scar-ocfg-read-span-is-reference-under-ocl-relation`
- `books/wildmat-cursor.lisp`: `fn-wmc-core-codepoint-start-work-bound`
- `books/wire-invariants.lisp`: `fn-wire-article-event-is-the-held-body`
- `books/wire-scan.lisp`: `fn-wire-scan-is-span-fold`
- `books/wire.lisp`: `fn-wire-statep-article-holds-at-most-the-body-limit`

**authentication** (7 theorems)

- `books/config-owner-live-authorize.lisp`: `fn-olau-authorize-is-the-replayed-authorization`
- `books/nntp-auth-roles.lisp`: `fn-auth-step-binds-a-peer-role-by-sasl-only-to-a-found-credential`
- `books/nntp-auth.lisp`: `fn-auth-config-with-accounts-after-an-account-delete-offers-only-the-operators-credential`, `fn-auth-established-starts-the-owed-compression`, `fn-auth-failed-pass-at-the-limit-is-481-400-and-closes`, `fn-auth-failed-pass-below-the-limit-is-481-and-keeps-the-connection`
- `books/sasl.lisp`: `fn-sasl-scram-final-success-is-bound-to-the-exchange`

**acceptance and identity binding** (8 theorems)

- `books/acceptance-payload-ref.lisp`: `fn-apr-payload-of-is-the-article-payload`
- `books/accounts.lisp`: `fn-acct-admin-deltas-expire-at-now-plus-expires-on-both-paths`, `fn-acct-delete-is-admitted-exactly-when-held-and-unobligated`, `fn-acct-delete-keeps-the-login-taken`, `fn-acct-invite-expiry-agrees-across-the-running-and-stopped-paths`, `fn-acct-offline-invite-refusal-is-no-clock-exactly-without-a-wall`, `fn-cfg-record-redeeming-an-expired-code-is-refused-and-faults-replay`
- `books/identity-retain-carried.lisp`: `fn-irc-pout-prepare-identity-of-refresh-is-pout`

**durable log and its recovery refinement** (51 theorems)

- `books/checkpoint-reserve.lisp`: `fn-ckr-two-generations-fit-the-reserve-at-every-cut`
- `books/pagestore-exec.lisp`: `pgs-x-commit-refines`
- `books/pagestore-reclaim.lisp`: `pgs-reclaim-never-frees-live`
- `books/pagestore-refine.lisp`: `pgs-x-commit-refines-plan`, `pgs-x-fork-refines`
- `books/recovery-refinement-concurrent.lisp`: `fn-rrc-recovery-refines-a-prefix-with-every-acknowledged-record`
- `books/recovery-refinement-pages.lisp`: `fn-rrp-commit-writes-within-the-generation`
- `books/recovery-refinement.lisp`: `fn-rr-recovery-refines-a-prefix-with-every-acknowledged-record`
- `books/replay-historical-limits.lisp`: `fn-rhl-extend-open-is-limit-free`
- `books/replay-identity-index.lisp`: `fn-rii-classified-open-is-classified-open`, `fn-rii-sco-cpr-prefix-is-sco-cpr-prefix`, `fn-rii-sco-extend-is-sco-extend`, `fn-rii-sco-extend-open-is-extend-then-open`
- `books/store-log-buffer.lisp`: `fn-lg-entry-okp-holds-the-chain-field`, `fn-lgb-descriptor-is-the-attached-place`, `fn-lgb-descriptor-of-an-accepted-record`, `fn-lgb-next-record-advances-the-cursor`, `fn-lgb-next-record-descriptor-is-the-attached-place`, `fn-lgb-next-record-has-a-descriptor`, `fn-lgb-next-record-within-max`, `fn-lgb-next-record-yields-the-records`, `fn-lgb-span-records-are-the-records`, `fn-lgb-span-within-max`, `fn-lgw-step-buf-count-is-step`
- `books/store-log-damage.lisp`: `fn-lgdm-damage-lies-in-the-last-write`, `fn-lgdm-no-silent-prefix`, `fn-lgdm-open-verdict-is-the-classification`, `fn-lgdm-refusal-text-refuses-exactly-a-break-or-damage`
- `books/store-log-durable.lisp`: `fn-lgu-acknowledge-acknowledges-only-recoverable-records`
- `books/store-log-extend.lisp`: `fn-lg-extend-program-keeps-the-relation`, `fn-lg-extension-written-crash-reads-the-committed-records`
- `books/store-log-history-ceiling.lisp`: `fn-lgo-history-ceiling-bounds-the-intern`
- `books/store-log-kernel-concrete.lisp`: `fn-lgc-run-refines-the-kernel`, `fn-lgc-take-never-joins-the-batch-in-flight`
- `books/store-log-lineage.lisp`: `fn-lgl-open-of-rotated-segment`
- `books/store-log-open-scan.lisp`: `fn-lgo-chain-is-the-fold`, `fn-lgo-fold-from-no-skip-bounds-any-skip`, `fn-lgo-fold-is-the-wire-fold`, `fn-lgo-head-genesis-is-the-open-lineage-start`, `fn-lgo-host-suffix-covers-the-opened-store`, `fn-lgo-observed-covers-the-opened-store`, `fn-lgo-run-is-the-fold`, `fn-lgo-scan-plan-scans-every-present-segment`, `fn-lgo-wire-fold-covers-the-replay`
- `books/store-log-reclaim.lisp`: `fn-lgr-decide-checkpoints-the-rewrite`
- `books/store-log-recover-copy.lisp`: `fn-lgrc-open-keeps-the-relation-at-every-cut`
- `books/store-log-rotate-spare.lisp`: `fn-lgrs-journal-fence-names-the-acknowledged-batch`
- `books/store-log-stream.lisp`: `fn-lgw-run-is-the-open`, `fn-lgw-segment-drop-preserves-the-open`
- `books/store-log-walk-once.lisp`: `fn-lgw-run-nf-then-fold-is-run`
- `books/store-log.lisp`: `fn-lg-scan-of-rotation-entry-append`

**BP node machine** (40 theorems)

- `books/bp-carry-control.lisp`: `fn-bpcc-gate-refuses-a-held-work`
- `books/bp-carry-frame.lisp`: `fn-bpcc-frame-decode-of-sealed`
- `books/bp-carry-waiver.lisp`: `fn-bpcw-waiver-releases-exactly-once`
- `books/bp-evidence-host-names.lisp`: `fn-bpn-host-evidence-next-result-name-names-exactly-the-next-record`
- `books/bp-fnbs-deletion-publication.lisp`: `fn-bpnf-delete-publication-authorize-admits-exactly-the-issued-pending-deletion`
- `books/bp-fnbs-delivery-publication.lisp`: `fn-bpah-publication-authorize-admits-exactly-the-issued-pending-delivery`
- `books/bp-fnbs-dispatch-publication.lisp`: `fn-bpnp-dispatch-publication-authorize-admits-exactly-the-issued-pending-dispatch`
- `books/bp-fnbs-family-publication.lisp`: `fn-bpnf-family-publication-authorize-admits-exactly-the-issued-pending-family`
- `books/bp-fnbs-forward-publication.lisp`: `fn-bpnp-forward-publication-authorize-admits-exactly-the-issued-pending-forward`
- `books/bp-forward-attempt.lisp`: `fn-bpnp-configured-budgets-admits-exactly-the-frame-bounded-positive-budgets`
- `books/bp-fragment-resume.lisp`: `fn-bpfr-run-is-reassemble`, `fn-bpfr-step-resumes`
- `books/bp-handoff-report.lisp`: `fn-bpah-handoff-report-is-application-disposition`
- `books/bp-ingress-carried.lisp`: `fn-bpi-ingress-prepare-carried-is-prepare`
- `books/bp-native-app-fast.lisp`: `fn-bpaj-node-record-committed-carriedp-is-committedp`, `fn-bpaj-record-lookup-fast-found-is-an-accepted-match`
- `books/bp-node-fragment-job.lisp`: `fn-bpfj-plan-is-the-plan-within-the-limit`, `fn-bpfj-plan-refuses-past-the-limit-by-name`, `fn-bpfj-query-is-the-query`
- `books/bp-node-fragment-step.lisp`: `fn-bpfj-next-candidate-is-a-ready-family-representative`
- `books/bp-node-host-machine.lisp`: `fn-bpn-host-existing-sequence-reuses-exactly-the-keyed-jobs-sequence`, `fn-bpn-host-lifecycle-recovery-agrees-with-the-replayed-machine`
- `books/bp-node-host-sequence.lisp`: `fn-bpn-host-authored-wire-name-names-the-reserved-sequence`, `fn-bpn-host-sequence-reserve-reserves-exactly-below-the-ceiling`
- `books/bp-node-host-transfer.lisp`: `fn-bpn-host-receive-keeps-the-three-outcomes-distinct`, `fn-bpn-host-receive-of-host-send-hands-over-the-adu`
- `books/bp-node-machine-codec.lisp`: `fn-bpn-lifecycle-publication-authorize-admits-exactly-the-pending-persist`
- `books/bp-node-progress.lisp`: `fn-bpnp-tcpcl-outcome-keeps-sent-refused-failed-and-uncertain-distinct`
- `books/bp-node-rotation-buffer.lisp`: `fn-bpnrb-checkpoint-decode-is-decode`
- `books/bp-node-rotation-codec.lisp`: `fn-bpnr-publish-outcome-is-pending-exactly-while-the-loop-runs`
- `books/bp-node-rotation-due.lisp`: `fn-bpnrd-rotation-keeps-every-held-family`
- `books/bp-primary.lisp`: `fn-bpp-crc16-scan-table-is-scan`
- `books/bp-receipt-log-crash.lisp`: `fn-brlc-receipt-regenerated-after-log-crash`
- `books/bp-receive-evidence.lisp`: `fn-bpn-evidence-authorize-admits-exactly-the-locked-next-identity`
- `books/bp-report-observe.lisp`: `fn-bpn-report-observe-next-selects-exactly-the-least-yielding-row`
- `books/bp-report-outbox.lisp`: `fn-bpn-report-outbox-next-selects-exactly-the-least-yielding-row`
- `books/bp-request-ref.lisp`: `fn-bpaj-ref-request-resolves-exactly`
- `books/bp-request-reference.lisp`: `fn-bpaj-transit-context-binds-the-live-request`, `fn-bpaj-transit-intent-pins-its-request-and-projection`
- `books/bp-transit-join.lisp`: `fn-bpaj-transit-plan-under-refuses-past-the-limits-before-any-intent`

**TLS with our own crypto** (9 theorems)

- `books/blake3-stobj.lisp`: `fn-blake3-of-prefixed-range-is-blake3`
- `books/tls-handshake-budget.lisp`: `fn-hsb-admits-per-tick-are-bounded`, `fn-hsb-buckets-are-bounded`, `fn-hsb-source-admits-are-bounded`
- `books/tls-handshake-decision.lisp`: `fn-hsb-steps-keep-the-bound`
- `books/tls-proxy.lisp`: `fn-pxy-direct-unless-trusted`, `fn-pxy-handover-keeps-the-bound`, `fn-pxy-observe-keeps-the-read-bound`, `fn-pxy-step-reads-within-the-bound`

Rows are appended by the commit that creates the debt, one line each,
newest last. `G4` is the line `tools/cut_measure.sh` printed for that commit.

| commit | book or theorem | claim it carried | replacement path | state |
|---|---|---|---|---|
| c626d6eb7 | 5 theorem(s) cited by PRF-046, in books/bp-node-forward-resume.lisp, books/bp-request-recovery.lisp (fn-bpnp-resumed-result-clears-only-the-slot, ...) | restart resumption of stranded BP rows and request-plan recovery (progress evidence for the fn-bpn-step target) | none: tier-A books unreached from every host build (M1-a sweep); PRF-046 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 2 theorem(s) cited by PRF-081, in books/bp-node-rotation-equivalence.lisp, books/bp-node-rotation-recovery.lisp (fn-bpnj-rotation-restart-succeeds-with-owed-work, ...) | BP checkpoint recovery equals full recovery and rotation restart keeps owed work | none: tier-A books unreached from every host build (M1-a sweep); PRF-081 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 2 theorem(s) cited by PRF-383, in books/config-walk-loops.lisp (fn-cfg-peer-names-loop-is-revappend-of-the-walk, ...) | loop-twin lemmas in the PRF-362 rev-onto pattern | none: tier-A books unreached from every host build (M1-a sweep); PRF-383 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 24 theorem(s) cited by PRF-958, in books/owner-number-bound-join.lisp (fn-onbj-arm-acar-outcome, ...) | owner number bounds joined across node and store (fn-onbj-) | none: tier-A books unreached from every host build (M1-a sweep); PRF-958 keeps its statement on the surviving subject | owed |
| c626d6eb7 | 7 theorem(s) cited by PRF-1131, in books/decoded-window-clear-trajectory.lisp, books/decoded-window-finite-output-trajectory.lisp, books/decoded-window-yield-trajectory.lisp (fn-pwf-actual-completed-finite-output-yields-match-basic-loop, ...) | the dormant fn-ewz finite-output and yield trajectories complete effects | none: tier-A books unreached from every host build (M1-a sweep); PRF-1131 keeps its statement on the surviving subject | owed |
| 84edb68af | 5 theorem(s) cited by PRF-011, in books/transfer-assembly-invariants.lisp, books/transfer-invariants.lisp, books/transfer-reservation.lisp, books/transfer.lisp (fn-transfer-exact-duplicate-no-overwrite, fn-transfer-reserve-preserves-statep, ...) | Validated fact-set merge | none: tier-B books unreached from every host build (M1-b park); the PRF-011 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 4 theorem(s) cited by PRF-016, in books/transfer-work.lisp, books/transfer.lisp (fn-transfer-initial-statep, fn-transfer-invalid-chunk-no-overwrite, ...) | Bounded parsing and staging | none: tier-B books unreached from every host build (M1-b park); the PRF-016 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 6 theorem(s) cited by PRF-230, in books/transit-header-limits.lisp (fn-peer-decide-transfer-under-admits-exactly-the-limits, fn-peer-decide-transfer-under-wants-only-what-transfer-wants, ...) | The header limits of one article are the operator's: the parse under a profile's limits admits exactly the headers within them and refuses the next by name, and | none: tier-B books unreached from every host build (M1-b park); the PRF-230 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 5 theorem(s) cited by PRF-313, in books/transit-bound.lisp (fn-tb-open-peer-body-limit-is-the-profile-bound, fn-tb-served-run-retains-at-most-the-body-limit, ...) | A transit article is bounded by the operator's profile before its verdict: the transit connection opens at the profile bound, the served run retains at most it, | none: tier-B books unreached from every host build (M1-b park); the PRF-313 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 1 theorem(s) cited by PRF-929, in books/transit-bound.lisp (fn-tb-served-run-holds-at-most-the-body-limit-mid-article) | Mid-article a connection holds at most the body limit and one octet: the wire closes :body-overlimit at the octet that dooms the line, not at its LF | none: tier-B books unreached from every host build (M1-b park); the PRF-929 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 44 theorem(s) cited by PRF-1178, in books/bpsec-asb-aggregate.lisp, books/bpsec-asb-body.lisp, books/bpsec-asb-control.lisp, books/bpsec-asb-head-invariant.lisp, books/bpsec-asb-metadata.lisp, books/bpsec-asb-position.lisp, books/bpsec-asb-quanta.lisp, books/bpsec-asb-spine.lisp, books/bpsec-asb-target-types.lisp, books/bpsec-asb-terminal.lisp, books/bpsec-asb.lisp, books/bpsec-head-invariant.lisp, books/bpsec-head.lisp, books/bpsec-received-window.lisp (fn-bps-head-drive-consumes-at-most-quantum, fn-bps-head-drive-consumes-at-most-window, ...) | Bounded ASB window cursor preserves exact consumed prefix and refines the RFC sequence | none: tier-B books unreached from every host build (M1-b park); the PRF-1178 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 5 theorem(s) cited by PRF-1179, in books/bpsec-target-cursor.lisp, books/bpsec-target-spine.lisp (fn-bps-target-drive-work-does-not-exceed-quantum, fn-bps-target-drive-composes-quanta, ...) | BPSec target graph binds actual block numbers and preserves opaque encrypted BIB status | none: tier-B books unreached from every host build (M1-b park); the PRF-1179 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 4 theorem(s) cited by PRF-1185, in books/bpsec-operation.lisp (fn-bps-op-evidence-requires-issued-current-verified, fn-bps-op-complete-preserves-operation, ...) | BPSec evidence requires exact issued operation and current verified completion | none: tier-B books unreached from every host build (M1-b park); the PRF-1185 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 12 theorem(s) cited by PRF-1176, in books/substrate-committed-row.lisp, books/substrate-committed-transcript.lisp (fn-stce-resume-retains-existing-evidence, fn-stce-publish-retains-the-envelope, ...) | Resumable committed transcript preserves signed envelopes and refuses commit-ID collisions | none: tier-B books unreached from every host build (M1-b park); the PRF-1176 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 7 theorem(s) cited by PRF-1189, in books/substrate-commit-profile-bounds.lisp, books/substrate-commit-profile-codec.lisp, books/substrate-commit-profile-refinement.lisp, books/substrate-commit-profile-resume.lisp (fn-stcp-enc-drive-work-bound, fn-stcp-dec-drive-work-bound, ...) | Explicit resumable commit codec profile v2 work budget | none: tier-B books unreached from every host build (M1-b park); the PRF-1189 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 4 theorem(s) cited by PRF-1224, in books/transit-same-decision.lisp (fn-tsd-bp-gate-is-the-drain-decision, fn-tsd-nntp-and-bp-transit-decide-alike, ...) | K6: one transit decision for the NNTP and BP carriers | none: tier-B books unreached from every host build (M1-b park); the PRF-1224 row stays in planning/proofs.json for the register sweep | owed |
| 84edb68af | 2 theorem(s) cited by PRF-1303, in books/tcpcl-source-control-refinement.lisp (fn-tclsctl-source-drive-keepalive-refines-session, fn-tclsctl-source-drive-keepalive-preserves-custody-and-reception) | Actual one-frame TCPCL source parser preserves control reception and inbound custody | none: tier-B books unreached from every host build (M1-b park); the PRF-1303 row stays in planning/proofs.json for the register sweep | owed |
| c8e5055fa | HST-043 (requirement) and its proof targets PRF-1177, PRF-1196, PRF-1202, PRF-1206, PRF-1207 (no theorem among them; planned rows) | the 9P view requirement: a bounded native read-only 9P2000 committed view (specs/views-9p.md, last tree 64c84e0d3) | none: the feature left by ember's decision (host-parked F07 and the park bin); the five rows sit in planning/proof-retirements.json (deferred, restorable by ledger.py --restore) and the requirement row left planning/requirements.json and planning/families.json | retired by decision |
| 249a737f0 | 1 theorem cited by PRF-123, in books/post-record-width-owner.lisp (fn-prwo-owner-post-record-is-narrow-within-the-profile; its R corollary fn-prwo-owner-post-record-is-within-r, the PKT-250 keystone) | the record the owner's two host calls (fn-pak-post-admission, then fn-owner-prepare-buffer's catalog prepare) stage is narrow within the profile and within its R | none: tier-B book reached by no host build (M1-b post-identity); PRF-123 keeps its statement on the surviving producers (books/record-width-producers.lisp) and loses this event and its two evidence paths | owed |
| 249a737f0 | PRF-1145 whole (16 books: books/post-identity-source-cursor*.lisp, the D25 virtual-byte agent and injection inverse; fn-psc-) | the bounded source-cursor agent yields incoming-derived spans and per-source K,A,B descriptors matching fn-pb-path-agent and fn-pbb-source-index | none: tier-B stack reached by no host build (M1-b post-identity); the row is retired deferred to this ledger in planning/proof-retirements.json | owed |
| 249a737f0 | PRF-1148 whole (18 books: books/post-identity-captured*.lisp, the captured-row resumable SAME authority; fn-pic-) | duplicate/conflict decisions over the captured row equal fn-rclb-same-articlep plus exact held groups after the binding gate | none: tier-B stack reached by no host build and its native caller parked and removed by M1-a (M1-b post-identity); the row is retired deferred to this ledger in planning/proof-retirements.json | owed |
| 6496bf5ee | 4 theorem(s) cited by PRF-365, in books/history-pages-owner.lisp (fn-hpo-installed-records-are-checkpoint-then-suffix, fn-hpo-records-at-is-installed-nth, ...) | The served owner's records are the history image's followed by the log suffix: the owner the host installs from a checkpoint holds exactly the checkpoint's reco | none: tier-B books unreached from every host build (M1-b history); the PRF-365 row stays in planning/proofs.json for the register sweep | owed |
| 6496bf5ee | 8 theorem(s) cited by PRF-997, in books/history-knowledge.lisp (fn-hkn-knowledge-is-one-of-the-five-states, fn-hkn-tombstoned-keeps-the-identity, ...) | The event history keeps every acceptance through reclamation, and an acceptance records its commitment | none: tier-B books unreached from every host build (M1-b history); the PRF-997 row stays in planning/proofs.json for the register sweep | owed |
| 6496bf5ee | 10 theorem(s) cited by PRF-998, in books/history-knowledge.lisp (fn-hkn-reduce-pins-keeps-the-ids, fn-hkn-reduce-pin-keeps-the-identifying-fields, ...) | Reclamation is a logical release the continuation language cannot distinguish, except by the freed charge | none: tier-B books unreached from every host build (M1-b history); the PRF-998 row stays in planning/proofs.json for the register sweep | owed |
| 6496bf5ee | 1 theorem(s) cited by PRF-999, in books/history-knowledge.lisp (fn-hkn-replay-binds-the-recorded-evidence-not-the-policy) | Replay binds the recorded evidence, never the replay's policy | none: tier-B books unreached from every host build (M1-b history); the PRF-999 row stays in planning/proofs.json for the register sweep | owed |
| 6496bf5ee | 2 theorem(s) cited by PRF-1000, in books/history-knowledge.lisp (fn-hkn-refused-prepare-is-the-identity-by-definition, fn-hkn-refusal-keeps-the-recovery-barriers) | Every refusal's footprint is named and bounded | none: tier-B books unreached from every host build (M1-b history); the PRF-1000 row stays in planning/proofs.json for the register sweep | owed |
| 6496bf5ee | 6 theorem(s) cited by PRF-1190, in books/history-event-directory-refinement.lisp, books/history-event-directory.lisp (fn-hed-grow-step-preserves-chronological-prefix, fn-hed-grow-begin-is-one-chronological-page, ...) | Chronological persistent forest growth and exact resumable page selection | none: tier-B books unreached from every host build (M1-b history); the PRF-1190 row stays in planning/proofs.json for the register sweep | owed |
| 6496bf5ee | 4 theorem(s) cited by PRF-1191, in books/history-event-backing.lisp (fn-hep-offer-retains-exact-row-and-complete-producer, fn-hep-completion-registration-is-once-only, ...) | Registered exact candidate, completion replay and epoch custody frames | none: tier-B books unreached from every host build (M1-b history); the PRF-1191 row stays in planning/proofs.json for the register sweep | owed |
| M1-d | the deleted registers: `planning/` proofs, proof-events, cost-obligations, requirements, critical-*, twins, premise-*, retired-paths, proof-retirements, current-view, known-reds, repair/ and the rest of the apparatus's data | every citation of a theorem by a PRF id, every cost obligation, every requirement row and every carried-red record | none on this branch: the last tree is `git show 40015b3f8:planning/`; the tools that read them are `git show 40015b3f8:tools/`; 5.4 reads them from git and rebuilds only what its must-fail books need | owed |
