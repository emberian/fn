PYTHON ?= python3
# Maximum concurrent ACL2 processes. Books still certify in local
# include-book dependency order; 1 reproduces the sequential run.
FN_CERTIFY_JOBS ?= 1
# The wall clock an interactive `ld` gets before tools/acl2 kills it and frees
# its slot: the brief's three-minute rule, with a minute of slack.
FN_LD_TIMEOUT_SECONDS ?= 240
ACL2_BOOKS ?= books/defrecord \
	books/defkeystone \
	books/deftransition \
	books/rev-onto \
	books/acceptance-alloc \
	tests/acl2/defrecord-tests \
	tests/acl2/defkeystone-tests \
	books/acceptance \
	books/acceptance-invariants \
	tests/acl2/acceptance-tests \
	books/wire \
	books/wire-invariants \
	books/wire-outbound-invariants \
	tests/acl2/wire-outbound-tests \
	tests/acl2/wire-tests \
	books/cbor \
	books/cbor-invariants \
	tests/acl2/cbor-tests \
	tests/acl2/cbor-teeth-tests \
	books/wildmat \
	books/wildmat-utf8-invariants \
	books/wildmat-parser-invariants \
	books/wildmat-matcher-invariants \
	books/wildmat-work \
	tests/acl2/wildmat-parser-invariants-tests \
	tests/acl2/wildmat-tests \
	tests/acl2/wildmat-teeth-tests \
	books/article \
	books/article-invariants \
	books/article-properties \
	books/article-header-census \
	books/article-header-limits \
	tests/acl2/article-header-limits-tests \
	tests/acl2/article-tests \
	tests/acl2/article-teeth-tests \
	books/article-work-primitives \
	books/article-work-scanners \
	books/article-work \
	books/article-work-budget \
	books/article-public-work \
	books/article-public-bound \
	tests/acl2/article-work-tests \
	books/article-fields \
	tests/acl2/article-fields-tests \
	books/post-fields \
	tests/acl2/post-fields-tests \
	books/store-config \
	books/sha256 \
	tests/acl2/sha256-tests \
	books/blake3 \
	tests/acl2/blake3-tests \
	books/blake3-stobj \
	tests/acl2/blake3-stobj-tests \
	books/frame-octets \
	books/frame-fields \
	books/frame-journal \
	books/frame \
	books/frame-invariants \
	tests/acl2/frame-tests \
	books/frame-trailer \
	tests/acl2/frame-trailer-tests \
	books/tcpcl-spool \
	tests/acl2/tcpcl-spool-tests \
	books/identity \
	books/identity-invariants \
	tests/acl2/identity-tests \
	books/provenance \
	books/retention \
	books/retention-invariants \
	tests/acl2/retention-tests \
	books/node \
	books/node-invariants \
	books/node-retention-transitions \
	tests/acl2/node-tests \
	books/node-traces \
	books/records-shape \
	books/records \
	books/records-invariants \
	books/records-stamp \
	books/records-canonicality \
	books/records-seam \
	books/records-schema-v1 \
	books/records-attach \
	books/store-events \
	tests/acl2/store-events-tests \
	books/store-retention-codec-invariants \
	tests/acl2/store-retention-codec-invariants-tests \
	books/consumer-position \
	tests/acl2/consumer-position-tests \
	books/consumer-store-events \
	tests/acl2/consumer-store-events-tests \
	books/consumer-store-projection \
	tests/acl2/consumer-store-projection-tests \
	books/consumer-local-control \
	tests/acl2/consumer-local-control-tests \
	books/consumer-poll-projection \
	tests/acl2/consumer-poll-projection-tests \
	tests/acl2/records-tests \
	tests/acl2/records-teeth-tests \
	tests/acl2/records-schema-v1-teeth-tests \
	tests/acl2/records-ceiling-tests \
	tests/acl2/records-shape-tests \
	books/provenance-codec \
	tests/acl2/provenance-tests \
	books/config \
	books/config-invariants \
	books/replay \
	books/replay-invariants \
	tests/acl2/store-event-replay-tests \
	tests/acl2/store-identity-replay-tests \
	tests/acl2/replay-tests \
	books/config-records \
	books/node-config \
	tests/acl2/config-tests \
	books/native-config \
	tests/acl2/native-config-tests \
	books/native-config-show \
	tests/acl2/native-config-show-tests \
	books/native-auth-profile \
	tests/acl2/native-auth-profile-tests \
	tests/acl2/native-auth-host-tests \
	books/native-auth-admin \
	tests/acl2/native-auth-admin-tests \
	tests/acl2/native-auth-admin-host-tests \
	books/journal-publish \
	books/bp-eid-shape \
	books/native-admin-shape \
	books/native-admin-peer \
	books/native-admin \
	tests/acl2/native-admin-tests \
	books/native-config-observation \
	tests/acl2/native-config-observation-tests \
	books/native-operator \
	tests/acl2/native-operator-tests \
	tests/acl2/native-operator-host-tests \
	tests/acl2/docs-operator-grammar-tests \
	books/native-mission \
	tests/acl2/native-mission-tests \
	books/native-control \
	books/native-hybrid-control \
	books/hybrid-lifecycle \
	tests/acl2/hybrid-lifecycle-tests \
	books/hybrid-lifecycle-store-invariants \
	books/owner-verdict-read \
	books/owner-list-counts-read \
	books/config-descriptions \
	books/owner-descriptions-read \
	books/owner-xref-read \
	books/posting-account \
	books/injection-info-policy \
	books/injection-info-params \
	books/injection-info-params-invariants \
	books/owner-injection-info \
	books/owner-signed-post \
	tests/acl2/hybrid-lifecycle-store-invariants-tests \
	tests/acl2/native-hybrid-control-tests \
	tests/acl2/native-control-tests \
	books/native-control-reason \
	tests/acl2/native-control-reason-tests \
	tests/acl2/native-control-host-tests \
	books/native-live-status \
	tests/acl2/native-live-status-tests \
	books/retention-figures \
	books/control-evidence-grammar \
	books/control-evidence \
	tests/acl2/control-evidence-tests \
	books/moderation-verbs \
	tests/acl2/moderation-verbs-tests \
	books/log-sink \
	tests/acl2/log-sink-tests \
	books/native-health \
	tests/acl2/native-health-tests \
	books/feed-filename \
	tests/acl2/feed-filename-tests \
	books/feed-wire-input \
	tests/acl2/feed-wire-input-tests \
	books/feed-auth-profile \
	tests/acl2/feed-auth-profile-tests \
	books/feed-connection \
	tests/acl2/feed-connection-tests \
	books/feed-connection-invariants \
	tests/acl2/feed-connection-invariants-tests \
	tests/acl2/feed-connection-teeth-tests \
	books/store-files \
	books/store-files-invariants \
	tests/acl2/store-files-tests \
	books/store-files-traces \
	tests/acl2/store-files-traces-tests \
	tests/acl2/store-files-exploration-tests \
	tests/acl2/store-files-teeth-tests \
	books/store-node \
	books/store-node-existing-invariants \
	books/poster-bytes \
	books/store-node-invariants-base \
	books/store-node-invariants \
	books/acceptance-stamp-invariants \
	tests/acl2/acceptance-stamp-tests \
	tests/acl2/held-rows-tests \
	tests/acl2/held-rows-intern-tests \
	tests/acl2/store-node-tests \
	tests/acl2/consumer-store-node-tests \
	tests/acl2/store-node-existing-tests \
	books/store-intern \
	tests/acl2/store-intern-tests \
	books/store-existing-alpha \
	tests/acl2/store-existing-alpha-tests \
	books/store-recover-stream \
	tests/acl2/store-recover-stream-tests \
	books/store-node-traces-prepare \
	books/store-node-traces \
	tests/acl2/store-node-traces-tests \
	books/store-prepare-correspondence \
	tests/acl2/store-prepare-correspondence-tests \
	tests/acl2/store-prepare-carried-tests \
	books/store-node-retention \
	tests/acl2/store-node-retention-tests \
	books/store-budget \
	tests/acl2/store-budget-tests \
	books/store-budget-stored \
	tests/acl2/store-budget-stored-tests \
	books/store-carried-folds \
	tests/acl2/store-carried-folds-tests \
	books/store-profile-facts \
	books/store-replay-bound \
	tests/acl2/store-replay-bound-tests \
	books/store-export \
	tests/acl2/store-export-tests \
	books/store-export-stream \
	tests/acl2/store-export-stream-tests \
	books/store-import-stream \
	tests/acl2/store-import-stream-tests \
	books/store-export-durability \
	tests/acl2/store-export-durability-tests \
	books/store-import-publication \
	tests/acl2/store-import-publication-tests \
	books/store-init-publication \
	tests/acl2/store-init-publication-tests \
	tests/acl2/store-profile-facts-tests \
	books/store-genesis \
	tests/acl2/store-genesis-tests \
	books/store-format-9 \
	books/store-format-9-records \
	tests/acl2/store-format-9-tests \
	tests/acl2/store-format-9-records-tests \
	books/store-profile-open \
	tests/acl2/store-profile-open-tests \
	books/store-profile-namespace \
	tests/acl2/store-profile-namespace-tests \
	books/store-mount-identity \
	tests/acl2/store-mount-identity-tests \
	books/store-checkpoint-open \
	books/store-checkpoint-codec \
	tests/acl2/store-checkpoint-open-tests \
	books/owner-checkpoint-open \
	tests/acl2/owner-checkpoint-open-tests \
	tests/acl2/store-checkpoint-tables-tests \
	tests/acl2/store-checkpoint-arena-tests \
	books/heap-store-figure \
	books/heap-figure \
	books/heap-open-nursery \
	tests/acl2/heap-open-nursery-tests \
	books/heap-reservation \
	tests/acl2/heap-reservation-tests \
	tests/acl2/heap-figure-tests \
	books/connection-budget \
	tests/acl2/connection-budget-tests \
	books/store-open-pre-c1 \
	tests/acl2/store-open-pre-c1-tests \
	books/store-open-replay-refusal \
	tests/acl2/store-open-replay-refusal-tests \
	tests/acl2/history-fold-refinement-tests \
	tests/acl2/linear-recognizers-tests \
	tests/acl2/open-one-pass-tests \
	books/byte-store-state-checkpoint-program \
	books/byte-store-range-read \
	tests/acl2/byte-store-state-checkpoint-program-tests \
	books/store-node-resolution \
	books/store-identity-sequence-invariants \
	tests/acl2/store-identity-sequence-invariants-tests \
	books/consumer-store-invariants \
	tests/acl2/consumer-store-invariants-tests \
	tests/acl2/store-node-resolution-tests \
	tests/acl2/store-node-resolution-traces-tests \
	tests/acl2/store-identity-traces-tests \
	books/store-sweep \
	tests/acl2/store-sweep-tests \
	books/store-observed \
	tests/acl2/store-observed-tests \
	books/store-observed-traces \
	tests/acl2/store-observed-traces-tests \
	books/byte-store \
	books/byte-store-invariants \
	books/byte-store-scan \
	books/byte-store-stable-prefix \
	tests/acl2/byte-store-stable-prefix-tests \
	books/byte-store-record-fence \
	tests/acl2/byte-store-record-fence-tests \
	books/byte-store-record-provenance-bytes \
	books/byte-store-arena \
	books/byte-store-record-provenance-node \
	books/byte-store-record-provenance-owner \
	books/byte-store-record-provenance \
	tests/acl2/byte-store-record-provenance-tests \
	books/byte-store-k0 \
	books/byte-store-k0-staging \
	books/byte-store-k0-recovery \
	tests/acl2/byte-store-k0-tests \
	tests/acl2/byte-store-k0-recovery-tests \
	books/store-open-bridge \
	tests/acl2/store-open-bridge-tests \
	books/store-open-node-bridge \
	tests/acl2/store-open-node-bridge-tests \
	books/source-projection-bridge \
	tests/acl2/source-projection-bridge-tests \
	books/byte-store-retention-publication \
	tests/acl2/byte-store-retention-publication-tests \
	books/byte-store-keystones \
	books/byte-store-observation \
	tests/acl2/byte-store-observation-tests \
	books/byte-store-observation-scan \
	tests/acl2/byte-store-observation-scan-tests \
	tests/acl2/byte-store-scan-tests \
	tests/acl2/byte-store-sweep-tests \
	books/byte-store-programs \
	tests/acl2/byte-store-tests \
	books/byte-store-frame \
	tests/acl2/byte-store-frame-tests \
	books/byte-store-txn-name \
	tests/acl2/byte-store-txn-name-tests \
	books/byte-store-initializer \
	tests/acl2/byte-store-initializer-tests \
	books/byte-store-relation \
	tests/acl2/byte-store-relation-tests \
	books/byte-store-program-invariants \
	tests/acl2/byte-store-program-invariants-tests \
	books/byte-store-native-correspondence \
	tests/acl2/byte-store-native-correspondence-tests \
	books/byte-store-fault-keystones \
	tests/acl2/byte-store-fault-keystones-tests \
	books/assumptions \
	tests/acl2/assumptions-tests \
	tests/acl2/store-node-guards-tests \
	tests/acl2/store-node-teeth-tests \
	books/checkpoint \
	tests/acl2/checkpoint-tests \
	books/checkpoint-codec \
	tests/acl2/checkpoint-codec-tests \
	books/checkpoint-publish \
	tests/acl2/checkpoint-publish-tests \
	books/checkpoint-compaction \
	tests/acl2/checkpoint-compaction-tests \
	books/store-event-fields \
	books/catalog-load-index \
	tests/acl2/catalog-load-index-tests \
	books/reclaim-tombstone \
	books/reclaim-rule \
	books/store-reclaim \
	books/nntp-reclaimed \
	tests/acl2/store-reclaim-tests \
	books/store-reclaim-buffer \
	tests/acl2/store-reclaim-buffer-tests \
	books/visibility-join \
	tests/acl2/visibility-join-tests \
	books/store-reclaim-holders \
	tests/acl2/store-reclaim-holders-tests \
	tests/acl2/native-status-columns-tests \
	tests/acl2/native-live-pages-tests \
	books/store-reclaim-pack \
	tests/acl2/store-reclaim-pack-tests \
	books/store-reclaim-stream \
	tests/acl2/store-reclaim-stream-tests \
	books/reclaim-admission \
	tests/acl2/reclaim-admission-tests \
	books/store-log \
	tests/acl2/store-log-tests \
	books/store-log-crash \
	books/store-log-kernel \
	books/store-log-recover \
	tests/acl2/store-log-kernel-tests \
	books/store-log-txid \
	tests/acl2/store-log-txid-tests \
	books/owner-batch \
	tests/acl2/owner-batch-tests \
	books/store-log-decode \
	tests/acl2/store-log-decode-tests \
	books/store-log-programs \
	tests/acl2/store-log-programs-tests \
	books/store-log-route \
	tests/acl2/store-log-route-tests \
	books/store-log-kernel-concrete \
	tests/acl2/store-log-kernel-concrete-tests \
	books/store-log-stream \
	tests/acl2/store-log-stream-tests \
	books/store-log-damage \
	tests/acl2/store-log-damage-tests \
	books/store-log-buffer \
	tests/acl2/store-log-buffer-tests \
	books/store-log-walk-once \
	tests/acl2/store-log-walk-once-tests \
	books/store-log-segments \
	tests/acl2/store-log-segments-tests \
	books/store-log-reclaim \
	tests/acl2/store-log-reclaim-tests \
	books/reclaim-instant \
	tests/acl2/reclaim-instant-tests \
	books/store-log-route-phases \
	books/store-log-extend \
	tests/acl2/store-log-extend-tests \
	books/store-init-log-publication \
	tests/acl2/store-init-log-publication-tests \
	books/owner-feed-txid-reuse \
	tests/acl2/owner-feed-txid-reuse-tests \
	books/byte-store-log-initializer \
	tests/acl2/byte-store-log-initializer-tests \
	books/owner-log-route \
	tests/acl2/owner-log-route-tests \
	books/payload-lz \
	tests/acl2/payload-lz-tests \
	books/payload-lz-value \
	books/payload-lz-record \
	books/payload-lz-replay \
	tests/acl2/payload-lz-record-tests \
	books/payload-lz-append \
	tests/acl2/payload-lz-append-tests \
	books/checkpoint-auxiliary \
	tests/acl2/checkpoint-auxiliary-tests \
	books/hybrid-signature-invariants \
	tests/acl2/hybrid-signature-invariants-tests \
	books/index \
	tests/acl2/index-tests \
	books/msgid-index \
	tests/acl2/msgid-index-tests \
	books/bp-ingress \
	tests/acl2/bp-ingress-tests \
	tests/acl2/bp-ingress-guards-tests \
	books/bp-ingress-carried \
	books/snoc-list \
	tests/acl2/bp-ingress-carried-tests \
	tests/acl2/snoc-list-tests \
	books/record-width-producers \
	tests/acl2/record-width-producers-tests \
	tests/acl2/profile-monotonicity-tests \
	books/store-budget-article \
	tests/acl2/store-budget-article-tests \
	books/store-maintenance-reserve \
	tests/acl2/store-maintenance-reserve-tests \
	books/store-capacity-vector \
	tests/acl2/store-capacity-vector-tests \
	books/store-capacity-config \
	tests/acl2/store-capacity-config-tests \
	books/config-carried-candidate \
	tests/acl2/config-carried-candidate-tests \
	books/config-carried-open \
	tests/acl2/config-carried-open-tests \
	tests/acl2/config-carried-readback-tests \
	books/config-policy-delta \
	tests/acl2/config-policy-delta-tests \
	books/bp-adu \
	tests/acl2/bp-adu-tests \
	books/bp-primary-cbor \
	books/bp-primary \
	books/bp-primary-invariants \
	tests/acl2/bp-primary-tests \
	books/bp-status-report \
	books/bp-status-report-invariants \
	tests/acl2/bp-status-report-tests \
	books/bp-bundle \
	books/bp-bundle-invariants \
	tests/acl2/bp-bundle-tests \
	books/bp-node \
	tests/acl2/bp-node-tests \
	books/bp-node-records \
	tests/acl2/bp-node-records-tests \
	books/outcome-class \
	books/bp-run-class \
	books/bp-node-profile \
	tests/acl2/bp-node-host-tests \
	books/bp-authored-wire \
	tests/acl2/bp-authored-wire-tests \
	books/bp-sequence-persistence \
	tests/acl2/bp-sequence-persistence-tests \
	books/bp-node-machine \
	books/bp-contact-service \
	tests/acl2/bp-contact-service-tests \
	books/bp-app-handoff \
	tests/acl2/bp-app-handoff-tests \
	books/bp-app-handoff-time \
	tests/acl2/bp-app-handoff-time-tests \
	books/bp-report-deletion \
	tests/acl2/bp-report-deletion-tests \
	books/bp-handoff-status \
	tests/acl2/bp-handoff-status-tests \
	books/bp-session-admission \
	tests/acl2/bp-session-admission-tests \
	books/bp-channel-ingress \
	tests/acl2/bp-channel-ingress-tests \
	books/bp-listener-set \
	tests/acl2/bp-listener-set-tests \
	books/bp-node-forward-plan \
	tests/acl2/bp-node-forward-plan-tests \
	books/bp-signed-binding \
	tests/acl2/bp-signed-binding-tests \
	books/post-identity-index \
	tests/acl2/post-identity-index-tests \
	books/post-retain-carried \
	tests/acl2/post-retain-carried-tests \
	books/store-profile-carried \
	tests/acl2/store-profile-carried-tests \
	books/replay-identity-index \
	tests/acl2/replay-identity-index-tests \
	books/bp-fnbs-delivery-codec \
	tests/acl2/bp-fnbs-delivery-codec-tests \
	books/bp-fnbs-delivery-replay \
	tests/acl2/bp-fnbs-delivery-replay-tests \
	books/bp-fnbs-delivery-publication \
	tests/acl2/bp-fnbs-delivery-publication-tests \
	books/bp-node-machine-codec \
	books/bp-node-machine-invariants \
	books/bp-node-machine-guards \
	books/bp-node-machine-authorization \
	tests/acl2/bp-node-machine-tests \
	books/bp-node-foundation \
	tests/acl2/bp-node-foundation-tests \
	books/bp-node-fragment-family \
	tests/acl2/bp-node-fragment-family-tests \
	books/bp-node-fragment-plan \
	tests/acl2/bp-node-fragment-plan-tests \
	books/bp-node-fragment-expiry \
	tests/acl2/bp-node-fragment-expiry-tests \
	books/bp-fnbs-family-codec \
	tests/acl2/bp-fnbs-family-codec-tests \
	books/bp-fnbs-deletion-codec \
	tests/acl2/bp-fnbs-deletion-codec-tests \
	books/bp-node-fragment-replacement \
	tests/acl2/bp-node-fragment-replacement-tests \
	books/bp-fnbs-family-replay \
	tests/acl2/bp-fnbs-family-replay-tests \
	books/bp-node-profile-replay \
	tests/acl2/bp-node-profile-tests \
	books/bp-node-profile-admission \
	tests/acl2/bp-node-profile-admission-tests \
	books/bp-node-fragment-step \
	tests/acl2/bp-node-fragment-step-tests \
	books/bp-node-fragment-guards \
	books/bp-node-report-step \
	tests/acl2/bp-node-report-step-tests \
	books/bp-report-outbox \
	tests/acl2/bp-report-outbox-tests \
	books/bp-report-author \
	tests/acl2/bp-report-author-tests \
	books/bp-node-progress \
	tests/acl2/bp-forward-live-tests \
	books/bp-forward-image \
	tests/acl2/bp-forward-image-tests \
	books/bp-forward-attempt \
	tests/acl2/bp-forward-attempt-tests \
	books/bp-fnbs-forward-codec \
	tests/acl2/bp-fnbs-forward-codec-tests \
	books/bp-fnbs-forward-publication \
	tests/acl2/bp-fnbs-forward-replay-tests \
	books/bp-node-progress-invariants \
	books/bp-node-progress-guards \
	books/bp-node-progress-premises \
	tests/acl2/bp-node-progress-premises-tests \
	books/bp-node-progress-bridge \
	books/bp-node-fragment-jobs \
	tests/acl2/bp-node-fragment-jobs-tests \
	books/bp-fnbs-conflict-codec \
	books/bp-fnbs-conflict-invariants \
	books/bp-fnbs-conflict-publication \
	books/bp-node-machine-gaps \
	books/bp-node-busy-delivery \
	books/bp-node-receipt-send \
	books/bp-fnbs-replay-append \
	books/bp-node-rotation-codec \
	books/bp-node-rotation \
	books/bp-node-rotation-slice \
	books/bp-node-rotation-buffer \
	tests/acl2/bp-node-rotation-buffer-tests \
	books/bp-held-projection \
	tests/acl2/bp-held-projection-tests \
	books/bp-handoff-report \
	tests/acl2/bp-handoff-report-tests \
	books/bp-request-ref \
	books/bp-request-reference \
	tests/acl2/bp-request-reference-tests \
	books/bp-held-payload \
	tests/acl2/bp-held-payload-tests \
	books/bp-node-rotation-step \
	books/bp-node-retire \
	tests/acl2/bp-node-retire-tests \
	tests/acl2/bp-node-counterexamples-tests \
	books/bp-node-rotation-due \
	tests/acl2/bp-node-rotation-due-tests \
	books/bp-node-progress-selection-invariants \
	tests/acl2/bp-node-machine-teeth-tests \
	books/bp-node-forward-retry \
	tests/acl2/bp-node-forward-retry-tests \
	books/bp-route \
	books/bp-route-step \
	tests/acl2/bp-route-tests \
	tests/acl2/bp-node-receipt-send-tests \
	books/bp-route-jobs \
	tests/acl2/bp-route-jobs-tests \
	books/bp-node-contact-driver \
	tests/acl2/bp-node-contact-driver-tests \
	books/bp-node-job-offer \
	books/bp-node-job-offer-progress \
	tests/acl2/bp-node-job-offer-tests \
	books/bp-node-job-cursor \
	tests/acl2/bp-node-job-cursor-tests \
	books/bp-node-run-class \
	tests/acl2/bp-run-class-tests \
	tests/acl2/outcome-class-tests \
	books/bp-node-forward-resume \
	tests/acl2/bp-node-forward-resume-tests \
	books/bp-fnbs-dispatch-codec \
	books/bp-fnbs-dispatch-invariants \
	books/bp-node-dispatch \
	books/bp-fnbs-dispatch-publication \
	tests/acl2/bp-fnbs-dispatch-codec-tests \
	books/bp-report-observe \
	tests/acl2/bp-report-observe-tests \
	books/bp-report-guards \
	books/bp-fnbs-deletion-publication \
	tests/acl2/bp-fnbs-deletion-publication-tests \
	books/bp-fnbs-family-publication \
	tests/acl2/bp-fnbs-family-publication-tests \
	books/bp-node-receive-boundary \
	tests/acl2/bp-node-receive-boundary-tests \
	books/bp-fnbs-codec \
	books/bp-fnbs-inspect \
	tests/acl2/bp-fnbs-inspect-tests \
	books/bp-fnbs-codec-invariants \
	tests/acl2/bp-fnbs-codec-tests \
	books/bp-fnbs-byte-publisher \
	books/bp-fnbs-byte-invariants \
	books/bp-fnbs-replay \
	books/bp-fnbs-replay-invariants \
	tests/acl2/bp-fnbs-replay-tests \
	books/bp-fnbs-namespace \
	tests/acl2/bp-fnbs-namespace-tests \
	books/bp-node-debt \
	tests/acl2/bp-node-debt-tests \
	books/bp-node-debt-cache-invariants \
	tests/acl2/bp-node-debt-cache-tests \
	tests/acl2/bp-node-forwarding-teeth-tests \
	books/bp-fnbs-publication \
	tests/acl2/bp-fnbs-publication-tests \
	books/bp-clock-domain \
	tests/acl2/bp-clock-domain-tests \
	tests/acl2/bp-fnbs-byte-publisher-tests \
	tests/acl2/bp-fnbs-byte-counterexamples \
	books/bp-sequence-fidelity \
	tests/acl2/bp-sequence-fidelity-tests \
	books/bp-receive-evidence \
	tests/acl2/bp-receive-evidence-tests \
	tests/acl2/bp-node-machine-authorization-tests \
	books/bp-fragment \
	books/bp-fragment-invariants \
	books/bp-fragment-fast \
	books/bp-fragment-sweep \
	books/bp-fragment-resume \
	tests/acl2/bp-fragment-resume-tests \
	books/bp-limits \
	tests/acl2/bp-fragment-tests \
	tests/acl2/bp-fragment-fast-tests \
	tests/acl2/bp-fragment-sweep-tests \
	tests/acl2/bp-limits-tests \
	books/bp-fragment-send \
	tests/acl2/bp-fragment-send-tests \
	books/clock \
	books/clock-invariants \
	tests/acl2/clock-tests \
	books/tcpcl-records \
	books/tcpcl-octets \
	books/tcpcl-session \
	books/tcpcl-invariants \
	books/tcpcl-host-drive \
	books/tcpcl-delivery \
	books/tcpcl-delivery-invariants \
	tests/acl2/tcpcl-tests \
	tests/acl2/tcpcl-delivery-tests \
	books/anchor \
	books/anchor-wire \
	books/anchor-servers \
	books/anchor-replace \
	books/anchor-record \
	books/anchor-invariants \
	tests/acl2/anchor-tests \
	tests/acl2/anchor-wire-tests \
	tests/acl2/anchor-server-tests \
	tests/acl2/anchor-replace-tests \
	tests/acl2/anchor-teeth-tests \
	books/membership-epochs \
	books/membership-epochs-invariants \
	tests/acl2/membership-epochs-tests \
	books/bp-workflow \
	books/bp-workflow-invariants \
	books/bp-workflow-transport-invariants \
	books/bp-workflow-binding-core \
	books/bp-workflow-binding-invariants \
	tests/acl2/bp-workflow-binding-invariants-tests \
	tests/acl2/bp-workflow-tests \
	tests/acl2/bp-workflow-teeth-tests \
	books/app-journal \
	tests/acl2/journal-publish-tests \
	books/bp-workflow-records \
	books/bp-workflow-records-invariants \
	books/bp-workflow-replay-status \
	tests/acl2/bp-workflow-records-tests \
	tests/acl2/bp-workflow-records-guards-tests \
	books/bp-receipt \
	tests/acl2/bp-receipt-tests \
	books/bp-receipt-alpha \
	tests/acl2/bp-receipt-alpha-tests \
	books/bp-receipt-records \
	tests/acl2/bp-receipt-records-tests \
	books/bp-native-app \
	tests/acl2/bp-native-app-tests \
	books/bp-native-app-fast \
	tests/acl2/bp-native-app-fast-tests \
	books/bp-transit-join \
	tests/acl2/bp-transit-join-tests \
	books/bp-release-authority \
	tests/acl2/bp-release-authority-tests \
	books/bp-receiver-store-invariants \
	books/bp-receiver-context-invariants \
	books/bp-receiver-journal-invariants \
	books/bp-receiver-invariants \
	books/bp-receiver-retention-invariants \
	books/bp-receiver-state-invariants \
	books/bp-receiver-trace-invariants \
	tests/acl2/bp-receiver-invariants-tests \
	tests/acl2/bp-receiver-teeth-tests \
	books/bp-receiver-evolving-history-invariants \
	books/bp-receiver-evolving-node-invariants \
	books/bp-receiver-evolving-store-invariants \
	tests/acl2/bp-receiver-evolving-tests \
	books/bp-outbound \
	tests/acl2/bp-outbound-tests \
	tests/acl2/bp-outbound-guards-tests \
	books/bp-ion-observation \
	tests/acl2/bp-ion-observation-tests \
	books/bp-ion-workflow \
	tests/acl2/bp-ion-workflow-tests \
	books/bp-ion-workflow-replay \
	tests/acl2/bp-ion-workflow-replay-tests \
	books/bp-request-plan \
	tests/acl2/bp-request-plan-tests \
	books/bp-request-recovery \
	tests/acl2/bp-request-recovery-tests \
	books/journal \
	tests/acl2/journal-tests \
	books/exchange \
	tests/acl2/exchange-tests \
	books/exchange-invariants \
	books/transfer \
	books/transfer-reservation \
	books/transfer-union \
	books/transfer-invariants \
	books/transfer-assembly-invariants \
	books/transfer-work \
	books/transfer-public-work \
	books/transfer-public-bound \
	tests/acl2/transfer-tests \
	books/transfer-journal \
	books/transfer-journal-invariants \
	tests/acl2/transfer-journal-tests \
	books/container \
	books/container-invariants \
	tests/acl2/container-tests \
	books/nntp-syntax \
	books/nntp-session \
	books/nntp-projection \
	books/nov-fields \
	books/nntp-article-pass \
	books/nntp-responses \
	books/nntp-article-block \
	books/nntp-reader-compat \
	books/nntp \
	books/nntp-overview \
	books/nntp-legacy \
	books/nntp-xpat \
	books/nntp-search-scope \
	books/nntp-newnews \
	books/nntp-invariants \
	books/nntp-effects \
	tests/acl2/nntp-tests \
	tests/acl2/nntp-pinned-index-tests \
	tests/acl2/nntp-teeth-tests \
	books/mailbox \
	books/injection-shape \
	books/injection-path \
	books/injection \
	books/injection-invariants \
	tests/acl2/injection-tests \
	books/nntp-post \
	books/nntp-pinned-effects \
	books/nntp-pinned-msgid \
	tests/acl2/nntp-pinned-msgid-tests \
	books/nntp-list-counts \
	tests/acl2/nntp-list-counts-tests \
	tests/acl2/group-descriptions-tests \
	tests/acl2/nntp-xref-tests \
	tests/acl2/nntp-reader-compat-tests \
	tests/acl2/nntp-article-block-tests \
	tests/acl2/posting-account-tests \
	tests/acl2/injection-info-params-tests \
	tests/acl2/owner-injection-info-tests \
	tests/acl2/nntp-post-tests \
	tests/acl2/served-line-iterative-tests \
	books/path \
	books/path-update \
	books/path-update-tail \
	books/peer-config \
	books/peer-inbound \
	books/peer-inbound-invariants \
	tests/acl2/peer-inbound-tests \
	books/peer-transit-forms \
	tests/acl2/peer-transit-forms-tests \
	books/relay-checks \
	books/refused-offers \
	books/peer-refused-offers \
	tests/acl2/transit-hygiene-tests \
	books/nntp-auth \
	tests/acl2/nntp-auth-tests \
	books/served \
	books/served-tls-prefix \
	books/served-implicit-tls \
	tests/acl2/served-implicit-tls-tests \
	books/owner-tls-prefix \
	books/owner-config-observe \
	books/peer-offer-indexed \
	books/peer-guard-carried \
	books/served-carried \
	books/owner-served-carried \
	books/wire-span \
	books/wire-scan \
	books/served-scan \
	books/served-span \
	books/owner-offer-indexed \
	books/store-events-carried \
	books/owner-commit-carried \
	books/owner-prepare-carried \
	books/store-prepare-carried \
	books/records-concrete \
	books/records-concrete-owner \
	books/records-attach-concrete \
	books/msgid-index-concrete \
	books/octets-stobj \
	books/octet-text \
	books/payload-arena-bytes \
	books/payload-arena-paged \
	books/payload-arena-extent-logic \
	books/payload-arena-extent \
	books/store-intern-once \
	tests/acl2/store-intern-once-tests \
	books/payload-extent \
	books/payload-commit-extent \
	books/frame-digest-buffer \
	books/payload-extent-read \
	books/payload-arena \
	books/payload-arena-attach \
	books/records-freeze \
	books/catalog-record \
	books/catalog \
	books/catalog-commit \
	books/catalog-delta \
	books/catalog-relation \
	books/catalog-view \
	books/catalog-entries \
	books/catalog-refresh \
	books/catalog-number-index \
	books/served-catalog-view \
	books/served-columns \
	tests/acl2/served-columns-tests \
	books/served-catalog \
	books/served-catalog-chain \
	books/served-catalog-owner \
	books/served-catalog-join-refresh \
	books/served-catalog-join-step \
	books/served-catalog-join \
	books/served-catalog-join-number \
	books/served-catalog-join-open \
	books/served-catalog-join-entry \
	books/served-catalog-join-finish \
	books/served-catalog-join-conns \
	books/served-catalog-join-frame \
	books/served-catalog-join-frame-conns \
	books/served-catalog-join-frame-store \
	books/served-catalog-join-pinned \
	books/served-catalog-join-read \
	books/served-catalog-join-inv \
	books/poster-bytes-buffer \
	books/store-checkpoint-buffer \
	books/store-checkpoint-reader \
	books/store-checkpoint-tables \
	books/store-checkpoint-tables-reader \
	books/owner-checkpoint-writer \
	books/owner-checkpoint-pipeline \
	books/store-checkpoint-arena \
	books/store-checkpoint-share \
	books/store-checkpoint-arena-load \
	books/store-checkpoint-arena-writer \
	tests/acl2/octets-stobj-tests \
	tests/acl2/octet-text-tests \
	tests/acl2/hostile-reader-archive \
	tests/acl2/octets-bulk-tests \
	tests/acl2/payload-arena-tests \
	tests/acl2/payload-arena-paged-tests \
	tests/acl2/payload-arena-extent-tests \
	tests/acl2/payload-extent-tests \
	tests/acl2/payload-commit-extent-tests \
	tests/acl2/frame-digest-buffer-tests \
	tests/acl2/records-freeze-tests \
	tests/acl2/catalog-record-tests \
	tests/acl2/catalog-tests \
	tests/acl2/catalog-commit-tests \
	tests/acl2/catalog-delta-tests \
	tests/acl2/catalog-relation-tests \
	tests/acl2/catalog-view-tests \
	tests/acl2/catalog-entries-tests \
	tests/acl2/catalog-refresh-tests \
	tests/acl2/served-catalog-tests \
	tests/acl2/served-catalog-view-tests \
	tests/acl2/served-catalog-chain-tests \
	tests/acl2/served-catalog-scan-tests \
	tests/acl2/served-catalog-owner-tests \
	tests/acl2/served-catalog-join-tests \
	tests/acl2/served-catalog-join-open-tests \
	tests/acl2/served-catalog-join-entry-tests \
	tests/acl2/served-catalog-join-finish-tests \
	tests/acl2/served-catalog-join-frame-conns-tests \
	tests/acl2/served-catalog-join-frame-store-tests \
	tests/acl2/served-catalog-join-pinned-tests \
	tests/acl2/served-catalog-join-inv-tests \
	books/acceptance-payload-ref \
	tests/acl2/acceptance-payload-ref-tests \
	books/payload-kinds \
	tests/acl2/payload-kinds-tests \
	books/owner-feed-article \
	tests/acl2/owner-feed-article-tests \
	tests/acl2/catalog-number-index-tests \
	books/octet-window \
	books/subject-id-buffer \
	tests/acl2/subject-id-buffer-tests \
	books/owner-advance-carried \
	books/owner-intent-carried \
	books/owner-commit-ocl \
	books/owner-recover-ocl \
	tests/acl2/owner-tls-pin-tests \
	tests/acl2/served-tls-prefix-tests \
	tests/acl2/served-pipelining-tests \
	books/nntp-auth-invariants \
	books/nntp-help \
	tests/acl2/nntp-help-tests \
	books/nntp-auth-fold \
	tests/acl2/served-tests \
	tests/acl2/nntp-auth-teeth-tests \
	tests/acl2/nntp-auth-fold-tests \
	books/config-stream \
	tests/acl2/config-stream-tests \
	books/config-physical-replay \
	tests/acl2/config-physical-replay-tests \
	books/config-observed \
	tests/acl2/config-observed-tests \
	books/config-store-traces \
	tests/acl2/config-store-traces-tests \
	books/config-owner-live \
	books/config-owner-advance-invariants \
	tests/acl2/config-owner-advance-invariants-tests \
	books/config-owner-advance-reader-invariants \
	tests/acl2/config-owner-advance-reader-invariants-tests \
	books/config-owner-read-invariants \
	tests/acl2/config-owner-read-invariants-tests \
	tests/acl2/config-owner-live-tests \
	tests/acl2/owner-config-observe-tests \
	tests/acl2/owner-served-carried-tests \
	tests/acl2/wire-span-tests \
	tests/acl2/served-span-tests \
	tests/acl2/served-scan-tests \
	tests/acl2/peer-offer-indexed-tests \
	tests/acl2/peer-guard-carried-tests \
	tests/acl2/owner-commit-carried-tests \
	tests/acl2/owner-prepare-carried-tests \
	books/store-budget-stored-post \
	tests/acl2/store-budget-stored-post-tests \
	tests/acl2/records-concrete-tests \
	tests/acl2/msgid-index-concrete-tests \
	tests/acl2/owner-advance-carried-tests \
	tests/acl2/owner-intent-carried-tests \
	tests/acl2/store-events-carried-tests \
	tests/acl2/owner-recover-ocl-tests \
	books/config-owner-publish \
	tests/acl2/config-owner-publish-tests \
	books/config-owner-carried \
	tests/acl2/config-owner-carried-tests \
	books/config-store-steps \
	books/owner-log-ocl \
	tests/acl2/owner-log-ocl-tests \
	books/config-owner-live-authorize \
	tests/acl2/config-owner-live-authorize-tests \
	books/owner-prepare-served \
	books/store-prepare-served \
	tests/acl2/store-prepare-served-tests \
	books/owner-prepare-served-ocl \
	tests/acl2/owner-prepare-served-tests \
	tests/acl2/owner-prepare-served-events-tests \
	tests/acl2/owner-identity-served-tests \
	tests/acl2/owner-prepare-served-abort-tests \
	books/owner-prepare-outcome \
	tests/acl2/owner-prepare-outcome-tests \
	books/owner-prepare-outcome-topic \
	tests/acl2/owner-prepare-outcome-topic-tests \
	books/native-control-launch \
	tests/acl2/native-control-launch-tests \
	books/clock-reading \
	tests/acl2/clock-reading-tests \
	books/provenance-inspect \
	tests/acl2/provenance-inspect-tests \
	books/config-crash-replay \
	tests/acl2/config-crash-replay-tests \
	books/owner-config \
	books/ideal \
	books/nntp-index \
	tests/acl2/nntp-index-tests \
	tests/acl2/serve-depth-tests \
	books/nntp-index-runtime \
	books/group-number-index \
	books/group-bucket-index \
	books/group-bucket-article \
	books/group-bucket-article-invariants \
	books/group-bucket-invariants \
	books/nntp-range-indexed \
	books/nntp-range-indexed-invariants \
	tests/acl2/group-bucket-index-tests \
	tests/acl2/nntp-range-indexed-tests \
	tests/acl2/nntp-reader-profile-tests \
	tests/acl2/nntp-legacy-tests \
	tests/acl2/nntp-xpat-tests \
	tests/acl2/nntp-search-scope-tests \
	tests/acl2/nntp-newnews-tests \
	books/bp-release \
	books/bp-release-invariants \
	books/bp-workflow-constructors \
	books/bp-release-replay-status \
	tests/acl2/bp-release-tests \
	books/scheduler \
	books/scheduler-invariants \
	tests/acl2/scheduler-tests \
	books/peer-feed \
	books/peer-feed-invariants \
	books/feed-events \
	books/feed-correspondence \
	books/feed-port-replay \
	books/feed-journal \
	tests/acl2/feed-journal-tests \
	tests/acl2/peer-feed-tests \
	tests/acl2/feed-correspondence-tests \
	tests/acl2/feed-port-replay-tests \
	books/owner-feed \
	books/owner-feed-port \
	tests/acl2/owner-feed-port-tests \
	tests/acl2/owner-feed-tests \
	books/owner \
	books/transit-header-limits \
	tests/acl2/transit-header-limits-tests \
	tests/acl2/owner-feed-form-tests \
	books/owner-invariants \
	books/owner-fault \
	books/owner-feed-subject \
	books/owner-prepare-correspondence \
	books/owner-served-invariants \
	books/owner-numbering \
	books/owner-retention-preparation \
	books/owner-agent \
	books/owner-log \
	books/owner-results \
	books/owner-served-bound \
	books/transit-bound \
	tests/acl2/wire-bounds-tests \
	books/owner-log-reopen \
	books/owner-bound-commit \
	books/consumer-event-index \
	tests/acl2/consumer-event-index-tests \
	books/history-columns \
	books/history-columns-relation \
	tests/acl2/history-columns-relation-tests \
	tests/acl2/history-columns-tests \
	books/pagestore-words \
	books/pagestore-words-blake3 \
	books/pagestore \
	books/pagestore-keystones \
	books/pagestore-reclaim \
	books/pagestore-exec \
	books/pagestore-gc \
	tests/acl2/pagestore-tests \
	books/pagestore-refine \
	tests/acl2/pagestore-refine-tests \
	books/history-columns-store \
	tests/acl2/history-columns-store-tests \
	books/snapshot-segments \
	tests/acl2/snapshot-segments-tests \
	books/consumer-poll-index \
	tests/acl2/consumer-poll-index-tests \
	books/consumer-owner-local \
	tests/acl2/consumer-owner-local-tests \
	books/consumer-owner-local-progress \
	tests/acl2/consumer-owner-local-progress-tests \
	books/consumer-bound \
	tests/acl2/consumer-bound-tests \
	books/consumer-wait-codec \
	tests/acl2/consumer-wait-codec-tests \
	books/consumer-wait \
	tests/acl2/consumer-wait-tests \
	books/consumer-reason \
	tests/acl2/consumer-reason-tests \
	books/consumer-withdrawal \
	tests/acl2/consumer-withdrawal-tests \
	books/consumer-owner-index-invariants \
	tests/acl2/consumer-owner-index-invariants-tests \
	tests/acl2/owner-tests \
	books/poster-bytes-invariants \
	tests/acl2/poster-bytes-tests \
	tests/acl2/source-routes-tests \
	books/consumer-artifact-retry \
	tests/acl2/consumer-artifact-retry-tests \
	books/relay-source \
	tests/acl2/relay-source-routes-tests \
	tests/acl2/owner-served-invariants-tests \
	tests/acl2/owner-numbering-tests \
	tests/acl2/owner-fault-tests \
	tests/acl2/owner-verdict-tests \
	tests/acl2/owner-verdict-read-tests \
	tests/acl2/owner-signed-post-tests \
	tests/acl2/owner-operator-tests \
	tests/acl2/owner-agent-tests \
	tests/acl2/owner-log-tests \
	tests/acl2/owner-results-tests \
	tests/acl2/owner-served-bound-tests \
	tests/acl2/owner-log-reopen-tests \
	tests/acl2/owner-bound-commit-tests \
	tests/acl2/owner-config-tests \
	tests/acl2/owner-prepare-correspondence-tests \
	books/owner-store-budget \
	tests/acl2/owner-store-budget-tests \
	books/store-budget-naming \
	tests/acl2/store-budget-naming-tests \
	tests/acl2/owner-retention-preparation-tests \
	books/relay \
	books/relay-invariants \
	books/relay-crash-invariants \
	tests/acl2/relay-tests \
	books/crypto-seam \
	tests/acl2/crypto-seam-tests \
	tests/acl2/hybrid-signature-tests \
	books/hybrid-carrier \
	tests/acl2/hybrid-carrier-tests \
	books/hybrid-store-injected \
	books/hybrid-store-invariants \
	books/control-classify \
	books/peer-authored-accept \
	tests/acl2/peer-authored-accept-tests \
	books/peer-carriage-rows \
	books/peer-carriage \
	books/owner-parse-carried \
	tests/acl2/owner-parse-carried-tests \
	books/owner-identity-intern \
	tests/acl2/owner-identity-intern-tests \
	books/owner-identity-served \
	tests/acl2/peer-carriage-tests \
	books/peer-pull \
	tests/acl2/peer-pull-tests \
	books/peer-pull-session \
	tests/acl2/peer-pull-session-tests \
	books/peer-catchup-serve \
	books/peer-catchup-effects \
	books/peer-catchup \
	tests/acl2/peer-catchup-tests \
	books/protocol-table \
	books/protocol-builders \
	books/protocol-codes-rows \
	books/protocol-codes \
	books/protocol-framing \
	books/protocol-dispatch \
	tests/acl2/protocol-codes-tests \
	tests/acl2/protocol-dispatch-tests \
	tests/acl2/protocol-codes-hra-tests \
	tests/acl2/protocol-text-tests \
	tests/acl2/control-tests \
	books/control-authority \
	tests/acl2/control-authority-tests \
	books/key-statements \
	tests/acl2/key-statements-tests \
	books/peer-invite \
	tests/acl2/peer-invite-tests \
	books/tls-reload \
	tests/acl2/tls-reload-tests \
	books/control-visible \
	tests/acl2/control-visible-tests \
	books/control-visible-indexed \
	tests/acl2/control-visible-indexed-tests \
	books/owner-refresh-indexed \
	tests/acl2/owner-refresh-indexed-tests \
	books/node-secret \
	tests/acl2/node-secret-tests \
	books/cancel-lock-lines \
	books/cancel-lock \
	tests/acl2/cancel-lock-tests \
	tests/acl2/owner-cancel-lock-tests \
	tests/acl2/owner-cancel-refresh-tests \
	books/cancel-lock-d25 \
	tests/acl2/cancel-lock-d25-tests \
	books/control-served \
	tests/acl2/control-served-tests \
	books/nntp-control \
	tests/acl2/nntp-control-tests \
	books/owner-control-read \
	books/nntp-enrollment \
	books/owner-enrollment-read \
	tests/acl2/owner-enrollment-read-tests \
	books/login-binding \
	tests/acl2/login-binding-tests \
	books/login-binding-live \
	tests/acl2/login-binding-live-tests \
	tests/acl2/native-admin-peer-budget-tests \
	tests/acl2/account-list-tests \
	tests/acl2/accounts-snapshot-tests \
	tests/acl2/accounts-tests \
	tests/acl2/feed-totality-tests \
	tests/acl2/group-access-tests \
	tests/acl2/group-status-tests \
	tests/acl2/moderation-tests \
	tests/acl2/peer-host-tests \
	tests/acl2/topic-history-identity-disjoint-tests \
	books/public-exposure \
	tests/acl2/public-exposure-tests \
	books/public-exposure-reply \
	tests/acl2/public-exposure-reply-tests \
	books/served-reply-buffer \
	tests/acl2/served-reply-buffer-tests \
	books/served-plan \
	tests/acl2/served-plan-tests \
	books/owner-scheduler \
	tests/acl2/owner-scheduler-tests \
	books/owner-commit-class \
	tests/acl2/owner-commit-class-tests \
	books/owner-commit-steps \
	tests/acl2/owner-commit-steps-tests \
	books/owner-commit-pipeline \
	tests/acl2/owner-commit-pipeline-tests \
	books/owner-ack-after-barrier \
	tests/acl2/owner-ack-after-barrier-tests \
	books/owner-reader-view \
	tests/acl2/owner-reader-view-tests \
	books/owner-reader-read \
	tests/acl2/owner-reader-read-tests \
	books/clock-wall-reading \
	books/owner-time-model \
	books/owner-time-journal \
	books/owner-time-admission \
	tests/acl2/owner-time-model-tests \
	books/owner-time-journal-writer \
	tests/acl2/owner-time-journal-writer-tests \
	books/owner-stop-drain \
	tests/acl2/owner-stop-drain-tests \
	books/web-request \
	tests/acl2/web-request-tests \
	books/web-2047 \
	books/web-render \
	books/web-render-keystones \
	tests/acl2/web-render-tests \
	books/web-session \
	books/web-session-keystones \
	tests/acl2/web-session-tests \
	books/web-config \
	tests/acl2/web-config-tests \
	books/state-digest \
	tests/acl2/state-digest-tests \
	books/store-log-route-programs \
	tests/acl2/store-log-route-programs-tests \
	books/store-log-open-barriers \
	tests/acl2/store-log-open-barriers-tests \
	books/owner-open-carried \
	tests/acl2/owner-open-carried-tests \
	books/reader-open-carried \
	tests/acl2/reader-open-carried-tests \
	tests/acl2/group-number-index-tests \
	books/topic-history-metadata \
	books/topic-history-metadata-invariants \
	books/topic-history-authorship \
	books/topic-history-admission \
	books/topic-history-store-events \
	books/topic-history-prefix-invariants \
	books/topic-history-store-invariants \
	books/topic-history-recovery-invariants \
	books/topic-history-local-proposals \
	books/topic-history-local-control \
	tests/acl2/topic-history-metadata-tests \
	tests/acl2/topic-history-authorship-tests \
	tests/acl2/topic-history-admission-tests \
	tests/acl2/topic-history-store-events-tests \
	tests/acl2/topic-history-store-union-tests \
	tests/acl2/topic-history-prefix-tests \
	tests/acl2/topic-history-prefix-invariants-tests \
	tests/acl2/topic-history-store-invariants-tests \
	tests/acl2/topic-history-recovery-invariants-tests \
	tests/acl2/topic-history-v2-crash-tests \
	tests/acl2/topic-history-local-admin-tests \
	tests/acl2/topic-history-store-node-tests \
	tests/acl2/consumer-topic-store-tests \
	tests/acl2/topic-history-local-proposals-tests \
	tests/acl2/topic-history-local-control-tests \
	tests/acl2/topic-history-native-vector-tests \
	tests/acl2/hybrid-store-tests \
	books/crypto-attach \
	books/auth-secret \
	tests/acl2/auth-secret-tests \
	books/statement-items \
	books/statement-codec \
	books/statement-seam \
	books/statement-attach \
	books/codec-attach \
	tests/acl2/codec-seam-tests \
	books/statement \
	books/statement-invariants \
	tests/acl2/statement-tests \
	books/principal \
	books/principal-invariants \
	tests/acl2/principal-tests \
	books/lace \
	books/lace-invariants \
	tests/acl2/lace-tests \
	books/policy \
	books/policy-invariants \
	tests/acl2/policy-tests \
	books/stx-carrier \
	books/stx-verify \
	books/stx-reader \
	tests/acl2/stx-reader-tests \
	books/nntp-verdict \
	books/nntp-verdict-effects \
	tests/acl2/nntp-verdict-tests \
	books/stx-invariants \
	books/stx-lace \
	books/stx-index \
	books/stx-policy \
	books/stx-epochs \
	books/stx-authority \
	books/stx-evidence-records \
	books/stx-keyring-records \
	books/stx-accept-records \
	tests/acl2/stx-tests \
	tests/acl2/stx-transit-tests \
	tests/acl2/stx-evidence-records-tests \
	tests/acl2/stx-keyring-records-tests \
	tests/acl2/stx-accept-records-tests \
	tests/acl2/store-node-index-tests \
	tests/acl2/store-node-composite-index-tests \
	books/scheduler-peers \
	tests/acl2/scheduler-peers-tests \
	books/proto/adt-lib \
	books/proto/adt \
	books/proto/adt-consumer-position \
	tests/acl2/proto-adt-tests \
	books/proto/adt-key-lib \
	books/proto/adt-nest-lib \
	books/proto/adt-keyed \
	books/proto/adt-bytes-lib \
	books/proto/adt-bytes \
	books/proto/adt-compact-lib \
	books/proto/adt-config-policy \
	books/proto/adt-config-groups \
	books/proto/adt-topic-accepted-type \
	books/proto/adt-topic-accepted \
	tests/acl2/proto-adt-2-tests \
	books/history-pages \
	tests/acl2/history-pages-tests \
	tests/acl2/history-pages-digest-tests \
	books/history-pages-words \
	books/history-pages-exec \
	books/history-pages-row \
	books/history-pages-read \
	tests/acl2/history-pages-read-tests \
	books/history-pages-arith \
	books/history-pages-write \
	books/history-pages-write-exec \
	books/history-pages-write-keys \
	tests/acl2/history-pages-write-tests \
	books/history-pages-placed \
	books/history-pages-nest \
	books/history-pages-placed-write \
	tests/acl2/history-pages-placed-tests \
	books/history-pages-grow \
	books/history-pages-grow-cap \
	books/history-pages-grow-append \
	books/history-pages-relocate \
	tests/acl2/history-pages-relocate-tests \
	books/history-pages-append-grown \
	books/history-pages-grow-then-append \
	tests/acl2/history-pages-grow-then-append-tests \
	tests/acl2/history-pages-grow-five-tests \
	books/history-pages-step \
	books/history-pages-import \
	books/history-pages-view \
	tests/acl2/history-pages-step-tests \
	tests/acl2/history-pages-import-tests \
	books/history-pages-owner \
	tests/acl2/history-pages-owner-tests \
	books/history-records \
	tests/acl2/history-records-tests

.PHONY: extract-check site check check-lane check-host-translate certify acl2-ld certs-install certs-publish model-test tooling-test test test-modules labs labs-quick
# The books a codec seam has cleared (plan 2026-09-22 §4.1, step T1): none
# opens a codec theory at the top or names a seam's implementation, and
# `make check` fails if one starts to.  Each cluster lane of the step appends
# its books; when the list is every book, `--strict` runs without `--books`.
THEORY_STRICT_BOOKS ?= books/store-events books/replay books/replay-invariants \
	books/store-files books/store-files-invariants books/store-files-traces \
	books/store-node books/store-node-invariants-base books/store-node-invariants \
	books/store-node-traces-prepare \
	books/store-node-traces \
	books/store-node-resolution books/store-observed books/store-observed-traces \
	books/store-prepare-correspondence books/config-records books/node-config \
	books/checkpoint books/checkpoint-compaction books/checkpoint-publish \
	books/records-shape books/statement books/statement-invariants

# The extraction differential (A-EXTRACT, specs/failures.md; lane extract-2):
# the world extracted to a CHICKEN program and compared with the developer
# image -- the served transcripts, the boundary probes, a real store's replies
# and the per-function differential -- on hbox (tools/extract/check.sh; from
# elsewhere tools/extract/remote_check.sh ships the tree with hbox_native.sh).
EXTRACT_REV ?= .
extract-check:
	sh tools/extract/remote_check.sh $(EXTRACT_REV)

# fn's static website: a newsreader over the guides' Usenet articles
# (docs/articles/*.txt) in build/site/ (open build/site/index.html); GitHub
# Pages builds the same thing (.github/workflows/pages.yml).
site:
	$(PYTHON) site/build_site.py --out build/site

# `make check` for a lane worktree: planning/ledger.json, ledger.md and
# current.md are regenerated into one temporary directory and compared there
# (printed, never failing) instead of against the committed files, which a
# lane must not commit.  Their generation still has to succeed, and every
# other check is the same.
check-lane:
	FN_LANE_CHECK=1 FN_LANE_CHECK_DIR=$$(mktemp -d "$${TMPDIR:-/tmp}/fn-lane-check.XXXXXX") $(MAKE) check

# `make check` runs every step even when one fails, then prints a table of
# them (step, exit, seconds, first finding) and fails if any step failed:
# make stops a recipe at its first red line, and one sibling's red step used
# to hide every check after it (tools/check_steps.py).
CHECK_STEPS_DIR ?= build/check-steps
CHECK_STEP = $(PYTHON) tools/check_steps.py run $(CHECK_STEPS_DIR) --

check:
	@$(PYTHON) tools/check_steps.py begin $(CHECK_STEPS_DIR)
	@$(CHECK_STEP) $(PYTHON) tools/check_scaffold.py
# Every command the docs name exists with the grammar the docs give (NNT-032):
# operator invocations are judged by ACL2's grammar in the generated book
# tests/acl2/docs-operator-grammar-tests.lisp, which this fails on when it is
# not what the docs say now; the Python tools' invocations by their own
# argparse parsers; quoted reply lines against the source that prints them.
	@$(CHECK_STEP) $(PYTHON) tools/docs_check.py --check
# The shape-books table in docs/proof-style.md (books by certification
# fan-in, the farm's graph).  A WARNING when stale, never a failure: the
# counts move with every include (lane lane-tools-2, for served-columns).
	@$(CHECK_STEP) $(PYTHON) tools/shape_books.py --check
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_shape_books
# The website renders the guides' articles (site/build_site.py, stdlib only):
# every article is well-formed (tools/docs_articles.py: its headers, its
# Message-ID, 72 columns), every repository path it names exists, and every
# internal link on every page resolves.
	@$(CHECK_STEP) $(PYTHON) site/build_site.py --check --out build/site
# Every byte of a tracked file under books/ and host/ is ASCII (PKT-379): ACL2,
# SBCL's compile-file and the Python tests read them with different default
# encodings; the files that still carry a section sign are listed debt
# (tools/ascii_debt.json, PKT-496) that may only shrink.
	@$(CHECK_STEP) $(PYTHON) tools/ascii_check.py --strict
# A certified registry row must name existing ACL2 events whose defining
# books have source- and include-closure-compatible manifest evidence, and
# must itself cite an archived manifest that certified each event book at its
# current digest. Any warning fails; --explain PRF-xxx names the manifest.
	@$(CHECK_STEP) $(PYTHON) tools/certified_claims.py
# planning/current.md, the per-capability current view, is generated from
# planning/current-view.json and the tree (host call lines, keystones, the
# archived manifests, the tested and deployed images' source digests); this
# fails when it is stale or names something absent.
	@$(CHECK_STEP) $(PYTHON) tools/current_view.py --check
# The fastest passed attempt at each current book/include closure, grouped by
# host and toolchain. The ten-second rule (D26) over
# planning/proof-cost-baseline.json: a new book conclusively (quietly) over
# 11 s, or a baseline book whose prover steps rose over 10%, fails; a loaded
# figure is UNQUIET, a failed attempt FAILED. Installed pairs have no proof time.
	@$(CHECK_STEP) $(PYTHON) tools/proof_cost.py
# The throughput gate (PKT-407): the newest hbox run under
# planning/evidence/throughput/ for HEAD or its nearest measured ancestor,
# against planning/throughput-baseline.json per operation (25% or the
# metric's floor); a regression fails unless planning/throughput-causes.json
# names the run's revision with a reason.  No run: NOT MEASURED, passes.
	@$(CHECK_STEP) $(PYTHON) tools/throughput_gate.py check
# Both images' ACL2-mode prefixes (every include-book and host `ld`) in
# their build order: the dynamic half of the host-names lint.  Needs FN_ACL2
# and installed certificates (make certs-install); without them it is NOT
# RUN, exit 2, a failed step -- never a pass (lane lane-tools-2: loading each
# file alone printed SKIPPED and exited 0 without FN_ACL2, and failed 39/80
# on build order with it).
	@$(CHECK_STEP) $(PYTHON) tools/host_check.py
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_host_check_modes
# specs/crash-model-v2.md section 2.3's check, in both directions: every cut
# the campaign kills at is a :cut of the model program that transcribes its
# host function, and every :cut of a model program is a host faults.at site.
# It is mechanical and needs no ACL2, so it belongs in `check`.  It fails on a
# fidelity defect; missing host cuts and syscall drift are reported and do not
# fail (--strict fails on those too).
	@$(CHECK_STEP) $(PYTHON) tools/transcribe_check.py
# The same transcription check for the native host, which transcribe_check
# does not read: for each program tests/campaign/native_cuts.py names, the
# host function's success-path syscalls, file-kernel observations and fnn-at
# cuts in source order equal the program's steps (kind and directory), and
# every error-arm observation is one of the program's error constants.  A
# source check; it states what it cannot decide.  Mechanical, no ACL2.
	@$(CHECK_STEP) $(PYTHON) tools/native_program_check.py
# No Python on the path a deployed node executes (D35): the process sites in
# host/, the libraries the image loads, the shipped launcher and service files.
	@$(CHECK_STEP) $(PYTHON) tools/runpath_check.py --quiet
# The served command chain is four session records deep and every base
# accessor is `car', so a call that stops one level short is answered with a
# plausible value rather than an error: four such misses shipped on
# 2026-09-20, one of them leaving POST with no reply at all.  This infers
# every formal's session level from the books and fails on a wrong depth.  A
# walk spelled by hand instead of through a named projection is drift and is
# counted, not failed (--strict fails on those too).  Mechanical, no ACL2.
	@$(CHECK_STEP) $(PYTHON) tools/session_depth.py
# Every certification claim in this tree cites a run directory under
# `build/`, which `.gitignore:6` excludes: the directory exists only on the
# box that ran it, and a worktree removal, a farm root or a gate reaper
# deletes it.  At dev 5698648, 314 run ids were cited in tracked files and
# none resolved, so a reader could not check a single one.  The manifest is
# the claim and is committed under planning/evidence/manifests/; this fails
# on a NEWLY cited run with no committed manifest and tolerates the 177 the
# lane could not recover, which are named in that directory's LOST.txt.
# `--strict` fails on those too, once their owners re-run or retract them.
# Mechanical, no ACL2.  `tools/cite_check.py` is the same family for
# repository paths and deliberately does not read `build/`.
	@$(CHECK_STEP) $(PYTHON) tools/evidence_manifests.py check
# The teeth audit's static half: assertions that exercise ACL2 rather than fn,
# recognisers that no test ever makes TRUE, keystones with no witness in any
# test book, and citations of theorems the tree no longer defines.  It needs
# no ACL2 and REPORTS, never fails: the findings on the tree at the time it
# landed are pre-existing and are triaged in
# planning/lanes/HANDOFF-w10-teeth-audit.md.  `--strict` fails on any finding;
# `--report` adds the evaluated half from build/teeth/values.json, which
# `python3 tools/teeth_check.py --evaluate` produces in about twenty minutes
# of one ACL2.
	@$(CHECK_STEP) $(PYTHON) tools/teeth_check.py --summary
# Two static lints over the harness, both from the 2026-09-19 incident: a
# host entry point gained a required keyword-only argument, two callers in
# tests/ were never updated, and both integration labs were dead for a day
# while every `make check` was green -- because nothing ran a lab and the one
# test that would have failed had a skip keyed on a failure message.
# `signatures` binds every resolvable Python call against the definition it
# names and fails on a disagreement; `acl2-arity` does the same for the `ld`ed
# host files, which no certification reads, and fails on unwaived defects;
# `waivers` fails on a
# skip keyed on a failure that carries no `waiver-ok:` declaration.  All three
# are static, need no ACL2 and take about a second.
	@$(CHECK_STEP) $(PYTHON) tools/harness_check.py
# A tooth whose body does not translate passes as a must-fail and bites
# nothing: std must-fail accepts ANY error, silently.  The keystone audit of
# 2026-09-27 found 41 forms in two test books calling functions at pre-flip
# arities, so PRF-191/132/144 had never been evaluated while certification
# was green.  Every must-fail in tests/acl2 is `must-fail-checked`
# (tests/acl2/must-fail-checked.lisp), which translates the body's claim
# first and so makes certification refuse such a tooth; this fails on a bare
# must-fail unless its line declares `; must-fail-ok: <reason>`.
# `--convert` rewrites bare ones after a merge.  Static, no ACL2.
	@$(CHECK_STEP) $(PYTHON) tools/must_fail_check.py
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_must_fail_check
# A retained payload is a HANDLE (books/payload-kinds.lisp); every definition
# that reads one declares which kind it takes (lane entry-guards, 2026-09-27).
	@$(CHECK_STEP) $(PYTHON) tools/payload_kind_check.py
# Every node thread runs on a 1,024 KiB control stack, and a non-tail
# recursion costs a frame per step: LIST ACTIVE and GROUP stopped the owner
# past ~30,000 articles in fn-nntp-group-low (PKT-877), the open in
# fn-retain-obligation-ids (PKT-876).  This lists every non-tail recursion on
# the host-called closure (the functions a raw host file names and what they
# execute, mbe :exec branches only) and fails on one tools/depth_baseline.json
# does not classify: "bounded" names its bound, "debt" (a walk whose depth is
# an article count, a group's articles, a history, a queue or an octet count)
# only shrinks.  Source-level, no ACL2; the extractor agreed (604 of 604, then 383 of 383) at
# lane serve-depth's head.
	@$(CHECK_STEP) $(PYTHON) tools/depth_check.py
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_depth_check
# The multiple-value shape of every ACL2-mode host call.  At 9c344d1d the
# image build refused host/owner-host.lisp because an error triple,
# `(fn-owner-clock-observation state)', was passed as an argument; `make
# check' was green because nothing here translates a host file, and hbox saw
# it hours later.  This infers every book and host `defun''s value count and
# fails where a single-value position, an `mv-let', `er-progn' or `er-let*'
# gets the wrong one, or where conditional arms disagree.  Static, no ACL2,
# about two seconds; forms it does not model are counted as undecidable.
# `make check-host-translate' is the dynamic check, when an ACL2 is local.
	@$(CHECK_STEP) $(PYTHON) tools/host_shape_check.py
# Every host file build.lisp `ld`s is `ld`ed by build-dtn.lisp or listed, with
# its reason, as DTN-omitted; and no name an omitted file defines is spelled
# as a counterpart in a raw module the DTN image loads.  At 6c0626c5 the DTN
# images omitted host/checkpoint-host.lisp and could not `store init'.
# And every book a DTN-loaded host file calls is included before its `ld`:
# at 32842f50 build-dtn.lisp lacked books/octets-stobj and the image failed.
# Static, under a second, with its teeth test.
	@$(CHECK_STEP) $(PYTHON) tools/build_lists_check.py
	@$(CHECK_STEP) $(PYTHON) tools/host_defun_check.py
# A host macro used before its definition in load order compiles as a
# function call (batch AW: every format-9 restart faulted; lane ops-fixes).
	@$(CHECK_STEP) $(PYTHON) tools/host_macro_order_check.py
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_host_macro_order_check
# The raw files loaded in build.lisp's order into one bare ACL2 with SBCL's
# warnings on (seconds, no image build): errors, arity, macro order and names
# nothing defines (lane tooling-leftovers).  No ACL2: NOT RUN, exit 2.
	@$(CHECK_STEP) $(PYTHON) tools/host_check.py --load
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_host_check_load.ClassifyTests
# Every global hash table in host/ is :synchronized t, or declared
# thread-confined or guarded-by a lock the file takes (static, no ACL2; lane
# host-lints, after entry-guards-2's owner stop on an unsynchronized table).
	@$(CHECK_STEP) $(PYTHON) tools/host_check.py --tables
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_host_check_tables
# Every name a raw host/native file hands to fnn-core*/fnn-call is defined in
# the world of the image that loads it (build.lisp, build-dtn.lisp): static,
# no ACL2 (lane lane-tools-2, after payload-lz-record was outside the world).
	@$(CHECK_STEP) $(PYTHON) tools/host_check.py --world
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_host_check_world
# Every launcher path (packaging/'s shell launchers, host/'s process spawns)
# classifies a child's failure: an unknown one is a fault (4) or uncertain,
# never forwarded as the refusal code 1 (lane lane-tools-2; openbsd-datasize's
# SBCL ENOMEM read as "refused", fb12148f8).  Static, no ACL2.
	@$(CHECK_STEP) $(PYTHON) tools/launcher_exit_check.py
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_launcher_exit_check
# The repository is public: no 32-hex code, password=, bearer token or
# Authorization value within five lines of redeem/invite/invitation/
# credentials in planning/, docs/ or tests/ (lane lane-tools-2, after two lane
# records nearly committed a live invitation code).  No waivers: a fixture is
# synthetic by the rule in the tool's header.  Static, about ten seconds.
	@$(CHECK_STEP) $(PYTHON) tools/secrets_check.py
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_secrets_check
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_build_lists_check
# Every ACL2 a tool or test starts takes the machine's pool and heap cap
# (tools/acl2_slots.py run/popen/tree_slot; PKT-162, harness-repair).
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_acl2_launchers.LauncherRuleTests
# specs/identity.md "The signed bytes" is what an independent verifier is
# written from.  On 2026-09-24 tools/fn_verify.py had to read the books for
# the preimage layout, the dropped fields and the ML-DSA context, because the
# prose did not give them.  This fails when a function or constant that
# section names is no longer defined in books/, or when the section, the book
# constants and the verifier state different tag bytes, widths or dropped
# fields.  Static, no ACL2, no crypto library, under a second.
	@$(CHECK_STEP) $(PYTHON) -m unittest -q tests.test_fn_verify.SpecBookTieTests
# Every repository path this tree cites and no file answers.  On 2026-09-21
# `books/stx-lace.lisp` was found citing a book and a test book that have
# never existed, for the observation four keystones hypothesise.  The counts
# for `specs/`, `planning/` and `tools/` are REPORTED: a design naming the
# book a packet will add is not a defect.  A citation inside `books/` or
# `tests/acl2/` is a claim about EVIDENCE, there are none undisclosed on this
# tree as of w11/phantom-cites, and `--strict` is what keeps it that way: a
# new one fails `make check` until the file exists, the path is corrected, or
# the comment says the file does not exist and what rests on it.  Mechanical,
# no ACL2; triage in planning/lanes/HANDOFF-w11-phantom-cites.md.
	@$(CHECK_STEP) $(PYTHON) tools/cite_check.py --summary --strict
# Every Lisp name a spec or doc cites in backquotes is defined by a book, a
# test book or a host file (PKT-312: a spec cited a retired theorem whose
# statement was false at the new widths).  Templates, one-segment prefixes and
# -vN tags pass by visible rule; tools/spec_cite_exemptions.json names each
# exemption with its reason and each known-stale citation under its packet
# (PKT-446), and --strict fails on a new one or an entry no longer cited.
	@$(CHECK_STEP) $(PYTHON) tools/spec_cite_check.py --summary --strict
# Every theorem the registry cites whose subject no host line can reach.
# AGENTS.md's first assurance rule -- "the theorem subject is the function
# the host calls" -- was prose with nothing behind it, and the defect it
# names cost us the most: on 2026-09-21 K3's duplicate suppression was found
# proved of an offer decision that read the node pinned at `:open', the
# transit CAPABILITIES list was found proved and answered by the auth layer
# above it, and `fn-own-feed-durable-records' and `fn-feed-lost' were found
# with no caller at all.  Each was true, certified and irrelevant to the
# running server.  41 registry events are orphaned on this tree and are
# accepted by name, with a reason each, in planning/reach-baseline.json;
# `--strict' fails on any orphan NOT listed there, so the number can shrink
# and cannot grow silently.  Deliberately generous about what counts as a
# subject, so every orphan it reports is real and it misses some.
	@$(CHECK_STEP) $(PYTHON) tools/reach_check.py --summary --strict
	@$(CHECK_STEP) $(PYTHON) tools/keystone_emit.py --check
# Which host entries walk retained state (PKT-334, answers 2026-09-26 §2): a
# function called once per request that traverses the Store history, the
# held BP fragments or the queued BP jobs.  tools/hot_path_check.py follows the
# executed path (mbe's :exec under raw Lisp, the guard a counterpart call
# evaluates, defattach) from every host definition and lists each traversal of
# a seeded value; planning/hot-path-findings.json names every find's owning
# packet, and `--strict' fails on an unexpected find not listed there or a
# listed find that no longer occurs.  Its silence is not a proof: it is
# path-insensitive and prints the cuts it was told to take.
	@$(CHECK_STEP) $(PYTHON) tools/hot_path_check.py --summary --strict
# Whether each book is certified AT THE SOURCE DIGEST IT CARRIES NOW.  On
# 2026-09-21 `dev` had been red for a day in books/stx-evidence-records,
# books/checkpoint-compaction, books/hybrid-store and books/feed-connection,
# each committed by a lane that never certified it, and every reader took
# `git log` for certification.  The archived manifests had already recorded
# those failures at exactly the digests the tree carried; nothing asked.  This
# reads every manifest under planning/evidence/manifests/ plus this worktree's
# unarchived runs and gives every root and every book in the roots' closure
# one of four answers: green at this digest, RED at this digest, never at this
# digest, or never a requested root anywhere.  It REPORTS here -- 32 books are
# red at their digest on this tree and are the certification lanes' worklist
# -- and `--strict` fails on a book whose newest verdict at its current bytes
# is a failure, which is what stops a lane committing over a known red.
# `--table` is the whole list; deliberately generates nothing committed, since
# every archived manifest and every edited book would stale it.  Mechanical,
# no ACL2, about three seconds.
	@$(CHECK_STEP) $(PYTHON) tools/green_check.py --summary
	@$(CHECK_STEP) $(PYTHON) tools/theory_check.py --summary
	@$(CHECK_STEP) $(PYTHON) tools/theory_check.py --strict --books $(THEORY_STRICT_BOOKS)
	@$(PYTHON) tools/check_steps.py summary $(CHECK_STEPS_DIR)

# The integration labs.  Deliberately NOT part of `check`: the quick tier is
# about two and a half minutes and the box tier is hours, while `check` is
# seconds and runs before every commit.  `tests/README.md` has the table of
# tiers and costs.  Each lab reports passed, failed, or not-runnable with the
# exact reason; the exit code is 1 only when one actually failed.
labs:
	$(PYTHON) tools/labs.py --tier local
labs-quick:
	$(PYTHON) tools/labs.py --tier quick

certify:
	$(PYTHON) tools/certify_books.py --jobs $(FN_CERTIFY_JOBS) $(ACL2_BOOKS)

# One interactive ACL2 inside the machine-wide slot pool, for `ld` iteration:
# `make acl2-ld < driver.lsp`.  Call tools/acl2 directly to pass ACL2 its own
# arguments.  Never plain `acl2`: that takes no slot, and the pool is the only
# thing keeping a wave of lanes off this box's memory.
acl2-ld:
	$(PYTHON) tools/acl2 --timeout $(FN_LD_TIMEOUT_SECONDS)

# Content-hashed certificates are valid in any worktree whose book content
# matches, so a lane installs what the cache already has instead of certifying
# it again.  `certify` publishes automatically; this target is for a tree
# certified some other way.  FN_CERT_REMOTE=hbox also mirrors to that box.
certs-install:
	$(PYTHON) tools/certs.py install

# The dynamic half of tools/host_shape_check.py: the ACL2-mode prefix of
# host/native/build.lisp (every include-book and host `ld`), translated the
# way the image build does it, without saving an image.  Exit 2 is NOT RUN
# (no ACL2, or certificates missing or not composing), 1 is an ACL2 error.
check-host-translate:
	$(PYTHON) tools/certs.py install
	$(PYTHON) tools/host_translate_check.py

certs-publish:
	$(PYTHON) tools/certs.py publish $(if $(FN_CERT_REMOTE),--remote $(FN_CERT_REMOTE))

model-test: certify
	$(PYTHON) tools/run_simulator.py

# The tools' own tests, each module in its own process under tools/test_budget.py's
# rule (180 s a module, 20 s a test, distinct pass/fail/over-budget/all-skipped exits).
# It was one `unittest` process under a 120 s timeout, which the honest total
# outgrew: 29 modules take 170 s on the laptop (2026-09-26, tooling-velocity),
# most of it real-tree reads -- certify_runner 39 s (49 fake-ACL2 runs),
# green_check 34 s (four command-line runs over every manifest, 6-7 s each),
# ledger 16 s (a cold tree analysis), reach_check 12 s -- and the 120 s kill
# landed in whichever module was running then, before the later modules ran
# (PKT-305).  No module or test is over its budget.
TOOLING_TEST_MODULES = tests.test_certify_runner tests.test_acl2_wrapper \
	    tests.test_ledger tests.test_cite_check tests.test_reach_check tests.test_hot_path_check tests.test_fixture_stderr tests.test_native_process tests.test_fixture_init_refusal \
	    tests.test_evidence_manifests tests.test_green_check tests.test_certified_claims tests.test_current_view tests.test_proof_cost tests.test_throughput_gate tests.test_service_envelope \
	    tests.test_process_supervisor tests.test_node_probe tests.test_fn_client tests.test_theory_check tests.test_rule_cost tests.test_proof_repl tests.test_native_raw_scripts \
	    tests.test_test_budget tests.test_bridge_image tests.test_acl2_launchers tests.test_scenario_implementation tests.test_docs_check tests.test_post_docs \
	    tests.test_farm tests.test_merge_registry tests.test_next_id tests.test_host_check_load tests.test_wait_for tests.test_native_harness tests.test_native_program_check \
	    tests.test_hbox_native tests.test_acl2_slots tests.test_build_native_host tests.test_spec_cite_check tests.test_ascii_check tests.test_runpath_check tests.test_changelog tests.test_release_sequence tests.test_cut_release tests.test_fundamentals tests.test_check_steps tests.test_cert_cache_sync \
	    tests.test_extract_gate
tooling-test:
	$(PYTHON) tools/test_budget.py $(TOOLING_TEST_MODULES)

# Every test module in its own process under a wall-time budget (PKT-163):
# the report lists each module's seconds and slowest tests, and a module
# still running at 180 s is terminated, or one whose test ran over 20 s is
# named, and either fails the target (exit 2; test failures exit 1).
# `--order reverse` runs each module's tests last to first, which is how a
# test that relies on an earlier one's leftovers is found (harness-repair).  tests/test_budgets.json may lower a module's budget,
# never raise it.  `make test-modules MODULES="tests.test_store ..."` runs a
# chosen set the same way.  A module whose every test skipped is reported
# SKIPPED (N of N) with its reasons and exits 4 (PKT-437 (2)); --discover
# includes the native modules, which skip on a machine without their image,
# so `test` passes --allow-skipped (the report and its SKIPPED count stay;
# native modules run under tools/hbox_native.sh, where a SKIPPED module fails).
test: check certify
	$(PYTHON) tools/run_simulator.py
	$(PYTHON) tools/test_budget.py --allow-skipped --discover --logs build/test-budget --json build/test-budget/report.json

test-modules:
	$(PYTHON) tools/test_budget.py $(MODULES) --logs build/test-budget
