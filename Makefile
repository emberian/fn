PYTHON ?= python3
# Maximum concurrent ACL2 processes. Books still certify in local
# include-book dependency order; 1 reproduces the sequential run.
FN_CERTIFY_JOBS ?= 1
# The wall clock an interactive `ld` gets before tools/acl2 kills it and frees
# its slot: the brief's three-minute rule, with a minute of slack.
FN_LD_TIMEOUT_SECONDS ?= 240
ACL2_BOOKS ?= books/defrecord \
	books/deftransition \
	books/acceptance-alloc \
	tests/acl2/defrecord-tests \
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
	books/store-config \
	books/sha256 \
	tests/acl2/sha256-tests \
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
	books/native-mission \
	tests/acl2/native-mission-tests \
	books/native-control \
	books/native-hybrid-control \
	books/hybrid-lifecycle \
	tests/acl2/hybrid-lifecycle-tests \
	books/hybrid-lifecycle-store-invariants \
	books/owner-verdict-read \
	books/owner-list-counts-read \
	books/owner-signed-post \
	tests/acl2/hybrid-lifecycle-store-invariants-tests \
	tests/acl2/native-hybrid-control-tests \
	tests/acl2/native-control-tests \
	tests/acl2/native-control-host-tests \
	books/native-live-status \
	tests/acl2/native-live-status-tests \
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
	books/store-node-invariants \
	books/acceptance-stamp-invariants \
	tests/acl2/acceptance-stamp-tests \
	tests/acl2/store-node-tests \
	tests/acl2/consumer-store-node-tests \
	tests/acl2/store-node-existing-tests \
	books/store-node-traces-prepare \
	books/store-node-traces \
	tests/acl2/store-node-traces-tests \
	books/store-prepare-correspondence \
	tests/acl2/store-prepare-correspondence-tests \
	books/store-node-retention \
	tests/acl2/store-node-retention-tests \
	books/store-budget \
	tests/acl2/store-budget-tests \
	books/store-profile-upgrade \
	books/byte-store-profile-program \
	tests/acl2/store-profile-upgrade-tests \
	books/store-profile-namespace \
	tests/acl2/store-profile-namespace-tests \
	books/store-checkpoint-open \
	books/store-checkpoint-codec \
	tests/acl2/store-checkpoint-open-tests \
	books/owner-checkpoint-open \
	tests/acl2/owner-checkpoint-open-tests \
	tests/acl2/linear-recognizers-tests \
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
	books/byte-store-record-provenance-node \
	books/byte-store-record-provenance-owner \
	books/byte-store-record-provenance \
	tests/acl2/byte-store-record-provenance-tests \
	books/byte-store-k0 \
	books/byte-store-k0-staging \
	books/byte-store-k0-staging-error \
	books/byte-store-k0-authority-error \
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
	books/byte-store-compaction-correspondence \
	tests/acl2/byte-store-compaction-correspondence-tests \
	books/byte-store-programs \
	tests/acl2/byte-store-tests \
	books/byte-store-frame \
	tests/acl2/byte-store-frame-tests \
	books/byte-store-profile-v1 \
	tests/acl2/byte-store-profile-v1-tests \
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
	books/checkpoint-pack-retire \
	tests/acl2/checkpoint-pack-retire-tests \
	books/checkpoint-compaction \
	tests/acl2/checkpoint-compaction-tests \
	books/checkpoint-compaction-preservation \
	tests/acl2/checkpoint-compaction-preservation-tests \
	books/store-compact-verb \
	tests/acl2/store-compact-verb-tests \
	books/store-history-marker \
	books/reclaim-tombstone \
	books/reclaim-rule \
	books/store-reclaim \
	books/nntp-reclaimed \
	tests/acl2/store-reclaim-tests \
	books/store-reclaim-buffer \
	tests/acl2/store-reclaim-buffer-tests \
	books/store-reclaim-holders \
	tests/acl2/store-reclaim-holders-tests \
	books/reclaim-admission \
	tests/acl2/reclaim-admission-tests \
	tests/acl2/store-history-marker-tests \
	books/store-history-required \
	tests/acl2/store-history-required-tests \
	books/byte-store-marker-program \
	books/byte-store-k0-marker \
	tests/acl2/byte-store-k0-marker-tests \
	books/byte-store-k0-step-lemmas \
	books/byte-store-k0-step-root-fence \
	books/byte-store-k0-step \
	tests/acl2/byte-store-k0-step-tests \
	books/byte-store-k0-step-bridge-marker \
	books/byte-store-k0-step-bridge-prefix \
	books/byte-store-k0-step-bridge \
	tests/acl2/byte-store-k0-step-bridge-tests \
	books/byte-store-k0-step-bridge-frontier \
	tests/acl2/byte-store-k0-cuts-tests \
	books/byte-store-k0-step-bridge-root \
	tests/acl2/byte-store-k0-step-bridge-root-tests \
	books/byte-store-k0-window \
	books/byte-store-k0-recover-program \
	tests/acl2/byte-store-k0-recover-program-tests \
	books/byte-store-k0-pre-init \
	tests/acl2/byte-store-k0-pre-init-tests \
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
	books/bp-fnbs-conflict-codec \
	books/bp-fnbs-conflict-invariants \
	books/bp-fnbs-conflict-publication \
	books/bp-node-machine-gaps \
	books/bp-node-busy-delivery \
	books/bp-node-receipt-send \
	books/bp-fnbs-replay-append \
	books/bp-node-rotation-codec \
	books/bp-node-rotation \
	books/bp-node-rotation-step \
	tests/acl2/bp-node-counterexamples-tests \
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
	books/bp-limits \
	tests/acl2/bp-fragment-tests \
	tests/acl2/bp-fragment-fast-tests \
	tests/acl2/bp-limits-tests \
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
	books/nntp-responses \
	books/nntp \
	books/nntp-overview \
	books/nntp-legacy \
	books/nntp-xpat \
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
	tests/acl2/nntp-post-tests \
	books/path \
	books/path-update \
	books/path-update-tail \
	books/peer-config \
	books/peer-inbound \
	books/peer-inbound-invariants \
	tests/acl2/peer-inbound-tests \
	books/nntp-auth \
	tests/acl2/nntp-auth-tests \
	books/served \
	books/served-tls-prefix \
	books/owner-tls-prefix \
	books/owner-config-observe \
	books/peer-offer-indexed \
	books/peer-guard-carried \
	books/served-carried \
	books/owner-served-carried \
	books/owner-offer-indexed \
	books/store-events-carried \
	books/owner-commit-carried \
	books/owner-prepare-carried \
	books/records-concrete \
	books/records-concrete-owner \
	books/records-attach-concrete \
	books/msgid-index-concrete \
	books/octets-stobj \
	books/poster-bytes-buffer \
	tests/acl2/octets-stobj-tests \
	books/sha256-buffer \
	tests/acl2/sha256-buffer-tests \
	books/owner-advance-carried \
	books/owner-intent-carried \
	books/owner-commit-ocl \
	books/owner-recover-ocl \
	tests/acl2/owner-tls-pin-tests \
	tests/acl2/served-tls-prefix-tests \
	books/nntp-auth-invariants \
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
	tests/acl2/peer-offer-indexed-tests \
	tests/acl2/peer-guard-carried-tests \
	tests/acl2/owner-commit-carried-tests \
	tests/acl2/owner-prepare-carried-tests \
	tests/acl2/records-concrete-tests \
	tests/acl2/msgid-index-concrete-tests \
	tests/acl2/owner-advance-carried-tests \
	tests/acl2/owner-intent-carried-tests \
	tests/acl2/store-events-carried-tests \
	tests/acl2/owner-recover-ocl-tests \
	books/config-owner-publish \
	tests/acl2/config-owner-publish-tests \
	books/config-crash-replay \
	tests/acl2/config-crash-replay-tests \
	books/owner-config \
	books/ideal \
	books/nntp-index \
	tests/acl2/nntp-index-tests \
	books/nntp-index-runtime \
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
	books/owner-invariants \
	books/owner-fault \
	books/owner-feed-subject \
	books/owner-prepare-correspondence \
	books/owner-served-invariants \
	books/owner-numbering \
	books/owner-retention-preparation \
	books/owner-agent \
	books/owner-log \
	books/owner-served-bound \
	books/owner-log-reopen \
	books/owner-bound-commit \
	books/consumer-event-index \
	tests/acl2/consumer-event-index-tests \
	books/consumer-poll-index \
	tests/acl2/consumer-poll-index-tests \
	books/consumer-event-index-store-invariants \
	tests/acl2/consumer-event-index-store-invariants-tests \
	books/consumer-owner-local \
	tests/acl2/consumer-owner-local-tests \
	books/consumer-owner-index-invariants \
	tests/acl2/consumer-owner-index-invariants-tests \
	tests/acl2/owner-tests \
	books/poster-bytes-invariants \
	tests/acl2/poster-bytes-tests \
	tests/acl2/owner-served-invariants-tests \
	tests/acl2/owner-numbering-tests \
	tests/acl2/owner-fault-tests \
	tests/acl2/owner-verdict-tests \
	tests/acl2/owner-verdict-read-tests \
	tests/acl2/owner-signed-post-tests \
	tests/acl2/owner-operator-tests \
	tests/acl2/owner-agent-tests \
	tests/acl2/owner-log-tests \
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
	tests/acl2/peer-carriage-tests \
	tests/acl2/control-tests \
	books/control-authority \
	tests/acl2/control-authority-tests \
	books/key-statements \
	tests/acl2/key-statements-tests \
	books/peer-invite \
	tests/acl2/peer-invite-tests \
	books/control-visible \
	tests/acl2/control-visible-tests \
	books/control-served \
	tests/acl2/control-served-tests \
	books/login-binding \
	tests/acl2/login-binding-tests \
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
	tests/acl2/scheduler-peers-tests

.PHONY: check check-host-translate certify acl2-ld certs-install certs-publish model-test tooling-test test labs labs-quick
# The books a codec seam has cleared (plan 2026-09-22 §4.1, step T1): none
# opens a codec theory at the top or names a seam's implementation, and
# `make check` fails if one starts to.  Each cluster lane of the step appends
# its books; when the list is every book, `--strict` runs without `--books`.
THEORY_STRICT_BOOKS ?= books/store-events books/replay books/replay-invariants \
	books/store-files books/store-files-invariants books/store-files-traces \
	books/store-node books/store-node-invariants books/store-node-traces-prepare \
	books/store-node-traces \
	books/store-node-resolution books/store-observed books/store-observed-traces \
	books/store-prepare-correspondence books/config-records books/node-config \
	books/checkpoint books/checkpoint-compaction books/checkpoint-publish \
	books/records-shape books/statement books/statement-invariants

check:
	$(PYTHON) tools/check_scaffold.py
# A certified registry row must name existing ACL2 events whose defining
# books have source- and include-closure-compatible manifest evidence, and
# must itself cite an archived manifest that certified each event book at its
# current digest. Any warning fails; --explain PRF-xxx names the manifest.
	$(PYTHON) tools/certified_claims.py
# planning/current.md, the per-capability current view, is generated from
# planning/current-view.json and the tree (host call lines, keystones, the
# archived manifests, the tested and deployed images' source digests); this
# fails when it is stale or names something absent.
	$(PYTHON) tools/current_view.py --check
# Newest measured attempts at each current book/include closure, grouped by
# host and toolchain. The ten-second rule is a ratchet over
# planning/proof-cost-baseline.json: a new slow book, or one 25% over its
# baseline, fails. Installed pairs have no proof time.
	$(PYTHON) tools/proof_cost.py
# Every host file loaded alone in its own ACL2: the dynamic half of the
# host-names lint.  Needs FN_ACL2 and installed certificates; without
# FN_ACL2 it prints that it did not run and exits 0.
	$(PYTHON) tools/host_check.py
# specs/crash-model-v2.md section 2.3's check, in both directions: every cut
# the campaign kills at is a :cut of the model program that transcribes its
# host function, and every :cut of a model program is a host faults.at site.
# It is mechanical and needs no ACL2, so it belongs in `check`.  It fails on a
# fidelity defect; missing host cuts and syscall drift are reported and do not
# fail (--strict fails on those too).
	$(PYTHON) tools/transcribe_check.py
# The same transcription check for the native host, which transcribe_check
# does not read: for each program tests/campaign/native_cuts.py names, the
# host function's success-path syscalls, file-kernel observations and fnn-at
# cuts in source order equal the program's steps (kind and directory), and
# every error-arm observation is one of the program's error constants.  A
# source check; it states what it cannot decide.  Mechanical, no ACL2.
	$(PYTHON) tools/native_program_check.py
# The served command chain is four session records deep and every base
# accessor is `car', so a call that stops one level short is answered with a
# plausible value rather than an error: four such misses shipped on
# 2026-09-20, one of them leaving POST with no reply at all.  This infers
# every formal's session level from the books and fails on a wrong depth.  A
# walk spelled by hand instead of through a named projection is drift and is
# counted, not failed (--strict fails on those too).  Mechanical, no ACL2.
	$(PYTHON) tools/session_depth.py
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
	$(PYTHON) tools/evidence_manifests.py check
# The teeth audit's static half: assertions that exercise ACL2 rather than fn,
# recognisers that no test ever makes TRUE, keystones with no witness in any
# test book, and citations of theorems the tree no longer defines.  It needs
# no ACL2 and REPORTS, never fails: the findings on the tree at the time it
# landed are pre-existing and are triaged in
# planning/lanes/HANDOFF-w10-teeth-audit.md.  `--strict` fails on any finding;
# `--report` adds the evaluated half from build/teeth/values.json, which
# `python3 tools/teeth_check.py --evaluate` produces in about twenty minutes
# of one ACL2.
	$(PYTHON) tools/teeth_check.py --summary
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
	$(PYTHON) tools/harness_check.py
# The multiple-value shape of every ACL2-mode host call.  At 9c344d1d the
# image build refused host/owner-host.lisp because an error triple,
# `(fn-owner-clock-observation state)', was passed as an argument; `make
# check' was green because nothing here translates a host file, and hbox saw
# it hours later.  This infers every book and host `defun''s value count and
# fails where a single-value position, an `mv-let', `er-progn' or `er-let*'
# gets the wrong one, or where conditional arms disagree.  Static, no ACL2,
# about two seconds; forms it does not model are counted as undecidable.
# `make check-host-translate' is the dynamic check, when an ACL2 is local.
	$(PYTHON) tools/host_shape_check.py
# Every host file build.lisp `ld`s is `ld`ed by build-dtn.lisp or listed, with
# its reason, as DTN-omitted; and no name an omitted file defines is spelled
# as a counterpart in a raw module the DTN image loads.  At 6c0626c5 the DTN
# images omitted host/checkpoint-host.lisp and could not `store init'.
# And every book a DTN-loaded host file calls is included before its `ld`:
# at 32842f50 build-dtn.lisp lacked books/octets-stobj and the image failed.
# Static, under a second, with its teeth test.
	$(PYTHON) tools/build_lists_check.py
	$(PYTHON) -m unittest -q tests.test_build_lists_check
# specs/identity.md "The signed bytes" is what an independent verifier is
# written from.  On 2026-09-24 tools/fn_verify.py had to read the books for
# the preimage layout, the dropped fields and the ML-DSA context, because the
# prose did not give them.  This fails when a function or constant that
# section names is no longer defined in books/, or when the section, the book
# constants and the verifier state different tag bytes, widths or dropped
# fields.  Static, no ACL2, no crypto library, under a second.
	$(PYTHON) -m unittest -q tests.test_fn_verify.SpecBookTieTests
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
	$(PYTHON) tools/cite_check.py --summary --strict
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
	$(PYTHON) tools/reach_check.py --summary --strict
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
	$(PYTHON) tools/green_check.py --summary
	$(PYTHON) tools/theory_check.py --summary
	$(PYTHON) tools/theory_check.py --strict --books $(THEORY_STRICT_BOOKS)

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

tooling-test:
	$(PYTHON) tools/run_command.py --timeout 120 -- $(PYTHON) -m unittest tests.test_certify_runner tests.test_acl2_wrapper \
	    tests.test_ledger tests.test_cite_check tests.test_reach_check \
	    tests.test_evidence_manifests tests.test_green_check tests.test_certified_claims tests.test_current_view tests.test_proof_cost \
	    tests.test_process_supervisor tests.test_node_probe tests.test_fn_client tests.test_theory_check tests.test_proof_repl tests.test_native_raw_scripts -v

test: check certify
	$(PYTHON) tools/run_simulator.py
	$(PYTHON) -m unittest discover -s tests -v
