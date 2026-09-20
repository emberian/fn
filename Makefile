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
	books/identity \
	books/identity-invariants \
	tests/acl2/identity-tests \
	books/provenance \
	books/retention \
	books/retention-invariants \
	tests/acl2/retention-tests \
	books/node \
	books/node-invariants \
	tests/acl2/node-tests \
	books/node-traces \
	books/records \
	books/records-invariants \
	books/records-canonicality \
	tests/acl2/records-tests \
	tests/acl2/records-teeth-tests \
	books/provenance-codec \
	tests/acl2/provenance-tests \
	books/config \
	books/config-invariants \
	books/replay \
	books/replay-invariants \
	tests/acl2/replay-tests \
	books/config-records \
	books/node-config \
	tests/acl2/config-tests \
	books/store-files \
	books/store-files-invariants \
	tests/acl2/store-files-tests \
	books/store-files-traces \
	tests/acl2/store-files-traces-tests \
	tests/acl2/store-files-exploration-tests \
	tests/acl2/store-files-teeth-tests \
	books/store-node \
	books/store-node-invariants \
	tests/acl2/store-node-tests \
	books/store-node-traces \
	tests/acl2/store-node-traces-tests \
	books/store-node-resolution \
	tests/acl2/store-node-resolution-tests \
	books/store-sweep \
	tests/acl2/store-sweep-tests \
	books/store-observed \
	tests/acl2/store-observed-tests \
	books/store-observed-traces \
	tests/acl2/store-observed-traces-tests \
	books/byte-store \
	books/byte-store-invariants \
	books/byte-store-scan \
	books/byte-store-programs \
	tests/acl2/byte-store-tests \
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
	books/index \
	tests/acl2/index-tests \
	books/bp-ingress \
	tests/acl2/bp-ingress-tests \
	tests/acl2/bp-ingress-guards-tests \
	books/bp-adu \
	tests/acl2/bp-adu-tests \
	books/bp-primary-cbor \
	books/bp-primary \
	books/bp-primary-invariants \
	tests/acl2/bp-primary-tests \
	books/bp-bundle \
	books/bp-bundle-invariants \
	tests/acl2/bp-bundle-tests \
	books/bp-node \
	tests/acl2/bp-node-tests \
	books/bp-fragment \
	books/bp-fragment-invariants \
	tests/acl2/bp-fragment-tests \
	books/clock \
	books/clock-invariants \
	tests/acl2/clock-tests \
	books/tcpcl-records \
	books/tcpcl-octets \
	books/tcpcl-session \
	books/tcpcl-invariants \
	tests/acl2/tcpcl-tests \
	books/anchor \
	books/anchor-record \
	books/anchor-invariants \
	tests/acl2/anchor-tests \
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
	books/bp-workflow-records \
	books/bp-workflow-records-invariants \
	tests/acl2/bp-workflow-records-tests \
	tests/acl2/bp-workflow-records-guards-tests \
	books/bp-receipt \
	tests/acl2/bp-receipt-tests \
	books/bp-receipt-records \
	tests/acl2/bp-receipt-records-tests \
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
	books/nntp-invariants \
	books/nntp-effects \
	tests/acl2/nntp-tests \
	tests/acl2/nntp-teeth-tests \
	books/injection \
	books/injection-invariants \
	tests/acl2/injection-tests \
	books/nntp-post \
	tests/acl2/nntp-post-tests \
	books/path \
	books/peer-config \
	books/peer-inbound \
	books/peer-inbound-invariants \
	tests/acl2/peer-inbound-tests \
	books/nntp-auth \
	tests/acl2/nntp-auth-tests \
	books/served \
	books/nntp-auth-invariants \
	tests/acl2/served-tests \
	books/config-stream \
	tests/acl2/config-stream-tests \
	books/owner-config \
	books/ideal \
	books/nntp-index \
	tests/acl2/nntp-index-tests \
	tests/acl2/nntp-reader-profile-tests \
	tests/acl2/nntp-legacy-tests \
	books/bp-release \
	books/bp-release-invariants \
	tests/acl2/bp-release-tests \
	books/scheduler \
	books/scheduler-invariants \
	tests/acl2/scheduler-tests \
	books/peer-feed \
	books/peer-feed-invariants \
	tests/acl2/peer-feed-tests \
	books/owner-feed \
	tests/acl2/owner-feed-tests \
	books/owner \
	books/owner-invariants \
	tests/acl2/owner-tests \
	books/relay \
	books/relay-invariants \
	books/relay-crash-invariants \
	tests/acl2/relay-tests \
	books/crypto-seam \
	tests/acl2/crypto-seam-tests \
	books/crypto-attach \
	books/auth-secret \
	tests/acl2/auth-secret-tests \
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
	books/stx-invariants \
	books/stx-lace \
	books/stx-index \
	books/stx-policy \
	books/stx-epochs \
	books/stx-authority \
	tests/acl2/stx-tests \
	tests/acl2/stx-transit-tests \
	books/scheduler-peers \
	tests/acl2/scheduler-peers-tests

.PHONY: check certify acl2-ld certs-install certs-publish model-test tooling-test test
check:
	$(PYTHON) tools/check_scaffold.py
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
# The served command chain is four session records deep and every base
# accessor is `car', so a call that stops one level short is answered with a
# plausible value rather than an error: four such misses shipped on
# 2026-09-20, one of them leaving POST with no reply at all.  This infers
# every formal's session level from the books and fails on a wrong depth.  A
# walk spelled by hand instead of through a named projection is drift and is
# counted, not failed (--strict fails on those too).  Mechanical, no ACL2.
	$(PYTHON) tools/session_depth.py

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

certs-publish:
	$(PYTHON) tools/certs.py publish $(if $(FN_CERT_REMOTE),--remote $(FN_CERT_REMOTE))

model-test: certify
	$(PYTHON) tools/run_simulator.py

tooling-test:
	$(PYTHON) -m unittest tests.test_certify_runner tests.test_acl2_wrapper \
	    tests.test_ledger -v

test: check certify
	$(PYTHON) tools/run_simulator.py
	$(PYTHON) -m unittest discover -s tests -v
