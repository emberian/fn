PYTHON ?= python3
# Maximum concurrent ACL2 processes. Books still certify in local
# include-book dependency order; 1 reproduces the sequential run.
FN_CERTIFY_JOBS ?= 1
ACL2_BOOKS ?= books/assumptions \
	tests/acl2/assumptions-tests \
	books/acceptance-alloc \
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
	books/frame-octets \
	books/frame-fields \
	books/frame-journal \
	books/frame \
	books/frame-invariants \
	tests/acl2/frame-tests \
	books/identity \
	books/identity-invariants \
	tests/acl2/identity-tests \
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
	books/replay \
	books/replay-invariants \
	tests/acl2/replay-tests \
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
	books/store-observed \
	tests/acl2/store-observed-tests \
	books/store-observed-traces \
	tests/acl2/store-observed-traces-tests \
	tests/acl2/store-node-guards-tests \
	tests/acl2/store-node-teeth-tests \
	books/checkpoint \
	tests/acl2/checkpoint-tests \
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
	books/bp-fragment \
	books/bp-fragment-invariants \
	tests/acl2/bp-fragment-tests \
	books/clock \
	books/clock-invariants \
	tests/acl2/clock-tests \
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
	books/nntp-syntax \
	books/nntp-session \
	books/nntp-projection \
	books/nntp-responses \
	books/nntp \
	books/nntp-invariants \
	books/nntp-effects \
	tests/acl2/nntp-tests \
	tests/acl2/nntp-teeth-tests \
	books/nntp-index \
	tests/acl2/nntp-index-tests \
	books/bp-release \
	books/bp-release-invariants \
	tests/acl2/bp-release-tests \
	books/relay \
	books/relay-invariants \
	books/relay-crash-invariants \
	tests/acl2/relay-tests \
	books/crypto-seam \
	tests/acl2/crypto-seam-tests \
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
	tests/acl2/policy-tests

.PHONY: check certify certs-install certs-publish model-test tooling-test test
check:
	$(PYTHON) tools/check_scaffold.py

certify:
	$(PYTHON) tools/certify_books.py --jobs $(FN_CERTIFY_JOBS) $(ACL2_BOOKS)

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
	$(PYTHON) -m unittest discover -s tests -p test_certify_runner.py -v

test: check certify
	$(PYTHON) tools/run_simulator.py
	$(PYTHON) -m unittest discover -s tests -v
