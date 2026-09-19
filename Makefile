PYTHON ?= python3
ACL2_BOOKS ?= books/assumptions \
	tests/acl2/assumptions-tests \
	books/acceptance \
	books/acceptance-invariants \
	tests/acl2/acceptance-tests \
	tests/acl2/acceptance-guards-tests \
	tests/acl2/acceptance-teeth-tests \
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
	books/frame \
	books/frame-invariants \
	tests/acl2/frame-tests \
	books/identity \
	books/identity-invariants \
	tests/acl2/identity-tests \
	books/retention \
	books/retention-invariants \
	tests/acl2/retention-tests \
	tests/acl2/retention-teeth-tests \
	books/node \
	books/node-invariants \
	tests/acl2/node-tests \
	tests/acl2/node-teeth-tests \
	books/node-traces \
	tests/acl2/node-traces-tests \
	books/records \
	books/records-invariants \
	books/records-canonicality \
	tests/acl2/records-tests \
	tests/acl2/records-teeth-tests \
	books/replay \
	books/replay-invariants \
	tests/acl2/replay-tests \
	tests/acl2/replay-guards-tests \
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
	books/store-node-resolution-traces \
	tests/acl2/store-node-resolution-traces-tests \
	books/store-observed \
	tests/acl2/store-observed-tests \
	tests/acl2/store-node-guards-tests \
	tests/acl2/store-node-teeth-tests \
	books/checkpoint \
	tests/acl2/checkpoint-tests \
	books/index \
	tests/acl2/index-tests \
	books/bp-ingress \
	tests/acl2/bp-ingress-tests \
	books/bp-adu \
	tests/acl2/bp-adu-tests \
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
	books/bp-outbound \
	tests/acl2/bp-outbound-tests \
	books/journal \
	tests/acl2/journal-tests \
	books/exchange \
	tests/acl2/exchange-tests \
	books/exchange-invariants \
	tests/acl2/exchange-invariants-tests \
	tests/acl2/exchange-guards-tests \
	tests/acl2/exchange-teeth-tests \
	books/transfer \
	books/transfer-invariants \
	books/transfer-assembly-invariants \
	books/transfer-work \
	books/transfer-public-work \
	books/transfer-public-bound \
	tests/acl2/transfer-tests \
	books/nntp \
	books/nntp-invariants \
	books/nntp-effects \
	tests/acl2/nntp-tests \
	tests/acl2/nntp-teeth-tests

.PHONY: check certify model-test tooling-test test
check:
	$(PYTHON) tools/check_scaffold.py

certify:
	$(PYTHON) tools/certify_books.py $(ACL2_BOOKS)

model-test: certify
	$(PYTHON) tools/run_simulator.py

tooling-test:
	$(PYTHON) -m unittest discover -s tests -p test_certify_runner.py -v

test: check certify
	$(PYTHON) tools/run_simulator.py
	$(PYTHON) -m unittest discover -s tests -v
