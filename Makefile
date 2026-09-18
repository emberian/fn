PYTHON ?= python3
ACL2_BOOKS ?= books/acceptance \
	books/acceptance-invariants \
	tests/acl2/acceptance-tests \
	tests/acl2/acceptance-guards-tests \
	books/wire \
	books/wire-invariants \
	tests/acl2/wire-tests \
	books/cbor \
	books/cbor-invariants \
	tests/acl2/cbor-tests \
	books/wildmat \
	books/wildmat-utf8-invariants \
	books/wildmat-parser-invariants \
	books/wildmat-matcher-invariants \
	books/wildmat-work \
	tests/acl2/wildmat-parser-invariants-tests \
	tests/acl2/wildmat-tests \
	books/article \
	books/article-invariants \
	books/article-properties \
	tests/acl2/article-tests \
	books/article-fields \
	tests/acl2/article-fields-tests \
	books/retention \
	books/retention-invariants \
	tests/acl2/retention-tests \
	books/node \
	books/node-invariants \
	tests/acl2/node-tests \
	books/node-traces \
	tests/acl2/node-traces-tests \
	books/records \
	books/records-invariants \
	books/records-canonicality \
	tests/acl2/records-tests \
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
	books/journal \
	tests/acl2/journal-tests \
	books/exchange \
	tests/acl2/exchange-tests \
	books/exchange-invariants \
	tests/acl2/exchange-invariants-tests \
	tests/acl2/exchange-guards-tests \
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
	tests/acl2/nntp-tests

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
