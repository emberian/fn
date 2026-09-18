PYTHON ?= python3
ACL2_BOOKS ?= books/acceptance books/acceptance-invariants tests/acl2/acceptance-tests \
	books/wire tests/acl2/wire-tests \
	books/cbor books/cbor-invariants tests/acl2/cbor-tests \
	books/retention tests/acl2/retention-tests \
	books/node tests/acl2/node-tests \
	books/journal tests/acl2/journal-tests \
	books/exchange tests/acl2/exchange-tests \
	books/nntp tests/acl2/nntp-tests

.PHONY: check certify model-test tooling-test
check:
	$(PYTHON) tools/check_scaffold.py

certify:
	$(PYTHON) tools/certify_books.py $(ACL2_BOOKS)

model-test: certify
	$(PYTHON) tools/run_simulator.py

tooling-test:
	$(PYTHON) -m unittest discover -s tests -p test_certify_runner.py -v
