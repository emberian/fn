PYTHON ?= python3
ACL2_BOOKS ?= books/acceptance tests/acl2/acceptance-tests \
	books/wire tests/acl2/wire-tests \
	books/cbor tests/acl2/cbor-tests \
	books/retention tests/acl2/retention-tests

.PHONY: check certify model-test
check:
	$(PYTHON) tools/check_scaffold.py

certify:
	$(PYTHON) tools/certify_books.py $(ACL2_BOOKS)

model-test: certify
	$(PYTHON) tools/run_simulator.py
