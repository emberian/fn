# coverage-gap continuation
Commits: 774ee84b9 (tools/coverage_gap.py, tests, Makefile check-coverage, ACKS.md), 1b3909eac (certs install exit 1 on unreadable).
Report on dev: /tmp/covgap-report.log -- LANDED 185, IN-FLIGHT 19, PARKED 4, UNOWNED 190 (all unacked), CLOSED 23, NEVER-RUN 80 (23 scenarios, 57 modules; unacked).
Open: the 190 UNOWNED need lanes or ACKs (coordinator). Module never-run matching is by evidence-index path names only (heuristic; tools/coverage_gap.py names_module). ACKS.md has zero entries by design.
Not in check-fast until the backlog is dispositioned. Note check-host-translate runs certs install, which now exits 1 on unreadable books.
