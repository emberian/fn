# Pinned peer inbound proof cost, 2026-09-24

The combined `8c61c098` hbox run `run-20260924T033100Z-4833`
([manifest](manifests/certify-20260924T033144Z-795753.json)) certified
`books/peer-inbound` in 55.35 seconds of ACL2 `certify-book` time
(55.432 seconds book wall time). Four pinned-session proofs accounted for
48.95 seconds. The largest, the local
`fn-peer-nntp-command-pinned-preserves-consistent-session`, took 29.70 seconds
and 17,051,682 prover steps. Its `Rules` and splitter list show
`fn-gidx-pin-correspondencep` and `fn-gidx-pinp` opened under the command
dispatcher, splitting 103 top-level cases. The book was already importing
the reader's theorem with exactly the same statement.

The proof-only edit retains every function and theorem statement. The local
reader-command, reader-step and POST-step wrappers now cite their existing
certified theorems explicitly. The peer pinned-step preservation and effects
proofs keep the pinned-index correspondence closed while dispatching. The
ledger marks the three wrappers as instance corollaries, not keystones.

On the pinned w28 hbox toolchain
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
the scoped run `run-20260924T041903Z-149f`
([manifest](manifests/certify-20260924T041906Z-867071.json)) passed
`books/peer-inbound`, `books/peer-inbound-invariants`, and
`tests/acl2/peer-inbound-tests`: 96 matching dependencies installed from
the shared cache, three roots certified, two jobs, 90-second per-book cap.
ACL2 `certify-book` time for `peer-inbound` was 8.79 seconds (12.79 seconds
book wall time). The same four proof events took respectively 0.01, 0.01,
0.05, and 2.91 seconds; the peer pinned-step effects proof used 1,770,383
steps. The old and new hbox runs use the same toolchain, but their source
closures differ beyond this proof edit (`8c61c098` versus the lane based on
`af47c79a`), so this is a measured regression repair rather than a
controlled single-commit benchmark.

`make check` passed after regenerating the ledger. `green_check
--changed-since af47c79a --strict` reports 99 affected books, including
the edited book; the scoped run certifies the changed book, its immediate
invariants, and its test book. The wider dependent closure belongs to the
next frozen combined gate. No runtime semantics or proof hypothesis changed.
