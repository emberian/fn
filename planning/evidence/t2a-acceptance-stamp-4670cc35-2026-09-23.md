# T2a acceptance-stamp lane evidence, 2026-09-23

Source: branch `implement/acceptance-stamp`, revision `4670cc35` (base
`24a5df6b`). The ACL2 certification source ends at `cb00bc4b`; subsequent
commits change the simulator and host clock adapters, not ACL2 books. T2b
NEWNEWS date selection is not in this batch.

An article prepared from a usable owner clock observation now carries its
derived stamp in the pending article, accepted article, record schema 1, node,
and recovered replay. A legacy schema-0 record decodes with `:legacy`, and
re-encodes byte for byte; live `fn-sn-prepare` and the served optimized
`fn-spc-prepare` refuse a new legacy article. The refusal at the owner and
signed/BP ingress is `:clock-unusable`, separate from durable acceptance and
uncertain persistence. The stamp is an acceptance observation, not an author
identity or a cursor.

The keystone `fn-replay-article-stamps-are-the-journal-stamps` in
`books/acceptance-stamp-invariants.lisp` states that the final article stamp
projection equals the projection of a mixed schema-0/schema-1 journal, including
a composite child. Its test book exercises the mixed journal, one-record
article and composite paths, finish paths, and must-fail cases for the
meaningful hypotheses. `fn-spc-prepare-equals-specification-under-relation`
licenses the host's optimized preparation call after the new legacy refusal
was added to that projection.

Real ACL2 8.7 certification ran on `persvati` with executable
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (SHA-256
`346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`),
two shared jobs and the incremental cache `/home/ember/fn-certcache`. The
selected stamp test closure passed in
`build/acl2/certify-20260923T155856Z-97680`. The broad affected run
`build/acl2/certify-20260923T161451Z-1543548` found one stale acceptance
fixture and the optimized prepare mismatch; the repair run
`build/acl2/certify-20260923T161928Z-1585422` passed all five affected roots.
`python3 tools/green_check.py --changed-since 24a5df6b41e8885f992610cbcfc267c0dbfdb17c --summary`
then reported 94 changed books, 229 books including one, and zero not green at
the bytes this lane carries. Manifests record each source digest and certificate
provenance. `make check` passed after `python3 tools/ledger.py --write`.

The independent cbor2 6.1.4 probe passed 39/39 cases; its raw manifest is
`build/cbor-interop/run-20260923T150521Z-82870/manifest.json` (SHA-256
`a3d32308fe220761795cf91c80153d061f55864419c931afedf30024d69aa901`).
The BP ingress host tests passed 5/5. `python3 tools/run_simulator.py` passed
`acceptance-durable` with an exact persisted-stamp assertion in
`build/simulator/run-20260923T162147Z-13182`.
Focused Store adapter tests passed 2/2 for pre-epoch and missing wall readings:
both are passed to ACL2 with `has-wall` false, so the core can refuse them
instead of writing a fabricated epoch-zero stamp. The native owner and Store
adapters share the same wall reading and unusable flag. The live Python Store
prepare/finish lifecycle test passed again after this adapter change.

An optional broader Python Store fault-matrix run was stopped after 25 minutes.
Its completed live Store-node cases passed, but several corruption cases were
red before the matrix finished: their JSON checksum/config fixtures and
diagnostics predate framed metadata. The same JSON expectations and explicit
legacy-JSON refusal are both present in the `24a5df6b` base, so this run is
not evidence of a T2-specific failure or of a passing corruption matrix.

The native carried-over-store witness remains open until a T2 native image is
built and `tests/test_native_stamp_migration.py` runs against the frozen
pre-T2 image and that new image on hbox. The old image is already frozen at
`f0b8b166`; this lane neither rebuilt it nor changed `/tank/fn/node`.
