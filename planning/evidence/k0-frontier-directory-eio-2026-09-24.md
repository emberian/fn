# K0 frontier root-directory EIO: applied byte choice and owner fence

At `host/native/io.lisp:1515-1547`, `fnn-advance-frontier` marks publication
attempted before `fnn-replace`.  If the later root `fnn-fsync-dir` signals
`fnn-os-error`, its inner handler reports `:frontier-directory :error` through
`fnn-observe`; the outer handler returns `fnn-indeterminate` and leaves the
writer fenced.  The shared native owner binds that callback to
`fnn-owner-observe` (`host/native/owner.lisp:718`), which reaches the ACL2
`fn-ocfg-step` `(:store (:io ...))` event.  An fsync error does not establish
whether the pending root replacement landed.

`fn-bs-k0-frontier-node-root-eio-applied-fences-related-state` proves, from a
related ready byte/Store-node input, a typed next-frontier frame and fresh
staging path, that the actual rename followed by `fn-bs-fsync-dir :root
'(:eio :apply)` returns an EIO byte state with the candidate durable.  The
Store-node `:frontier-directory :error` callback enters `:fenced-frontier`
and preserves the full byte/kernel relation.  The owner projection
`fn-bs-k0-owner-frontier-root-eio-applied-run-fences-related-state` joins that
result to the actual `fn-ocfg-step` callback; its byte subject is pair 12 of
`fn-bs-run` with the EIO schedule, equated by
`fn-bs-k0-frontier-eio-applied-run-has-actual-failed-cut`.  The reachable ACL2
test has a full thirteen-pair stopped run and distinguishes `:apply` (new
durable frontier) from `:drop` (old durable frontier) under the same owner
error/fence.  Four `must-fail` cases each execute the exact three-conjunct
public conclusion with one theorem premise absent; matching positive
assertions establish the other three premises and the false conclusion.

The isolated packet source is `e0a5351f` merged with dev `67d026ad` to
include the current Store v6 field/cost updates.  The exact source digests
in the manifest are `1c9383213234560b17ebedbacceff4531ff39d37d9621c139d87a301de632982`
for `books/byte-store-record-provenance.lisp` and
`cd2dde76dd732a81b1935fa797dd4b92a4d4152d5f92c14bb7ca1258cbddb451`
for its final ACL2 test.  A bounded persvati proof REPL admitted the new lemmas
before certification (the substantive Store-node theorem took 0.32 s; the
actual failed-run cut equality took 0.52 s), then was stopped.

Selected certification: `python3 tools/farm.py --root
/Users/ember/dev/fn/build/lanes/storage-k0-failure --remote-root
/home/ember/fn-gates/storage-k0-failure-eio-20260924 --jobs 2
--timeout-seconds 180 submit persvati books/byte-store-record-provenance
tests/acl2/byte-store-record-provenance-tests`; run
`run-20260924T045443Z-10ad`, [manifest](manifests/certify-20260924T045455Z-319551.json).
ACL2 8.7, executable SHA-256
`346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`,
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`;
status passed with fifteen changed or uncached parent/book/test certificates,
no failed books, 193.53 s wall time.  The provenance book took 11.588 s and
the test book 3.772 s; the updated Store-node traces parent took 41.879 s.

Review tightened the premise teeth after that first pass.  Two cached
test-root attempts exposed test harness errors rather than theorem failures:
`run-20260924T050147Z-63ca` stopped on a guard violation while evaluating
an intentionally invalid composed state, and `run-20260924T050329Z-1a3a`
stopped on an `mv-nth` translation/signature mismatch in the occupied-stage
assertion.  The invalid-state test now uses `with-guard-checking :none` so its
logical conclusion is actually evaluated; the occupied-stage test uses
`mv-let`.  The final selected test-root run
`run-20260924T050510Z-3534`, [manifest](manifests/certify-20260924T050518Z-418371.json),
passed in 3.999 s with the previous book certificate installed from cache.

This is one selected modeled EIO outcome, not a theorem over arbitrary
directory-error choices.  The `:drop` test is a reachable counterexample to
inferring persistence from EIO.  The theorem begins with a related ready
entry; served call-entry relation establishment, other error/torn/recovery
paths, program-mode host execution and physical filesystem barrier
qualification remain open.  The existing native `frontierbarrier` injection
occurs *before* `fnn-fsync-dir`; it can check classification and recovery but
cannot qualify a real fsync EIO or the modeled `:apply` choice.
