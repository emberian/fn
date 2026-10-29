# From layer B to layer A: simulated-storage defects and gaps found by B1 (2026-10-28)

B1's differential (`fn2/tests/crash-model-differential.lisp` on branch `fn2/b-durability`) drives
A's `fn2/sim/storage.lisp` entry points beside the block-device crash model
(`fn2/books/crash-model.lisp`) and checks every concrete result by membership. 10,000 traces:
`B1-DIFF traces=10000 unexpected=0 live=15 stale=13 teeth=4/4`. The 28 stopped traces are two
reproducible simulator defects (each has a fixed regression in the driver):

1. **Live tear then honest fence loses the covered write.** `fn2-storage-land-bytes` copies the
   pending completion stamp into the durable stamp when it lands garbage; a later
   `fn2-storage-fence-complete` then skips the unit because durable-stamp = snapshot-stamp, and the
   garbage stays durable after a successful honest fence. Repro: complete pending byte 17 at stamp 1,
   capture the fence, land garbage 93 without process death, complete the fence: durable holds 93.
   First random seed 20261539.
2. **Stale cache overwrites a newer durable version at crash.** After reopen (revert) and a later
   fence completion, durable stamps are newer than the reopened cache; `fn2-storage-crash-unit`
   treats any stamp inequality as dirty and may land old cached bytes or garbage over the newer
   durable value. Fix: dirty means pending stamp strictly newer. First seed 20261329.

Gaps (model behaviours the simulator cannot produce) are listed with papers-table rows in
`fn2/docs/b-durability.md` §3 on `fn2/b-durability`: collateral damage within a radius (row 6),
pre-completion physical redirection of in-flight writes (3, 11), per-unit loss under a lying fence
and lying FUA (5), torn landing on a failed fence and the cached-but-lost reopen view (8), a
preflush stage (14), per-byte garbage variety (10), unreported progress on :io/:no-space (22).

Also from the review (finding 11): `fn2-storage-init` takes `nfences = O`, one full-image snapshot
per operation row; layer B's commit machine needs a concrete-profile device of hundreds of sectors
with one fence in flight per domain (ROUND2 §D.3), so a fence-slot count independent of O.

Layer B does not edit `fn2/sim/`. When these land on fn2/main, B reruns the differential and expects
`live=0 stale=0`.
