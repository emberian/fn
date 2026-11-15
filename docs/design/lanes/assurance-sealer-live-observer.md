# Live sealer source observation

The actual resident sealer acquires its endpoint receipt before
`fn2-seal-start` enumerates sources. The receipt stays in `fn2-seals` through
build, installation, overlay/hash-window return, and retirement of the old
installed run rows. The final `fn2-seal-release` step reaches `IDLE` only after
its actual retired-row selector is exhausted. A separate actor `:draining`
turn then releases the exact receipt and wakes the actual writer returned by
the source barrier. Failed release retains the receipt.

`CLOSING` refuses new sealer prefixes. An existing positive receipt may resume
while closing, including when the barrier writer is pending. Snapshot prepare
retains the allocator token/owner without changing freeze-phase0; the resident
sealer's build/install/release path uses its existing pool/cache resources and
has no new B lifecycle admission. The final snapshot poll refuses `HELD` until
the actual lower seal row is `IDLE`, held0, receipt0, and its real reader
endpoint is not live. Thus the post-fence writer does not wait for a sealer
that the held snapshot has already paused.

Old merge cursor fields are nonresumable at lower `IDLE`: only the start branch
can run, and it establishes the next actual source plan before the build
branch can read it. No receipt is released merely because installation has
returned or a page appears complete. Sealer initialization refuses a live
receipt.

The prepared `sealer-source-quiescence-unit` fixture uses real overlay codecs,
freeze, sealer callbacks and snapshot polling with two large windows. It does
not plant observer/phase/ready state. It is authored but unexecuted. Eight
Python source controls check these callback boundaries. Reader/structure
checks do not establish ACL2 admission or runtime behavior.

This source slice depends on the actual shared `c-source-observer` leaves and
registered source control/readers children plus the actual endpoint geometry.
It covers the current resident output path; it does not supply a streaming
physical sealer publisher or establish unbounded maintenance progress.
