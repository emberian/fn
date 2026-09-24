# K0 frontier root-directory EIO choices

The native `fnn-advance-frontier` call in `host/native/io.lisp:1515-1547`
observes a root `fnn-fsync-dir` error through the configured-owner `:store/:io`
callback and returns an indeterminate, fenced result.  In the byte model,
`fn-bs-k0-root-error-outcomes` supplies the two supported pending-root-entry
choices, `:apply` and `:drop`.  Both stop the actual `fn-bs-run` at pair 12
with EIO.  The first makes the new frontier durable; the second retains the
old durable frontier.

`fn-bs-k0-frontier-eio-choice-run-has-actual-failed-cut` proves the pair-12
equality.  `fn-bs-k0-owner-frontier-root-eio-choice-run-fences-related-state`
then proves the exact four `fn-ocfg-step` callbacks leave the owner
`:fenced-frontier` and preserve the full `fn-bs-store-relation` for either
choice.  Its premises are a Store-node state, the ready byte/kernel relation,
a typed successor frontier input, and an absent staging name.  The ACL2 test
reaches both outcomes from one related input; the exact public conclusion
holds for both, and the durable values are distinct.  Four existing
`must-fail` cases execute the exact `:apply` arm of that conclusion, each
without one premise while the other three hold.  The theorem also covers
other selector atoms because this one-entry model interprets every
non-`:apply` selector as `:drop`; only `:apply` and `:drop` are admissible
physical choices.

A bounded hbox ACL2 proof REPL loaded the book in source order through the
choice theorem, then stopped.  Selected certification used:

`python3 tools/farm.py --root /Users/ember/dev/fn/build/lanes/k0-frontier-eio-choices --remote-root /tank/fn/gates/k0-eio-choices-4ce25e-farm --jobs 2 --timeout-seconds 180 --acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache submit hbox books/byte-store-record-provenance tests/acl2/byte-store-record-provenance-tests`

Run `run-20260924T055517Z-0bfc` passed; [manifest](manifests/certify-20260924T055529Z-974811.json).
ACL2 8.7 used executable SHA-256
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`
and toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The exact source digests were
`087f4b6a160be941d02ea06763e063a887ab4ff68cc80d1eeddffa86077b5cc0`
for the provenance book and
`8e2f46c7222a71d4d7efc44718abbc83f22be11e66c93f4a38aed8c19ea20386`
for its test.  Both selected roots passed, in 13.403 s and 4.077 s
respectively; total certification wall time was 17.519 s.  This was an
incremental selected run, with 139 dependencies installed from the matching
shared cache and no closure certification.

The result starts from a related ready input.  It does not establish that
relation at every served call entry, cover other error/torn/recovery paths,
prove the native program/byte-run correspondence, or qualify the physical
filesystem barrier and its error classification.  The native
`frontierbarrier` injection occurs before the actual `fnn-fsync-dir`, so it
does not qualify either physical EIO choice.
