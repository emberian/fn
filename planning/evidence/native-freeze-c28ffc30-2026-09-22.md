# Native image closure of dev — 2026-09-22 (incomplete)

This record preserves what the FREEZE lane established about the native image
closure of `dev` on 2026-09-22.  **No image was built.**  The closure is not
certified: 129 of its 164 books certify at the frozen origin, two books in it
carry defects this lane did not repair, and the rest sit above them.  Nothing
here is a server, proof or flight-readiness claim.

## Sources and toolchain

- Branch `w31/freeze` at `c28ffc30163bb229c35ab5dd2c53ac1f2e9fe493`, from
  `dev` at `dbf2e1ab`.
- Frozen origin: `hbox:/tank/fn/gates/freeze-dev-28fb4bd0` (the name records
  the first snapshot mirrored into it, not the revisions mirrored later).
- ACL2 wrapper: `/tank/fn/toolchains/w28/acl2-literal-4g`, SHA-256
  `9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`,
  compatibility identity
  `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
  reported ACL2 Version 8.7.  Local iteration used ACL2 8.7 at
  `/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` on darwin-arm64; certificates
  from it were never mixed into the frozen origin.
- Selection: the 62 roots `tools/proof_artifacts.py roots --profile default`
  names, plus `tests/acl2/native-admin-tests`,
  `tests/acl2/native-operator-tests` and
  `tests/acl2/checkpoint-compaction-tests`; 164 books with the closure.  The
  `dtn` profile's 46 roots are a subset of the default 62, so both image
  profiles are covered by this selection.

## Certification runs at that origin

| handle | manifest | requested | failed | wall (s) |
|---|---|---:|---:|---:|
| `run-20260922T031236Z-c1fb` | `certify-20260922T031240Z-2615431` | 164 | 51 | 1995 |
| targeted 1 | `certify-20260922T034701Z-2641627` | 51 | 51 | 2408 |
| targeted 2 | `certify-20260922T050741Z-2682176` | 51 | 49 | 2404 |
| targeted 3 | `certify-20260922T054916Z-2704241` | 54 | 45 | 313 |
| targeted 4 | `certify-20260922T060312Z-2712514` | 51 | 41 | 2434 |

Each targeted run recertified the failures of the one before it in the same
tree, so the dependencies already certified there were not rebuilt.  The
manifests are committed beside this file.  129 of the 164 books hold
certificates at the frozen origin as of this record; a fifth run
(`build/farm/w31-targeted-6.log` in the frozen tree) was still certifying
when it was written, so that number is a floor.  The rest cascade behind the
two books below and behind the books that run was still working on.

## What the closure was failing on

One shape accounts for most of it.  The bounded CBOR profile that landed on
2026-09-21 made the record and statement codecs much larger, and several books
above them open a recognizer whose definition reaches those codecs.  A goal
that only dispatches on a record kind then carries the whole codec: the
prover does not fail, it stops returning.  Three image roots were killed at
the per-book limit rather than reporting a checkpoint, which is why the first
run read as 51 failures with one named red.

The repairs, in order, with the form each one fixes:

1. `40a51389` — `books/hybrid-store`, the guard of
   `FN-HSIG-KEYRING-SNAPSHOT-VALUE` (`(NTH 2 (FN-STMT-VALUE (FN-STMT-DECODE-
   ITEMS-PRECHECKED 5 ... 65535)))`, no induction suggested), of
   `FN-HSIG-VERDICT-DETAIL` (`FN-CBOR-VALUEP-BOUNDED` of a bytes item) and of
   `FN-HSIG-ARTICLE-EVENT-SNAPSHOT-BINDSP` (the `cdr` of an item it had just
   recognized).  Adds `fn-stmt-item-listp-implies-true-listp` and
   `fn-stmt-item-listp-nth-is-item-or-nil` to `books/statement` beside
   `fn-stmt-id-listp-implies-true-listp`, and
   `fn-stmt-uint-item-p-implies-consp` and
   `fn-stmt-bytes-item-p-implies-consp` to `books/statement-invariants`
   beside the reconstruct twins.
2. `6f41c2b9` — `books/replay`, `( VERIFY-GUARDS FN-REPLAY-IDENTITY-ADVANCE)`
   on `(ACL2-NUMBERP (FN-STXK-CONTEXT-NEXT CTX))`.  `nfix`, as its sibling
   `fn-sn-advance-identity-next` got in the same commit that asked for this
   function's guards.
3. `19c7453e` — `books/feed-connection-invariants`,
   `FN-FC-TABLE-PUT-PRESERVES-TABLE`, killed at 1800 s.  The state
   recognizers stay closed; `fn-fc-tablep-implies-unique-names` states the
   conjunct the open recognizer used to supply.
4. `f407fc56` — `books/replay`,
   `FN-REPLAY-APPLY-RECORD-NON-NIL-IS-NODE-STATE`, 600 s without leaving
   `Goal''` for 620 prover steps.  The event recognizers and the composite
   decoder are closed below the dispatch; the theorem then proves in 0.32 s
   over 90 subgoals.
5. `af06f90e` — `books/store-events` withdraws `fn-store-event-p`, the
   retention recognizer and the nine field accessors on export, which it had
   never done.  `books/store-files` (`FN-SFG-RECORD-SEQUENCE-IS-NATURAL`,
   28572 subgoals) and `books/config-records` (the guard of
   `FN-CONFIG-AWARE-LOOP`) are what that was costing.  `books/replay` exports
   the per-kind facts a book above needs instead.
6. `45aa972e` — `books/byte-store-scan` (`1+` on an unchecked counter),
   `books/node-config` (the withdrawn recognizer in a guard hint) and
   `books/store-node` (`FN-SN-COMPOSITE-DELTA` declared `:guard t` and called
   `fn-stx-delta`, whose guard is `fn-prin-keyringp`; that conjecture is
   false, not hard).
7. `8d7c09ba` — `books/byte-store-frame`, `FN-BS-FRONTIER-CBOR-PAYLOAD-BOUND`
   stopping at `(FN-CBOR-OCTET-LISTP (FN-CBOR-ENCODE-BOUNDED (CONS :UINT N)
   65535))`.
8. `c28ffc30` — `books/peer-inbound`, three reader-session constructor facts.
   **This book still does not certify**, see below.

No `skip-proofs`, `defaxiom` or trust tag was used, no theorem was deleted, and
no function that was guard verified before lost its guards.  Two definitions
changed, both by the totalization idiom this tree already uses and both on a
branch the composed machine does not reach: the counters in
`fn-replay-identity-advance` and `fn-bs-txn-observation-pairs`, and the
keyring branch of `fn-sn-composite-delta`.  Each says so in a comment beside
it.

## What is still red

### `books/peer-inbound`

`FN-PEER-SESSIONP-OF-FN-PEER-WITH-NODE`, an exported theorem.
`fn-peer-with-node` replaces a session's node and keeps its
configuration, so for a reader session whose configuration is `NIL` the result
has a checked node beside a null configuration and satisfies neither reader
shape of `fn-peer-sessionp`.  The conjecture reduces to
`(NOT (FN-NODE-STATEP NODE))` under exactly those hypotheses.  Either the
theorem needs the configuration hypothesis its statement omits, or
`fn-peer-with-node` needs to say what it does to a reader session; that is a
decision about the peering interface `books/owner` depends on.

### `books/store-node-invariants`

`FN-SN-FINISH-PRESERVES-STATE` does not leave `Goal''` within 600 s, the same
symptom as the three books repaired above.  `fn-sn-finish` reaches the record
and statement codecs through several paths, and closing them one at a time --
`fn-replay-composite-record`, `fn-sn-composite-delta`,
`fn-replay-identity-step`, `fn-replay-apply-record` -- did not change the
symptom, so the term this goal is growing was not identified.  Nothing was
committed for this book; the hint it needs is still to be found.

16 of the uncertified books are above `books/peer-inbound` and the rest above
`books/store-node-invariants` or still waiting.  `books/byte-store-frame`,
`books/config-stream` and `books/byte-store-txn-name` certify with the
repairs above; the first was still uncertified at the frozen origin when the
counts in this record were taken.

## Limitations

- No image was built and no image identity is recorded here.  No runtime
  qualification is claimed by this record, and none was attempted.
- Source correspondence is by the manifests' own source digests and by the
  commits named above; this record does not carry a build-source manifest
  because there is no build.
- The counts above describe certificates at one origin with one ACL2
  executable.  They are not a coverage claim.
- `books/statement`, `books/statement-invariants` and `books/store-events` are
  below most of the tree, so the repairs in `40a51389` and `af06f90e` reach
  31 books outside this selection.  Those were not certified by this lane;
  the tree-wide gate owns them.
