# Native image closure of dev — 2026-09-22, second pass (incomplete)

This record continues
[`native-freeze-c28ffc30-2026-09-22.md`](native-freeze-c28ffc30-2026-09-22.md).
**No image was built.**  The closure is not certified.  Nothing here is a
server, proof or flight-readiness claim.

## What the first pass got wrong about the cause

The first pass diagnosed the reds as the bounded CBOR profile making the
record and statement codecs large, so that goals which only dispatch on a
record kind carry the whole codec and stop returning.  That is real, it
accounts for most of the *timeouts*, and every repair it made on that reading
stands.  It is the smaller half.

The larger half is that five commits landed behaviour into books whose
invariants books did not certify afterwards, and nobody ran them:

| commit | time (2026-09-21) | what it changed |
|---|---|---|
| `6e992351` | 12:03 | widened `fn-sn-state` from six fields to ten (keyring generation, acceptance verdicts, keyring snapshots, identity sequence) |
| `6ab2c783` | 12:43 | a retention arm in `fn-sn-finish` and in `fn-replay-apply-record` |
| `64a80197` | 13:02 | AUTHINFO binds the inbound peer role to an authenticated principal; a null peer beside a checked node now fails `fn-peer-sessionp` |
| `4bb7bb3d` | 13:24 | an identity arm in `fn-sn-finish` and in `fn-replay-apply-record` |
| `40bb3f74` | 14:34 | a `:fault` arm in `fn-sn-recover` |

`books/store-node-invariants` last certified at 2026-09-21 01:20 and
`books/nntp-auth` at 01:21.  So the statements those books carried about
`fn-sn-finish`, `fn-replay-apply-record`, `fn-sn-recover` and the AUTHINFO
session were never proved in the shape the machine now has, and several were
**false** on arms that did not exist when they were written.  A red book here
is not only a hard proof; it is often a claim that stopped being true and no
run said so.

## Sources and toolchain

- Branch `w31/freeze-2` at `01fbdad4e70b36353d1c9e5b12befec95932c96a`, from
  `dev` at `27dc5a21`.
- Frozen origin: `hbox:/tank/fn/gates/freeze-dev-28fb4bd0`.
- ACL2 wrapper `/tank/fn/toolchains/w28/acl2-literal-4g`, SHA-256
  `9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`,
  compatibility identity
  `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
  reported ACL2 Version 8.7.  No certificate from any other machine was mixed
  into the frozen origin; this lane started no ACL2 on the laptop.
- Selection: the 62 roots `tools/proof_artifacts.py roots --profile default`
  names, plus `tests/acl2/native-admin-tests`,
  `tests/acl2/native-operator-tests` and
  `tests/acl2/checkpoint-compaction-tests`; 164 books with the closure.

## The closure, in one run

`run-20260922T115350Z-6809`, manifest
`certify-20260922T115409Z-2912983`, on hbox at the frozen origin with the w28
wrapper: all 164 books of the selection requested with `--closure` and
certified from an empty certificate set, `--jobs 8`, 1800 s per book.
**140 passed and 24 failed.**  That is the number this record claims; the
per-book runs below are how each repair was reached, not a second count.  The
first pass left 130.

The 24 are `books/store-node-traces` and `books/checkpoint`, and 22 books
above one of them that failed only on a missing certificate for a dependency.

## What now certifies that did not

Named with the manifest that certified it.

| book | manifest |
|---|---|
| `books/peer-config` | `certify-20260922T080733Z-2782785` |
| `books/peer-inbound`, `books/nntp-auth` | `certify-20260922T085537Z-2810518` |
| `books/served`, `books/served-tls-prefix`, `books/native-auth-profile`, `books/native-auth-admin` | `certify-20260922T090724Z-2818492` |
| `tests/acl2/peer-inbound-tests` | `certify-20260922T091017Z-2820528` |
| `books/store-node-invariants` | `certify-20260922T113956Z-2906927` |
| `books/bp-ingress`, `books/bp-receipt`, `books/bp-receipt-records`, `books/bp-receiver-state-invariants` | `certify-20260922T112931Z-2901579` |

## What changed, by book

### `books/peer-config`

`fn-cfg-peerp-auth-field`: a peer record's authentication half is a cons,
beside `fn-cfg-peer-find-is-a-peer` where that comment block says such facts
belong.  It is the guard obligation `fn-auth-clear-principal-peer` could not
discharge.

### `books/peer-inbound`

Three session lemmas stop being local, because `books/nntp-auth` builds and
drops peer roles and cannot open the recognizer:
`fn-peer-sessionp-of-make-session-peer`,
`fn-peer-sessionp-of-make-session-reader-configured` and
`fn-peer-session-consistentp-of-make-session`.

### `books/nntp-auth`

The octet check on the principal (`a8954441`, already on dev), plus: a
configuration's peer rows are a `fn-cfg-row-listp`, and a peer name found in
them is a string.  The two `-preserves-consistentp` lemmas now hold the POST
and NNTP session recognizers closed as they already held the peer one;
opened, the promotion branch unfolded the base's recognizer into a
`true-listp` obligation on the NNTP session instead of using the hypothesis it
already had.

### `books/store-node-invariants`

The identity replay context's snapshot list and next sequence number, stated
over `fn-stxk-apply-snapshot`, `fn-stxk-apply-verdict`,
`fn-replay-identity-step` and the fold, so `fn-sn-finish` and `fn-sn-recover`
carry them without the record codec.  The `:fault` file state `40bb3f74`
introduced.  `fn-sn-file-recovery-retains-history` extended with the successes
conjunct that state needs.  An article record is none of the other four store
events, by length, and on one the composed store-event accessors are the
record's own.  The store equations for the two arms of `fn-sn-finish` that
publish no article.  And, for the replay loop, four facts about one function
each — an advance from an idle node lands idle at its transaction id, an
advance that IS a node was given one, an advance that landed was not past it,
a preparation that staged moved the id by exactly one, and a durable
completion leaves the id where the preparation put it — which compose into the
step fact the loop's induction needs over **every** arm of
`fn-replay-apply-record`, not the article arm alone.

Four keystones now name the arm they are about, because on the other arms they
are false: `fn-sn-finish-records-the-acceptance-verdict`,
`fn-sn-finish-is-actual-durable-completion`,
`fn-sn-finish-installs-exact-article-and-archive-pin` and
`fn-sn-replay-is-actual-live-durable-completion`.
`fn-sn-new-success-requires-actual-matching-durable-node-completion` keeps its
safety conjunct — no acknowledgement without an enabled completion — at full
strength for all three arms, and makes only the article-specific conclusions
conditional.  What the retention arm does to the verdict query is now stated
rather than left implied.

### `tests/acl2/peer-inbound-tests`

The assertion on the effects of an IHAVE from `(fn-peer-with-node *pt-reader*
*pt-node1*)` expected 502.  That object is not a `fn-peer-sessionp` — the
assertion two lines above it says so, and `64a80197` is what made it so — and
`fn-peer-step`'s first branch returns the object it was given with no effects
and no submission.  Measured on hbox: the effects are NIL.  The assertion says
that now, in both halves; the 502 is the answer a real reader session gets and
this book already asserts it of `*pt-reader*` sixty lines further down.

### `books/store-node-traces` (still red)

Three statements repaired: `fn-snt-state-reconstruction` rebuilt a state
through the six-field `fn-sn-make` and so lost the four fields `6e992351`
added; `fn-snt-record-pair-after-prefix-absent` bounded `fn-record-sequence`
where `fn-sf-record-listp` orders `fn-store-event-sequence`; and
`fn-snt-candidate-is-frontier-predecessor` read `fn-record-txid` where
`fn-sf-candidatep` pins `fn-store-event-txid`.

## What is still red, and why

### `books/store-node-traces` — the trace relation itself

`FN-SNT-RECORD-DIRECTORY-PRESERVES-RELATION` reduces to
`(NOT (FN-STORE-RETENTION-EVENT-P (FN-SF-RECORD-CANDIDATE (FN-SN-FILES S))))`
(`certify-20260922T114635Z-2909699`).  That is not a missing hint.
`fn-snt-relation` relates the node a state carries to a replay of its history,
and it was written when every history entry was an article record.  A
retention or identity candidate has no article to relate, so the relation has
to say what it means on those arms before the preservation theorems above it
can be true.  **This is the packet the next lane should take**: every other
book left in the closure is above it or above `books/checkpoint`.

### `books/checkpoint`

`FN-CHECKPOINT-RESTORE-REJECTS-FRONTIER-REUSE` fails on a goal whose
hypotheses are all in store-event vocabulary and whose one record-shaped term
is `(CADR RECORD)`; the same disease, not yet diagnosed to a line.

### The rest

`books/store-node-resolution`, `books/store-observed`,
`books/store-observed-traces`, `books/store-prepare-correspondence`,
`books/store-sweep`, `books/owner`, `books/owner-invariants`,
`books/owner-config`, `books/owner-fault`,
`books/owner-prepare-correspondence`, `books/owner-tls-prefix`,
`books/checkpoint-codec`, `books/checkpoint-publish`,
`books/bp-native-app`, `books/bp-native-app-fast`, `books/native-admin`,
`books/native-config-observation`, `books/native-control`,
`books/native-hybrid-control`, `books/native-operator`,
`tests/acl2/native-admin-tests` and `tests/acl2/native-operator-tests` failed
in `certify-20260922T112931Z-2901579` only on a missing certificate for a
dependency, so nothing is known about them beyond that they were not reached.

## Assurance

No `skip-proofs`, `defaxiom` or trust tag was used anywhere in this lane, no
function that was guard verified lost its guards, and no `:verify-guards nil`
was added.  **Nothing ACL2 had proved was weakened.**  Five exported theorems
gained hypotheses; every one of them was a statement this tree had never
admitted, in a book that had not certified since before the commit that
falsified it, and each says so at its site with the commit named.

One obligation is newly open and recorded in `planning/proofs.json` under
PRF-023: `fn-sn-finish-preserves-indexedp` now carries
`(not (fn-stxa-p (fn-sn-completion-record s)))`.  On the accepted-statement
arm the store grows by the article the event carries while the index grows by
`fn-sn-composite-delta` of the same event, and that those two are the same
growth is not proved.  The three arms it does cover are retention, the
verdict/snapshot identity arm and durable acceptance.

## Limitations

- No image was built and no image identity is recorded here.  No runtime
  qualification is claimed and none was attempted.
- The counts and manifests above describe certificates at one origin with one
  ACL2 executable.  They are not a coverage claim, and a green manifest is not
  a certificate in any other tree.
- `books/peer-config`, `books/peer-inbound` and `books/store-node-invariants`
  sit below books outside this selection; the tree-wide gate owns those.
