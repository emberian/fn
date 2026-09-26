# served-path-scale, 2026-09-26 (Opus 5.5): the open's quadratic walks gone; what the 20,000-article fixture costs now

Lane `lane/served-path-scale` from dev 273cd980 (wave 4, lane 4). Ids:
PRF-173, SCN-103, PKT-455 (what remains); PKT-456 not taken (no decision
surfaced). Commits 7f822c7d (open: freshness and archive bindings),
1f5acd35 (refresh: group index), 5e15ad4c (admission: identity test), and
the registry/record commit that carries this file.

## What changed, and the assurance chain

Four executed functions, each the `:exec` of an `mbe` whose `:logic` is the
old definition, unchanged, so every existing theorem keeps its statement:

| Subject (book) | Executed | Keystone (hypotheses) |
| --- | --- | --- |
| `fn-articles-freshp` (acceptance.lisp) | `fn-fr-freshp`: one hash set of the memberships seen, each article checked against the earlier ones, then added | `fn-articles-freshp-is-one-pass` (none) |
| `fn-node-articles-have-archive-bindingsp` (node.lisp) | `fn-nab-articles-boundp`: bindings and pins indexed once in two hash tables, the first element per key kept | `fn-node-articles-have-archive-bindingsp-is-indexed` (none) |
| the identity test in `fn-retain-admissiblep` (retention.lisp) | `fn-retain-known-id-scanp`: the pins and releases walked, no identity lists consed | `fn-retain-known-id-scanp-is-known-idp` (none; iff) |
| the group index `fn-own-refresh` installs (owner.lisp) | `fn-gidx-refresh`: the old index with the new head article's entries put in when the visible list grew by one; else the rebuild | `fn-gidx-refresh-is-build` (the old index is the build of the old list, or NIL) |

The freshness pass checks each article against the EARLIER articles where
the logic checks it against the LATER ones; they agree because
disjointness is symmetric (`fn-fr-disjointp-commutes`).

Chain: native entry `store STORE recover` / `operator CONFIG run` ->
host/store-node-host.lisp `fn-store-sn-open-extended` ->
`fn-sco-store-open` -> `fn-sco-finalize-from`'s `(fn-sn-statep opened)` ->
`fn-node-statep` -> `fn-statep` -> `fn-articles-freshp` and
`fn-node-articles-have-archive-bindingsp` (executed: the one pass) ->
refinement keystones above -> the relation `fn-node-statep` itself, whose
preservation by every admitted transition is the existing carried
invariant (acceptance-invariants, node-invariants; the transitions never
evaluate it: their guards carry it) -> observed: the fixture opens (below).
The reader open reaches the same recognizers through `fn-nntp-projectionp`
(`fn-own-open`) and `fn-own-reader-context`'s `fn-peer-open-session`
(host/owner-host.lisp `fn-owner-open` -> `fn-ocfg-open`); a BP acceptance
check through `fn-bpi-node-record-committedp`. The admission's scan is
reached from `fn-node-prepare` on every POST and every replayed
acceptance. The group index: `fn-own-refresh` (every owner transition that
refreshes, `fn-own-start` at open), whose relation conjunct
`fn-own-view-okp` (group index = build of the visible articles, or none)
is what the keystone's hypothesis names; `fn-own-refresh-preserves-relation`
(owner-invariants.lisp) proves unchanged over the new refresh.

On the brief's "carried pattern": the relation carried through transitions
is `fn-node-statep`, already carried (no transition evaluates it). What the
open had was not a missing carry but a quadratic ESTABLISHMENT: the open
must check a node decoded from bytes it did not write (the checkpoint) or
replayed, and it now does so in one pass (the brief's "one membership table
built once, each record checked against the table: linear"). The commit
adds no check (its guard carries the relation).

Teeth: tests/acl2/open-one-pass-tests.lisp. Part 1: a reachable node of
twelve articles committed through `fn-node-prepare`/`fn-node-complete`;
the executed checks and quadratic references (the logic bodies copied)
agree on it and on CORRUPTED states (labelled: no transition makes them):
the first article repeated at the end, one membership shared by articles
six apart, a membership repeated inside one article (fresh, both paths:
the relation's own edge), equal non-cons elements (fresh), a released pin,
a dropped binding, a wrong-subject binding or pin placed BEFORE the good
one (refused) and AFTER it (accepted: first key wins, both paths), and a
node recognizer refusing the corrupted node. The executed functions'
callee closure contains none of fn-all-article-memberships,
fn-memberships-conflictsp, fn-pair-memberp, fn-node-find-binding,
fn-retain-find-id, fn-retain-obligation-ids, member-equal (the statement
about the executed function; the :exec branch of each recognizer is
asserted to be the one-pass call). Part 2: `fn-gidx-refresh-is-build`'s
reachable extension witness (the put branch runs and equals the rebuild),
the no-change and no-index branches, a stale-index counterexample and a
`must-fail` of the statement without its hypothesis. Part 3: the
admission refuses a committed identity and admits a fresh one through the
scan. The three refinements in parts 1 and 3 have no hypothesis, so no
must-fail applies.

Visits (the witness for "the open no longer calls fn-all-article-memberships
per article"): the logic body visits N(N+1) list cells of
fn-all-article-memberships for N articles of two memberships each (each
membership of article i walks the memberships of the N-i later ones):
400,020,000 at N = 20,000; the executed pass visits none (callee closure,
above) and puts 2N keys. REPL on persvati (repl-recognizer-scaling.txt),
reachable nodes of N articles, `fn-node-statep` executed against the
references evaluated in the logic:

| N | fn-node-statep | reference freshness | reference bindings |
| --- | --- | --- | --- |
| 1,000 | 0.00 s | 0.08 s | 0.14 s |
| 2,000 | 0.00 s | 0.25 s | 0.40 s |
| 4,000 | 0.01 s | 0.98 s | 2.24 s |

## Measurements (hbox; the fixture, never opened in place)

planning/evidence/served-path-scale-2026-09-26/fixture_open.py over a copy
of hbox:/tank/fn/scratch/fixtures/chain-20000-8cc3cd4c (pack-chain-open's,
SCN-064); K = 16 unless noted. Every FIRST open below is a full replay (the REOPEN rows open from the checkpoint the first run published): the current
format refuses the fixture's checkpoint (written by the 8cc3cd4c image;
`open=full-replay reason=checkpoint-open-refused` on every image here, the
base included), so the fixture no longer measures pack-chain-open's
checkpoint path (196 s there, on bf5b2471).

| Image | recover | LISTENING | greeting median (min) | GROUP | log sha256 |
| --- | --- | --- | --- | --- | --- |
| base 273cd980 (core 6cb25213) | 311.9 s, 5.57 GB | 280.7 s | | | time-base-273cd980.log 8240e6ce... |
| base 273cd980, K = 1, run beside the scale test | 378.1 s | 367.5 s | 116,539 ms (one) | 0.10 s | open-base-273cd980.log |
| base 273cd980 REOPEN from its published checkpoint, same run | 251.2 s | 260.4 s | 95,302 ms (one) | 0.06 s | same |
| 7f822c7d (core 7ad17b92) | 103.0 s, 5.64 GB | 115.0 s | 1,183 ms (378) | 4.71 s | open-img1-7f822c7d.log a160c6f0... |
| 5e15ad4c (core bacf7937) | 110.0 s, 5.64 GB | 119.3 s | 1,039 ms (591) | 3.97 s | open-img2-5e15ad4c.log 632da4de... |
| 5e15ad4c REOPEN from the checkpoint its first run published | 51.4 s, 5.66 GB | 43.1 s | 369 ms (355; p95 378) | 0.07 s | same |

The first run's greetings, GROUP and OVER overlap the automatic checkpoint
publication a full-replay start triggers (2 x 20,000 >= K), so their
spread is the collector's; the REOPEN row has no publication. OVER median
70 ms, ARTICLE 7.4 ms, STAT 1.1 ms at N = 20,000 (5e15ad4c).
The 5e15ad4c full-replay row ran while hbox built the production image,
so its wall time is not comparable to 7f822c7d's; the CPU profile is:
sb-sprof over `store recover` (prof.sh: `sb-ext:exit` encapsulated to write
the report), 121.1 s sampled on 7f822c7d (`fn-retain-obligation-ids` 26.8
percent via `fn-retain-known-idp`, the next quadratic) and 94.6 s on
5e15ad4c, where it no longer appears (prof-recover-img1-flat.txt,
prof-recover-img2-flat.txt). What the full replay costs now is linear per
octet: `fn-record-string-octets-aux` 24.2, `fn-cbor-octet-listp` 20.5,
`fn-record-payloadp` 20.3 percent cumulative (the history recognizer and
record decode over octet LISTS, D27's representation), collector 11.3.
pack-chain-open's profile had 54.8 + 22.1 percent in the freshness walk and
13.9 + 5.9 in the binding searches; none of the four appears in either
profile here.

The greeting at N = 20,000 is 369 ms on the reopened owner against 95.3 s on
the base image's reopened owner (one sample, run beside the scale test; the
base's first-run greeting 116.5 s): no longer the quadratic (at N = 4,096 it
was 1.4 s, checkpoint-cost). The checkpoint reopen: 43.1 s against 260.4 s. but still three
LINEAR whole-state recognizers per connection under the owner mutex:
`fn-statep` of the view's archive twice (`fn-nntp-projectionp` in
`fn-own-open`'s session, and again in `fn-own-reader-context`) and
`fn-node-statep` of the store's node once (`fn-peer-open-session`). This is
PKT-190's remainder, not done: PKT-455 (1).

POST at N = 10,000 (the gate's rows) was not measured on this lane's image:
not done, PKT-455 (4).

## Certification (persvati, 2 jobs, 300 s)

- r1 run-20260926T111554Z-905f, certify-20260926T111625Z-902587: 727
  passed, 0 failed (acceptance.lisp, node.lisp and the test book's closure;
  acceptance 0.7 s, node 0.8 s).
- r2 run-20260926T114117Z-7f51, certify-20260926T114213Z-1217897: 147
  passed, 0 failed (owner.lisp's closure; owner 2.1 s).
- r3 run-20260926T115656Z-16bc, certify-20260926T115813Z-1406816: 693
  passed, 0 failed (retention.lisp's closure, which includes node, owner
  and the test book at the final bytes; retention 0.4 s, node 0.6 s, owner
  2.0 s, open-one-pass-tests 1.5 s). Its source digests of the five changed
  files equal 5e15ad4c's.
- Over 10 s at two jobs: books/owner-invariants 10.1 s (r3; 11.8 s before
  this lane, PKT-371/PKT-437, not this lane's); r1's list of fourteen
  books between 10.0 and 14.6 s was measured under a 727-book run and none
  is a book this lane changed.

## Native (hbox, tools/hbox_native.sh)

- native-img1-7f822c7d (SHA256SUMS 27638725...): test_native_checkpoint OK
  (skipped 4), test_native_reader_index OK (skipped 5: FN_RUN_NATIVE_READER_INDEX
  unset), test_native_state_checkpoint OK (skipped 4: no production image).
- native-img2-5e15ad4c, developer and production images, with
  FN_RUN_NATIVE_READER_INDEX=1 (SHA256SUMS a2a01b4b...):
  test_native_checkpoint OK (skipped 3: the combined E2 developer image
  cases), test_native_reader_index OK (all run), test_native_state_checkpoint
  OK (all run). Logs 073f97c1..., f17abdaf..., f76ebb79....
- test_scale_store_compacts_into_a_chain from the fixture on 5e15ad4c
  (FN_P5_FIXTURE, --mem 40G; SCN-064's 20,000-article served-identical
  claim over the compacted chain): OK in 1,249.9 s, against 2,564.2 s on
  089f932b (pack-chain-open); log
  native-img2-5e15ad4c/logs/test-tests.test_native_pack_chain.NativePackChainTests.test_scale_store_compacts_into_a_chain.log,
  sha256 6d7c95970ed709b12bffca78833362deee74fa6575cad2ecfb77bc99a9870189.
  The served view after compaction still equals the pre-compaction view
  byte for byte: the served bytes are unchanged by this lane.

## What is not done (PKT-455)

1. The greeting is linear, not O(1): 369 ms at N = 20,000 under the owner
   mutex. Design: a carried open (`fn-scar`-style, books/owner-served-carried.lisp's
   shape) whose session takes `fn-statep` of the view's archive and
   `fn-node-statep` of the store's node from `fn-ocl-relation`
   (`fn-scar-ocl-relation-carries-node-statep` exists; the archive's needs
   the view conjunct), evaluating only the O(groups) conjuncts of
   `fn-nntp-projectionp` and the article count; the keystone: under the
   relation it equals `fn-ocfg-open`; host/owner-host.lisp `fn-owner-open`
   calls it.
2. The full replay is linear but heavy (110 s at 20,000 records): the
   history recognizer and decode over octet lists (above), and one linear
   lookup per replayed step (`fn-acceptedp`, the identity scan) that an
   index carried in the Store state would make O(1). The checkpoint reopen
   is 43 to 51 s; not profiled here.
3. The fixture's checkpoint is refused by the current format: every open of
   it is a full replay until the fixture is re-captured (never rebuilt:
   pack-chain-open's rule) or the refusal is found to be a compatibility
   bug. Not investigated.
4. POST at N = 10,000 (bytes consed per commit, owner CPU) not measured on
   this image; the refresh's group index no longer rebuilds (keystone
   above), and `(len (fn-sf-records ...))` in `fn-own-refresh` still walks
   the history per refresh.
5. PKT-041 (checkpoint-mode `fnn-open-live-store` rebuilding all N
   records' octets): not reached.

## Continuation (served-path-scale-2, 2026-09-26, Opus 5.5)

Lane `lane/served-path-scale-2` from dev a931ed8d, dev merged at 6e3ccd15
(hot-path-scans-2's count in the tree). Ids: PRF-188 (new; PRF-173 not
extended), SCN-117, PKT-514 (what remains), PKT-515 not taken (the index
shape was a defect with a fix, not a decision). Commits: 7a728986 (the
carried greeting), 9b6eb8ec (the checkpoint index shape refusal), and the
record/registry commit carrying this section. Scripts and results:
`served-path-scale-2026-09-26/continuation/`.

### 1. The greeting carries the owner's invariant (PKT-455 (1), PKT-190)

Host lines: host/owner-host.lisp `fn-owner-exposure-open` (the native
accept, host/native/owner.lisp `fnn-owner-serve-client`) calls
`fn-ocar-exp-open`; `fn-owner-open` (host/native/admin.lisp) calls
`fn-ocar-ocfg-open` (books/owner-open-carried.lisp). Each is the reference
(`fn-exp-open`, `fn-ocfg-open`) with the three whole-state recognizers a
reader open evaluated taken from `fn-ocl-relation`:

| Recognizer (reference path) | Carried from |
| --- | --- |
| `fn-statep` of the view archive, in `fn-nntp-projectionp` via `fn-served-open-indexed`'s session | `fn-acar-ocl-relation-carries-view-statep` (the projection recorded by `fn-acar-open-session`) |
| the same, again, in `fn-own-reader-context`'s `fn-peer-open-session` | the same |
| `fn-node-statep` of the store node, same call | `fn-scar-ocl-relation-carries-node-statep` |
| `fn-cfgp` of the configuration, same call | `fn-ocl-relation`'s own conjunct |

KEYSTONES (hypothesis `(fn-ocl-relation oc)` only):
`fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation` and
`fn-ocar-exp-open-is-exp-open-under-ocl-relation`: equal as values, the
greeting effects and the whole configured owner, for every AUTHINFO
policy, exposure state, limits, peer, address and time. The served bytes
are therefore unchanged. Chain: native accept -> `fn-owner-exposure-open`
-> `fn-ocar-exp-open` (executed) -> keystone -> `fn-exp-open` -> the
relation `fn-ocl-relation`, established at every host-called open
(`fn-ock-recover-installs-ocl-relation`, `fn-orec-recover-installs-ocl-relation`)
and preserved by every configured-owner transition (`fn-ocl-open-`,
`-close-`, `-observe-`, `-read-`, `-advance-preserves-historical-relation`;
the open's own preservation reaches the carried result through the
keystone) -> observed: the greeting rows below. books/owner-store-indexed.lisp's
host-step model now names the carried functions in its `:open` and
`:exposure-open` arms (`fn-ocar-ocfg-open-keeps-store`,
`fn-osi-ocar-exp-open-keeps-store`, no hypothesis), so PRF-144's
`fn-osi-live-owner-store-is-indexed` still describes the host.

What a greeting still evaluates per connection: the connection bound (`len`
of the connections), the group list and next-number table (O(groups)), the
article count (`len` of the view's articles: pointer steps, no recognizer)
and the AUTHINFO policy recognizer. The peer open (`fn-ocfg-open-peer`) is
not carried (peer connections are configured, not strangers): PKT-514.

Teeth (tests/acl2/owner-open-carried-tests.lisp, 71 forms admitted in the
persvati REPL and certified in r1): reachable witness
`*acar-t-committed*` (the configured owner the host's open installs, one
POST committed through the host's commit; `fn-ocl-relation` holds; the
view has an article): the carried and reference opens are equal, the
greeting is written, connection 2 is installed and pinned, its session
records the projection and pins the store node and the configuration, and
the relation holds after; the exposure open admits it under
public-exposure-tests' limits and returns id 2. Hypothesis (labelled
corrupted state, no transition makes it): `*acar-t-bad-view-oc*`, a
non-article added to the view archive: the relation fails, the carried
open records the projection `t`, the reference `nil`; `must-fail` for both
keystones and the conclusion asserted false. Each step lemma's hypotheses
one at a time (archive `fn-statep`, node `fn-node-statep`, `fn-cfgp`,
`fn-acar-view-statep`), each with its conclusion asserted false. All seven
carried functions are `:common-lisp-compliant`.

Measurements (hbox, 24 CPUs, SHARED with the qualification's units: load
average 14 to 17 during every row below; none is a quiet-box figure):

| Greeting (32 fresh connections after 32 warm) | base a931ed8d (core 03f2b892) | lane 6e3ccd15 (core b098e499) |
| --- | --- | --- |
| N = 10,000 (2 KiB, loaded by rep_measure; the same store copied) median / p95 | 241.3 / 359.3 ms | 0.47 / 1.20 ms |
| N = 20,000 fixture, reopened owner, median / p95 | 477.7 / 596.7 ms | 0.53 / 0.89 ms |
| N = 20,000 fixture, first (full-replay) owner, median / p95 | 872.4 / 6,252.5 ms (overlaps its checkpoint publication) | 0.53 / 0.99 ms (same overlap) |

Logs: continuation/greet-10k-base-a931ed8d.json,
continuation/greet-10k-g1-6e3ccd15.json, continuation/open-base-a931ed8d.log
(sha256 df97382d2acf97c4e9a1e6e096d1277a51267514c39107b854d652013708568f),
continuation/open-g1-6e3ccd15.log (sha256 23a8192248fa859179109e398d97aa7762978af50692f052e56ee2fb1aa564c3).
The same fixture runs time the opens: full replay `store recover` 168.5 s
(base) and 199.3 s (lane, 174.9 s user; load 13 to 15), LISTENING 176.5 /
179.6 s; the reopen from the checkpoint each published 50.9 / 49.2 s,
LISTENING 57.1 / 51.5 s. This lane changed neither; the replay's cost is
section 4.

### 2. PKT-395: the fixture's checkpoint refusal was an unversioned index shape, and it hid a silent mis-open

The checkpoint file carries the Store's derived event index and, where
the index yields the record list, only the count (`fn-sco-freeze`); the
records are thawed out of the index (`fn-sco-thaw`). The file names no
index shape, and the shape changed twice:

- a249a699 (signed-history-index): a single sequence trie became a pair
  (SEQ-TRIE . MSGID-TRIE). The fixture's image (8cc3cd4c) and the deployed
  bbf52159 predate it. Their checkpoints thaw a garbage record list and are
  refused only because a later check fails:
  `open=full-replay reason=checkpoint-open-refused`. The refusal is
  incidental, not deliberate.
- d0df09ed (hot-path-scans-2): the pair became (SEQ-TRIE MSGID-TRIE .
  COUNT). A checkpoint written between the two (a931ed8d's, dfa810fc's)
  thaws the RIGHT records, because the sequence trie is still the car, but
  its Message-ID trie is read as the car of the old one and its count as 0.
  `fn-sn-statep` leaves the derived index out by design (D21), so the open
  SUCCEEDS with an index that does not correspond to the history.

Evidence. The ACL2 value: over the 3-record history of
`*acar-t-o*`'s store, the pair built from the correct index has count 0
against 3, the same thawed records, and 0 records for the committed
Message-ID against 1 (continuation/ — REPL session p395 on persvati).
Native: the base image a931ed8d reopened the fixture from the checkpoint
it published (`open=checkpoint:20000 suffix=0`, 50.9 s); a copy of that
store recovered by the lane image WITHOUT the check (6e3ccd15, post
d0df09ed) says `open=checkpoint:20000 suffix=0` in 57.2 s (load 14.0): the
mis-open. With the check (9b6eb8ec, native-g2): `open=full-replay
reason=checkpoint-index-shape`, 217.2 s (load 14.8); and the lane's own
checkpoint (published by 6e3ccd15, the same shape) recovered by 9b6eb8ec:
`open=checkpoint:20000 suffix=0`, 46.7 s (load 13.1). continuation/cross.log.

The fix, by name, no translation: books/store-checkpoint-shape.lisp
`fn-sco-thaw-checked` refuses a thawed checkpoint whose index count is not
its record count (`:index-shape`, O(1)); `fn-sco-select-named` reports it
as `(:full-replay :checkpoint-index-shape)` and is `fn-sco-select` on every
other status. host/store-node-host.lisp `fn-store-sco-decode` calls
`fn-sco-thaw-checked`, `fn-store-sco-select` calls `fn-sco-select-named`;
host/native/io.lisp `fnn-state-checkpoint-load` passes the named status.
KEYSTONE `fn-sco-thaw-checked-accepts-own-publication` (hypothesis
`(true-listp suffix)`, the decoded suffix the host passes): the freeze of
`fn-sco-extend` of a capture thaws to `(:ok C)`, so this image never
refuses its own publication. Teeth (tests/acl2/store-checkpoint-shape-tests.lisp,
30 forms admitted in the REPL): the reachable recovery image's frozen
capture (count 2) thaws `:ok`; the pair shape thaws the right records with
count 0, does not correspond, and is refused `:index-shape`; the single
trie is refused the same way; `must-fail` of the keystone with an atom
suffix (its conclusion asserted false) and of the selection lemma without
its hypothesis. The shape test is necessary, not sufficient: a file this
image wrote is still trusted as its capture, as before. docs/operator.md
"Upgrade, and what a rollback loses" says which checkpoints are refused and
that no image from d0df09ed up to this check may be deployed over a node
whose checkpoint was published between a249a699 and d0df09ed.

### 3. POST at N = 10,000 and PKT-517 (the group index rebuild)

rep_measure on the lane's profiling twin (6e3ccd15, core 1186ed7a) over a
10,000 x 2 KiB store on /dev/shm, K = 32, R = 3, load average 14:
bytes consed per POST 2,497,908 (hot-path-scans-2 measured 7,955,659 and
7,965,868 at N = 10,000 on images that predate served-path-scale's
group-index extension, 1f5acd35: neither 5c6825b2 nor ff2eacb3 contains
c150c506); POST median 7.95 ms, p95 8.92 ms on tmpfs; STAT 49 KB, ARTICLE
430 KB per op. Call counts over 200 POSTs after a reopen (continuation/count.lisp,
sb-int:encapsulate): `fn-own-refresh` 1,800, `fn-gidx-refresh` 800,
`fn-midx-refresh` 800, `fn-ctl-refresh-visible`, `-withdrawn`,
`-withdrawals` 800 each, and ZERO calls of `fn-gidx-build`,
`fn-index-build` and `fn-midx-build`. PKT-517's rebuild is not on the
current code: its 19,900 samples were the images before the fix. The
allocation profile of those 200 POSTs (continuation/alloc-g1-flat.txt) is
now the served per-byte fold (`fn-scar-feed-byte` 36 percent of samples,
under `fn-scar-feed-counted` 50): ingress-span's lane, not this one.

`fn-own-refresh`'s `(len (fn-sf-records ...))` stays: 10,000 pointer
steps, no allocation, a few microseconds; replacing it with
`fn-sbud-count`'s O(1) count needs the Store's index premise inside
`fn-own-refresh`, i.e. a carried twin of every refreshing owner transition
(the logic body of `fn-own-refresh` is what every owner theorem reads).
Measured cost against that proof cost: not done, PKT-514.

### 4. What the 20,000-record open costs now (PKT-455 (2), for ember's "why still slow")

served-path-scale's sb-sprof graph of `store recover` on the fixture
(5e15ad4c, 94.6 s sampled; hbox:/tank/fn/scratch/served-path-scale/prof-img2/out/graph.txt)
read for callers: (a) the chain/checkpoint link decode
(`fn-ccc-decode-link` 30.2 percent cumulative) re-validates each record's
octets as octet LISTS in several decoders: `fn-record-payloadp` (20.3),
`fn-cbor-octet-listp` (20.5, from `fn-stmt-decode-prefix-items-bounded-impl`,
`fn-cc-octet-event-listp`, `fn-record-decode-exact-impl`,
`fn-ccc-decode-link`, `fn-ccc-framed-link`, `fn-cc-decode-exact`,
`fn-frame-trailer`), `fn-record-string-octets-aux` (24.2): D27's
representation at open (PKT-168 (4)); (b) the two per-step linear lookups
of the replay, O(N) per step and so O(N^2) per replay:
`fn-retain-known-id-scanp` (retention.lisp, `fn-retain-admissiblep`'s
:exec, from `fn-node-prepare` per replayed acceptance) 12.3 percent and
`fn-acceptedp` (acceptance.lisp `fn-accept-prepare`'s duplicate test)
about 4; (c) the collector about 11. Not done here (budget): the index
carried through the replay (design in the LANEDUMP: a fast-alist identity
set beside `fn-sco-cpr-prefix`, extended when the node's lists grew by one
and rebuilt otherwise, the `fn-gidx-refresh` pattern; an indexed twin of
`fn-cpr-apply-event` -> `fn-replay-apply-record` -> `fn-node-prepare` whose
two lookups read it; keystone: equal to the reference fold under the
index's correspondence). PKT-514 (1).

### 5. PKT-041 (checkpoint-mode `fnn-open-live-store` rebuilding the prefix octets)

Not reached. The reopen from a checkpoint is 46.7 to 50.9 s at N = 20,000
on this box against 168 to 217 s of full replay; the envelope measured the
two equal at N = 10,000 on tmpfs (11.9 against 12.7 s). The prefix octets
are `fn-store-sco-prefix-octets` re-encoding every record of the checkpoint
(host/store-node-host.lisp) for pack, compact and the owner; not profiled
by this lane. PKT-514 (2).

### Native gate (hbox, tools/hbox_native.sh)

- native-g2 (9b6eb8ec: both changes; developer and production images;
  SHA256SUMS sha256 92c19bfd...): test_native_bounds_join OK (2 ran, 1
  skipped: FN_FORMAT7_IMAGE), log 79c85490...; test_native_checkpoint OK (23
  ran, 3 skipped: the combined E2 developer image cases), log 7d8dd16e...;
  test_native_owner FAILED (2 of 18), log a4ed64b9...: the two
  NativeOwnerHandlerStructureTests (`developer_selectors_gate_arm...`,
  `the_chunk_loop_keeps_its_suffix...`) fail identically on the base image
  a931ed8d (native-base-a931ed8d, SHA256SUMS d606dc9d..., which also failed
  `two_client_uncertainty_fences...` once): environment/harness of the base,
  not this lane's change. native-g1 (6e3ccd15) the same (SHA256SUMS c7aa3f27...).
- The served bytes: the keystones equate the carried opens with the
  reference as values; the greeting rows above answer the same 200/201.
  bounds_join's LargeReplyTests ran inside test_native_bounds_join (OK).
  The v0 matrix's served rows were not rerun (PKT-514 (3)).

### Certification

persvati r1 run-20260926T145403Z-5ed0, certify-20260926T145454Z-3119631: 7
passed (owner-open-carried 1.9 s, owner-store-indexed 3.7 s, the test books
1.8 to 2.2 s). r2 run-20260926T150340Z-9b58, certify-20260926T150419Z-3212490:
2 passed (store-checkpoint-shape and its tests). No book over 10 s.
store-checkpoint-shape.lisp was changed after r2 (a lemma renamed
`fn-sco-select-named-unfolds`, readmitted in the REPL with its test book):
the batch certifies it.

### What remains (PKT-514)

1. The replay's per-step lookups (section 4 (b)) and the octet-list
   re-validation at open (section 4 (a), with PKT-168 (4)).
2. PKT-041 (section 5).
3. The peer open (`fn-ocfg-open-peer`) still evaluates `fn-node-statep` and
   the archive's `fn-statep` per peer connection; `fn-own-refresh`'s `len`;
   the v0 matrix's served rows on the lane image; a quiet-box repetition of
   every figure above (PKT-476).

Packets: PKT-455 (1) done (the greeting: 0.53 ms at N = 20,000 against
478 ms); (2) narrowed to PKT-514 (1); (3) answered: PKT-395's refusal was
an unversioned index shape, now refused by name, and the silent mis-open of
a249a699..d0df09ed checkpoints is fixed; (4) measured (2.50 MB per POST;
PKT-517's rebuild is absent on the current code); (5) PKT-514 (2).
PKT-190 ticked (the greeting evaluates no whole-state recognizer).
PKT-395 ticked by 9b6eb8ec (the rehearsal of the next deployment should
still record `reason=checkpoint-index-shape` for a dfa810fc node).
PKT-517 answered: not on the current code (zero builds in 200 POSTs).
