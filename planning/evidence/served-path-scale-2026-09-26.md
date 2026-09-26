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
SCN-064); K = 16. Every open in this table is a FULL REPLAY: the current
format refuses the fixture's checkpoint (written by the 8cc3cd4c image;
`open=full-replay reason=checkpoint-open-refused` on every image here, the
base included), so the fixture no longer measures pack-chain-open's
checkpoint path (196 s there, on bf5b2471).

| Image | recover | LISTENING | greeting median (min) | GROUP | log sha256 |
| --- | --- | --- | --- | --- | --- |
| base 273cd980 (core 6cb25213) | 311.9 s, 5.57 GB | 280.7 s | see below | | time-base-273cd980.log 8240e6ce... |
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

The greeting at N = 20,000 is 369 ms on the reopened owner: no longer the
quadratic (at N = 4,096 it was 1.4 s, checkpoint-cost), but still three
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
- test_scale_store_compacts_into_a_chain from the fixture on 5e15ad4c:
  see "Scale test" below.

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
