# pack-chain-cut: the chain program's between-links cut, 2026-09-26

Lane pack-chain-cut (Opus 5.5), a join-defect fix lane launched by deputy 3;
brief build/coordinator/queue/done/w4-pack-chain-cut.txt. Retires PKT-459;
the remainder is PKT-460. PRF-085 gains two keystones. The record is this
new file; bounds-p5-2026-09-25.md's Join section points here.

## The defect

`python3 -m unittest tests.test_native_cut_map` failed at dev fac2c417:
"native compaction cuts with no model program cut: pack-chain-link". The
stop hook `(fnn-checkpoint-test-stop "pack-chain-link")` in
host/native/checkpoint.lisp `fnn-pack-extend-chain` (from e4c693cb) was a
process-death cut that no model program named, so no crash theorem covered
it.

## The coordinate (the cut named, not moved)

In `fnn-pack-extend-chain`'s loop each link is: `(funcall admit ...)` (after
the first link), `fnn-pack-publish-generation` (the fn-jpub publication, its
candidate-* cuts), `fnn-pack-select` (the marker replacement; it returns
only on :durable, after the selection-directory cut), then the hook. Between
`fnn-pack-select` and the hook the host makes no call; after it, it only
recomputes the chain's coverage in memory (`fn-store-checkpoint-chain-coverage`)
before the next admit. So the cut is after link N's publish and select and
before link N+1's admit, as the brief expected; the model cut is placed
there. The host is unchanged (no diff under host/).

## The model (books/checkpoint-pack-chain.lisp, and why that book)

`*fn-cverb-pack-steps*` lives in books/store-compact-verb.lisp, which
includes checkpoint-pack-chain and only decides. The walk (`fn-ccc-walk`),
the publication crash keystone and `fn-ccc-chain-reconstructs-the-history`
are in checkpoint-pack-chain, and several of the lemmas the new proofs use
are local there, so the chain program goes in that book.

- `fn-ccc-chain-program links`: per link, oldest first,
  `(list :publish e)`, `(list :select generation)`, `(list :cut "pack-chain-link")`.
  A publication and a selection are one step each here; their inner cuts
  are `fn-ccc-publication-crash-walks-old-or-new-chain`'s.
- `fn-ccc-chain-step`, `fn-ccc-chain-run`: the state is (FILES . MARKER),
  FILES the generation alist the walk reads; element K of the run is the
  state a death right after step K leaves; a :cut changes nothing.
- Lemma `fn-ccc-chain-cut-state-is-previous-state` (the byte-store-k0 shape
  of `fn-bs-k0c-cut-pair-is-previous-pair`): the state at a :cut step is the
  state of the step before it.
- Lemma `fn-ccc-chain-run-at-link-cut`: the state at the (J+1)th cut is the
  files with links 1..J+1 published and the marker naming link J+1.

Keystones (PRF-085 events):

    fn-ccc-chain-link-cut-walks-the-extended-chain
      run   = (fn-ccc-chain-run (cons files old) (fn-ccc-chain-program links))
      image = (nth (+ -1 (* 3 n)) run)            ; the Nth pack-chain-link cut
      old-chain = (if old (fn-ccc-walk files old fuel max) nil)
      (posp n), (<= n (len links)), (natp fuel), old-chain /= :bad,
      (fn-ccc-entry-triplesp (take n links)),
      (fn-ccc-new-links-okp (revappend (take n links) nil) old max),
      (no-duplicatesp-equal (fn-ccc-entries-generations (revappend (take n links) old-chain)))
      =>  image = (nth (+ -2 (* 3 n)) run)        ; the selection's state
          (cdr image) = generation of link N
          (fn-ccc-walk (car image) (cdr image) (+ n fuel) max)
            = (revappend (take n links) old-chain) ; links N..1 on the old chain

    fn-ccc-chain-link-cut-reopens-to-the-history
      the same cut hypotheses, and fn-ccc-chain-reconstructs-the-history's
      hypotheses over chain = (revappend (take n links) old-chain) (its
      decoded entries links-okp, their events a prefix of H, H a true list,
      M <= the chain's boundary, the observation contiguous from M and
      matching H, M + |observed| = |H|, the suffix valid under FRONTIER)
      =>  (fn-ccc-observe-chain (fn-ccc-walk (car image) (cdr image) (+ n fuel) max)
                                observed frontier max) = (:ok H frontier)

The second cites `fn-ccc-chain-reconstructs-the-history` in its :use (no
restatement: its hypotheses are over the chain the host holds, and the walk
equality discharges the step to the image). `fn-ccc-new-links-okp` is the
order: each link's walk step decodes and names the next-older link (the old
chain's head, or none with lower 0) with a nonzero lower. The distinct
generations are what `fn-store-checkpoint-pack-next-generation` gives.

The per-link crash keystone bounds-p5 left under PKT-197 (superseded by
PKT-168 (1) to (3)): this is the K0 relation at the chain's own cut, which
PKT-168 (3) said did not exist; the composition of the publication crash
keystone with `fn-cpp-crash-selects-old-authority-or-complete-candidate`
(the other half of (3)) is not done here (PKT-460 (2)).

## The assurance chain

native entry (`operator CONFIG store compact`, `checkpoint pack STORE
select`) -> `fnn-compact-steps` :pack arm / `fnn-pack-publish` ->
`fnn-pack-extend-chain` (publish, select, hook) -> model
`fn-ccc-chain-program` (the tie: tests/campaign/native_cuts.py
`verify_compact_entries`) -> `fn-ccc-chain-link-cut-walks-the-extended-chain`
-> the reopen: host/native/checkpoint.lisp `fnn-pack-walk` (calls
`fn-store-checkpoint-chain-step` = `fn-ccc-entry-step`, one step of
`fn-ccc-walk`) and `fnn-pack-recover-records` (calls
`fn-store-checkpoint-chain-observe` = `fn-ccc-observe-chain`,
host/checkpoint-host.lisp) -> `fn-ccc-chain-link-cut-reopens-to-the-history`
-> the native kill below. The relation is established by the run from the
state before the compaction and preserved by each :publish/:select; the cut
preserves it by being the identity.

## The checker (tests/campaign/native_cuts.py)

CHECKPOINT_CUTS gains `NativeCut("pack-chain-link", "fn-ccc-chain-program",
"present", book="checkpoint-pack-chain.lisp")`. `verify_compact_entries`
now also asserts: `fnn-pack-extend-chain` admits, publishes, selects and
stops at pack-chain-link in that order; `fn-ccc-chain-program`'s cuts are
exactly (pack-chain-link) and its steps are :publish, :select, then the cut;
and no `fnn-` call lies between `fnn-pack-select` and the hook. Checked by
mutation (in-memory source edits): a host call between select and hook, the
hook before select, the hook dropped, and an extra unmodelled hook each
fail; the real source passes. Nothing was loosened.
tools/native_program_check.py does not check the pack programs, so it has no
tie to add.

## Teeth (tests/acl2/checkpoint-pack-chain-tests.lisp)

- The program for links A (generation 0) and B (1) is exactly
  publish, select, cut, publish, select, cut.
- Reachable witness at the second cut (N = 2, FUEL 0, no old chain): the
  complete antecedent of both keystones (with the full observation from 0),
  then the image equals the selection's state, the marker is 1, the walk is
  the two-link chain, and the reopen answers the five-event history. And at
  the first cut: link A alone.
- Hypothesis removals, each asserting the retained hypotheses, the failure of
  the omitted one, and the failure of the conclusion (`must-fail` plus an
  `assert-event` of its negation): the order (B then A: the walk is A alone;
  and with every covered file reclaimed the reopen answers A's three
  records, `(:ok (take 3 H) 6)` (checked in the REPL), not the history); distinct generations (B under A's 0: the walk loops out
  of fuel); a readable chain below (B on a selected generation with no file);
  the host's triples (a four-element entry). Not toothed: POSP N,
  N <= (LEN LINKS), NATP FUEL.

## Certification

- REPL on persvati (`~/fn-gates/pack-chain-cut-repl`, session pcc) first: the
  book's new events and the test book's forms, all admitted.
- Farm: persvati run-20260926T114113Z-6464, `--affected-by
  books/checkpoint-pack-chain.lisp`, 2 jobs, 300 s, w25, at 1664fc13:
  passed, 6 certified, 0 failed, 170 from the cache; manifest
  planning/evidence/manifests/certify-20260926T114206Z-1216102.json.
  checkpoint-pack-chain 5.28 s (5.02 s before), store-reclaim-pack 4.98 s,
  store-compact-verb-tests 2.27 s, store-compact-verb 2.12 s,
  store-reclaim-pack-tests 1.82 s, checkpoint-pack-chain-tests 1.07 s. No
  book over 10 s.
- `python3 -m unittest tests.test_native_cut_map
  tests.test_native_crash_correspondence`: 11 tests OK on the laptop.
- `make check-lane`: green. reach_check first flagged
  `fn-ccc-chain-cut-state-is-previous-state` (its subject `fn-ccc-chain-run`
  has no host caller); it is a lemma the keystones are built on, so it is
  not a registry event, and no baseline was edited.

## Native (hbox)

`tools/hbox_native.sh --label link1 1664fc13
tests.test_native_pack_chain.NativePackChainTests.test_pack_chain_link_cut_leaves_exactly_the_selected_links`
(scratch /tank/fn/scratch/pack-chain-cut/native-link1; the changed books
certified there, developer image built clean: no ACL2 error in
image-developer.log or native-build-developer.log). **OK, 1 test in 817 s.**
The fixture is the module's CUT_N store (4,500 two-KiB articles, three or
more links), never the 20,000-record fixture. From both entries
(`operator CONFIG store compact`, `checkpoint pack STORE select`), killed at
pack-chain-link occurrence 1 and 2: `status` shows exactly N links with
0 < boundary < 4,500 (the same boundary from both entries, and b1 < b2),
generations equal to the uncut chain's oldest N, newest first (the marker
names link N); the N pack files byte-identical to the uncut compaction's;
the transaction files byte-identical to before the compaction; `store
recover` reports transactions=4500 articles=4500; the same entry then
completes to the uncut chain (links, boundary 4,500, pack files byte for
byte) and recovers the same history.

SHA-256 (native-link1/SHA256SUMS):
- fn-host-developer e44026d5dacd8258f23f0672334ec88fe568ef9fd6748545f519dbcecd654304
- fn-host-developer.core cdd4147298f03a4dd37cdc9ab011d8153c0aa5e5ecd7453f366a71b28d617028
- test log a92b069fe91ffbc0f7a4dbfbeabf700be6d040c15498a7977f57da0f229e4239
- image-developer.log ce56d7f140170fe4c81e867e3e996e3433406f538708ddd59783f16874c214f6
- native-build-developer.log 0470e2ca0debbb5a1159eac21ef561db2e2faac12a3f7c5756dc35842890a596
- certify.log a7e9f0b6b783c10d0fbf0c8bdd855712cb6c0a153f2978066ec9103ce8eb7b34

The module's other cases (the seven-cut publication campaign, EIO, reclaim
and retire) were not rerun: the host did not change, and the looser
pack-chain-link rows of `test_every_chain_publication_cut_from_both_entries`
are subsumed by this exact case.

## What is not done (PKT-460)

1. The reopen keystone takes `fn-ccc-chain-reconstructs-the-history`'s
   hypotheses over the host's N-link chain instead of deriving them from the
   N captures (`fn-ccc-capture-extends-the-chain` per link needs the link
   codec round trip, PKT-168 (2)).
2. The chain program's :publish and :select are single steps; their inner
   cuts still rest on `fn-ccc-publication-crash-walks-old-or-new-chain`
   under the pack program's two facts (PKT-168 (3)'s composition half).
3. Finding: CHECKPOINT_CUTS names `fn-cpp-publication-step`, which is no
   defun in books/, and `verify_checkpoint_cut_map` does not check the
   phase-machine rows against a model program.
4. tests/campaign/native_operator_campaign.py iterates CHECKPOINT_CUTS, so
   it now runs a pack-chain-link row through both entries; that campaign
   was not run.
