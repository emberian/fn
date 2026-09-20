# Handoff: w9/reconfig (packets R5 onward of specs/reconfiguration.md)

Lane `w9/reconfig`, branched at `52eb0db` (dev), worktree
`build/lanes/w9-reconfig`. Commits `7f59156` (R5 definitions), `b08edbe`
(R6 host and CLI), `c914216` (R5 certification, registries, spec §8).
The board carries one CHANGE per milestone, the R5 wire ASK, and the R7 and
R8 proposals.

## What landed, and what it is worth

**`books/config-stream.lisp` (`fn-cstr-`) — CERTIFIED.** ACL2 8.7 on
persvati; evidence `build/acl2/certify-20260920T181223Z-1585622` (book) and
`certify-20260920T181256Z-1591093` (`tests/acl2/config-stream-tests`).
`python3 tools/ledger.py --write` and `make check` pass.

The decision it carries, stated before its proofs: **the two-kind on-disk
interleaving is a sequence field, not a file format.** The layout stays two
directories; the stream is one, because every record of either kind carries
its position in the unified stream in its own sequence field, and recovery
merges the two files by that field. Keystones:

- `fn-cstr-merge-keeps-every-config-record`, `-keeps-every-article-record` —
  the merge drops nothing and invents nothing. Independent enumeration: the
  left walks the merge, the right walks the input file.
- `fn-cstr-merge-is-sequence-ordered` — two sorted files merge to one sorted
  stream, so the layout split loses no ordering information.
- `fn-cstr-ok-merged-replay-ends-in-a-configured-node` — an `:ok` merged
  replay ends in `fn-cnode-statep`, which carries `reserved <= capacity`.
  This is the statement a configuration-only replay cannot make.
- `fn-cstr-created-group-is-served-exactly-from-its-generation` and
  `-retired-group-is-served-exactly-below-its-generation` — both directions.
  A connection pinned below the creating generation must NOT see the group;
  that half is what a "creation is monotone" statement would drop.

`books/node-config` is untouched; `fn-cnode-replay-loop` and its fold
keystone are unchanged, and the merge feeds that loop.

**The separating witness is the whole argument** (`tests/acl2/config-stream-tests.lisp`):
one `(:set-capacity 1)` over a history whose two articles hold a reservation
total of 2. The configuration-only replay the host runs today reports `:ok`
with capacity 1 and is about to replay two articles that need 2; the merged
replay reports `:config-refusal` at that record. Controls in the same book: a
raise and a decrease to exactly the reservation total are both admitted, so
the merged replay is not simply refusing every decrease.

**`books/owner-config.lisp` (`fn-ocfg-`) — WRITTEN, NOT CERTIFIED.** The
owner event `(:reconfigure id deltas)` and the per-connection pin.
`fn-ocfg-make (owner config pins staged)` layers over `books/owner` exactly
as `books/node-config` layers over `books/node`; `books/owner.lisp` and
`books/owner-invariants.lisp` are untouched. The reconfiguration takes the
owner's single pending-transaction slot, so a post and a reconfiguration
cannot straddle a generation bump; `fn-ocfg-reconfig-refusal` is a named
reason and never `nil`. Keystones stated:
`fn-ocfg-reconfiguration-never-changes-what-an-open-connection-serves`,
`fn-ocfg-pin-is-stable-without-advance`,
`fn-ocfg-open-pins-the-live-configuration`,
`fn-ocfg-advance-observes-the-live-configuration`,
`fn-ocfg-list-active-lists-the-pinned-served-table`.

**No event is claimed for it.** `books/owner` has no certificate on any box —
it is the milestone's own current task — so nothing that includes it can
certify. A closure run for `books/owner` and `books/owner-invariants` was
submitted to persvati at the start of this lane
(`run-20260920T175315Z-343c`, remote root `/home/ember/fn-lanes/w9-reconfig`,
`installed 163, uncached 58`). **It failed, and not for a proof reason.**
`books/served` died in 0.02 s at `(INCLUDE-BOOK "nntp-post")` with "that book
is not certified": with `--jobs 8` the runner started `served` before
`books/nntp-post` had finished, and `books/owner` was blocked behind it. So
the evidence does NOT say `books/served` or `books/owner` fails to certify --
only that this parallel run mis-ordered them. Whoever picks this up: retry
serially, `python3 tools/farm.py submit persvati --jobs 1 --remote-root
/home/ember/fn-lanes/w9-reconfig --closure books/owner books/owner-invariants
books/owner-config`, then `wait` with the same `--remote-root` (omitting it
silently polls the laptop's own path and reports "no runs"). Parens in
`books/owner-config.lisp` balance and every symbol it names resolves to a
`defun` under `books/`; nothing else about it has been checked by a prover.

**The worktree `build/lanes/w9-reconfig` was removed under this lane** by the
cycle's worktree sweep while it was still working; every commit is on branch
`w9/reconfig` (`dd8ac86`) and nothing was lost, but the stray directory left
behind holds this lane's certification evidence under `build/acl2/`.

**R6, capacity.** `fn store capacity <n>` and `run_store.py capacity <n>`.
`fn-store-cfg-reconfigure (kind name-octets n monotonic wall state)` accepts
`:set-capacity`; the delta, the bound and the record are `books/config`'s,
admitted by the same `fn-cnode-record-acceptablep` replay applies against the
live node's reservation total. A decrease carries one extra gate before
anything becomes durable: the candidate configuration history is replayed
against the store's real article records in a second core
(`_candidate_history_opens`), and the record is refused if that store would
not open. Three outcomes distinct: refused 1, uncertain 3, accepted 0.
`*fn-store-capacity*` is out of `fn-store-sn-reset`, whose pre-open state now
has capacity 0 — §1.6's fail-closed floor. It survives only in
`host/checkpoint-host.lisp`, another lane's file.

## Deviations, each forced, each in the book header

1. The pin is a **table beside the owner**, not a ninth slot of
   `fn-own-conn-make` (design §2.2). The slot rewrites forty call sites in a
   file `w5/clock-seam` and `w9/peering-e2e` are editing this cycle.
   `fn-ocfg-statep` holds the table's domain equal to the open connections,
   which is what makes the pin a derived quantity rather than a writable one.
2. The board proposal's name `fn-own-conn-config` is **taken**: it is the
   posting configuration (`fn-inj-configp`) pinned at open. The
   reconfiguration pin is `fn-ocfg-conn-config`.
3. `fn-cstr-nondecreasingp` is *sorted* (every element at least every earlier
   one), not pairwise. Stronger, and the form the merge proof needs.
4. `fn-cstr-config-jrecs-is-fn-cnode-config-jrecs-by-definition` is
   `:rule-classes nil` and named for what it is. As a rewrite it turned every
   goal about this book's own arm into one about a withdrawn definition.

## Open, recorded rather than weakened (specs/reconfiguration.md §8)

- **The wire.** `LIST ACTIVE` on the served port still lists the allocation
  domain: `fn-nntp-dispatch` supplies `(fn-state-groups archive)` at
  `books/nntp-responses.lisp` 225, 308 and 319. `fn-ocfg-list-active` is
  therefore a sibling API, and the equating theorem is written down in the
  book where it would go and deliberately **not** stated. Fix: one
  served-table argument on `fn-served-conn`, `fn-served-dispatch` and
  `fn-nntp-dispatch`. ASK on the board.
- **Recovery.** `fn-own-reopen` replays the article history only, so the
  owner cannot state the recovered generation and §3.5's owner statement has
  no subject. Its store-level half is proved
  (`fn-cnode-recovered-generation-is-at-most-the-live-generation`,
  `fn-cstr-ok-merged-replay-ends-in-a-configured-node`).
- **The interleaving is in the model, not on disk.** The one host edit that
  changes that: `host/store-node-host.lisp:124` still numbers a configuration
  record by the previous generation; it must number it by the journal
  position, as `fn-ocfg-reconfig-record` does. Then `fn-cstr-replay` is
  usable at open and the capacity dry-run gate can be deleted.
- **R7, contact plans: not written.** The configuration value has no contact
  slot and neither does `fn-cfg-peerp`, and both owning books were being
  certified by other lanes. Exact shape on the board (two delta kinds into
  the peers slot under a `"contact"` slot label, a slot-aware
  `fn-cfg-rows-without-key`, and a reader book producing
  `fn-sched-contact`).
- **R8, propagation: the guarantee is proved, the path is not built.**
  `fn-cnode-article-transitions-never-change-config`
  (`books/node-config.lisp:331`) is exactly "a group creation on A becomes a
  configuration record on B only through B's own admissibility": no article
  or ingest transition moves `fn-cnode-config`. The proposal path is designed
  on the board and deliberately keeps `:proposed-group` **out** of the
  configuration value, because a proposal that were a delta would force that
  theorem to be reproved weaker. The two-node harness scenario is **not** in
  `tools/twonode_gate.py`: `fn group create` refuses while an owner is live,
  so the scenario needs `(:reconfigure ...)` wired into
  `host/owner-host.lisp` first — the R5 host step this lane did not take.
- **The Python suite was not run.** It needs a local ACL2 bridge and this
  lane runs no local ACL2 by its box rule.
  `tests/test_store_config.py::test_capacity_is_a_configuration_record_with_three_outcomes`
  is written and UNRUN: it is the first thing a successor should run
  (`python3 -m unittest tests.test_store_config`), and it is where a defect
  in the `capacity` command will surface. It checks that a raise moves the
  generation, that a capacity below the live reservation total is refused
  with the core's reason and writes nothing, and that an accepted value
  survives a reopen.

## Registries

`planning/proofs.json` gains PRF-027 (the stream) and PRF-028 (what a
generation serves), both `in-progress`, both citing keystones rather than
corollaries and carrying their covered scope in the statement; STO-004 and
NNT-006 gain the reciprocal links. No requirement status was advanced: the
only rows this lane could have advanced depend on `books/owner`.
