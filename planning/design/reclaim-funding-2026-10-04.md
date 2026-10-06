# Decision: where a live reclaim pass's second state is funded from (2026-10-04)

Lane reclaim-funding (Opus), from S152 (`build/coordinator/lanedumps/s152.md`). ember, 10-04: "seems fine
to do C but i'm slightly wary … i don't mind doing something sophisticated." Code coordinates are at
`origin/integrate/20261004` @ `355b49b56`.

## 1. The problem, with coordinates

A live `store reclaim --recorded` (`host/native/owner.lisp` `fnn-owner-reclaim-pass`) reserves its memory
in the run's credit ledger before it captures (`host/owner-host.lisp` `fn-owner-orcp-capture` →
`books/owner-reclaim-pass.lisp` `fn-orcp-reserve`). Two facts make that reservation unfundable:

- **The estimate is an era-1 figure.** `fn-orcp-estimate h` = 16 × (6 − 2) × h: the offline compaction
  verbs' list copies of the history (`books/heap-figure.lisp` `*fn-heap-compaction-history-copies*`), at
  sixteen octets a list octet. The live pass holds no list copy of the history.
- **The free credit is the users' pool.** `fn-mca-initial-funds-exactly-the-articles`: what the ledger
  leaves free is exactly `fn-heap-articles-octets` (≤ max(reserve, 64 MiB)). So the reclaim borrows from
  the articles in flight, and a pass is admitted only while 64 h ≤ the pool less the articles in flight:
  h ≤ 53,776 octets on the development preset, 1 MiB on the defaults, whatever H is. The S152 run
  (2,100 articles, h = 7,077,639) asked 452,968,896 and was refused `deferred-credit`, as was the same run
  at an explicit 64 MiB H.

The live pass landed after 6.6.0 (6.6.0 answers `offline-only`), so this is a missing feature, not a
deployed regression.

## 2. What the pass actually holds (read before choosing)

- **The walk is already streamed.** Lane reclaim (PRF-1315, `books/reclaim-chunked-walk.lisp`) walks the
  pinned P3 root three times in chunks of 1,024 rows and keeps no rewritten-row list. The brief's
  "stream the walk so the second state is bounded by a chunk" is done for the walk.
- **What is left is a whole second generation, and it is the swap's object.** Pass 3 accumulates the
  predicted held rows into the rebuilt capture (`fn-rcw-acc-step`); `fn-owner-orcp-rebuild` builds the
  rebuilt owner from it; a fresh `fn-cat` and a P3 history candidate are loaded over its records. The
  rows come from DECODING the history pages (`fnn-owner-history-root-at`), so they share nothing with the
  served rows; only the payload arena is shared (the pass interns its tombstones into the live arena in
  the swap quantum). The swap then replaces the served Store, catalog and history columns whole, under
  `readers = 0`. That second generation is O(N) records, by construction, until D41 stage 5 ("pages are
  the state; checkpoint = the dirty pages; snapshot = a root") makes a reclaim's new generation the pages
  it dirties. Nothing this wave can do makes it chunk-bounded. The tree already says so
  (`LANEDUMP.md`: "Fresh logical Store/catalog/history and node lists still allocate proportional
  copies").
- **Its size, in the figure's own model.** The served state of a store of USED charged octets, N records
  and M memberships is `fn-heap-store-state-octets` = arena(USED) + 48 N + 2 × 4,160 N + 8 USED + 640 M
  (`books/heap-store-figure.lisp`). The second generation is that state less the arena it shares:
  ≤ 8,368 N + 8 C, C = USED + 320 M the history budget's charged octets (`fn-sbud-record-octets`, what
  `fn-owner-record-octets` carries). The rebuild is the full open over in-memory rows
  (`fn-orcp-rebuild-is-the-full-open`), so it also builds the open's per-record transient, 2 × 1,024 N
  (`*fn-heap-open-record-octets*`), which covers the reclaim context the pass frees before the rebuild.
  One walk chunk of decoded rows is live beside it. And the reclaimed rows' tombstones (145 octets and the
  Path agent, `books/reclaim-tombstone.lisp`) are held as OCTET LISTS from the rewrite until the swap
  quantum seals them (`fn-orcs-payloads`, the checkpoint walk's sources): 2 × 16 × 145 = 4,640 a record,
  and 32 a Path-agent octet, which is a header octet the budget charges at least 8, so at most 4 a charged
  octet (finding 4 of the review, §10). So the demand at the captured shape is

      D(N, C) = 10,416 × (N + min(N, 1,024)) + 4,640 × N + 12 × C     (10,416 = 48 + 2·4,160 + 2·1,024)

  For S152: D(2,100, 7,077,639) = 127,215,252 octets, where the era-1 estimate asked 452,968,896. The
  tombstone term is a D27 defect in its own right (a byte vector would cost an octet an octet); it falls
  when the pass's payloads stop being lists. The pass's checkpoint
  capture and history image (pass 2) are the publication's: the pass IS the publication in flight (its
  capture refuses another), so they are funded where every publication's are, not here.

## 3. The options

- **A. A term in the launcher's figure.** The figure holds D at the profile's bounds; the ledger holds it
  as a reserve. Live reclaim at every fill level. Cost: every node's figure grows.
- **B. Room in the store budget.** While a pass runs it holds its shape in the history gate (the
  capacity vector's maintenance component), so the figure's state term at (T, H) covers the served store
  and the pass together. No figure change.
- **C. The completion reserve.** E_completion (the open's transient) is idle after the open; the pass's
  rebuild is an open; the pass draws E_completion and repays it.
- **Streaming the second state to a chunk.** See §2: the walk is streamed; the generation is not
  streamable in this representation.

Precedents read for this:
- **LMDB / libmdbx.** Copy-on-write: a write transaction's second version is its dirty pages, bounded by
  the dirty-room limit and spilled past it; reuse of freed pages waits on the oldest reader (free by
  generation), and libmdbx ousts the laggard (handle-slow-readers). The second version is bounded because
  the state is pages. That is D41's target, not this tree.
- **KeyKOS.** The checkpoint area for two image generations is reserved at format time, before any user
  allocation; space banks give the system's own needs their own bank. The owner's maintenance is prepaid
  by construction (design-store-representation §2, §4 stage 7: "the two-generation checkpoint reserve").
- **PostgreSQL.** VACUUM's memory is a separately configured term of the capacity plan
  (`maintenance_work_mem`, `autovacuum_work_mem`, times `autovacuum_max_workers`), never drawn by queries'
  `work_mem`, and bounded independently of table size because VACUUM works in index passes when its
  dead-tuple store fills; autovacuum's cost budget (`vacuum_cost_limit`/`_delay`) bounds work per quantum.
  VACUUM FULL, which rewrites into a second copy, needs that copy's room and is the operational trap
  (it cannot run on the full disk it was meant to relieve). SQLite's VACUUM has the same shape;
  `incremental_vacuum(N)` is the bounded form.

The live pass is VACUUM FULL-shaped (a whole second copy) until D41. The precedents agree on two things:
maintenance memory is the system's own reserve, never drawn by user work; and a rewrite-into-a-copy must
have its copy's room reserved or it fails exactly when the store is full.

## 4. DECISION: combined — the owner's work reserve

(Lane reclaim-funding, 2026-10-04. Coordinator-level per `planning/design/README.md`; ember may
overturn. The outward-facing part — every figure grows by the amounts in §7 — is stated here and in the
READY so she sees it.)

1. **The demand is the figure's own model at the captured shape**, D(N, C) above
   (`fn-heap-reclaim-demand-octets`, `books/heap-store-figure.lisp`), replacing the era-1 64 h. One model:
   the figure and the pass read the same constants.
2. **The reserve is the owner's own term of the figure**, admitted at start by the launcher and at
   `init` by its sizing: the owner's work reserve = max(the open's transient, D at the profile's bounds),
   written as the open's terms plus `fn-heap-reclaim-excess-octets` = max(0, D(T, H) − open), BOTH at the
   observation the figure is taken at (the launcher's for a run: the store on disk), so every figure
   holds D(T, H) whatever the store was at start (an empty store's run holds all of it). The open and
   a live pass never coexist in a run (the run's ledger is installed after the open, `fnn-owner-install`
   then `fnn-mux-budget-install`; a recovery event stops the service and the open runs in the next
   process), so ONE reserve serves the owner's two mutually exclusive own operations: the KeyKOS
   two-generation reserve in its cons-structure form.
3. **The ledger holds it as the completion reserve, and only the pass draws it.** `fn-mca-initial`'s
   completion term becomes that owner reserve (at the bounds, as the ledger is today). The pass BORROWS
   its demand from it under `:reclaim` (`fn-mcr-borrow`: completion − x, the op + x, the funded total
   unchanged) and RETURNS it at the pass's end, whatever the end (`fn-mcr-return`). The articles' pool is
   never touched: a borrow leaves budget − total as it was, and no article transition changes completion.
   That is C's mechanism (the pass's rebuild is an open; the open's term is idle while serving), sized by
   A's guarantee.
4. **The guarantee:** every pass over a store the profile admits (N ≤ T, C ≤ H, which the history gate
   keeps) is funded, on every ledger the run reaches with no pass in flight. A refusal is by name and
   leaves the ledger unchanged; it is unreachable in composition for an admitted store.
5. **When D41 stage 5 lands**, the demand function is redefined as the dirty pages; the reserve shrinks with
   it; the keystones are stated over `fn-heap-reclaim-demand-octets`, so nothing else moves.

## 5. Why not the others

- **C alone loses on soundness and on its contract.** (a) The ledger's budget is the figure at the
  profile's bounds (`fn-mca-initial` → `fn-heap-figure-octets`, observed NIL), but the launcher sizes a
  `run`'s dynamic space with the open's term at the OBSERVED store (`fn-heap-operation-figure-octets :run
  … observed`). So E_completion in the ledger is at most partly real: on a node that started with a small
  store it is mostly octets the process was never given, and a pass drawing it would over-commit the
  dynamic space. (b) Made real (the ledger at the observed store), live reclaim would depend on how large
  the store was at the last restart. (c) At the bounds, E_completion is below D(T, H) on every T-heavy or
  H-heavy profile (friend rungs, scale: §7), so live reclaim would be refused at the fill where it is
  needed. The decision keeps C's insight — the open's term is the owner's and idle while serving — and
  sizes it so it always covers the pass.
- **B loses on D27 and on the full-store mandate.** A store more than about half full (in the model's
  units) could not reclaim live — VACUUM FULL's trap: the maintenance fails exactly when the store is
  full (`books/store-maintenance-reserve.lisp`: "A full store must always be able to finish or safely
  abandon its own maintenance"). And while a pass held room, POSTs would be refused on a store that is
  not full: a user-visible refusal from an internal operation. It also reopens the store-budget admission
  closure for a heap concern, a unit bridge the history gate does not otherwise need.
- **A as a sum loses to the max.** The open and the pass never coexist; reserving both pays twice. With
  the max, the development preset and every large-R profile (the S152 test profile among them) pay
  nothing at `init` (their open term already exceeds D(T, H)).
- **Streaming to a chunk is not available** (§2): the residual is the generation the swap installs.
- **A conditional default** (reserve only when the machine happens to hold it) was considered and
  dropped: `init` sizes the store to its budget, so on init-sized nodes the reserve would never fit, and
  live reclaim would come and go with a cgroup limit — the "branch that fails in operation for no
  meaningful reason" D27 forbids.

What would change my mind: a measured pass (`FN_RUN_RECLAIM_RSS=1`, 1k/10k) far below D (the rebuilt rows
sharing more than the model credits), which would lower the constants by measurement under matched
conditions; or an incremental, in-place rewrite of the reclaimed rows with an equivalence theorem to the
full open, which makes D O(reclaimed rows) — the D41 route, not this lane's.

## 6. Keystones (statements first)

**K1 — the pass is funded on every admitted store.** `books/owner-reclaim-pass.lisp`
`fn-orcp-profile-admitted-reclaim-is-funded`:

    (implies (and (fn-mca-pass-free-p credits profile)
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix c) (nfix (fn-bs-profile-max-history-octets profile))))
             (equal (car (fn-orcp-reserve credits n c)) :ok))

`fn-mca-pass-free-p`: the completion reserve is at least `fn-mca-owner-octets profile`, nothing is drawn
of it, and `:reclaim` holds nothing.
- Satisfiable: `fn-mca-initial` of the S152 profile (development, T 16,384, H 64 MiB) at
  (2,100, 7,077,639), and of the development preset at its bounds.
- Teeth: the old `fn-orcp-reserve` (a resize from the articles' pool at 64 h) refuses the S152 point
  (must-fail witness); without `fn-mca-pass-free-p` a ledger whose `:reclaim` already holds credit refuses
  (`:operation-already-admitted`); without C ≤ H, D(T, H + 1) past the reserve refuses (hypothesis
  removal at a ledger whose reserve is exactly D(T, H)).
- Premise inhabitation: **K2** — `fn-mca-initial-is-pass-free` (the run's ledger) and
  `fn-mca-served-steps-keep-pass-free` (every article transition the host calls — `fn-mca-read-span`,
  `-take`, `-untake`, `-seal`, `-batch-done`, `-settle`, `-stop`, `-close` — keeps it), and
  `fn-orcp-release-of-reserve-is-pass-free` (a pass's end restores it). N ≤ T and C ≤ H are the history
  gate's (`fn-cvec-roomp-is-within-the-profile`); the host passes the captured count and
  `fn-owner-record-octets`.

**K3 — the reserve never takes the users' room.** `fn-orcp-reserve-keeps-the-articles-room`: an admitted
reservation leaves budget − total unchanged and every other operation's credit unchanged; with
`fn-mcr-resize-and-move-keep-the-rest` (no article transition changes completion) the two pools are
disjoint. Teeth: the old reserve (a resize) lowers the room by the estimate (mutation witness).

**K4 — the figure holds every admitted store with a live pass over it.**
`books/heap-store-figure.lisp` `fn-heap-store-figure-holds-every-store-and-its-reclaim`: in a dynamic
space D ≥ the figure AT ANY OBSERVATION (so at the launcher's, which is the observed store's for a run),
every store the profile admits (USED + 320 M ≤ H, N ≤ T) with
the pass's demand D(N, USED + 320 M), the request in flight, the buffers, the articles, the image and the
collector's room at the trigger fits. Teeth: the figure without the excess term fails it at the small
preset's bounds (D(T, H) = 248 MB > its open term 130 MB). Premise inhabitation: the launcher's
reservation is the figure (PRF-198's keystones); the store shapes are the history gate's.

**K5 — the ledger transitions.** `books/memory-credits.lisp`: `fn-mcr-borrow-and-return-keep-funded`;
`fn-mcr-borrow-keeps-the-total`; `fn-mcr-borrow-refuses-exactly-past-the-reserve` (admitted iff the id
holds nothing and drawn + x ≤ completion); `fn-mcr-return-of-borrow` (the round trip restores completion
and ops). Teeth in `tests/acl2/memory-credits-tests.lisp`.

Restated, not weakened: `fn-mca-initial-funds-exactly-the-articles` keeps its first three conjuncts and its
fourth now says the completion reserve is `fn-mca-owner-octets` (the open's terms and the reclaim
excess); `fn-orcp-reserve-holds-the-estimate` holds the demand; `fn-orcp-reserve-refused-by-name` names
the borrow's reasons; `fn-orcp-release-frees-the-pass` stands.

## 7. Migration and cost

Books: `heap-store-figure` (demand, excess, base, K4), `heap-figure` (the small preset's empty-store
base value), `heap-breakdown` (a `:reclaim-reserve` term, the excess), `heap-reservation`
(`fn-heap-figure-octets-is-the-formula-by-definition`), `memory-credits` (K5), `owner-credits`
(`fn-mca-owner-octets`, K2), `owner-reclaim-pass` (K1, K3; `fn-orcp-estimate` deleted). Host:
`fn-owner-orcp-capture` passes the captured count and octets; the deferred line names the demand; the
walk's chunk is ACL2's (`*fn-heap-reclaim-chunk-rows*`). Tests: the teeth books above; the native walk
fixture loses its `--max-history-octets` workaround's comment and gains a capacity-free `init` case.

The cost, ACL2's definitions evaluated (heap octets before the collector's 8/7 and the threads):

| profile | open at bounds | D(T, H) | `init` / ledger excess | first run of an empty store |
|---|---|---|---|---|
| small floor (8 MiB, T 16,384) | 130.0 MB | 358.0 MB | +228.0 MB | +358.0 MB |
| friend 16 MiB (T 32,768) | 180.4 MB | 705.3 MB | +525.0 MB | +705.3 MB |
| friend 32 MiB (T 65,536) | 281.0 MB | 1,400.0 MB | +1,119.0 MB | +1,400.0 MB |
| friend 64 MiB (T 131,072) | 482.3 MB | 2,789.4 MB | +2,307.0 MB | +2,789.4 MB |
| development preset (T 128, 24 MiB) | 1,214.6 MB | 305.3 MB | 0 | +305.3 MB |
| S152 test (T 16,384, 64 MiB) | 1,331.7 MB | 1,062.6 MB | 0 | +1,062.6 MB |
| scale (T 4,096, 768 MiB) | 2,783.0 MB | 9,736.0 MB | +6,953.0 MB | +9,736.0 MB |

`init` promises the full store's run, so the `init` column is what sizing sees; no run's reservation
exceeds it (`fn-heap-store-figure-observed-is-at-most-unobserved` stands). The small preset's run stays
within 1,536 MiB for any core up to 512 MiB (`fn-heap-small-profile-run-fits-a-small-machine` re-proved
at the new value, 642,868,234 octets of base: 1,286 MiB at the 512 MiB core).

What `init` now does, ACL2's evaluation (`tests/acl2/heap-reservation-tests.lisp`, hbox's core), before
→ after:

| machine | rung before | rung after | reservation |
|---|---|---|---|
| 2 GiB (the friend's: 1,536 MB budget) | 16 MiB (T 32,768) | 8 MiB floor (T 16,384) | 1,367 → 1,265 MB |
| 3 GiB (2,304 MB budget) | 32 MiB (T 65,536) | 16 MiB (T 32,768) | 1,982 → 1,869 MB |
| hbox under MemoryMax=2G | 32 MiB | 16 MiB | |
| hbox, no limit | 64 MiB | 64 MiB | 3,209 → 5,409 MB |
| `init --profile scale` | scale | scale | 16,203 → 22,834 MB |

The small preset's full-store heap goes from 662 to 911 MB (its empty store's first run from 520 to 911
MB); the small profile still fits 1.5 GB (the F8 bar; 1,265 MB reserved in all). **This is the
outward-facing cost, and it is the one part of this decision escalated to ember (§11).** **Deployed nodes:** their profiles were sized by `init` against the old figure; before
the redeploy each node's `operator CONFIG status` reservation must be compared with its MemoryMax (the
integrator's packet; a node that no longer fits refuses to start by name, `machine-cannot-hold-profile`).

## 8. What F8's memory bar sees

F8 splits virtual reservation, accountable physical memory and working set
(`docs/resource-contract.md` M8). The reserve is VIRTUAL: dynamic-space size, untouched while no pass
runs, so the working set of a served node does not move, and the virtual figure grows by the §7 column.
During a pass the resident set rises by at most D(N, C) above the served working set (the model's
claim); the measurement that checks it is `FN_RUN_RECLAIM_RSS=1 tests.test_native_reclaim_walk` (1k,
10k), the F1-style evidence the decision's constants need, not a proof. The accountable-physical bar
(256 MiB) is unaffected outside a pass; a pass over a store of 10,000 articles of the S152 shape (about
3,370 charged octets each) is D = 566 MB of model, most of it the header term (12 C): the measurement
will say how much of that model is real.

## 9. Findings outside this decision

- **The ledger's budget is not the launcher's reservation.** `fn-mca-initial` is built from the figure
  at the bounds; a `run`'s dynamic space is the figure at the observed store. Nothing but the pass ever
  drew the completion term, and the pass now draws at most D(T, H), which both include; but the ledger's
  `fn-mca-initial-funds-exactly-the-articles` claim "the budget is the launcher's reservation" is true only
  for a store observed at its bounds. A ledger built from the dynamic space the run observes would close
  it (connection-budget already receives DYNAMIC).
- **The arena keeps every reclaimed handle until the forget is wired.** Each pass seals its tombstones as
  new handles and the old handles stay named (`reclaim-2026-10-04.md` L2, slice 7). In a served node the
  arena's RESIDENT payloads are the tombstones (`arena-forget-2026-10-03.md` §6: committed payloads are
  file extents), and the tombstones are charged to the history budget, so the state term holds them; what
  the missing forget costs is disk (the files never go quiet) and the extent entries, not the heap
  figure. (Corrected after the review's finding 5.)
- **The publication's history image** (`fnn-history-image-build`, an `fn-hrecs$c` of the whole history)
  is in the dynamic space for every publication, the pass's included; whether a figure term names it is
  the publication's question, not the reclaim's.

## 10. Advisory review

One review per `planning/how-we-work.md` (advisory, not a gate): Kimi (`kimi` 0.39.1, an agent file with
no tools, an empty working directory, no skills), 2026-10-04, over a 40 KB prompt of this file's first
draft and pasted excerpts (`owner-reclaim-pass`'s reservation, `memory-credits`' ledger, `owner-credits`'
initial ledger and keystone, `heap-store-figure`'s state/open/base, `heap-figure`'s per-action figure,
`owner-host`'s capture and budget install, the native pass abridged). No keys in argv. It completed.
Verbatim:

```text
1. **DISAGREE — the chosen design has the exact over-commit it rejects C for.** §5(a) rejects C because "on a node that started with a small store it is mostly octets the process was never given, and a pass drawing it would over-commit the dynamic space." But `fn-heap-operation-figure-octets` (heap-figure.lisp) sizes a `:run`'s dynamic space at the *observed* store, while the excess is computed at the bounds — §7's own arithmetic ("small floor … +118.4 MB" = 248.4 − 130.0, D(T,H) − open at bounds). For a run launched on an empty store, `fn-heap-open-octets-bound`/`fn-heap-open-records-bound` with observation `(0 . 0)` make the open term 0 (`fn-heap-store-open-octets` at ou=0, on=0 is 0), so the process gets excess + open(observed) = 118.4 MB of owner headroom. Once the store grows to the gate's limits, the pass draws D(T,H) = 248.4 MB — 130 MB the process was never given. §9's "the pass now draws at most D(T,H), which both include" is false for the `:run` figure. Fix: index the excess by observed, `max(0, D(T,H) − fn-heap-store-open-octets profile (open-octets-bound observed) (open-records-bound observed))`, or size `:run` at bounds.

  2. **DISAGREE — K4 rests on a wrong premise.** Its premise inhabitation says "the launcher's reservation is the figure (PRF-198's keystones)", and K4 quantifies over "a dynamic space D ≥ the figure". `fn-heap-operation-figure-octets` shows a `:run`'s reservation is the figure at the observed store, i.e. D = figure(observed) < figure(nil) for any store that grows after launch. The premise is uninhabited for exactly the runs in finding 1; K4 as stated proves nothing about them.

  3. **DISAGREE (too weak) — K1 proves ledger admission, not funding.** `fn-orcp-profile-admitted-reclaim-is-funded` concludes `(equal (car (fn-orcp-reserve credits n c)) :ok)` — a borrow against `fn-mcr-completion`. §4.4's "every pass over a store the profile admits … is funded, on every ledger the run reaches" equates the ledger's budget (`fn-heap-figure-octets profile core nursery`, at bounds, per `fn-mca-initial`) with the process's dynamic space. §9 finding 1 concedes these differ. The theorem is true and operationally vacuous for grown stores.

  4. **DISAGREE — D misses the retained seal payloads.** The host excerpt accumulates per-chunk payloads across the *whole* pass-3 walk — `(when (third r) (push (third r) payload-chunks))`, then `(setq seal-payloads … (dolist (c payload-chunks …)))` before the rebuild. One payload per rewritten row is live simultaneously: O(N) payloads, not "one walk chunk of decoded rows … live beside it" (§2), which is all the `min(N, 1,024)` term buys. The 8C term is `*fn-heap-charge-heap-octets* × used` (header charges with the collector's copy), not payload storage. If those payloads are arena-resident at seal (`fn-orcs-seal-is-the-intern`), see finding 5; otherwise D is not an upper bound.

  5. **DISAGREE — D drops the arena while the arena grows.** §2: the second generation is the state "less the arena it shares", i.e. ≤ 8,368 N + 8 C with no arena term. But §9 finding 2: "Each pass interns its tombstones as new handles and the old payloads stay … arena residency can exceed 2 H", and the excerpt interns during pass 3, before the swap. `fn-heap-store-state-octets` counts the arena at the budget's charged history, "which a reclaim lowers" (§9). During and after the pass, actual arena > modelled arena, and neither D nor the state term covers the delta. K4 is unprovable as stated until the forget lands or an arena-growth term is added.

  6. **DISAGREE — capture and rebuilt owner coexist; D funds one generation.** The excerpt binds `e` (`fn-rcw-acc-finish`), then `rebuilt` (`fn-owner-orcp-rebuild`), then uses `(fnn-core 'fn-sco-records e)` *after* the rebuild to build `history-candidate` and load `cat`. So the accumulated capture, the rebuilt owner, a fresh `fn-cat`, and the history candidate are live at once, beside the served generation. "(no copy)" covers record identity, not the two O(N) containers. D = 8,368 N (one generation; the ×2 in `2 * 4,160 N` is the collector's copy, not a second structure) + 2×1,024 N. If capture and rebuilt records are distinct 4,160-class structures, peak is ~two generations and 10,416 does not dominate it.

  7. **MISSING — no term for the catalog and history columns anywhere in D's basis.** §2 says the swap "replaces the served Store, catalog and history columns whole", yet `fn-heap-store-state-octets` — the sole source of D's constants — is arena + handles + records + memberships. No excerpt shows a `fn-cat` or P3-node octet term. D inherits the omission for the second generation of `cat` and `history-candidate` ("a fresh `fn-cat` and a P3 history candidate"). If those are O(N) with their own constants, nothing shown establishes 10,416 N bounds them.

  8. **DISAGREE — the pass-2 history image is unfunded, not "funded where every publication's are."** §2 defers "the pass's checkpoint capture and history image (pass 2)" to the publication's funding; §9 finding 3 states no figure term names the publication's `fn-hrecs$c` of the whole history. During the pass the image exists in the dynamic space; K4 claims the figure holds the pass; nothing funds the image. Deferring the question does not remove the octets.

  9. **AGREE, narrowly — open and pass are process-disjoint, so one max() reserve is legitimate as *virtual* accounting.** The owner-host excerpt ("Once per run, after recovery and before listen") supports non-coexistence, and the pass frees the context and unpins before rebuilding (`fn-owner-orc-ctx-free`, `fnn-owner-history-root-unpin` precede `fn-owner-orcp-rebuild`), so the open transient and the rebuild peak also don't stack. But as a *residency* claim it additionally needs the open's transient collected before the pass's peak; nothing cited establishes GC timing — only §8's "the reserve is VIRTUAL". The decision should say the max() is sound *because* the reserve is virtual, and that §5's "reserving both pays twice" is a virtual-space argument only.

  10. **DISAGREE — C is rejected for reasons that equally convict the decision.** §5(a) (over-commit at observed) is unresolved per finding 1; §5(b) ("live reclaim would depend on how large the store was at the last restart") is now true of the whole design, since a `:run`'s pass headroom is excess + open(observed at launch). Only §5(c) (E_completion < D(T,H) on T/H-heavy profiles) is a genuine differential. "Sizes it so it always covers the pass" sizes the ledger, not the process.

  11. **AGREE — B's rejection is well-grounded.** `books/store-maintenance-reserve.lisp`'s "A full store must always be able to finish or safely abandon its own maintenance" plus the user-visible POST refusal on a non-full store are the right D27 grounds, and §7's table confirms the maintenance component would exceed half the figure on the friend rungs.

  12. **AGREE — the sum is correctly rejected, but the reason is narrower than stated.** "The open and the pass never coexist; reserving both pays twice" holds only under finding 9's process-disjointness. Note the max() is also what *hides* the observed-vs-bounds gap (finding 1): taking the max at the bounds while the launcher pays open at observed is where the 130 MB went.

  13. **MISSING — K2 does not inhabit K1's "every ledger the run reaches."** §4.4's guarantee is over every ledger; K2 establishes pass-free only for `fn-mca-initial` and served transitions. `fn-mca-default` has completion 0 — a control-plane reclaim before `fnn-mux-budget-install` draws against a ledger no keystone covers. And "with no pass in flight" (§4.4) is an English side-condition, not a theorem antecedent: during a borrow, `fn-mca-pass-free-p` is false by definition, so K1's premises simply don't hold mid-pass — fine for exclusion, but it means the stated guarantee is conditional on a fact no theorem names.

  14. **MISSING — pass-3 arena writes race served POSTs.** The `readers = 0` discipline (§2) governs the swap, not the walk: pass 3 interns seal payloads into the *live* arena while POSTs are served and themselves intern payloads. Presumably `fnn-core` serializes this, but no keystone states the pass's arena mutations are atomic with served seals, and D's "the payload arena is shared" assumption needs the two write streams to commute without duplication or lost-count drift (cf. the excerpt's own "The raw (K . SUM) cache may lag the last committed batch").

  15. **MISSING — the collector's trigger is static; the pass raises the live set by D between collections.** K4 names "the collector's room at the trigger", and `fn-heap-with-nursery` scales the figure by 8/7. But the walk allocates ~D of short-lived garbage per chunk on top of serving; peak residency is 8/7 × (live including D), which is only safe if the trigger's premise (live ≤ base) holds mid-pass. No keystone ties the collection trigger to the pass-in-flight live set; on a figure-edge profile the pass can force a collection with the heap already at the trigger.

  16. **AGREE — the operational guards are right, but they undercut K4's status.** §7's `machine-cannot-hold-profile` redeploy check and §8's `FN_RUN_RECLAIM_RSS=1` measurement plan are correct. But "What would change my mind: a measured pass … far below D" concedes the constants are unmeasured, while §8 states "the resident set rises by at most D(N, C)" as "the model's claim" inside K4's fit guarantee. Until the 1k/10k evidence exists — and given findings 4–7 that D omits structures entirely — K4 is a hypothesis wearing a keystone's name, and the advisory review (§10, still pending) should not be the last stop before the READY.
```

Fact-check and disposition (each against the tree at the lane's head):

| # | verdict | what was done |
|---|---|---|
| 1, 2, 10, 12 | REBUTTED, and the draft's wording fixed | The excess is computed at the SAME observation as the open's term (`fn-heap-store-base-octets` passes `fn-heap-open-octets-bound profile observed` to both), so a run's figure holds max(open(observed), D(T, H)) ≥ D(T, H): an empty store's run holds all 358 MB on the small preset (ACL2: base at `'(0 . 0)` = base at NIL = 642,868,234 + core). The draft's §4 said "max(0, D(T, H) − open)" without saying at which observation; §4.2 now does. K4 is stated over ANY observation (`observed` is free in `fn-heap-store-figure-holds-every-store-and-its-reclaim`), so its premise is the launcher's figure. C's restart dependence does not carry over. |
| 3 | AGREED in part | K1 is ledger admission; the funding claim is K1 with K4 (the pass draws at most D(T, H), which every launcher figure holds). Both are now said together (K1's comment in the book, §4). The ledger's budget/launcher mismatch stays a finding (§9) — it no longer matters to the pass, whose draw is bounded below every figure. |
| 4 | AGREED, folded | The seal payloads are octet lists held from the rewrite to the swap; D gained 4,640 a record and 4 a charged octet (§2). This raised every reserve by about 40 %. |
| 5 | REBUTTED, finding corrected | Pass 3 PREDICTS; the tombstones are sealed only in the swap quantum (`books/owner-reclaim-seal.lisp`, `fn-orcs-seal-is-the-intern`). Resident payloads in a served node are tombstones, charged to the budget; §9's arena finding was wrong about the heap and now says disk. |
| 6 | REBUTTED | The capture and the rebuilt owner are the open's own pair (the open builds E then installs from it); the figure's open model already charges that pair as the per-record build, 2 × 1,024 a record, which D includes. |
| 7 | REBUTTED | The record's fixed part (`*fn-heap-record-fixed-octets*`, 4,096) is measured over "the held row's spine and facts, the catalog's and the history columns' entries, the handle's extent and the retention carry" (`books/heap-store-figure.lisp` header); the excerpt omitted that comment. |
| 8 | AGREED as a finding, not this decision's | The history image (`fn-hrecs$c`) of every publication is unnamed by any figure term (§9). The pass adds nothing a periodic publication does not; K4 is scoped to the model's terms and says so. |
| 9 | AGREED | The max is sound because the reserve is dynamic-space size and the open's transient is garbage before any pass can start; §4.2 says the open and the pass never coexist in a run. |
| 11 | AGREED | — |
| 13 | AGREED, stated | Before the budget is installed the ledger is `fn-mca-default` (completion 0): a reclaim then is refused by name (`:completion-reserve-exhausted`), which is the honest answer. A second pass is refused `:in-flight` before it reserves (S038). K1's premise, pass-free, is that composition. |
| 14 | REBUTTED | The pass writes the arena only in the swap quantum, under the owner mutex, after `fn-orcs-seal-word` checked the arena's count is the predicted base. |
| 15 | REBUTTED | K4's need includes the pass's live set AND 2 × the trigger the host sets in D; the collector's room is in the conclusion, not assumed. |
| 16 | AGREED | The constants are the figure's measured model; K4 is a theorem over them, as PRF-198 is. The 1k/10k RSS measurement (`FN_RUN_RECLAIM_RSS=1`) is owed and named in the READY. |

## 11. Escalated to ember (outward-facing; one decision)

**The default.** The decision funds live reclaim on every node: every figure grows by the reclaim's
excess over the open's transient (§7), and `init` on a small machine now picks one rung lower (a 2 GiB
machine: the 8 MiB floor where it got 16 MiB; 3 GiB: 16 MiB where it got 32). Deployed nodes must be
checked against their MemoryMax before the redeploy. The two positions:
- **as built** — guaranteed live reclaim at every fill level on every node (D27; the full-store
  maintenance mandate); cost: the table above, paid by capacity on small machines;
- **opt-in** — the same mechanism and keystones, the reserve term only when the operator's
  configuration asks for live reclaim (a `[resources]`-style key read by the launcher, as the output
  pool's is); without it a live `store reclaim --recorded` is refused by name (`deferred-credit`, as 6.6.0
  answered `offline-only`) and offline reclaim stays; cost: a configuration field (the native-config
  closure, held for batch R) and a node that must be told.
Either way the representation is what makes the price high (a second generation of ~10 KB a record);
D41 stage 5 lowers it for both.

**Decided: opt-in** (D53, coordinator ruling, ember-delegated, 2026-10-04; built on lane
reclaim-optin). The key is `[resources] reclaim_live = true` (native-config field 31, absent and
`false` the same configuration). Without it the figure is the store's alone: init's rungs and every
deployed node's figure are what they were before this decision (`fn-mca-figure-off-is-the-store-figure`,
`fn-rrv-without-the-opt-in-is-the-base-decision`), and a live `store reclaim` or `--recorded` is
refused by name, `offline-only` (not `deferred-credit`), before anything is recorded or reserved
(`fn-orcp-request-word-refuses-an-installing-pass-without-the-opt-in`; the capture's own check,
`fn-orcp-reserve-refused-without-the-opt-in`). With it the launcher extends the store decision
first (books/reclaim-reservation.lisp, before the cold and output allowances) and K4 becomes
`fn-heap-store-live-figure-holds-every-store-and-its-reclaim` over the live figure; the running
owner's budget holds the reserve (`fn-mca-figure-on-is-the-live-figure`). Small preset, production
core: the reserve grows the figure by 227,983,360 octets (the reserve 358,006,784 against the
open's 130,023,424; tests/acl2/owner-credits-tests.lisp). Init does not size for the key: a node
that adds it can be refused at start (`machine-cannot-hold-reclaim-reserve`), by name.
