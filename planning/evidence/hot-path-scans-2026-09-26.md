# hot-path-scans, 2026-09-26: the BP contact's single-traversal selector; the byte-count walk measured and held

Lane `lane/hot-path-scans` from dev `8ca933b1`, brief
`build/coordinator/queue/w3-hot-path-scans.txt` (gpt-6 review 2026-09-26 §4).
Ids: PRF-139, PKT-324.

## What changed for a user

A BP contact's job selection (`fn-bpnj-contact-next`) now examines each job
once. With only the last of N jobs ready, one ask costs 2N+1 job visits instead
of about N²/2. POST admission is unchanged on dev. The byte-count work is held
at `7f615571`, reverted by `58cb4f23`, and §3 explains why.

## 1. Before rows (hbox, profiling twin of dev 8ca933b1; launcher 33aff870, core bf18e4f8; ZFS; default profile; rep_measure K=32, R=3; checkpoint skipped)

| point | POST alloc | POST (alloc batch, median) | OVER | STAT | load |
| --- | ---: | ---: | ---: | ---: | ---: |
| N=1,000 × 2 KiB | 2.38 MB | 217.8 ms | 0.76 ms | 0.11 ms | 215.6 s |
| N=10,000 × 2 KiB | 7.84 MB | 171.0 ms | 3.71 ms | 0.09 ms | 2,422.9 s |

These rows reproduce the wave-d baseline (2.3 → 7.7 MB, 0.62 → 3.65 ms). The
JSON files are in `hot-path-scans-2026-09-26/before-*.json`. On ZFS the POST
time is the durable publish, so these rows cannot resolve a CPU term.

**Allocation profile.** An sb-sprof `:alloc` profile covered 200 POSTs on a
freshly opened store (`hot-path-scans-2026-09-26/alloc.lisp`, `allocprof.py`,
`alloc-before-n10000-flat.txt`). The table gives samples at about 32 KB each,
at N=1,000 and N=10,000:

| term | N=1,000 | N=10,000 | where |
| --- | ---: | ---: | --- |
| `fn-sbud-record-octets` (byte count) | 2,555 | 20,754 | `host/owner-host.lisp` `fn-owner-record-octets` |
| `fn-index-build` / `fn-gidx-build-entries` | 2,294 | 19,885 | `books/owner.lisp:916` `fn-own-refresh` → `(fn-gidx-build visible)` |

**Byte count.** The cache global is nil at open, so the first verdict after
open re-encodes the whole history: about 66 KB per 2 KiB record, about 660 MB
at N=10,000. Every later verdict walks `len` and `nthcdr` of the history. Those
pointer walks allocate nothing, so the growth in the steady-state POST
allocation between the two rows is not the byte count's.

**Group index.** The per-POST growth comes mainly from `fn-own-refresh`
rebuilding the whole group-bucket index on every refresh (about 3.2 MB per POST
at N=10,000 against 0.37 MB at N=1,000), plus the O(N) `append`s in §4. I did
not profile the commit-regression lane's octet-list pass through `fnn-core`.

## 2. PRF-139 part 2: the selector (commit 47695837)

`books/bp-node-job-offer.lisp`: `fn-bpnj-contact-next` reads the gate first,
then calls `fn-bpnj-scan`. The scan goes through the job list once, examines
each job where it stands, and remembers the first held candidate it meets. It
answers a job only if that job is the entry the start's lookup reads
(`fn-bpnj-own-entryp`).

Host lines: `host/native/bp-service.lisp` `fnn-bpc-drive-contact` (the
`fnn-core 'fn-bpnj-contact-next` call) and `host/native/bp-node.lisp`
`fnn-bpnode-send-receipts`.

- **KEYSTONE `fn-bpnj-contact-next-is-the-two-scan-selection`** (no hypothesis):
  on every state the answer equals the former body over `fn-bpnj-select` and
  `fn-bpnj-held`. The PRF-120 theorems keep their statements; only their hints
  changed, to cite this equation (`fn-bpnj-contact-offer-starts-the-ready-job`,
  `fn-bpnj-contact-next-offer-shape`,
  `fn-bpnj-contact-offers-while-a-ready-job-remains`).
- **`fn-bpnj-scan-finds-the-selected-job`**: if `jobs = pre ++ rest` and `pre`
  selects nothing, the scan's ready job over `rest` is `fn-bpnj-select`'s.
- **`fn-bpnj-scan-finds-the-held-job`**: if `jobs = pre ++ rest`, nothing in
  `jobs` is ready, and `held` is `pre`'s held job, the scan's held job is
  `(or held (fn-bpnj-held rest ...))`.
- **`fn-bpnj-unique-keys-make-every-job-its-own-entry`**: under
  `fn-bpn-job-listp`, every member is its own entry. This is the uniqueness
  invariant of the jobs field that `fn-bpn-machine-statep` carries. It is why
  the one confirming lookup succeeds at once, so a selection is one traversal
  plus the lookup that `fn-bpnj-start-job` performs anyway.
- **Why a confirmation is used instead of a uniqueness hypothesis.** The
  equation is unconditional, so no PRF-120 statement needed a new hypothesis.

**Teeth** (`tests/acl2/bp-node-job-offer-tests.lisp`, 38 assertions pass):
- Reachable witnesses for each answer kind: `:offer`, `:held`, `:close`.
- One removal witness per hypothesis of each theorem. The removal witnesses for
  the list-shape hypotheses use lists with a repeated key, labelled
  corrupted-list; no machine state holds such a list.

**Before and after** (REPL on hbox, the book loaded with the scaffold in
`hot-path-scans-2026-09-26/sel-scaffold.lisp`; a visit is one job record
touched, including the `fn-bpn-find-job` steps):

| case | N=64 | N=128 | N=256 |
| --- | ---: | ---: | ---: |
| one ask, only the last job ready: visits before / after | 2,146 / 129 | 8,386 / 257 | 33,154 / 513 |
| one ask, 100 asks: bytes before / after | 20.1 / 10.0 MB | 59.4 / 19.6 MB | 197.1 / 39.1 MB |
| one ask, 100 asks: time before / after | 0.01 / 0.00 s | 0.03 / 0.01 s | 0.11 / 0.02 s |
| one ask, held head, rest ready: visits before / after | 7 / 5 | 7 / 5 | 7 / 5 |
| whole contact drain (N−1 offers): visits before / after | 50,110 / 4,286 | 374,654 / 16,766 | 2,895,614 / 66,302 |
| whole contact drain: time before / after | 0.00 / 0.00 s | 0.02 / 0.01 s | 0.11 / 0.03 s |
| whole contact drain: bytes before / after | 2.9 / 0.5 MB | 19.2 / 1.4 MB | 142.1 / 4.4 MB |

The drain went from cubic to quadratic in N: each ask still restarts from the
head (PKT-324 (7)).

**Certification.** Farm run `run-20260926T070729Z-f4ff` on hbox, green, two
jobs, 300 s: five books certified (the job-offer book, its progress book, its
test book, and the run-class book with its test), no book over 10 s. Manifest:
`planning/evidence/manifests/certify-20260926T070754Z-693820.json`.
The seam with bp-lifecycle-5 is only this book and its test book.

## 3. PRF-139 part 1: not delivered (held at 7f615571, reverted by 58cb4f23)

**What the attempt did.** It added a fifteenth Store field, the tally
(COUNT . OCTETS), through `fn-sn-make-v7`, following the event-index precedent
(aebf2f92):
- `fn-sn-io` extended the tally at `:record-directory :ok`;
  `fn-sn-update-replayed` rebuilt it; every other transition carried it.
- `books/store-record-tally.lisp` proved the fold equality
  (`fn-srt-tally-is-the-fold`), the relation's establishment and preservation
  across all Store transitions, and the kernel-figure keystone. All of this
  loaded in the REPL.

**Why it failed.** pcert discovery on hbox (`certify-20260926T065630Z-661485`)
found two problems:
- **The encoder is not executable in test constants.** Extending the octets
  inside a Store transition calls `fn-record-encode`, a constrained function
  (`books/records-seam.lisp`). Defconst evaluation cannot run it, so every test
  book that builds a Store state holding an article in a defconst stops at
  Create. About 50 books fail this way, for example `tests/acl2/store-node-tests`
  at `*SN-COMPLETING*`.
- **Seven books need hint work.** Their hints must learn the v7 carriers:
  consumer-store-invariants, owner-invariants, store-node-retention,
  store-node-traces, store-node-traces-prepare, store-open-bridge,
  topic-history-store-invariants.

**The next exact action for a continuation:**
- The Store carries the committed count only; it is extended in `fn-sn-io`,
  which is executable.
- The host's (K . SUM) octet cache is advanced over sequences K..count-1
  through `fn-cei-get` on the derived event index, which is constant-bounded
  per lookup. The theorem uses `fn-cei-correspondence-lookup` under
  `fn-ceis-relatedp`.
- The fold is computed once, at `fn-owner-install-profile`.
- The v7 theory-list transform and the `fn-sn-*` field and nth lemmas at
  7f615571 carry over.

## 4. PKT-324: served-path prefix traversals found and not fixed

See `planning/backlog-2026-09-25.md`. Summary:
1. `fn-own-refresh` rebuilds the whole group index on every refresh (dominant).
2. The kernel's record append.
3. The kernel's success append.
4. The prepare's `len` and last-cons walk.
5. The byte-count cache: its `len` and `nthcdr`, and the full fold on the first
   query after open.
6. The PRF-099 carried-usage cache has the same pattern.
7. The BP contact drain restarts from the head on each ask, and the membership
   test on `offered` is linear.
8. Status, health and headroom reports still use `len` / `nthcdr`.

## 5. After rows

There are no POST after rows: part 1 did not land, so the image is unchanged
for POST and OVER. The selector's after rows are in §2.

## Part 1 (lane hot-path-scans-2, 2026-09-26): the count, octets, debt and carriage usage without walking the history

Lane `lane/hot-path-scans-2` from dev `5c6825b2`, brief
`build/coordinator/queue/done/w4-hot-path-scans-2.txt`. Ids: PRF-180, SCN-108,
PKT-474.

### What changed for a user

A POST no longer walks the committed history to learn how many records and
octets the Store holds, nor its completion debt or carriage usage. The count
is read from the Store's derived event index; the three per-POST caches are
advanced through that index by one lookup and one fold step per record
committed since the previous query. The first verdict after open no longer
re-encodes the whole history: the octets are folded once, at
`fn-owner-install-profile`.

### Design, and where it departs from the brief's letter

The brief asked for the count as a Store field extended in `fn-sn-io`. The
Store already carries exactly such a field: the derived event index
(`fn-sn-event-index`, slot 13), extended at `fn-sn-io`'s record-directory
append by `fn-cei-put` and built by every open. The index now also counts its
puts: it is `(SEQ-TRIE MSGID-TRIE . COUNT)`. Its maintained relation,
`fn-ceis-indexedp` (the index equals `fn-cei-build` of the history), is
already established at every host-called open and preserved by every owner
transition the host installs, with no hypothesis
(`fn-osi-live-owner-store-is-indexed`, PRF-144). Because the built index of any
list holds that list's length, the relation carries the count for free
(`fn-cei-count-of-correspondence`). So there is no fifteenth Store field, no v7
constructor, no new relation to preserve across the fifteen transitions, and
none of the seven books that needed hint work in the first attempt changed.
No Store transition encodes a record: this avoids the trap of §3.

**What the index holds.** It holds the committed event object itself, not
its encoded length. The octet cache therefore takes each new record's length
from the event it reads through `fn-cei-get`. That is one record encoding per
record committed since the last query, and never the history. Recording the
length beside the event at the append would put the constrained encoder back
inside a Store transition.

**Why `fn-sbud-used` keeps its `len` body.** An `mbe` whose `:exec` reads the
index equals `len` only under the relation, so the guard would have to carry
`fn-ceis-indexedp`. The :program host evaluates a guard when it calls the
function, and evaluating that guard rebuilds the whole index on every call.
The host therefore calls the named function `fn-sbud-count`, and a theorem
equates the two under the relation. This is the pattern of
books/owner-prepare-carried.lisp.

### Assurance chain

- **Native entry.** `fnn-owner-attempt-served`, which calls
  `fn-owner-prepare-buffer`, `fn-owner-publication-verdict`,
  `fn-owner-headroom`, `fn-owner-peer-carried-relay-event` and the
  install at open in host/native/owner.lisp `fnn-owner-install`.
- **Executed ACL2 subjects** (host/owner-host.lisp):
  - `fn-sbud-count` is read by the verdict, both prepares' budget and the
    headroom.
  - `fn-sbud-bytes-carried` is read by `fn-owner-record-octets`.
  - `fn-scf-debt-carried` is read by `fn-owner-record-debt`.
  - `fn-scf-usage-carried` is read by `fn-owner-carried-usage`.
  - `fn-sbud-headroom-carried` is read by `fn-owner-headroom`.
  - The fold at open is `fn-sbud-bytes-used` in `fn-owner-install-profile`.
- **Refinement and keystones:**
  - `fn-sbud-count-is-used`
  - `fn-sbud-bytes-carried-is-the-fold`
  - `fn-scf-debt-carried-is-the-record-debt`
  - `fn-scf-usage-carried-is-the-projection`
  - `fn-sbud-headroom-carried-is-headroom-at`

  Each holds under `fn-ceis-indexedp` and, for a cache, the cache's validity.
  Supporting lemmas: `fn-cei-count-of-correspondence`,
  `fn-sbud-lookup-of-correspondence` (the lookup with no true-list premise),
  the three `-advance-is-the-suffix-fold` lemmas, and
  `fn-sbud-octets-cache-valid-after-commit`, which keeps the stored cache
  valid as the history grows.
- **Maintained relation.** `fn-ceis-indexedp` is established by every open
  and preserved by every host-installed transition (PRF-144). The cache's
  validity holds because each query stores `(count . fold)` and the history
  only grows while one owner runs.
- **The uint32 bound.** A count past 2^32 falls back to the fold. A cheap
  test in the carried functions checks this, so no well-formedness hypothesis
  is needed.

### Teeth

`tests/acl2/store-carried-folds-tests.lisp` and
`tests/acl2/consumer-event-index-tests.lisp` carry the teeth.

**Positive witnesses** use the live owner's Stores built through the host's
own transitions (owner-store-indexed-tests):
- `*osi-before*` is the Store after the open and the barriers, with one record.
- `*osi-after*` is the same owner after the reservation, the carried identity
  prepare, the three record observations and the completion, with two records.
- The cache is the one taken before the commit. It is asserted valid after the
  commit, and the carried figure equals the fold, advancing over the one new
  record.

**Constructed indexed Stores** give a non-zero debt (an open undertaking) and a
non-zero carriage usage (peer-carriage-tests' carried event).

**Removal witnesses** assert every retained hypothesis, the failure of the
omitted one, and the failure of the conclusion, followed by a `must-fail` of
the instantiated claim:
- Without the relation, the witness is the kernel crash image. The host never
  issues the crash; this is labelled a model state. A constructed stale index
  is used for the debt and usage witnesses.
- Without validity, the witness is a CORRUPTED cache, labelled as such.
- The count's witness is a corrupted index: a second put at sequence 2.

### Measured (SCN-108; hbox, ZFS, default profile, 2 KiB articles)

**Setup.** Both images are developer profiling images built by the same
scripts (`hot-path-scans-2026-09-26/part1-all.sh`, which uses §1's `run.sh`,
`alloc.lisp` and `allocprof.py`):
- *before*: dev `5c6825b2`.
- *after*: lane `ff2eacb3`. Its host code is the same as at `695e7823`.

The box's load average was 6 to 10 throughout, so the times here are
indicative only. The allocation figures are counts and do not depend on load.

**rep_measure** (K=32, R=3, checkpoint skipped):

| point | POST bytes consed / op | STAT | ARTICLE | load |
| --- | ---: | ---: | ---: | ---: |
| N=1,000 before | 2,485,094 | 51,382 | 499,384 | 171.0 s |
| N=1,000 after | 2,484,820 | 50,314 | 500,415 | 193.3 s |
| N=10,000 before | 7,965,868 | 50,342 | 499,375 | 2,669.3 s |
| N=10,000 after | 7,955,659 | 51,370 | 499,355 | 2,485.7 s |

**Allocation profile.** An sb-sprof `:alloc` profile covered 200 POSTs after
the owner was reopened on the loaded store. Samples are about 32 KB each; the
table gives each function's total from the graph report:

| term | N=1,000 before | N=1,000 after | N=10,000 before | N=10,000 after |
| --- | ---: | ---: | ---: | ---: |
| `FN-SBUD-RECORD-OCTETS` (the byte-count fold) | 2,555 | 0 | 20,752 | 0 |
| `FN-SBUD-OCTETS-ADVANCE` (the index advance) | — | 401 | — | 401 |
| `FN-OWNER-RECORD-DEBT` | 660 | 673 | 5,432 | 5,436 (at ff2eacb3; see below) |

**Reading.**
- *Before*, the byte-count term is dominated by the first verdict after the
  open, which re-encodes the whole history. Hot-path-scans measured 2,555
  samples at N=1,000 and 20,754 at N=10,000 (§1).
- *After*, the history is folded once, inside `fn-owner-install-profile`
  before the owner serves. The 200 POSTs then cost about 2 samples each:
  one record's encoding, about 64 KB for a 2 KiB article.
- The steady-state POST allocation does not change. The walks the lane
  removed (`len` and `nthcdr` of the history, three caches per POST) are
  pointer walks that allocate nothing, so their cost was CPU and not
  allocation. What each POST still pays is the new record's encoding for its
  length (about 2 samples) and its kind for the debt (about 0.5 samples,
  through `fn-record-p`), both constant in N. That is PKT-474 (d).

**At N=10,000.** The byte-count term goes from 20,752 samples to 401, which
is the 401 measured at N=1,000: constant in N.

The steady-state POST allocation is 7.97 MB before and 7.96 MB after, against
2.49 MB at N=1,000. That growth is not these terms. It is `fn-own-refresh`'s
group-index rebuild (PKT-324 (1)), which served-path-scale owns and which is
not on this base.

The debt row exposed a second first-query fold: 5,432 samples at N=10,000
against 660 at N=1,000. The debt and usage caches were reset to nil at open,
so the first POST folded the history, calling `fn-record-p` on each record.
Commit `97a3a5ac` folds both once at `fn-owner-install-profile`, as it
already did for the octets. Its profile over the same stores is the "after2"
row below.

**after2** (commit `97a3a5ac`): the same `allocprof.py` over 200 POSTs, run on
the stores the after runs loaded, with the owner reopened on the `97a3a5ac`
profiling image.

| term | N=1,000 | N=10,000 |
| --- | ---: | ---: |
| `FN-SBUD-OCTETS-ADVANCE` | 403 | 405 |
| `FN-OWNER-RECORD-DEBT` (all under `FN-SCF-DEBT-ADVANCE`) | 104 | 107 |
| `FN-SBUD-RECORD-OCTETS` | 0 | 0 |

Every term is flat in N. At N=10,000, the octet and debt terms of the 200
POSTs after the open went from 26,184 samples (about 840 MB) to 512 (about
16 MB).

The runs' exit lines and the profile rows are in `hot-path-scans-2026-09-26/part1-runs.log`. It was produced by tools/rep_measure.py through `run.sh`, and by `allocprof.py`.

**Visits per POST**, from the definitions:

| | per query of the three caches | first query after open |
| --- | --- | --- |
| before | `len` of the history plus `nthcdr` K, three times (3 x 2N cons steps), plus one record's fold step each | an N-record encode |
| after | one `fn-cei-get` per new record (a fixed 4-level radix path) and one fold step each | 0 (the fold is at install) |

**Native gate on hbox** (`hbox_native.sh`, commit `695e7823`,
`native-gate2`; FN_NATIVE_HOST set; production image built):

| module | result | log SHA-256 |
| --- | --- | --- |
| test_native_operator_verdicts | OK (1 skipped) | bc8bdf6c… |
| test_native_capacity_vector | OK | b3ab30b6… |
| test_native_profile_upgrade | OK (4 skipped) | 3e0fb3e9… |
| test_native_hybrid_author | OK (11 skipped) | 5790bb8e… |
| test_native_operator_verbs | OK, 22 tests, FN_NATIVE_HOST = the production image | 12536d18… |

Image SHA-256s: developer `232b9cd9…` and production `78e9a14a…`.

An earlier run (`native-695e78235712`) had no FN_NATIVE_HOST set and no
production image. Its test_native_profile_upgrade errors were missing images
(`build/fn-host`), and `test_native_peer_carriage` was a module name that
does not exist. Both are harness errors, not behaviour.

### Not done (PKT-474)

- **The prepare's candidate test.** It still takes `len` and the last cons of
  the history (`fn-pcar-candidatep`, `fn-pcar-next-lower`). These are pointer
  walks that allocate nothing. Replacing them needs the index threaded into
  `fn-pcar-stage-record`, which would make `fn-pcar-sbud-prepare-is-sbud-prepare`
  conditional. Its users (owner-store-indexed's preservation theorems) would
  then need the relation.
- **The operator status and health reports** (`fn-nls-live-report`,
  `fn-nh-live-report`):
  - They still extend by `len`/`nthcdr`.
  - The status report folds the debt over the history
    (`fn-cvec-record-debt` in `fn-nls-report`).
  - Their test books build un-indexed owners, so the carried figure needs
    indexed witnesses there.
  - The headroom verb (`fn-owner-headroom`) is done.
- **The checkpoint capture's `len`.** `fn-owner-sco-capture` is per
  publication, not per POST.
- **The offline store host** (host/store-node-host.lisp) keeps the folds. It
  runs once per command.
- **(d) One record's encoding and kind per POST.** The octet advance
  encodes each new record for its length, about 64 KB for a 2 KiB article.
  The debt step takes its kind through `fn-record-p`. A length-only twin of
  the encoder, and the concrete-twin kind, would remove both. Both are
  constant in N.
