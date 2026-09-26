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
