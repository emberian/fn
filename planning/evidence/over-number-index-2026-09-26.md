# over-number-index (2026-09-26): OVER's rows from a number index the group index carries

Lane over-number-index, the performance ledger's fix lane 1 (rows 1 and 7,
PKT-476 (3)); PRF-189, SCN-118; PKT-544 for what remains. Base dev
`6407de33`; commits on `lane/over-number-index` (below).

## What changed

Each bucket of the owner's group index was `(group . entries)`; it is now
`(group entries . numbers)`. NUMBERS is a persistent binary trie keyed by
local article number, least significant bit first
(`books/group-number-index.lisp`, prefix `fn-gnix-`): at most 31 levels for
numbers up to 2^31 - 1 (RFC 3977 section 6), so a lookup costs at most 31
steps whatever the group's size. `fn-gnix-add` decides an entry's key --
`fn-nntp-index-entry-available`, its number and its Message-ID -- once, when
the entry is added; a lookup never re-decides it. `fn-gnix-build` adds a
list's entries last first, so the first entry of a number wins, as the walk
does. `fn-gidx-put` (books/group-bucket-index.lisp) keeps entries and trie
together.

The served renderer `fn-nntp-over-range-indexed` (books/nntp-range-indexed.lisp)
now renders its rows through `fn-nov-lines-for-numbers-numbered`, one trie
lookup (`fn-gidx-nidx-number-article`, books/group-bucket-article.lisp) and
one Message-ID trie lookup per row, instead of `fn-nov-lines-for-numbers-indexed`,
which walked the bucket with `fn-gidx-find-number-entry` per row and re-decided
each entry's Message-ID (`fn-nntp-index-msgid-okp` through
`fn-nntp-string-octets`) at every step: 94.9 percent of OVER's samples in the
ledger's profile. No data ceiling is added; the served bytes are unchanged
(measured below). The index is rebuilt only where the group index already was.

When the group index is (re)built today: `fn-own-refresh` (books/owner.lisp)
calls `fn-gidx-refresh`: nil -> `fn-gidx-build`; the same visible archive ->
kept; one prepended article -> `fn-gidx-put-all` of its entries (a put each,
O(groups + 31) per entry); anything else (several articles between refreshes,
withdrawals) -> a full `fn-gidx-build`. The number index rides on exactly
those transitions; no request rebuilds it.

## Assurance chain

- Native entry: host/owner-host.lisp `fn-owner-chunk` calls
  `fn-scar-ocfg-read-tls-prefix` (books/owner-served-carried.lisp) ->
  `fn-own-read` -> `fn-served-step` -> `fn-served-dispatch` ->
  `fn-auth-step-pinned` -> `fn-peer-step-pinned` -> `fn-nntp-post-step-pinned`
  -> `fn-nntp-step-pinned` -> `fn-nntp-command-pinned` ->
  `fn-nntp-archive-command-pinned`, whose OVER/XOVER arm (books/nntp.lisp)
  calls `fn-nntp-over-range-indexed` with the connection pin's buckets.
- Executed subject: `fn-nntp-over-range-indexed` -> `fn-nov-lines-for-numbers-numbered`
  -> `fn-gidx-nidx-number-article` -> `fn-gnix-find`; all guard-verified
  (`:guard t`, admitted with guards).
- Relation: `fn-gidx-numbers-okp buckets` -- every bucket's number index is
  `fn-gnix-build` of its entries. Proof-side only; no served step evaluates it.
  Established: `fn-gidx-numbers-okp-of-build`, `-of-build-entries` (no
  hypothesis: every build). Preserved: `fn-gidx-numbers-okp-of-put`,
  `-of-put-all`, `-of-refresh` (books/owner.lisp) -- the refresh is the only
  transition that changes the group index; the pin carries the view's
  buckets unchanged. The owner invariant (books/owner-invariants.lisp) already
  carries `group-index = fn-gidx-build (visible articles)`, from which the
  relation follows by `-of-build`.
- Keystone (PRF-189): `fn-gidx-nidx-number-article-is-walk`
  (books/group-bucket-article.lisp):

      (implies (fn-gidx-numbers-okp buckets)
               (equal (fn-gidx-nidx-number-article
                       number (fn-gidx-bucket-numbers group buckets) trie)
                      (fn-gidx-entry-number-article
                       group number (fn-gidx-bucket group buckets) trie)))

  with `fn-gnix-find-of-build` (no hypothesis: the trie answers the walk's
  first match) and `fn-gnix-get-of-set` (posp n, posp m: the trie is a map).
  At the host-called subject: `fn-nntp-over-range-indexed-is-walk` (same
  hypothesis) equates the served renderer with `fn-nntp-over-range-walk`, the
  per-row walk's; `fn-nov-lines-for-numbers-numbered-of-build` rewrites the
  numbered lines to the indexed ones under a build, so PRF-067's
  `fn-nntp-over-range-indexed-equals-fold` and
  `fn-nntp-carried-over-range-equals-archive-command`
  (books/nntp-range-indexed-invariants.lisp) keep their statements and
  re-certified unchanged.
- Behaviour: the OVER reply equals the archive fold (PRF-067, unchanged).
- Observed: the same bytes on both images (SHA-256 below), and the timings.

## Teeth (tests/acl2/group-number-index-tests.lisp)

Reachable buckets come from `fn-gidx-refresh` (a build, then a put of a
prepended article). Keystone: the reachable witness asserts the relation and
the conclusion at numbers 2^31 - 1 (fn.one) and 70 (fn.two), each a cons
article, and 70 absent from fn.one. Hypothesis removal: a CORRUPTED-STATE
bucket list (fn.one's number index emptied; not reachable) on which the
relation fails, the walk finds article 2 and the index does not; `must-fail`
of the keystone at that constant. Preservation: put, put-all and refresh
witnesses on the refreshed buckets; the corrupted list stays corrupted
through each, with a grounded `must-fail` for each. `fn-gnix-get-of-set`:
both branches witnessed; without `(posp n)` (0 reads the root 1 wrote) and
without `(posp m)` (setting 0 writes the root 1 reads), each asserted and
grounded in a `must-fail`. `fn-gnix-find-of-build`: duplicate numbers (the
first wins) and an entry with an invalid Message-ID (not indexed).
`fn-nntp-over-range-indexed-is-walk`: equal on the refreshed buckets with
three rows found (including 2^31 - 1), unequal on the corrupted.

## Validation (by batch)

REPL (persvati `/home/ember/fn-gates/over-number-index-repl`, `w25/acl2-literal`):
books/group-number-index, group-bucket-index and group-bucket-article form by
form; nntp-range-indexed and the test book (44 forms) admitted whole. Then
incremental certifications of named roots on persvati (2 jobs; no farm, no
closure), manifests in planning/evidence/manifests/:

- `certify-20260926T153521Z-3496991`: group-number-index 0.8 s, group-bucket-index 0.5, group-bucket-article 0.3.
- `certify-20260926T153632Z-3508033`: 11 books incl. nntp-range-indexed-invariants 1.4, nntp-reclaimed 0.7, nntp-invariants 6.8.
- `certify-20260926T153742Z-3519176`: nntp-pinned-effects 2.1 (its unconditional effect theorem needed the clean-line lemmas for the numbered renderer, added), peer-inbound, nntp-auth, served, owner 2.0.
- `certify-20260926T153813Z-3523837`: owner-invariants 10.7 s (unchanged book; recertified as a dependent, one of the known over-10 s books), owner-control-read 5.8, nntp-xpat, nntp-list-counts, peer-offer-indexed and five more.
- `certify-20260926T154221Z-3564932`: tests group-number-index-tests 1.4, group-bucket-index-tests 0.9, nntp-range-indexed-tests 1.7.

The change sits under group-bucket-index, a high-fan-in book: 341 affected
roots (`certify_books.py --dry-run --affected-by` over the changed books);
the batch certifies them. `make check-lane`: green after this record.

Native (hbox, `tools/hbox_native.sh --label r1 068fe7d1 tests.test_native_owner`,
image core `f22e32df...`, launcher `fc5d0b40...`): 18 ran, 16 passed, 2
FAILED -- `test_developer_selectors_gate_arm_the_owner_and_stop_synchronously`
(UNDEFINED-FUNCTION FN-OUTCOME-CODE) and
`test_the_chunk_loop_keeps_its_suffix_and_reads_a_clock_per_step` (SIMPLE-ERROR
on the chunk loop), the raw-SBCL structure harnesses qual-dfa810fc lists as
C23 (harness; this lane changes no host file). Log SHA-256
`fbbb4976fcfeae57171d2defb892f73ce664f189c19231cd2a00b259f76ddbef`
(`/tank/fn/scratch/over-number-index/native-r1/logs/test-tests.test_native_owner.log`).

## Measurement (hbox, tmpfs, same fixture, same harness)

Fixture registered: `/tank/fn/scratch/fixtures/n10k-2k` (10,000 x 2,048-octet
articles in fn.test, default profile; SHA256SUMS over store, README, origin),
written by `measure.py load` with the perf-ledger developer image. N = 20,000:
`/tank/fn/scratch/fixtures/chain-20000-8cc3cd4c` (its checkpoint is refused by
shape, so each open is a full replay; its Message-IDs are not the harness's,
so ARTICLE by Message-ID there is a 430 and not compared). Images: before =
the perf-ledger developer image (dev f314a5a3; the OVER path is unchanged
between it and this lane's base), after = the lane image above
(`images.sha256`). Harness: `measure.py reads` (planning/evidence/over-number-index-2026-09-26/),
each run its own `systemd-run --user --scope -p MemoryMax=24G` (40G at
20,000). Owner CPU is /proc utime+stime over the batch, all owner threads.
Median / p95 ms, owner CPU ms per op; box load beside each run.

| N | run (load) | OVER 40 rows | OVER 1-2000 | OVER 1 | ARTICLE by number | by Message-ID | STAT |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 10,000 | before2 (10.6) | 204.5 / 289.3, CPU 198.5 | 12,559 / 13,492, CPU 12,490 | 6.9 | 6.0 | 5.7 | 0.5 |
| 10,000 | after (10.8) | 9.9 / 10.8, CPU 5.0 | 554 / 812, CPU 336 | 1.6 | 3.0 | 2.9 | 0.3 |
| 20,000 | before20k (11.3) | 1,390 / 7,051 | 40,799 / 47,972, CPU 41,662 | 33.8 | 5.4 | -- | 1.0 |
| 20,000 | after20k (9.9) | 17.5 / 21.7 | 713 / 855, CPU 1,010 | 3.3 | 4.3 | -- | 0.7 |

Logs: planning/evidence/over-number-index-2026-09-26/after.json, before2.json,
after20k.json, before20k.json and before.json (each with its box state and
image). A first before run (`before.json`, load 12.6) agreed: OVER 40 184.5 ms,
OVER 1-2000 12,732 ms. Served bytes (one OVER 1-2000 reply and 32 ARTICLEs
by number): SHA-256 `d992a00e...` on both images at 10,000 and `f6648e69...`
on both at 20,000. At 20,000 the owner CPU per op includes the owner's other
threads after a full-replay open (it exceeds wall on some rows); the wall
figures are the ones to compare there.

Result: OVER 40 rows 20x faster at 10,000 (tens of ms, as expected), OVER
2,000 rows 23x (under 1 s) and flat from 10,000 to 20,000 (554 -> 713 ms,
against 12.6 -> 40.8 s before). Row 7: ARTICLE by number costs what ARTICLE
by Message-ID costs on the same image in both runs (6.0 vs 5.7, 3.0 vs 2.9
ms); the ledger's 7.2 vs 2.4 ms compared two different harnesses. ARTICLE by
number never used `fn-gidx-find-number-entry`: it walks the archive with
`fn-nntp-find-group-number` (`fn-nntp-number-retrieval`), whose cost is
STAT's 0.3 to 0.5 ms at 10,000. Row 7 is narrowed, not fixed (PKT-544 (2)).

PKT-476 (3) (OVER about 8 ms a row): ticked by this lane -- about 0.3 ms a
row at OVER 1-2000 (owner CPU 336 ms for 2,000 rows) and about 0.25 ms a row
at OVER 40.

## Not done (PKT-544)

1. The range's number selection `fn-nntp-index-group-range-numbers` still
   walks the bucket once per OVER (fn-index-listp, the range filter) and
   re-decides availability for the in-range entries; OVER 1 is 1.6 ms at
   10,000 and 3.3 ms at 20,000: linear in N, per request not per row. The
   same number index could answer the range (an ordered walk of the trie
   between low and high) under the same relation.
2. ARTICLE/HEAD/BODY/STAT by number walk the archive
   (`fn-nntp-find-group-number`, matching on membership number alone); they
   could use `fn-gidx-nidx-number-article` under the pin correspondence given
   a theorem equating the two on a valid archive. Small today (STAT 0.3 to
   0.5 ms at 10,000, 0.7 to 1.0 ms at 20,000), linear in N.
3. GROUP (28 ms at 10,000, 102 ms at 20,000) re-derives count/low/high from
   the bucket with three availability walks (`fn-gidx-group-summary`).
4. A full `fn-gidx-build` (several articles between refreshes, withdrawals)
   now also builds the tries: O(N x 31) conses per rebuild; not measured.
