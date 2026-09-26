# post-identity-index (2026-09-26): a POST's Message-ID tests without walking the history

Lane `lane/post-identity-index` from dev `6407de336` (Opus 5.5), the
performance ledger's fix lane 3 (planning/performance-2026-09-26.md row 5).
Ids: PRF-191, SCN-120, PKT-548 (what remains), PKT-549 (the decision packet
below). No wire, delta or format code taken. Commits: 50aebab85 (books, tests, host lines), and the record/registry commit carrying this file.

## What changed for a user

A POST's owner CPU at N = 10,000 was 10.8 ms against 4.7 ms near N = 0: three
tests compared the posted Message-ID or obligation id with every entry of a
list that grows with the history (the ledger's POST profile: `fn-retain-known-id-scanp`
28.0, `fn-rclb-existing-action` -> `fn-find-article` 21.9, `fn-accept-prepare`
-> `fn-acceptedp` 10.2 percent; 670 of EQUAL's 676 self samples). Two of the
three are now answered from the Message-ID trie the owner already carries over
its committed view, and the third is decided once instead of twice. Every
POST's verdict and served bytes are unchanged (the equalities below).

MEASURED on hbox, tmpfs copies of the registered fixtures, K = 400 POSTs of
2,048 octets per run, five alternating rounds pinned to cores 20-23 (the
box's load average 10.1 to 13.1 throughout, every figure's in
`results2/`), median of the five rounds:

| N | owner CPU per POST, base 6407de336 | lane 50aebab85 | bytes consed per POST, base / lane |
| ---: | ---: | ---: | ---: |
| 1,000 | 3.58 ms | 3.50 ms | 1,985,253 / 1,985,265 |
| 10,000 | 7.78 ms (rounds 6.92 to 8.17) | 4.95 ms (4.55 to 5.60) | 2,130,096 / 2,130,053 |

So at N = 10,000 a POST's owner CPU falls by 36 percent (2.8 ms), and the
growth from N = 1,000 to 10,000 falls from 4.2 ms to 1.45 ms. It is not yet
flat: the remaining growth is mostly the one retention scan left (PKT-549).
Bytes consed are unchanged, as expected: the removed walks compared
pointers and strings and allocated nothing. The base's 7.78 ms is below the
ledger's 10.8 ms (its profiling twin of f314a5a3, unpinned, load 13 to 16);
the ledger's figure and these are not the same conditions and are not compared.

CPU profile (sb-sprof :cpu, one run each at N = 10,000, K = 200,
`results/*-10k-cpu-flat.txt` and `-graph.txt`): the base's samples under
`FN-FIND-ARTICLE` 13.6 percent and `FN-ACCEPTEDP` 3.8 percent become none;
`FN-RETAIN-PIN-ID-SCANP` is reached from `FN-PIDX-NODE-PREPARE` alone (the base
reached it from both `FN-NODE-PREPARE`, 89 samples, and `FN-RETAIN-ADMIT`, 72).
Its share of this one run's window is 25.3 percent (223 of 882 samples)
against the base run's 21.1 (160 of 757): one scan, not two, but the single
remaining scan sampled higher in this run (the box was at load 10; a
single-run profile share is indicative, the five-round CPU medians above are
the figures).

## The three subjects and their host lines

`host/native/owner.lisp` `fnn-owner-attempt` makes two ACL2 calls for a
served POST, both in `host/owner-host.lisp`:

| Test | Before | Host line (function) | Now |
| --- | --- | --- | --- |
| held article (duplicate vs conflict) | `fn-rclb-existing-action` -> `fn-find-article` over the node's articles | `fn-owner-existing-action-buffer` and `fn-owner-prepare-buffer` (twice per POST) | `fn-pidx-existing-action` |
| acceptance duplicate test | `fn-accept-prepare` -> `fn-acceptedp`, reached through `fn-pcar-sbud-prepare` -> `fn-pcar-opc-prepare` -> `fn-pcar-opc-owner-prepare` -> `fn-pcar-spc-prepare` -> `fn-sn-prepare-node` -> `fn-node-prepare` | `fn-owner-prepare-buffer` | `fn-pidx-sbud-prepare` (the same chain, `fn-pidx-*`) |
| retention admission | `fn-node-prepare` -> `fn-retain-admissiblep` -> `fn-retain-known-id-scanp`, then `fn-retain-admit` -> the same test again | `fn-owner-prepare-buffer` | `fn-pidx-node-prepare`: decided once |

## Design, and where it departs from the brief's letter

**The trie is the view's, not the Store's event index.** The brief named
the Store's derived event index (the Message-ID half of `fn-sn-event-index`,
`fn-ceis-indexedp`, PRF-144). That half maps a Message-ID to the history's
article RECORDS; the three tests read the node's ARTICLES, which replay
derives from the records (a reclaimed article's payload is a tombstone that
no record holds, and `fn-rclb-existing-action` compares payloads). An
equation between the two would be a theorem about the whole replay. The
owner already carries a trie keyed by exactly the articles:
`fn-own-view-index`, the index of the committed view's visible list, kept
by `fn-own-refresh` (`fn-midx-refresh`, one path copy per acceptance) and
already read by the IHAVE/CHECK test (books/peer-offer-indexed.lisp). No
Store field, owner field or relation is added.

**Why the trie of the visible list answers the raw list.** The view carries
the raw article list (`fn-own-view-raw`) and the visible list that serves
readers (`fn-ctl-visible-articles` of the raw list under the withdrawal
records). A raw article is hidden only by a withdrawal record that targets
its own Message-ID (`fn-ctl-withdrawn-by-p`). So:

- `fn-pidx-find-article msgid arts view` takes the trie when `msgid` is a
  non-empty string, `arts` is EQUAL to the view's raw list (one pointer
  comparison: the refresh stores the node's own list), and no withdrawal
  record targets `msgid` (`fn-pidx-targetedp`, a walk of the withdrawal
  records, not of the history); otherwise it scans `arts`.
- `fn-pidx-find-in-visible-is-find`: for an untargeted Message-ID, finding
  in the visible list is finding in the list it filters. No distinctness
  premise is needed.

**The relations, and who carries them.** Both are existing:

- `fn-ocl-view-visiblep` (the visible list is the filter of the raw list):
  a conjunct of `fn-ocl-relation` through `fn-ocl-view-historyp`
  (`fn-ocl-view-historyp-is-visible`), established at every host-called open
  and preserved by every configured-owner transition.
- `fn-scar-view-indexedp` (the trie is `fn-midx-build` of the visible list):
  established by `fn-own-start` (`fn-oix-own-start-is-view-indexed`) and kept
  by every owner transition the host installs (books/owner-offer-indexed.lisp,
  `fn-oix-*`); for the new prepare, `fn-osi-pidx-prepare-keeps-view-indexed`
  (no hypothesis: only the refresh changes the view).
- `fn-pidx-view-okp-of-live-owner`: the two together give `fn-pidx-view-okp`,
  the named premise the prepare chain's guards carry.

**The prepare chain's guard.** Each twin keeps its reference's guard
(asserted in the test book); the chain the host enters
(`fn-pidx-spc-prepare` and above) also carries `fn-pidx-view-okp`, because
the guard of `fn-rcon-sn-record-bindsp` needs `fn-node-statep` of the staged
node, which holds only when the duplicate test is exact. The served host
runs a `:program` wrapper's callees raw (specs/host.md, "The served reader
path"), so no guard is evaluated per POST; the host's obligation for it is the
pair of carried relations above.

**The retention scan.** The ledger is keyed by obligation id (a digest of the
Message-ID and the content subject, or an operator's undertaking id), which
no carried index answers; a Message-ID trie cannot decide it. The second
scan was redundant: `fn-node-prepare` decides `fn-retain-admissiblep` and
then `fn-retain-admit` decides it again on the same arguments. The twin
builds the admitted ledger in the branch where it has just held
(`fn-retain-admit`'s own body there; the equality needs no hypothesis). The
first scan remains: PKT-549.

## Theorems (books/post-identity-index.lisp)

KEYSTONES, each with the hypotheses `fn-ocl-view-visiblep` of the owner's view
and the trie's correspondence (`fn-scar-view-indexedp` of the owner, or
`fn-midx-correspondencep` of the view's trie to its visible articles):

- `fn-pidx-find-article-is-find-article`: `(fn-pidx-find-article msgid arts view)`
  = `(fn-find-article msgid arts)`, for every Message-ID and every article list.
- `fn-pidx-existing-action-is-rclb-existing-action`:
  `(fn-pidx-existing-action msgid fn-octets groups o)` =
  `(fn-rclb-existing-action msgid fn-octets groups (fn-own-store o))`; hence,
  by `fn-rclb-existing-action-is-rcl-existing-action`, the tombstone-aware
  verdict of books/store-reclaim.lisp.
- `fn-pidx-sbud-prepare-is-pcar-sbud-prepare`:
  `(fn-pidx-sbud-prepare oc record budget)` = `(fn-pcar-sbud-prepare oc record budget)`
  for every record and budget; hence `fn-sbud-prepare`
  (`fn-pcar-sbud-prepare-is-sbud-prepare`), so every theorem about the
  prepare (budget refusal, the owner event under the relation) is about the
  host's call.

Supporting: `fn-pidx-find-in-visible-is-find`, `fn-pidx-view-okp-of-live-owner`,
the step equalities `fn-pidx-accept-prepare-is-accept-prepare`,
`fn-pidx-node-prepare-is-node-prepare`, `fn-pidx-sn-prepare-node-is-sn-prepare-node`,
`fn-pidx-spc-prepare-is-pcar-spc-prepare`,
`fn-pidx-opc-owner-prepare-is-pcar-opc-owner-prepare`,
`fn-pidx-opc-prepare-is-pcar-opc-prepare`. books/owner-store-indexed.lisp:
the host-step model `fn-osi-host-step` gains a `:prepare-buffer` arm naming
`fn-pidx-sbud-prepare`, kept by `fn-osi-pidx-prepare-keeps-indexed` with no
hypothesis, so PRF-144's `fn-osi-live-owner-store-is-indexed` still describes
the host (the list prepare `fn-owner-prepare` keeps the `:prepare` arm).

Every function is guard-verified (asserted `:common-lisp-compliant` in the
test book).

## Assurance chain

native entry `fnn-owner-attempt` -> `fn-owner-existing-action-buffer` /
`fn-owner-prepare-buffer` -> executed ACL2 subjects `fn-pidx-existing-action`,
`fn-pidx-sbud-prepare` (reading the view trie by string index,
books/msgid-index-concrete.lisp `fn-mxc-lookup`) -> refinement: the three
keystones to `fn-rclb-existing-action` and `fn-pcar-sbud-prepare` (and on to
`fn-rcl-existing-action`, `fn-sbud-prepare`) -> maintained relations
`fn-ocl-view-visiblep` (in `fn-ocl-relation`: established at the host's open,
preserved by every configured-owner transition) and `fn-scar-view-indexedp`
(established by `fn-own-start`, preserved by every installed owner transition,
books/owner-offer-indexed.lisp and `fn-osi-pidx-prepare-keeps-view-indexed`)
-> behavioural theorems about the references (duplicate/conflict verdict,
budget refusal, prepare-equals-owner-event) -> observed: tests.test_native_owner
on the lane's image and the SCN-120 rows below.

## Teeth (tests/acl2/post-identity-index-tests.lisp)

Reachable witness: owner-prepare-carried-tests' `*pcar-t-o*` (the owner the
host's POST events reach, Store `:reserved`, two committed articles), whose
view the refresh built from this node (raw list = node's list; no
withdrawals). Asserted: both hypotheses; a held Message-ID and a fresh one
answered through the trie (every test of the fast path asserted true) and
equal to the scan; another list takes the scan; `:duplicate`, `:conflict`
and nil on a live local buffer, each equal to the buffer decision; the
submission's own record and a fresh record stage (`:record-staged`) and
equal the reference; a record under the held Message-ID whose obligation the
ledger admits (asserted) is refused, equal to the reference; at the budget
both are the identity; the staged ledger is `fn-retain-admit`'s. A
constructed record targeting the held Message-ID (not a withdrawal, so both
hypotheses still hold) sends the lookup to the scan, which answers the same.

Hypothesis removal, labelled CORRUPTED (no owner transition builds these
views), for each of the three keystones: (1) without `fn-ocl-view-visiblep`:
an article under the fresh Message-ID on the visible side and in its trie
only; (2) without the correspondence: the visible list right, the fake
article in the trie only. For each: every retained hypothesis asserted, the
omitted one asserted false, the conclusion asserted false (the lookup finds
the fake article; the buffer decision answers `:duplicate` for a fresh
Message-ID; the prepare refuses the fresh record the reference stages), and a
`must-fail` of the instantiated claim. The corrupted prepares are evaluated
with guard checking off (the chain's guard carries the view facts), as the
host's raw call would run them.

tests/acl2/owner-store-indexed-tests.lisp: the host's open (`*osi-open*`)
satisfies `fn-ocl-relation`, `fn-scar-view-indexedp` and `fn-pidx-view-okp`,
and the lookup answers the signed composite's article as the scan does.

## Validation run here

- persvati REPL (proof_repl.py): books/post-identity-index (44 forms),
  books/owner-store-indexed (66), tests/acl2/post-identity-index-tests (57),
  tests/acl2/owner-store-indexed-tests (71): every form admitted.
- Certified singly on persvati to give the REPL its dependents (not a
  closure): certify-20260926T153906Z-3532313 (books/post-identity-index,
  2.0 s), certify-20260926T154311Z-3572486 (books/owner-store-indexed 3.9 s,
  tests/acl2/post-identity-index-tests 1.8 s). Manifests under
  planning/evidence/manifests/.
- `make check-lane`: green in the worktree (build/check-lane-2.log).
- hbox `tools/hbox_native.sh --label r1 50aebab85 tests.test_native_owner`
  (/tank/fn/scratch/post-identity-index/native-r1): certify, acquire,
  validate and the developer image exit 0 (core
  994b94c83570655498b37da39fdfe57ce253122ab73a84bb2c752d45e7b754c8);
  tests.test_native_owner FAILED (18 ran, 2 failures, 0 skipped), log SHA-256
  a36d7aed2c99a39bf0254c50e83ba658390b050a685eef13ff35f0d3e0a7dc02. Both
  failures are HARNESS, not this lane's: they are the two
  NativeOwnerHandlerStructureTests that load host/native/owner.lisp raw in a
  bare SBCL (tests/native_developer_selectors_raw.lisp: "The function
  ACL2::FN-OUTCOME-CODE is undefined" at `+fnn-exit-ok+`;
  tests/native_owner_chunk_loop_raw.lisp: "the suffix was not the next step's
  input"). host/native/owner.lisp, those two raw files and
  tests/test_native_owner.py are byte-identical to dev 6407de336 (no diff);
  this lane changes no raw Lisp. The other 16 passed on the lane's image, among them
  all 12 served tests (POST committed and readable, fresh readings,
  uncertainty fences, transit, feeds, faults). Reported to the deputy as a dev
  harness defect.
- SCN-120 (SHA256SUMS covers every file): run.sh (first pass; it registered
  the fixture /tank/fn/scratch/fixtures/n1k-2k, SHA256SUMS
  4e75e733f7d2d496ff01ced010967457e17f703fc49ca641b0c045a7bfe858ec, loaded by
  the base image) and run2.sh (the five pinned rounds). Images: base
  /tank/fn/scratch/throughput-gate/native-img-6407de336 (core 8cd82dcc...),
  lane native-r1 (core 994b94c8...), results/images.sha256.

## PKT-558: the POST's per-connection group index

Examined, not a rebuild. `fn-served-make-conn-group-indexed`
(books/served.lisp) is `list` of ten fields: the connection record, whose
group-index field is a pointer to the index the connection pinned. It is
called once per octet fed, by `fn-scar-feed-byte` (books/served-carried.lisp,
the reference `fn-served-feed-byte` alike), to rebuild the connection record
around the new wire state: ten conses per octet, about 2,100 records for a
2 KiB POST, 15.6 percent of the POST's bytes. The cost is in L (the article),
not in N; no index is built. It is the byte loop's allocation, the same loop
as `fn-scar-feed-counted` (49.5 percent of the POST's bytes), which the
running ingress-span lane owns; fixing it here would edit the same functions.
PKT-558 is narrowed to that and handed to ingress-span.

## Result (performance ledger, row 5, "The rows in full" / POST)

Result (post-identity-index, 50aebab85): the held-article lookup and the
acceptance duplicate test read the owner's view trie, the retention admission
is decided once; at N = 10,000 owner CPU per POST 7.78 -> 4.95 ms (N = 1,000:
3.58 -> 3.50 ms; five pinned rounds, load 10 to 13, hbox tmpfs), bytes
unchanged. Row 5 narrowed to the remaining retention scan (PKT-549) and the
byte loop's allocation (ingress-span, PKT-558).

## What is NOT done, and why

- PKT-549 (decision packet): the first retention admissibility scan. See below.
- PKT-548 (what remains): the list-payload prepare `fn-owner-prepare`
  (developer `store post`, not the served POST) still calls
  `fn-pcar-sbud-prepare` and `fn-rcl-existing-action`; the transit, control
  and identity prepares have their own paths and were not profiled here.
  A POST whose Message-ID a withdrawal record targets takes the scan (rare;
  its cost is the scan the POST paid before).

## PKT-549 (decision packet): a retention id index

- Trace: `fn-retain-pin-id-scanp`, the one scan left, is 25.3 percent of
  the samples of this lane's CPU window at N = 10,000 (one run), and most of
  the remaining growth from N = 1,000 (3.50 ms) to 10,000 (4.95 ms).
- Constraint: the ledger (`fn-retain-state`: capacity, reserved, pins,
  releases) is keyed by obligation id; a pin is created by an article (id
  derived from Message-ID and subject) or by an operator undertaking (any id),
  so neither trie answers "is this id known" without an assumption about id
  collisions.
- Default: a derived id trie beside the pins and releases, kept by
  `fn-retain-admit` and `fn-retain-release` (O(id length)), with a
  correspondence relation `trie = build(pins ids ++ release ids)`, as the view
  trie is kept.
- Rejected alternative: answering from the Message-ID trie and assuming
  distinct ids for distinct (Message-ID, subject) pairs; it is an assumption
  about SHA-256 and says nothing about operator undertakings.
- Affected: the retention state's shape (a fifth field or a derived field in
  the node), every book that builds or recognizes `fn-retain-state`
  (retention, node, store-node and their invariants), the checkpoint's node
  encoding if the node is persisted with it (a store format change), and the
  replay.
- Continues without it: everything in this lane; the remaining cost is one
  linear scan of the pins per POST.

## Files

planning/evidence/post-identity-index-2026-09-26/: `postmeasure.py`
(the SCN-120 driver), `heap.lisp` (the perf-ledger's heap hook, copied),
`sprof.lisp` (a CPU window for a developer core), `run.sh`, `run2.sh`, the
per-run JSONs (`results/`, `results2/`) and their summary
`planning/evidence/post-identity-index-2026-09-26/results.json` (the SCN-120
log), with `SHA256SUMS`.
