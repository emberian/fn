# The source tree: what the measurements say, and what to do (architect, 2026-09-28)

Status: a recommendation for ember, written against the proposal in
`planning/reorg-2026-09-28.md` (lane book-split-pilot, `92e0544f7`) and its
pilot record `planning/evidence/book-split-2026-09-28.md`. Every number below
was measured on origin/dev `abdc0db4c` (the graph, the three-day edit
history) or on this lane's own runs on persvati; the scripts are under
`planning/evidence/architect-2026-09-28/` and section 9 says how to rerun
them. Nothing here has landed on dev. The one code change this lane made (the
UTF-8 decoder moved out of `books/wildmat.lisp`, commit `fba0991e3`) is a
separate commit on `lane/architect`, for ember to take or leave.

## The short version

**1. The problem is not the flat directory, and only part of it is the
fan-in.** The tree is 1,469 books (848 under books/, 621 tests), 3,553
include edges, a median of 2 direct includes per book, closures that are
small (median 90 books, largest 336) and a graph that is **65 levels deep**
(median book at depth 31). A recertification's wall time is its longest
dependency chain, not its size or the core count: three runs, three matches.
The pilot's 984-book run on persvati took 509 s at 20 jobs against a 466 s
chain; its hbox run 656 s at 14 jobs against a 642 s chain; this lane's
1,138-book run 385 s at 20 jobs against a 384 s chain (summed work / 20
would be 317 s). More cores do not help; a split that puts more books in
sequence makes it worse.

**2. Per book, the time is loading and processing, not proving.** ACL2's
provisional certification separates the two: its Create wave processes each
book with proofs skipped and its Convert wave does the proofs. Run on the same
1,138 books, the Create wave cost the same per book as an ordinary
certification (median ratio 0.99) and, because Creates depend on each other
the way certifications do, its chain was 589 s; the proofs (Convert, fully
parallel) took 305 s of wall. Including a book's closure costs about 0.37 ms
per event in it (0.78 ms per definition, 0.12 ms per theorem; R² 0.83 over
18 books from `cbor` to `served-catalog-owner`), so `books/owner`'s 175-book,
11,261-event closure loads in 3.3 s and the foundation loads in a tenth of a
second. Compilation is not it either: certifying a chain book with and
without the compile step differs by a few percent. And 20 concurrent ACL2s
on 24 cores run each book 2.4 to 4.4 times slower than a quiet box (section
5.3), and the chain runs at that slowed rate.

**3. The edits that cost are definition changes to mid-level books that
dependents genuinely reason about.** Over three days (1,029 non-merge commits
touching books/), the median commit touched a book with 37 dependents; 21 %
of commits touched a book with more than 500, and those carry 74 % of the
recertification volume (about 227,000 book-certifications, some 370
CPU-hours). The churn-weighted hubs are `config` (22 edits, 751 dependents),
`nntp-responses` (25, 558), `byte-store-frame` (21, 642), `payload-arena`
(15, 702), `assumptions` (15, 752), `control-authority` (14, 658), `nntp`
(13, 534), `hybrid-store` (12, 953), then the codec books (`records`,
`records-shape`, `records-invariants`, 9 edits each, 1,100+ dependents).
Classifying all 1,061 edits to books with 200+ dependents by what changed:
50 % changed a definition; 42 % changed only theorems, hints, theories or
guards, but 31 of those 42 points were five rule-hygiene commits that
rewrote `in-theory` forms in 252 wide books at once; 6 % changed only
comments; 1 % an include. **Seven edits (0.7 %) changed only an `:exec`
branch.** Of the definition edits, 94 % changed a name that some dependent's
source mentions. So most of the volume is what ACL2 semantics require for
this proof style, where theorems are about the served bytes and therefore
about the actual definitions, and it should not be free: those dependents'
proofs may no longer go through.

**4. The seam (constrained function + `defattach` + exec twin) addresses the
0.7 %.** The pilot's flagship measurement, an `:exec` edit going from 1,132
recertified books to 5, is real and correctly measured, but it measures the
rarest kind of edit in the tree; a `:logic` edit to the seamed book still
costs 1,133 (the pilot says so). The seam has costs: callers reason about a
constrained function, so ground terms do not evaluate in proofs (the manual:
attachments are not used "especially [for] evaluation of ground terms …
during proofs") and every caller opens the `-by-definition` rewrite; each
constrained function is two raw stubs, each declaring a fresh special that
takes a thread-local-storage slot SBCL never frees, once per top-level
include that reaches it; extraction has to follow the attachment. Mature
ACL2 code separates spec from execution with `mbe` inside one book (5,350
uses in the community books against 461 `defattach` forms, most of them
hooks and tracing); the two places the community uses `defattach` as an
architectural seam are pluggable heavy implementations (kestrel's crypto
interfaces, GL's SAT backend), which is what fn's `crypto-seam` already is. A
seam is right where the implementation is heavy, pluggable or a D27
performance twin expected to churn (records qualifies; keep the pilot's
split). It is the wrong default.

**5. What I recommend, in order.** (i) Attack the chain, which nobody has
named: a critical-path report (`tools/critpath.py`, the counterpart of
cert.pl's `critpath.pl`, prototyped in `critical_path.py` here) so the
"books under 10 s" ratchet spends itself on the 60 books that set the wall
(`served-catalog-owner`, `catalog-entries`, `nntp-auth`,
`config-owner-live-read`, `owner-invariants-relation` …), and a scheduler that
starts the longest remaining chain first and runs fewer, faster ACL2s
instead of 20 slowed ones; both are tooling and change no book. (ii) Cut the
accidental fan-in book by book, simulated on the graph before touching
anything: the UTF-8 decoder out of `wildmat` (done on this lane: `wildmat`
1,137 → 738 dependents, three files, every form moved exactly once, the whole
closure recertified green), the item layer out of `records-invariants`
(simulated: `records` 1,138 → 1,019), the 97 includes whose includer uses
nothing in the included closure. Each is a day and one recertification.
(iii) Give lanes the rule-usage map (`tools/rule_users.py`, prototyped here
from the Convert logs' `Rules:` and `Hint-events:` lines): before editing a
theorem in a wide book, it says whether any dependent's proof uses it (39 %
of the theorem edits in the window touched theorems nothing downstream
uses), and a theorem nothing uses can move to a leaf. (iv) Give the images
one umbrella book so each stub costs one TLS slot instead of one per
top-level include (373 top-level `include-book` forms across 34 host files
today); independent of any reorganisation. (v) Keep the process rules the
coordinator already wrote (REPL first, one wide book at a time, no duplicate
certification): they attack the number of rounds, which multiplies
everything else; comment-only edits to wide books alone were 6 % of the
volume, and five theory-hygiene commits were 31 %.

**6. What it costs.** (i) is two days of tooling. (ii) is a day per cut plus
one recertification of that hub's dependents, which the cut then makes
cheaper forever. (iii) is a tool and then judgement per theorem. (iv) is a
small host-side change and one image build with the TLS probe. None of
these moves a file or rewrites a registry.

**7. What I would not do now: the eleven-subsystem api/impl/proofs
migration.** Its dry run moves 1,462 files, rewrites 3,552 include edges and
about 17,000 path references in the registries, Makefile and host files,
needs a per-book decision for 341 books whose includes point upward, and
then asks lanes to split 728 mixed books by hand. What it buys, by the
measurements: the impl side decouples the 0.7 % exec-only edits plus the 6 %
of definition edits that touch names no dependent mentions (about 4 % of
volume together); the proofs side decouples some of the ongoing proof-only
churn, which outside the one-off hygiene campaign was 11 % of volume, of
which about two fifths touched theorems nothing downstream uses; the api side
changes nothing, because an api edit is a definition edit and 94 % of those
are public. The chain, which sets the wall time, is untouched or lengthened.
The "image loads the proofs" finding is true (12,108 theorems in the image's
677-book closure) but only 35 of those books are proof-only (868 theorems);
the rest sit in mixed books, so getting them out means the whole split, for
a runtime that proves nothing and for a load cost of 0.12 ms per theorem.
If ember wants subsystem directories for navigation, a pure move is one
commit and one full recertification with no recertification savings
afterwards; do it for navigation and say so, never for cost.

**8. The two questions.** Q1, the seam's witness: today's cache key (the
book's whole include closure, local includes included) is what the ACL2
community's build system does (cert.pl treats a local include as a full
dependency); ACL2 itself does not check a locally included book's hash when
the includer is later included, so a stale certificate is accepted silently,
and a `make-event` expansion frozen in the certificate can drift from the
current local book. Simulated over the whole graph, excluding the tree's 30
`(local (include-book …))` edges from the key removes 2,863 of 154,513
book-recertifications (1.9 %), concentrated in four books
(`statement-codec` 1,017 → 302, `article-properties` 643 → 14,
`article-invariants` 646 → 17, `injection-invariants` 504 → 99). So (b)
buys 2 % at the price of leaving community practice and a real drift
hazard; keep the key. (a) is fine wherever a seam already exists; the
pilot's shape is right. But the question presupposes the seam. Q2, seam
every cross-subsystem call or the hot ones: neither by default. Seam what is
heavy or pluggable or a D27 performance twin, one at a time, each with its
`-by-definition` equation and its stub counted in the image gate.

**9. Open.** The rule-usage map covers the 1,138 books above `wildmat` and
`frame-fields` (one Convert wave); a tree-wide map needs one full
provisional run, which is also the run that names every red at once (the
farm's docstring already says this is what `--pcert` is for; it is not a
wall-time tool on this tree). The TLS accounting in `arena-store-8-tls.md`
counts `defun-nx` as a slot; the ACL2 8.7 source (`defun-nx-form` expands
to `throw-nonexec-error`, not `throw-or-attach`) suggests it is not, which
is worth one probe before a stub gate is written. Whether the `bp`, `store`
and `owner` towers can be flattened (section 4.3: 53 of the 61 edges on the
longest chain are genuine uses) is proof engineering per tower, not a tree
question. A certificate installed from another worktree records its
sub-books' hashes; recertifying an unchanged sub-book in-tree produced a
different hash than the cached dependents expected (section 5.3), which is
the closure key's reason to exist and worth knowing when hand-timing books.

---

## 1. The graph as it is

The farm's own graph (`certify_books.local_closure` over the Makefile roots,
the one `tools/shape_books.py` walks), on origin/dev `abdc0db4c`, computed on
persvati.

| quantity | value |
|---|---:|
| books in the root closure | 1,469 (848 under books/, 621 under tests/acl2/) |
| Makefile roots | 1,421 |
| include edges | 3,553 |
| direct includes per book | median 2, mean 2.42, max 17 |
| include closure per book (what a book loads) | median 90, mean 104, p90 224, max 336 |
| depth (longest include chain ending at the book) | median 31, p90 48, max 65 |
| dependents per book (what recertifies when it changes) | p50 2, p75 29, p90 503, p95 752, p99 1,071 |
| books with ≥ 900 dependents | 52 |
| books with ≥ 500 dependents | 148 |
| books with ≤ 10 dependents | 963 |

The deepest chain (section 4.3) runs from `cbor` through `frame`,
`assumptions`, `payload-arena`, the `nntp` tower, `served`, `owner`, the
`owner-invariants` tower, `config-owner-live`, the `owner-commit` books and
the `served-catalog-join` tower to a test. Closures are small because most
books include two or three others; dependents are large because the graph
is deep: `cbor` has 1,395 dependents with a closure of 0.

## 2. Three days of edits (2026-09-25 to 2026-09-28)

`git log origin/dev --no-merges --since=2026-09-25 -- books/`: 1,029
commits with at least one book in the graph (1,667 with merges). For each
commit the cost is the dependents of the widest book it touched (a lower
bound on the union).

| per-commit cost (dependents of the widest edited book) | commits |
|---|---:|
| ≤ 10 | 317 |
| 11–50 | 245 |
| 51–100 | 101 |
| 101–200 | 49 |
| 201–500 | 102 |
| 501–900 | 157 |
| > 900 | 58 |

Median 37, p75 420, p90 751, p95 953, p99 1,229. Summed: 227,453
book-certifications, about 373 CPU-hours at the contended 5.9 s per book;
the 215 commits above 500 (21 %) carry 74 %.

Most-edited books with ≥ 500 dependents (edits in three days, dependents):

| book | edits | dependents |
|---|---:|---:|
| nntp-responses | 25 | 558 |
| config | 22 | 751 |
| byte-store-frame | 21 | 642 |
| nntp-reader-compat | 15 | 536 |
| payload-arena | 15 | 702 |
| assumptions | 15 | 752 |
| control-authority | 14 | 658 |
| nntp | 13 | 534 |
| hybrid-store | 12 | 953 |
| store-node-invariants | 12 | 558 |
| config-invariants | 12 | 535 |
| group-bucket-index | 10 | 547 |
| injection | 10 | 632 |
| records | 9 | 1,138 |
| store-files | 9 | 802 |
| records-invariants | 9 | 1,122 |
| records-shape | 9 | 1,229 |
| store-node | 9 | 660 |
| records-canonicality | 8 | 1,001 |
| replay | 8 | 864 |
| frame, frame-journal, frame-octets, article | 7 each | 1,057–1,131 |

`cbor` and `defrecord`, the top of the fan-in table, were not edited in the
window. The foundation is stable; the churn is in the middle of the tower.

## 3. What the edits were

Each edit to a book with ≥ 200 dependents (1,061 edits) was classified by
parsing both versions with `tools/ledger.py`'s reader and diffing the
multiset of top-level forms: a form that differs only in its `:exec` branch
(after replacing every `(mbe :logic L :exec E)` by `(mbe :logic L)`) is
"exec-only"; a `defthm` that differs only in `:hints`, `:rule-classes` or
`:otf-flg` is "hints-only"; `in-theory`, `verify-guards`, `local` forms and
assert-events are proof-side; a changed `defun`/`define`/`defmacro`/record
form is a definition. Comment-only edits changed no form.

| kind | edits | book-recertifications | share |
|---|---:|---:|---:|
| definition (a logic change) | 534 | 328,483 | 50.2 % |
| proof-only, of which: | 451 | 276,450 | 42.3 % |
| — non-local `in-theory` changed | 304 | 204,237 | 31.2 % |
| — a non-local theorem's statement changed | 84 | 44,354 | 6.8 % |
| — hints, local lemmas or guards only (invisible to includers) | 63 | 27,859 | 4.3 % |
| comment-only | 65 | 41,099 | 6.3 % |
| include change | 11 | 7,780 | 1.2 % |
| of which exec-only (an `:exec` branch and nothing else) | 7 | | 0.7 % |

The 304 `in-theory` edits came from 33 commits, five of which
(`4f898594b` 72 books, `771e19681` 69, `66cdec798` 59, `eecda757e` 29,
`b72c5fe07` 23) were one rule-hygiene campaign. The seven exec-only edits:
`acceptance-alloc` (three commits), `nntp-index-runtime`, `nntp-session`,
`nntp-syntax`, `nntp-projection`. Restricting to books with ≥ 500 dependents
(677 edits) gives the same shares.

**Private or public definitions.** For the 462 definition edits whose
changed forms could be paired, `git grep` at the commit over books/ and
tests/acl2/ asked whether any *dependent* mentions a changed name: 435 do
(264,644 book-recertifications), 27 do not (17,895, 6.3 % of the definition
volume). The private ones are the `-loop` twins of D27 executables
(`fn-cfg-item-octets-loop`, `fn-sha256-appx-loop`, `fn-sl-append1-loop`, …)
and `*fn-proto-table*`. That is the ceiling of what an implementation-side
split can decouple in this class.

Per book, for the churn hubs (edits by kind): `config` 20 logic / 1 proof /
1 include; `nntp-responses` 17 / 7 / 1 comment; `byte-store-frame` 14 / 5 /
2 comment; `nntp` 13 / 0; `owner` 28 / 3 / 3 comment; `owner-invariants` 3 /
26 / 1; `records-canonicality` 0 / 8; `article-properties` 0 / 7;
`nntp-effects` 0 / 7. The invariants books are proof-only churn; the
definition books are definition churn.

## 4. What a book costs, and what a run costs

### 4.1 Per book, under load

From the pilot's two full runs (manifests
`certify-20260928T163441Z-33654`, persvati, 20 jobs, 984 books;
`certify-20260928T163631Z-1516505`, hbox, 14 jobs, 763 books) and this
lane's ordinary run (`certify-20260928T195000Z-1826984`,
persvati, 20 jobs, 1,138 books):

| | persvati (pilot) | hbox (pilot) | persvati (this lane) |
|---|---:|---:|---:|
| summed book wall seconds | 5,791 | 6,656 | 6,340 |
| median / mean per book | 5.15 / 5.89 | 6.99 / 8.72 | 4.93 / 5.57 |
| p90 / max | 10.4 / 25.9 | 17.0 / 47.9 | 9.5 / 49.1 |
| tests/ (count, summed) | 380, 1,919 s | 218, 1,495 s | |
| books/ (count, summed) | 604, 3,872 s | 545, 5,161 s | |
| books ≥ 10 s and their time | 115, 1,636 s | 224, 3,741 s | |

Regressing a book's seconds on its closure size (pilot, persvati):
`2.7 s + 24 ms × closure`, R² 0.22. Median seconds by closure bucket:
< 100 → 2.9 s, 100–199 → 5.9 s, 200–299 → 7.0 s, ≥ 300 → 8.6 s.

### 4.2 Per run: the critical path

Weighting each book on the include DAG with its measured seconds and taking
the longest chain within the books each run certified:

| run | jobs | summed | ideal (summed / jobs) | critical path | wall |
|---|---:|---:|---:|---:|---:|
| persvati (pilot) | 20 | 5,791 s | 290 s | **466 s** | 509 s |
| hbox (pilot) | 14 | 6,656 s | 475 s | **642 s** | 656 s |
| persvati (this lane, ordinary) | 20 | 6,340 s | 317 s | **384 s** | 385 s |
| persvati (this lane, pcert Create wave) | 20 | 11,298 s | 565 s | **589 s** | 594 s |

Every run was chain-bound. Over the whole graph (median fill for unmeasured
books) the longest weighted chain is 533 s, median 108 s, p90 348 s.

### 4.3 The chain

The 62-book chain that set the pilot's persvati wall (its seconds), top down:

```
served-catalog-join-inv-tests(5.1) → served-catalog-join-inv(15.1) →
served-catalog-join-frame-conns(16.9) → served-catalog-join-pinned(17.8) →
served-catalog-join-conns(11.1) → served-catalog-join-finish(11.8) →
served-catalog-join-entry(9.5) → served-catalog-join-open(6.0) →
served-catalog-join-number(6.8) → served-catalog-join(6.4) →
served-catalog-join-step(8.9) → served-catalog-join-refresh(7.5) →
served-catalog-owner(12.9) → catalog-entries(6.4) → owner-checkpoint-open(4.8) →
owner-recover-ocl(7.3) → owner-offer-indexed(11.9) → owner-advance-carried(6.9) →
owner-commit-ocl(7.6) → owner-commit-carried(12.8) → config-owner-live(6.4) →
config-owner-live-read(18.9) → config-owner-live-open(13.8) →
config-owner-live-complete(12.6) → owner-config(10.3) → owner-fault(2.4) →
owner-invariants(3.3) → owner-invariants-outcome(10.3) →
owner-invariants-served(10.9) → owner-invariants-step(14.9) →
owner-invariants-relation(15.2) → owner(8.4) → served(14.2) → nntp-auth(24.9) →
group-access(10.7) → peer-inbound(12.8) → nntp-pinned-effects(12.6) →
nntp-post(6.2) → nntp-effects(8.9) → nntp-invariants(10.0) →
group-bucket-cursor-invariants(3.8) → nntp-index(5.4) → nntp(5.0) →
nntp-reader-compat → nntp-xref → nntp-range-indexed → group-bucket-article →
group-bucket-index → group-number-index → nntp-index-runtime →
nntp-projection → nntp-session → payload-arena → payload-arena-extent-logic →
assumptions → byte-store-invariants → frame → frame-journal → frame-fields →
frame-octets → cbor-invariants → cbor
```

For each edge X → Y on it, does X's text name something Y itself defines?
53 of 61 do; the eight that do not (the test, `served-catalog-join-number →
served-catalog-join`, `owner-commit-carried → config-owner-live`,
`owner-fault → owner-invariants`, `owner-invariants-outcome →
owner-invariants-served`, `peer-inbound → nntp-pinned-effects`,
`assumptions → byte-store-invariants`, `byte-store-invariants → frame`) use
something further down. The chain is mostly genuine: each book proves
something about the one below. Shortening it is proof engineering (which
book needs which), not a directory question. What is a tree question is the
per-book time on it: the ten slowest books on the chain hold about 165 s of
the 466. This lane's run had the same chain (60 books, `served-catalog-owner`
9.9 s and `catalog-entries` 9.5 s at its top).

Across the whole graph, 606 of 3,553 edges (17 %) are pass-through (the
includer names nothing the included book defines); in 509 of those the
includer uses something in the included book's closure (it includes Y to
get Y's includes), in 97 it uses nothing in the closure at all (a dead
include, or one kept for rewrite rules).

## 5. Experiments

### 5.1 Provisional certification against ordinary, matched

Workload: everything above `books/wildmat` and `books/frame-fields` after the
UTF-8 cut (5.2): 1,099 roots, 1,317 books in the closure, 179 installed
from persvati's cache, 1,138 certified. Same box, 20 jobs, same toolchain
(`w25/acl2-literal`), `--incremental --no-publish`, run back to back.

| | wall | summed book seconds | chain |
|---|---:|---:|---:|
| ordinary (`certify-20260928T195000Z-1826984`), 1,138 passed | **385 s** | 6,340 s | 384 s |
| provisional (`certify-20260928T193126Z-1687215`): Create | 594 s | 11,298 s | 589 s |
| provisional: Convert (the proofs, one parallel wave) | 305 s | 6,035 s | longest single book 26 s |
| provisional: Complete | 6 s | 109 s | 6 s |
| provisional total | **907 s** | | |

Per book, Create (proofs skipped) cost the same as ordinary certification
(median ratio 0.99; median 5.09 s against 5.52 s for the 899 books in both
this run and the pilot's), because the time is include-load, event
processing, the second pass, compilation and writing, none of which Create
skips. Its wave runs in dependency order, so its chain is the ordinary
chain. Provisional certification is therefore not a wall-time tool on this
tree; what it does buy is what the farm's docstring says: one Convert wave
names every failing book at once. (The Complete wave also refused to rename
`utf8.pcert1`, because a sub-book's certificate installed from another
worktree was older than its source: "does not have a .cert file that is at
least as recent as that included book". That is the write-date check the
docstring warns about, and it is one more reason the ordinary run is the
claim.) The farm's own earlier measurement, 690.8 s → 337 s on a 63-book
closure at 8 jobs, was a proof-heavy small closure; this one is the tree.

### 5.2 The UTF-8 decoder out of `wildmat` (plain lemma move, no machinery)

`books/frame-fields.lisp` (1,122 dependents) included `books/wildmat.lisp`
for `fn-wildmat-decode-aux` and `fn-wildmat-result-okp` alone, which put the
RFC 3977 glob matcher and everything above it in the frame codec's closure.
This lane moved the UTF-8 section (two constants, 21 definitions, four guard
lemmas, their `verify-guards`, one forward-chaining shape rule and the
withdrawn-rules `in-theory`) to `books/utf8.lisp`, unchanged and in order;
`wildmat` includes `utf8`; `frame-fields` includes `utf8` instead of
`wildmat`; the Makefile lists the new book. Names are unchanged (the
registries key on them). Check: the multiset of top-level forms of the old
`wildmat` equals that of the new `wildmat` plus `utf8`, less the new book's
`in-package`, `include-book "cbor"` and the `include-book "utf8"` (153 forms
→ 104 + 52). Commit `fba0991e3` on `lane/architect`.

| | before | after |
|---|---:|---:|
| dependents of books/wildmat | 1,137 | **738** |
| dependents of books/frame-fields | 1,122 | 1,122 |
| dependents of books/utf8 | | 1,138 |

The three books certify (persvati `certify-20260928T193052Z-1683117`) and
the whole affected closure, 1,138 books, certified with 0 failures
(`certify-20260928T195000Z-1826984`). `wildmat`'s remaining dependents come
through `nntp-syntax` (720) and `peer-config` (528), which use the matcher.
Simulated next cuts of the same kind, from the graph alone:

| cut | book | dependents before → after |
|---|---|---:|
| item layer (`read-uint`, `read-bytes`, item encode/decode, parse-groups) out of `records-invariants` into a book that `crypto-seam`, `config`, `bp-adu` and `native-control` include instead | records | 1,138 → 1,019 |
| | records-invariants | 1,122 → 1,002 |
| the 97 dead pass-through includes removed | (per book) | to be listed by the tool |

### 5.3 Quiet-box timings

Include-book of a certified book in a fresh ACL2 (persvati, idle, warm
cache):

| book | closure | events in closure | include-book |
|---|---:|---:|---:|
| (ACL2 startup, `(quit)`) | | | 0.03 s |
| books/cbor | 1 | 94 | 0.11 s |
| books/records | 5 | 339 | 0.12 s |
| books/config | 10 | 816 | 0.26 s |
| books/payload-arena | 20 | 1,300 | 0.35 s |
| books/hybrid-store | 47 | 2,284 | 0.49 s |
| books/store-node | 72 | 3,590 | 0.49 s |
| books/nntp | 92 | 5,446 | 2.86 s |
| books/nntp-auth | 150 | 8,889 | 3.95 s |
| books/served | 152 | 9,205 | 3.96 s |
| books/owner | 175 | 11,261 | 3.27 s |
| books/bp-native-app-fast | 189 | 11,639 | 2.64 s |
| books/served-catalog-owner | 269 | 15,319 | 6.72 s |

Over 18 books: `0.78 ms × definitions + 0.12 ms × theorems − 0.18 s` (R²
0.83); equivalently `0.37 ms × events` or `22 ms × books` (R² 0.83–0.84).

Certify-book of one book on the idle box, its closure's certificates in
place, with and without the compile step (`(certify-book B 0 t)` against
`(certify-book B 0 nil)`), against the same book's time inside a 20-job run:

| book | quiet, compile | quiet, no compile | of which proving | in this lane's 20-job run | in the pilot's 20-job run (persvati) | pilot, hbox 14 jobs |
|---|---:|---:|---:|---:|---:|---:|
| books/nntp-responses | 1.56 s | 1.51 s | 0.6 s | 6.1 s | — | — |
| books/served-catalog-owner | 4.15 s | 4.21 s | 1.2 s | 9.9 s | 12.9 s | 16.4 s |
| books/config-owner-live-read | 4.35 s | 4.27 s | 4.6 s | 15.6 s | 18.9 s | 21.8 s |
| tests/acl2/nntp-auth-fold-tests | 1.33 s | 1.31 s | 0.0 s | 4.1 s | — | 5.1 s |
| books/nntp-auth | 5.60 s | 5.46 s | 5.2 s | 14.5 s | 24.9 s | 46.2 s |

The compile step is a few percent. Under 20 concurrent jobs the same book takes 2.4 to 4.4 times its quiet time, and on the chain's heavy books the quiet time is mostly proving (`nntp-auth` 5.2 of 5.6 s, `config-owner-live-read` 4.6 of 4.4 s), while the median book of the tree proves little (section 5.1). So the chain is made of proof-heavy books slowed by contention, which is what a chain-first scheduler with fewer concurrent jobs attacks.

Recertifying an unchanged book twice gave byte-identical certificates. But a
tree whose dependents' certificates came from the cache (made in another
worktree) rejected a freshly recertified unchanged sub-book:
"its certificate requires the book … with book hash 939920419, but we have
included a version … with [another]". That is the closure key doing its job,
and the reason the timing sequence below reinstalls before each book.

### 5.4 Question 1 by simulation: local includes out of the key

The tree has 30 `(local (include-book …))` edges (of 3,553). Recomputing
every book's dependents with those edges removed from the key changes 34
books and removes 2,863 of 154,513 book-recertifications (1.9 %):

| book | dependents, key as today | key without local includes |
|---|---:|---:|
| statement-codec | 1,017 | 302 |
| article-properties | 643 | 14 |
| article-invariants | 646 | 17 |
| injection-invariants | 504 | 99 |
| records-canonicality | 1,001 | 647 |
| topic-history-identity-disjoint | 562 | 542 |
| store-node-invariants | 558 | 538 |
| store-node-invariants-base | 560 | 540 |
| cbor-invariants | 1,260 | 1,243 |
| records-invariants | 1,122 | 1,118 |

The local edges are the invariants books included locally by the towers
(`bp-ingress → article-properties`, `nntp-post → injection-invariants`, the
four `owner-invariants-*` → `injection-invariants`, `records-seam →
records-canonicality`, `statement-seam → statement-codec`).
`article-properties` was edited seven times in the window, all proof-only,
at 643 each.

### 5.5 The seam's ergonomics, from the pilot and the manual

The pilot's twins cost 6,677 + 3,213 + 1,119 prover steps for their guard
proofs (the correspondence), one `-by-definition` equation per attached
entry point (flagged definition-restated by the ledger, uncited), and a
constrained `fn-record-decode-exact` that the host calls. The manual's rules
that matter here: the attachment's guard must be implied by the constrained
function's guard and the constraints must be proved of the attachment; "we
do not use attachments during evaluation … especially [for] evaluation of
ground terms … during proofs", so `(fn-record-decode-exact <constant>)`
does not compute in a proof and a caller opens the `-by-definition` rewrite
instead; a `defattach` is never redundant.

## 6. Rule usage: which hub theorems anything downstream uses

From the 1,138 Convert logs of the provisional run (every `Rules:` and
`Hint-events:` summary line, per event, per book), joined with the graph.
"Used" means some dependent's proof reported the theorem as a rule it
applied or a hint named it. Books below `wildmat`/`frame-fields` have no log
in this run, so the last column says how many of a hub's dependents were
covered.

| hub | exported theorems | used by ≥ 1 dependent | dependents covered |
|---|---:|---:|---:|
| nntp-responses | 12 | 8 | 557 / 557 |
| config | 60 | 32 | 738 / 750 |
| byte-store-frame | 22 | 11 | 641 / 641 |
| payload-arena | 68 | 21 | 701 / 701 |
| assumptions | 2 | 2 | 751 / 751 |
| control-authority | 38 | 12 | 657 / 657 |
| hybrid-store | 14 | 6 | 952 / 952 |
| records | 23 | 4 | 1,049 / 1,137 |
| records-shape | 25 | 4 | 1,098 / 1,228 |
| records-invariants | 45 | 17 | 1,044 / 1,121 |
| frame-fields | 25 | 18 | 1,121 / 1,121 |
| wildmat | 17 | 8 | 737 / 737 |
| utf8 | 5 | 3 | 1,137 / 1,137 |
| cbor | 14 | 5 | 1,138 / 1,395 |
| cbor-invariants | 48 | 24 | 1,124 / 1,259 |
| article-properties | 42 | 3 | 627 / 642 |
| store-node | 122 | 63 | 659 / 659 |
| owner | 111 | 51 | 315 / 315 |
| nntp-post | 35 | 16 | 495 / 495 |
| nntp-auth | 114 | 47 | 481 / 481 |
| peer-inbound | 59 | 36 | 491 / 491 |
| store-node-invariants | 18 | 3 | 557 / 557 |
| config-invariants | 50 | 5 | 531 / 534 |

Roughly half of a hub's exported theorems are used by something downstream;
for the invariants books it is far fewer (`article-properties` 3 of 42,
`store-node-invariants` 3 of 18, `config-invariants` 5 of 50). Those are the
theorems that could live in leaves without anything noticing, with the map
as the check.

Applied to the window's edits: of the 124 proof-only edits that changed a
non-local theorem's statement, 76 changed a theorem some dependent uses
(37,678 book-recertifications; those recertifications were necessary) and 48
changed one nothing downstream uses (23,570; avoidable had the theorem been
in a leaf). The other 327 proof-only edits changed no theorem name
(`in-theory`, hints, local lemmas).

## 7. What ACL2 does, and what the community does

Read from the ACL2 8.7 sources under `/Users/ember/tools/acl2-fn/acl2-8.7/`
(paths relative to it) and the community books under its `books/`.

**The certificate and local includes.** `certify-book-fn`
(other-events.lisp, ~18118) takes the post-alist from pass 1's
`include-book-alist-all`; `mark-local-included-books` (11293) wraps every
book included in pass 1 but not pass 2 as `(LOCAL <entry>)`, with its hash
at certification time. When the book is later included,
`include-book-ok-familiar-name-and-hash` (13821) compares the hash of the
book itself only; `include-book-certified-p` (13964) checks the post-alist
after `unmark-and-delete-local-included-books` (11325) has dropped every
LOCAL entry; the raw `local` macro turns `(local …)` into `(mv nil nil
state)` under `ld-skip-proofsp 'include-book`, so the locally included book
is never read. **If A changes and B, which locally includes A, is not
recertified, ACL2 accepts B's certificate with no error or warning.**
Make-event expansions are frozen in the certificate (`:expansion-alist`) and
replayed on include, not re-run; the `ignored-attachment` topic shows on
purpose how a local `defattach` changes an exported definition through a
frozen expansion. So a key that ignores local includes gives stale, not
inconsistent, results: what the includer exports can drift from what the
current local book would produce.

**cert.pl.** `books/build/lib/Bookscan.pm` (174–200) records the `local`
flag; `Certlib.pm` (747–765) pushes every include, local or not, onto the
dependency list; `Depdb.pm` `cert_deps` returns all of them and that is
what the Makefile writer and `check_up_to_date` use. The non-local-only
variant is used once, to choose what to *load*. The community build system
recertifies an includer when a locally included book changes: today's farm
key is community practice.

**defattach.** The `defattach` topic lists three primary uses: constrained
function execution, sound modification of the ACL2 system, program
refinement. Nowhere does the manual recommend it for keeping an
implementation book out of dependents' closures; `mbe` is presented as the
way to "cause evaluation to use alternate code". The one "without
recertifying" feature in 8.7 is `defabsstobj :attachable` / `attach-stobj`.
`throw-or-attach` (axioms.lisp 5476) binds a fresh gensym as a special on
every expansion; a constrained function has two raw stubs (`intro-udf-lst2`,
defuns.lisp 11842, and the `*1*` function from `oneify-cltl-code-1`,
interface-raw.lisp 2008); SBCL's `*free-tls-index*` (code/thread-structs.lisp
18) is a counter nothing decrements, and a slot is taken the first time the
special is bound. A redundant include-book does not reload the compiled file
(`include-book-raw`, interface-raw.lisp ~6194); distinct top-level includes
each load once. `defun-nx-form` (other-events 8029) expands to
`throw-nonexec-error`, not `throw-or-attach`.

**Organisation.** No major community library uses api/impl/proofs
directories. `centaur/aignet` keeps `aignet-logic`, `aignet-exec`,
`aignet-exec-thms` and `aignet-absstobj` as file names in one flat directory,
the absstobj book including the exec book non-locally and the theorems
locally. `kestrel/lists-light` is one book per function with as few
non-local includes as possible. `rtl/rel11` is the classic "lib states,
support proves" split, done with `(set-enforce-redundancy t)` and `(local
(include-book "../support/top"))`: users get statements without proof
machinery in their world, and cert.pl still recertifies every lib book when
support changes. `std/lists/list-defuns.lisp` records the community moving
away from local-include-and-re-export "to really optimize things and avoid
having lots of dependencies". `mbe :logic` appears 5,350 times; `defattach`
461 times in 166 files, most of them hooks (`vl-load-read-file-hook`,
`svex-rewrite-trace`); the architectural seams are kestrel's crypto
`interfaces/` with `attachments/` included only by executable leaves, and
GL's `bfr-sat` whose SAT backend `bfr-satlink` attaches. Saved images with
books preloaded (`using-extended-acl2-images`, `.image` files, `save-exec`)
exist in cert.pl and only Milawa uses them; here they would not help, since
the foundation loads in a tenth of a second and the expensive closures are
the ones that churn.

## 8. The image

`host/native/build.lisp` and the 33 host files it `ld`s contain 373
top-level `include-book` forms naming 352 distinct books; their closure is
677 books carrying 12,108 theorems (of 16,458 non-local top-level theorems
in the tree), 15,036 definitions, 38 constrained signatures, 23 `defun-nx`,
14 `defabsstobj`. Only 35 books in that closure are proof-only (no non-local
definition), carrying 868 theorems: `frame-invariants` (66),
`lace-invariants` (62), `bp-fragment-invariants` (51), `config-owner-live-open`
(48), `cbor-invariants` (48), `records-invariants` (45), `article-properties`
(42) … Each is included non-locally by two to eleven definition books
inside the closure (`cbor-invariants` by `anchor`, `frame-octets`, `records`,
`byte-store`, …). The other 11,240 theorems live in mixed books. The TLS
cost is stubs × top-level includes that reach them; one umbrella book makes
it stubs × 1 with no book moved. A theorem costs about 0.12 ms to load;
nothing in the image proves.

## 9. Reproducing the numbers

Scripts in `planning/evidence/architect-2026-09-28/`, each run on a box
against a synced tree (`~/fn-gates/architect` on persvati,
`/tank/fn/scratch/architect` on hbox), never on the laptop:

- `closure_stats.py`: closure sizes, the seconds-on-closure regression
  against a manifest's `book_wall_seconds`, direct includers of named hubs.
- `critical_path.py`: depth, weighted critical path, the chain.
- `passthrough.py`: pass-through edges and the chain's edge uses.
- `classify_edits.py MIN_DEP`: the edit-kind classification over the git
  mirror (`~/fn-gates/remote-check.git`, ref `refs/remote-check/architect`).
- `simulate.py`: the local-include key simulation, the rewires, private
  against public definitions.
- `image_closure.py`: what the image loads.
- `rule_users.py RUN_DIR`: rule usage from a provisional run's Convert logs.
- `include_mix.py`: include-book time against the closure's composition.
- `compile_flag.sh`: certify-book with and without the compile step.

Manifests, tracked under `planning/evidence/manifests/`:
`certify-20260928T193052Z-1683117` (the three-book run),
`certify-20260928T193126Z-1687215` (the provisional run),
`certify-20260928T195000Z-1826984` (the ordinary run), all persvati. The dependents
table came from `python3 tools/shape_books.py --json --top 3000` on persvati;
the three-day edit list from `git log origin/dev --no-merges
--since=2026-09-25T00:00Z --name-only -- books/`.
