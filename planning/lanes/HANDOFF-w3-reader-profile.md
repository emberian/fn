# Handoff: w3/reader-profile (C1-07, the selected reader profile)

HEAD at writing: see `git log -1` on branch `w3/reader-profile`, worktree
`build/lanes/w3-reader-profile`, branched from `dev` at `9321344`.

## What changed

RFC 3977 appendix B is the authority on which commands a capability label
covers, and `specs/nntp-audit.md` had it wrong: it claimed READER requires HDR,
NEWNEWS, OVER and POST. It does not. READER covers exactly **ARTICLE, BODY,
DATE, GROUP, LAST, LISTGROUP, NEWGROUPS, NEXT**; HDR, NEWNEWS, OVER and POST
each indicate their own capability, LIST ACTIVE/NEWSGROUPS belong to LIST, and
LIST OVERVIEW.FMT to OVER. That error is what kept the label unadvertised after
most of the bundle already worked. The matrix is corrected and the label is now
advertised, together with `OVER MSGID` and
`LIST ACTIVE NEWSGROUPS OVERVIEW.FMT`.

- **Reader environment.** `fn-nntp-step` takes a new fourth argument,
  `(:fn-nntp-env observation facts)`: one `fn-clock-observationp` and a list of
  `(:fn-nntp-group-fact name created-at-dtn-ms observation)` records. A creation
  fact carries the observation it was established under, so a creation time can
  never be back-filled from the reader's current clock. The mutable-owner lane
  persists these; this book consumes the shape. `fn-nntp-unix-dtn-ms` does the
  POSIX-to-DTN epoch shift **in ACL2**; `tools/run_reader.py` only reads a clock
  and passes the raw reading to `fn-reader-chunk`.
- **DATE (§7.1).** `111 yyyymmddhhmmss` from the observation's wall reading.
  With `has-wall` false the reply is `503 server holds no wall clock reading` —
  stated, never a fabricated timestamp. The calendar is Hinnant's closed-form
  `civil_from_days`, so DATE costs the same whatever the clock reads, and every
  rendered digit is a table lookup (`fn-nntp-digit-octet`), which is why the 111
  line is response text with no arithmetic book.
- **NEWGROUPS (§7.3).** Both date forms with §7.3.2's century rule; a two-digit
  year with no wall reading is `503`, not a guess. hhmmss with the leap second.
  Optional GMT in third position only. fn's local zone **is** UTC and the
  protocol cannot convey another; that is stated as local policy.
- **MODE READER (§5.3).** Non-mode-switching, MODE-READER never advertised:
  `201 posting prohibited`, no state change. One constant,
  `*fn-nntp-advertise-readerp*`, decides both the capability list and this
  response, so they cannot disagree.
- **OVER / LIST OVERVIEW.FMT (§§8.3, 8.4).** All three OVER forms. Fields come
  from the proved `fields` view (`books/article.lisp`, `books/article-fields.lisp`);
  the reader parses no article a second time and stores no overview database.
  Xref is omitted, so exactly eight fields are emitted and OVERVIEW.FMT lists
  exactly the seven fixed lines.
- **`books/nntp-overview.lisp`** (new) holds the §8.3.2 theorems that
  `books/nntp-effects.lisp` consumes. Layering is `nntp -> nntp-overview ->
  nntp-invariants -> nntp-effects`.

## Clause matrix summary (specs/nntp-audit.md, "The READER clause matrix")

Twelve rows over the READER bundle and the advertisement rule:
**proved 5** (GROUP cursor placement, LISTGROUP order/reset, LAST/NEXT movement,
message-id session preservation, one-owner advertisement),
**tested 6** (ARTICLE/BODY argument forms and 412/420/423/430 precedence, the
DATE line, both NEWGROUPS date forms with the century rule, the NEWGROUPS block
format, the no-clock refusals),
**open 1** — and it is an *assurance* gap, not a missing branch: no theorem says
the §6.1.1.2 211 count satisfies the estimate bounds. fn's count is exact and
the transcripts pin it; the theorem does not exist. The DATE civil conversion is
likewise tested (epoch, leap day, the profile's own boundaries) and not proved.
Both are the honest reasons the profile is "advertised with evidence", not
"conformant".

New proof events, by book:
- `books/nntp-overview.lisp`: `fn-nov-scrub-is-clean` (unconditional — the
  §8.3.2 transformation is total), `fn-nov-header-content-is-clean`,
  `fn-nov-missing-header-is-empty`, `fn-nov-bytes-is-the-retained-octet-count`,
  `fn-nov-lines-counts-the-retained-body-lines`, `fn-nov-line-is-a-clean-line`,
  `fn-nov-lines-for-numbers-are-clean`.
- `books/nntp-effects.lisp`: `fn-nntp-clean-line-is-response-text` and
  `fn-nntp-clean-lines-are-block-text` bridge those into the response grammar;
  `fn-nntp-effects-{over-current,over-range,over-msgid,over-response,date-response,mode-response,newgroups-response,list-overview-fmt}`;
  `fn-nntp-date-octets-{is-response-text,is-a-status-line,length}`;
  `fn-nntp-facts-since-are-facts`.
- `books/nntp-invariants.lisp`: `fn-nntp-{date,mode,newgroups,list-overview-fmt,over}-*-preserves-session`.

**No new hypothesis was added to any keystone.**
`fn-nntp-step-effects-well-formed` and
`fn-nntp-step-preserves-consistent-session` cover every new branch under exactly
the hypotheses they already had. An `fn-nntp-envp` hypothesis was written and
then removed: `fn-nntp-facts-since` screens each fact itself, so the hypothesis
would have had no teeth. `tests/acl2/nntp-reader-profile-tests.lisp` pins that
with a forged environment that is not an `fn-nntp-envp` and still produces a
well-formed reply.

## Evidence

- ACL2 books changed: `books/nntp.lisp`, new `books/nntp-overview.lisp`,
  `books/nntp-invariants.lisp`, `books/nntp-effects.lisp`. Test books:
  `tests/acl2/nntp-tests.lisp`, `tests/acl2/nntp-teeth-tests.lisp`, new
  `tests/acl2/nntp-reader-profile-tests.lisp` (appended to `ACL2_BOOKS` after
  `tests/acl2/nntp-teeth-tests`, as the packet requires).
- `python3 tools/ledger.py --write` run; `make check` green (104 Markdown files,
  50 requirements, 18 proof targets, 18 scenarios).
- Python: `tests/test_reader.py` gains
  `test_reader_profile_transcript_over_a_real_socket`, a raw-octet transcript of
  MODE READER, LIST OVERVIEW.FMT, GROUP, OVER (current, open range, message-id,
  reversed range), NEWGROUPS (three forms) and DATE over the real socket
  adapter. `tests/interop_nntplib.py` (needs `/opt/homebrew/bin/python3.12`;
  3.14 dropped `nntplib`) now exercises `date()`, `newgroups()`,
  `getoverviewfmt()`, `over()` by range and by message-id, and `mode_reader()`,
  and asserts the exact capability set.

### Certification status

Rebased onto the realigned tree on 2026-09-19 (`git merge dev` into
`w3/reader-profile`; base `05679a4`, dev `0714151`) and certified for the first
time. The lane's additions were re-applied onto the five-book split of
`books/nntp.lisp` (nntp's CHANGE of 2026-09-19):

- **`books/nntp-responses.lisp`** now carries every reader-profile response
  builder: the environment record, the civil calendar, DATE, NEWGROUPS, the
  §8.3.2 overview renderers (`fn-nov-*`), OVER, LIST OVERVIEW.FMT and MODE
  READER. All of them are withdrawn at that book's export event under the
  existing `fn-nntp-responses-vocabulary`.
- **`books/nntp.lisp`** carries only the dispatcher edits: the `OVER` and
  `NEWGROUPS` disjuncts in `fn-nntp-archive-keywordp`, the `MODE` and `DATE`
  clauses in `fn-nntp-session-command`, the `OVER` and `NEWGROUPS` clauses in
  `fn-nntp-archive-command`, and the `env` argument threaded through
  `fn-nntp-step`, `fn-nntp-command`, `fn-nntp-session-command` and
  `fn-nntp-archive-command`.
- **`books/nntp-overview.lisp`**, **`nntp-invariants`**, **`nntp-effects`** and
  the three test books each carry the prescribed
  `(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
  fn-nntp-projection-vocabulary fn-nntp-responses-vocabulary
  fn-nntp-vocabulary)))` line.

No keystone statement changed in the rebase. Five defects the uncertified lane
carried were fixed, each of them a certification-only failure:

1. **Forward reference.** `fn-nntp-list-unmaintained-response` answered
   `LIST OVERVIEW.FMT` with `fn-nntp-list-overview-fmt`, which the lane defined
   600 lines further down. `*fn-nov-fmt-lines*`, `fn-nov-fmt-octet-lines` and
   `fn-nntp-list-overview-fmt` now sit immediately above that function; likewise
   `*fn-nntp-advertise-readerp*` now sits above `fn-nntp-capabilities`, which
   reads it.
2. **`zp` under `:guard t`.** `zp`'s own guard is `(natp n)`, so `fn-ng-take`
   and `fn-ng-nthcdr` owed `(natp n)` they could not discharge. `(not (posp n))`
   is `zp`'s value on every input and `posp` has guard `t`.
3. **Eager guard verification.** A book whose `(verify-guards ...)` all sit at
   the end needs `:verify-guards nil` on every `:guard`-bearing defun;
   thirty of the lane's did not have it, so they tried to verify against callees
   whose guards were still deferred.
4. **`<=` on an unconstrained threshold.** `fn-nntp-facts-since` compared with
   `<=` under guard `t`; it now uses `fn-ng-less-equal`, whose equality with
   `<=` is `fn-ng-less-equal-is-less-equal` in `books/nntp-syntax.lisp`.
5. **The field-lookup guard.** `fn-nov-get-headers-car-is-a-field` needed an
   induction lemma over `fn-article-get-headers-aux` and a `true-listp`
   conjunct; both are `local` in `books/nntp-responses.lisp`, and the two
   `verify-guards` that use them keep `fn-article-get-headers` and
   `fn-article-syntax-p` closed so the lemma can fire.

Certification evidence (this laptop, ACL2 8.7/SBCL,
`FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py <book>`, one root
at a time, after `make certs-install`):

| book | verdict | evidence dir |
| --- | --- | --- |
| `books/nntp-syntax`, `nntp-session`, `nntp-projection` | certified (unchanged; installed cert kept) | `make certs-install` |
| `books/nntp-responses` | **certified** (export list is the union with dev's POST names) | `build/acl2/certify-20260920T015332Z-13805` |
| `books/nntp` | **certified** | `build/acl2/certify-20260920T015342Z-13993` |
| `books/nntp-overview` | **certified** | `build/acl2/certify-20260920T015343Z-14022` |
| `books/nntp-invariants` | **certified** | `build/acl2/certify-20260920T015349Z-14111` |
| `books/nntp-effects` | **certified** | `build/acl2/certify-20260920T015430Z-14448` |
| `books/injection`, `books/injection-invariants` | certified (dev books, recertified here because their certificates were foreign-local) | `build/acl2/certify-20260920T015727Z-37770`, `build/acl2/certify-20260920T015728Z-37777` |
| `books/nntp-post` | **certified** (522 s; the two keystone `:instance` hints bind `env`) | `build/acl2/certify-20260920T015941Z-67428` |
| `books/served` | **certified** (dev's byte fold, unchanged) | `build/acl2/certify-20260920T020824Z-80057` |
| `books/ideal` | certified (dev's file; this branch's `env` port argument dropped) | `build/acl2/certify-20260920T021106Z-81875` |
| `books/nntp-index` | certified | `build/acl2/certify-20260920T021107Z-81884` |
| `tests/acl2/nntp-tests` | **certified**: `*fn-nntp-caps*`, the IHAVE 500 and the POST 340/begin-article pins re-quoted from `ld` | `build/acl2/certify-20260920T021242Z-82609` |
| `tests/acl2/nntp-teeth-tests` | **certified** | `build/acl2/certify-20260920T021243Z-82618` |
| `tests/acl2/served-tests` | certified (dev's file) | `build/acl2/certify-20260920T021244Z-82627` |
| `tests/acl2/nntp-post-tests` | certified (one `fn-nntp-step` call given `(fn-nntp-env *fn-tp-obs* nil)`) | `build/acl2/certify-20260920T021246Z-82687` |
| `tests/acl2/nntp-index-tests` | certified | `build/acl2/certify-20260920T021248Z-82694` |
| `tests/acl2/nntp-reader-profile-tests` | **certified** (the leap-day pin read 11015 for 2000-02-29; 11016 is right and `days-from-civil` is now pinned to agree) | `build/acl2/certify-20260920T021728Z-8989` |

**The open root, closed 2026-09-20.** `books/nntp-overview.lisp` failed to certify on 2026-09-19: the shape lemma
`fn-nov-overview-is-an-overview`

```lisp
(defthm fn-nov-overview-is-an-overview
  (implies (fn-nov-okp (fn-nov-overview article))
           (fn-nov-overviewp (fn-nov-overview article))))
```

splits `Goal'` into **2056 subgoals** (`:DOC splitter` names
`fn-article-parse`, `fn-article-syntax-p`, `fn-nntp-split-article` and
`fn-nov-value-content` as the if-introducers) and exhausts the 1800-second
budget. ACL2 also warns that the rule can never fire, both its trigger symbols
being non-recursive and enabled. The lemma is not one of the seven §8.3.2
keystones this book exists for; it is a shape bridge between them. The next
owner should close it by keeping `fn-article-parse`, `fn-article-syntax-p`,
`fn-nntp-split-article` and `fn-nov-value-content` **disabled** in its hint and
proving it in accessor vocabulary, or remove it and repair whatever in
`nntp-invariants`/`nntp-effects` cited it. Until then no verdict exists for
`nntp-overview`, `nntp-invariants`, `nntp-effects` or the three test books, and
this lane's theorems are statements of what the books say, not of what ACL2 has
checked. The clause matrix rows that cite `nntp-reader-profile-tests.lisp` are
therefore **unverified** in this tree.

**Finisher pass, 2026-09-20 (branch `w3/reader-profile`, merged with dev `d83dea5`).**
The three model books certify; the test roots do not yet, so every clause
matrix row that cites a test book is still **unverified** and no row moved.
Open, in order: (1) re-pin `*fn-nntp-caps*` in `tests/acl2/nntp-tests.lisp`
and certify the seven remaining roots; (2) `python3 -m unittest tests.test_reader
tests.test_reader_partitions tests.test_served_differential` ran 11 tests,
2 failures and 11 errors, all because the host cannot load the uncertified
`books/served`; no `ACL2 prompt timeout` (the anchor-host `(logic)` fix is on
dev, not yet merged here); (3) the nntplib probe was not run: it needs a port
from a separately started `tools/run_reader.py`; (4) dev has since merged
`w4/post` and `w2/mutable-owner`: its `fn-served-step` is a byte fold over a
five-field conn `(fn-served-make-conn wire session archive config observation)`
and its `fn-nntp-step` is still `(session archive wire-event)`, so the merge of
this branch builds `(fn-nntp-env observation facts)` from the conn at dispatch
and passes it as `fn-nntp-step`'s third argument; `fn-served-nntp-run` and the
`env` argument this branch threads through `fn-served-step`/`fn-served-run` are
gone on dev. Cross-cluster proposal: `books/article.lisp` and `books/wildmat.lisp`
export `fn-article-nonempty-true-list-is-consp` and five `*-true-listp`
backchaining rules enabled; two books here withdraw them locally with the
accumulated-persistence figures; their exports should (proof-style section 8).

The clause matrix in `specs/nntp-audit.md` is unchanged by the rebase: eleven
rows, four **proved** plus one **proved by construction**, six **tested**, one
**stated local policy**, and the §6.1.1.2 count theorem **open**.


**Integration pass, 2026-09-20 (merged with dev `b7f106b`, HEAD in `git log -1`).**
Every root above certifies. The seam: dev's `fn-served-dispatch` calls
`fn-nntp-post-step (ps archive config observation wire-event)`, whose
signature is unchanged; it hands `fn-nntp-step` the environment
`(fn-nntp-env observation nil)`, the connection's pinned clock observation
and an empty fact list, because the five-field served conn carries no
creation facts (proposal 3 below now covers the seed path too: the host's
`*fn-reader-seed-facts*` and `fn-reader-facts` global are gone, and the
socket transcript expects the empty NEWGROUPS block). `fn-served-step (conn
octets)`, `fn-reader-chunk (octets state)` and `tools/run_reader.py` are dev's
shape. Python: 32 tests, 30 pass; the two failures are dev's store-backed
`test_post` read-back cases (`211 1 1 1` after 240): the served conn pins its
archive at open, `reselect` refreshes only the host global, and no host line
re-pins the connection, so a post is invisible on the connection that made
it. That is dev's seam (w4/post handoff recorded these cases as dying in
`setUp` before the anchor-host fix, never as passing), not this lane's.
nntplib probe: `tests/interop_nntplib.py` "status": "passed" (stdlib nntplib on python3.12: DATE, NEWGROUPS both ranges, LIST OVERVIEW.FMT, OVER by range and by message-id, MODE READER, exact capability set).

## Proposals for root

1. **Prove the §6.1.1.2 count row.** It is the only open READER clause and the
   statement is small: the emitted 211 count equals the number of available
   articles, which lies between 0 and `high - low + 1`.
2. **Prove the civil calendar**, or state it as a named assumption. It is the
   one piece of DATE that only transcripts hold up. `days_from_civil` and
   `civil_from_days` are mutually inverse on the representable range; that is
   the theorem, and it probably needs an arithmetic book this build refuses.
3. **Owner-side creation facts.** `host/reader-host.lisp` carries one seed fact
   and the store path carries none, so NEWGROUPS over a real store reports an
   empty list rather than an invented date. C1-05 should persist real
   `fn-nntp-group-factp` records and hand them to `fn-reader-env-from`.
4. **A fresh observation per command.** The adapter observes the clock on every
   `fn-reader-chunk`, which is right, but nothing forces the host to. Consider
   making the environment an explicit argument at the listener boundary so a
   stale observation is a type error rather than a policy slip.
5. **`fn-article-parse` implies `fn-article-syntax-p`.** `fn-nov-overview`
   discharges its guard with a runtime `fn-article-syntax-p` check, costing one
   extra linear pass per projected article. That theorem would remove it.
