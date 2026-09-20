# Evidence record: the realignment and server waves, 0bd0b5c to c8886ee

What this records: the proof-style realignment of every book cluster
(seven deputies, 2026-09-19) and the four server-facing waves that followed
(w2, w3, w4, w5), as landed on `dev` between `0bd0b5c` and `c8886ee`.

This is an evidence record in the sense of
[the validation plan](../../tests/README.md#evidence-record): it names the
revision, the tool versions, the exact runs, the results, and what was not
exercised. It certifies nothing itself. **No ACL2 process was started by the
lane that wrote this file**; every number below is read out of a manifest, a
log, or a lane report, and each is cited to the file it came from.

| fact | value | source |
| --- | --- | --- |
| commit range | `0bd0b5c`..`c8886ee`, 319 commits | `git log --oneline 0bd0b5c..c8886ee \| wc -l` |
| tree at the record | `dev` `c8886ee` (merge of `w4/tcpcl`) | `git log` |
| newest gated revision | `dev` `7a9e89a` | persvati `~/fn-gates/dev-7a9e89a/` |
| ACL2 | Version 8.7, `saved_acl2` sha256 `c8a7a804…5c8163` | gate manifest `acl2_version`, `acl2_executable_sha256` |
| host Lisp | SBCL 2.6.8 | gate manifest `host_lisp_banner` |
| gate platform | `Linux-6.17.0-40-generic-x86_64-with-glibc2.42`, Python 3.13.7 | gate manifest `platform`, `python` |
| laptop | macOS 26.6.1, Python 3.14.7, `acl2` at `/opt/homebrew/bin/acl2` (ACL2 8.7) | `sw_vers`, `python3 --version`, `which acl2` |

## 1. The farm gate

Manifest: persvati
`~/fn-gates/dev-7a9e89a/build/acl2/certify-20260920T024318Z-1528458/manifest.json`.
Read-only; not copied into the repository.

| gate | roots requested | success markers observed | status | wall |
| --- | --- | --- | --- | --- |
| `dev-7a9e89a` certify | 213 | 210 | `failed` | 940.259 s at `jobs=16`, `timeout_seconds=1800` |
| `dev-7a9e89a` pytests | — | `Ran 331 tests in 564.479s` | `FAILED (failures=3, errors=4, skipped=4)`, `exit=1` | 564.5 s |
| `dev-bdd59d2` certify | (in flight) | — | no `manifest.json` written | evidence dir `certify-20260920T032713Z-1926256` has per-book logs only |
| `dev-bdd59d2` pytests | — | — | no `pytests.log` | — |

`acl2_exit_codes` holds no nonzero entry: the three missing roots are missing
success markers, not crashed processes. Failing roots, by index of the missing
marker in `expected_success_markers`:

| failing root | owner | cause |
| --- | --- | --- |
| `books/owner` | w2/mutable-owner (owner cluster) | §3 defect 2 |
| `books/owner-invariants` | w2/mutable-owner | behind `books/owner` |
| `tests/acl2/owner-tests` | w2/mutable-owner | behind `books/owner` |

Summed per-book wall in that run is 3779.1 s against 940.3 s of wall clock at
sixteen slots (`book_wall_seconds`). The five costliest roots:
`books/bp-primary-invariants` 592.5 s, `books/article-properties` 566.1 s,
`books/nntp-post` 520.4 s, `books/bp-release-invariants` 391.3 s,
`books/bp-receiver-evolving-store-invariants` 224.7 s.

**Scope of the gate, stated because it is smaller than the tree.** The gate's
213 requested roots are the Makefile roots at `7a9e89a`. `dev` at `c8886ee`
has 221 roots ([`ledger.md`](../ledger.md)). The eight roots added after
`7a9e89a` — `books/scheduler`, `books/scheduler-invariants`,
`tests/acl2/scheduler-tests`, `books/tcpcl-records`, `books/tcpcl-octets`,
`books/tcpcl-session`, `books/tcpcl-invariants`, `tests/acl2/tcpcl-tests`, and
the two `nntp-legacy` roots — **have no farm-gate result at all**; their
evidence is the single-laptop certification recorded in each lane's handoff.
Nothing in this record claims a farm gate for them.

### The seven Python failures of the gated revision

From `~/fn-gates/dev-7a9e89a/pytests.log` (grep `^(FAIL|ERROR):`), four errors
and three failures, all in the owner/post/campaign area:

- `test_owner.OwnerTests` — four errors
  (`test_a_killed_owner_reopens_with_every_completed_post_durable`,
  `test_a_stalled_reader_does_not_block_a_post`,
  `test_clock_and_group_facts_go_through_the_owner`,
  `test_two_readers_keep_their_pins_across_a_post_until_advanced`); the owner
  books do not include, so the service does not start.
- `test_post.StorePostTests.test_post_reaches_240_and_the_article_can_be_read_back`
  — `211 1 1 1 fn.letters` where `211 2 1 2 fn.letters` was expected.
- `test_host_boundary.OwnershipAndOrphanTests.test_initialization_publishes_metadata_through_staging`.
- `campaign.test_campaign.CampaignTests.test_the_campaign_reports_no_failure`.

`23ffb83` and `886272b` land after `7a9e89a` and address the last two; no
gate has re-run since, so this record does not call them fixed.

## 2. What changed, per cluster, with the measured numbers

Ownership is [the cluster table](../deputies/CLUSTERS.md); the reports are
under [`planning/deputies/`](../deputies/BRIEF.md). "Before" and "after" are
each report's own measurement, and the two are **not always the same machine**
— where they are not, the report says so and so does the row.

| cluster | roots | certify wall before → after | the number's provenance |
| --- | --- | --- | --- |
| [core](../deputies/core.md) | 17 (was 25) | 182.8 s → 8.3 s | both `tools/certify_books.py`, laptop; `certify-20260919T192410Z-35697` |
| [store](../deputies/store.md) | 28 | per-root, below | before: persvati `dev-0a16592` `book_wall_seconds`; after: laptop |
| [codecs](../deputies/codecs.md) | — | per-root, below | laptop |
| [nntp](../deputies/nntp.md) | — | `nntp-invariants` 393.5 → 200.6 s; `nntp-effects` 62.5 → 34.2; `wire` 5.5 → 1.3; `nntp-tests` 3.6 → 0.4 | before farm, after laptop |
| [bp](../deputies/bp.md) | 27 | 1437.9 s → 1159.2 s | before persvati `dev-0a16592`, after laptop |
| [substrate](../deputies/substrate.md) | 18 | — (cache was empty; from-source) → 262 s | laptop, one root at a time |
| [tooling](../deputies/tooling.md) | 0 books touched | — | no ACL2 process started |

Store per-root (its report's table): `store-files` 42.9 → 2.6 s,
`store-files-invariants` 16.6 → 7.1, `store-node-invariants` 79.4 → 66.5,
`store-node-resolution` 3.6+0.5 → 1.1, `store-observed` 6.9+0.6 → 1.0,
`checkpoint` 1.1 → 2.4 (up), `index` 0.28 → 0.54 (up).
BP per-root: `bp-workflow-binding-core` 136.1 → 30.8,
`bp-workflow-records-invariants` 7.3 → 0.6, `bp-fragment-invariants` 35.6 →
23.9, `bp-release-invariants` 427.4 → 366.3, `bp-primary-tests` 505.6 → 0.9,
and one regression: `bp-primary-invariants` 251.1 → **676.7**, which the report
attributes to its local enable of the three CBOR vocabularies and leaves open.
Substrate's own two costs, unimproved: `books/policy` 143 s and
`books/statement-invariants` 76 s of the cluster's 262 s.

### Rules withdrawn

- core: exported enabled rules 172 → 164, of which 78 are now record lemmas, so
  non-record exported rules 172 → **86**; 61 proof-vocabulary lemmas withdrawn
  under five `deftheory` names; `:rule-classes nil` 0 → 18; SUSPECT-by-shape 12
  → 9; `minimal-theory` hints 2 → 0 ([core report](../deputies/core.md)).
- codecs: every book in the cluster ends with an explicit theory event, and the
  withdrawal names individual rules rather than a `deftheory` name so
  `tools/ledger.py` can see them. Measured reason (its §3.1b citation): the four
  `len`-backchaining frame rules plus the two value predicates cost one `append`
  associativity goal 108 s, and `fn-id-hex-octets-are-octets` 619 s.
- w5-article-exports (after the deputies, board entry 2026-09-20): seven rules
  withdrawn at the export — four `fn-article-*` and three `fn-wildmat-*` — and
  five re-exported as `:forward-chaining` shape facts only. Measured on
  persvati at 12 jobs, the same 22 roots twice, back to back on an idle box:
  whole closure **600.4 s → 112.1 s**; `books/article-properties` 494.1 → 1.8;
  `books/article-invariants` 105.7 → 1.1; `books/nntp-overview` 5.9 → 1.0;
  `books/nntp-responses` 8.8 → 1.1. No keystone statement, hypothesis or rule
  class changed, and no includer needed an edit
  ([BOARD](../deputies/BOARD.md), 2026-09-20 w5-article-exports).

### Recognizers off the served paths

Whole-state recognizer calls on the executable path (review finding D3): core
**10 → 0** (acceptance 662/695/720, node 229/283 and its test, retention
admissibility and release, exchange admissibility, the replay loop 144/153 and
advance); store **24 → 0** (fifteen `fn-sf-*` transitions, five `fn-sn-*`, the
two resolution gates, `fn-sn-open-observed` twice). Both clusters carry the
invariant under `mbe` with the original total `:logic` bodies, so no keystone
statement moved.

### Teeth converted

`must-fail` forms whose body was a bare `thm` are replaced by concrete
`assert-event` counterexamples on the negated conclusion, under
`with-guard-checking :none` where the witness is outside a guard: core (five
test books folded from fourteen), store (five test books), codecs (four test
books drop `std/testing/must-fail`). Two measured reasons to prefer the
witness: a codecs `must-fail` "refuted nothing and looped with the seal rules"
([codecs report](../deputies/codecs.md)), and a substrate one cost 219.5 s of
prove time, hit the step limit and refuted nothing in particular
([substrate report](../deputies/substrate.md)). Current
[`ledger.md`](../ledger.md) counts 3936 `assert-event` and 59 `must-fail`
checks, with the teeth-form lint at **0**.

## 3. Defects the lanes found, each with its cause

1. **The `article-properties` include.** `books/bp-ingress.lisp` carried a
   *non-local* `(include-book "article-properties")` added for one theorem
   cited in two guard hints. `article-properties` had no export theory, and
   `fn-article-successful-parse-input-octets` concludes over a bare variable, so
   every `fn-cbor-octet-listp` and `len` goal above `bp-ingress` backchained
   into the enabled parser: 1.92M frames, 20,384 tries, **0 useful**, inside the
   first 2M steps of one form. `books/bp-receiver-evolving-store-invariants`
   went from six minutes to the 1800 s timeout. With every `article-properties`
   rule withdrawn the book runs in 7.7 s on `ld`. Fix: the include is local; the
   book ends with an export theory ([bp report](../deputies/bp.md)). This is the
   defect the include-hygiene lint was written for.
2. **The served-conn arity.** `books/owner.lisp:461` calls `fn-served-open` with
   three arguments; `books/served.lisp:668` declares five
   (`archive line-limit body-limit config observation`), and
   `fn-served-make-conn` likewise grew to five. `fn-own-read-step` also calls
   `fn-nntp-step` with three where it now takes four (the `fn-nntp-env`). Three
   independent sightings: as a red root (w5-article-exports), as "`fn run` and
   `tools/run_owner.py` cannot start at all" (w5-fn-cli), and as "the service
   does not start on a farm box" (w5-deploy-gate). It is the whole of the gate's
   210/213 and of the four `test_owner` errors. Still open; see §4.
3. **The lost `@property`.** `tools/run_store.py` `config_record_path` lost its
   `@property` decorator in the config-records merge, which broke `run_store`
   initialization on `dev` (board 2026-09-20 w2/mutable-owner; commits
   `27d1077`, `6304db6`, `69b5a5a`).
4. **The `:program`-mode leak.** `fn-reader-chunk` in `host/reader-host.lisp`
   was `:program` mode and consumed at most one wire event, with a
   `while pending:` loop in `tools/run_reader.py` supplying the rest; together
   they computed `fn-wire-drive` then `fn-nntp-step` per event and **no theorem
   said so** — the wire `pending_subject` note. `fn-reader-effect-octets` and
   `fn-reader-close-effectsp` made the host a second owner of the reply framing.
   `books/served.lisp` replaces all three with one logic-mode, guard-`t`
   function the host calls once per socket read
   ([w4/served-path handoff](../lanes/HANDOFF-w4-served-path.md)).
5. **The identity twin in the campaign.** The fault campaign derived the
   enqueue identities in Python beside ACL2's derivation — the review's twins
   finding. `886272b` asks ACL2 for them instead.
6. **String-vs-octet host records.** `fn-sched-host-decision-octets`
   (`host/scheduler-host.lisp:82-85`) handed `fn-sched-decision` a contact peer
   that `fn-sched-contactp` types as `stringp`, plus `work-id`/`attempt-id` that
   `tools/scheduler.py` marshals as string literals, so **the host's own
   decision record came back `:bad`**. Fixed at that one site with
   `fn-record-string-octets`; `tests/test_scheduler.py::Acl2HostRecord` drives
   the wrappers through the bridge and asserts the protected octets
   (`5995eff`; board 2026-09-20 w3-scheduler).
7. **Five false statements in the configuration cluster.**
   [HANDOFF-w4-config-records](../lanes/HANDOFF-w4-config-records.md) heads the
   paragraph "Three statements were false as written" and then names five:
   `fn-cfg-groups-create-keeps-the-names-or-adds-one` and
   `fn-cfg-group-find-nil-means-not-a-name` (need `fn-cfg-group-listp`; witness
   `es = (nil)`, `name = nil`), `fn-cfg-groups-retire-preserves-group-listp`
   (needs the entry live at `gen`), `fn-config-replay-loop-generation-counts-records`
   (needs a numeric starting generation), and
   `fn-config-aware-loop-is-fn-config-replay-on-config-only-histories` (needs
   the configuration replay not to fault). The count in that prose is wrong and
   the list is right; each correction is an `assert-event` counterexample in
   `tests/acl2/config-tests.lisp`.
8. **Two false statements in the scheduler.**
   `fn-sched-promoted-work-is-selected-within-its-position` and
   `fn-sched-aging-bound` were false as stated from `a018394` on: at `n = 1/2`
   every run predicate is `t` (`(zp (nfix 1/2))`), `(< 0 1/2)` holds and
   `fn-sched-selected-withinp` is `nil`. Both now bound the position by
   `(nfix n)`, the horizon the run predicates actually count; the witness is
   evaluated in `tests/acl2/scheduler-tests.lisp`. No includer outside the
   cluster cites either ([HANDOFF-w3-scheduler](../lanes/HANDOFF-w3-scheduler.md)).

Both 7 and 8 are corrections, not weakenings: each has an exhibited
counterexample, which is stronger evidence than "ACL2 could not prove it".

## 4. Open

- **`books/owner` and its two roots.** Defect 2 above. The fix is the owner's:
  pin config and observation into the served conn, and pass
  `(fn-nntp-env (or (fn-own-clock o) blind) facts)` — the owner is the one
  record that carries `facts`. Until it lands, the concurrent server does not
  run, so no run of the deploy gate establishes that a reader's pinned snapshot
  survives another connection's POST.
- **The owner's three one-line host edits.** From w5-config-groups
  ([BOARD](../deputies/BOARD.md), 2026-09-20): `host/owner-host.lisp` line 40
  (replay the configuration records before `fn-sn-open-observed` and pass
  `(fn-cnode-domain cn)` and the configured capacity) and lines 79 and 179
  (`fn-store-groups-from-codes` takes the node's own group list, and staging
  refuses unless `fn-cnode-selection-servedp`). That lane did not edit the file.
- **tcpcl C2.** `books/tcpcl-invariants` is OPEN at
  `defthm fn-tcl-final-ack-means-every-segment`
  (`build/acl2/certify-20260920T022251Z-39001`, 14.03 s to the failing form);
  `tests/acl2/tcpcl-tests` is behind it. C2's equality has the variable `id` on
  its left, which ACL2 refuses as a rewrite rule, so it is `:rule-classes nil`
  and cited by `:use`; the statement is unchanged. Every entry of the
  `specs/tcpcl.md` §5 clause matrix that names a C1–C4 keystone is a **proposed**
  theorem until invariants certifies
  ([HANDOFF-w4-tcpcl](../lanes/HANDOFF-w4-tcpcl.md)). C1's hypotheses also have
  no separating witness.
- **The peering K1–K3 seam.** [DESIGN-peering-summary](../lanes/DESIGN-peering-summary.md)
  states seven keystones; K1 (peering refines acceptance: a transit node is the
  post-path node on ACL2-computed arguments), K2 (loop freedom) and K3 (merge
  convergence via `fn-exchange-merge-commutative-member` and the lace twin) are
  the refinement seam and are design, not theorems. No book states them.
- **Include hygiene: 87.** [`ledger.md`](../ledger.md) counts 87 non-local
  `include-book` forms whose target is a local book ending with no theory
  withdrawal — each one enables every rule of that book in the includer and
  everything above it. Defect 1 is what one of them costs. Export hygiene is 62
  and SUSPECT-by-shape 31 in the same table.
- **The staging orphan with no owner.** An injected uncertain publication leaves
  `staging-orphans=1`, and `recover` reports it and leaves it across two
  recoveries and a SIGKILL. Reported-not-collected is defensible; it has no
  registry row either way (board 2026-09-20 w5-deploy-gate → store).
- **`NNT-001`'s live counterexample.** The server answers POST with `340` while
  its CAPABILITIES block omits `POST`. RFC 3977 §5.2.2 requires the capability
  exactly when posting is permitted.

## 5. What was NOT exercised

- **No farm gate exists for `dev` at `c8886ee`, or for any revision after
  `7a9e89a`.** The `dev-bdd59d2` gate had written per-book certify logs and no
  `manifest.json` and no `pytests.log` when this record was made; its result is
  unknown and is not reported here. Eight of the tree's 221 Makefile roots
  (scheduler ×3, tcpcl ×4 plus tests, nntp-legacy ×2 — see §1) have never been
  through a gate.
- **No single machine certified the whole tree.** Every "after" number in §2 is
  a laptop run with a partly warm certificate cache; every "before" is a farm
  manifest. They are comparable in direction, not in absolute seconds.
- **Nothing here re-establishes a certificate.** The deploy gate
  ([deploy-cce4b11](deploy-cce4b11-2026-09-20.md)) copied 210 pairs by content
  from the host's own gate (`matched=210 mismatched=0 absent=0`) and ACL2 only
  read them; 58.1 s wall, and the three CLI outcomes came back with their
  distinct exit codes (accepted 0, refused 1, uncertain 3).
- **No independent decoder ran on the farm box**: persvati has only Python
  3.13.7, and PEP 594 removed `nntplib`, so `tests/interop_store_nntplib.py`
  cannot run there. No newsreader is installed (slrn, tin, nn, trn all absent).
- **No concurrent-session evidence**: `tools/run_reader.py` serves one
  connection at a time; the concurrent server is the owner, which does not run.
- **One process-death cut** in the deploy gate (inside an open POST). The
  enumerated cut table is `tests/campaign/cuts.py`; a SIGKILL is not a power
  loss and nothing here qualifies storage hardware.
- **No proof status is advanced by this record.** Registry statuses moved in
  this batch are listed in [`requirements.json`](../requirements.json) with
  their theorem names and evidence paths; a certified root is not a proved
  requirement, and this file is not a certification record.
