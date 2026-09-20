# w5/owner-followups — read-back, POST in CAPABILITIES, the staging sweep

Branch `w5/owner-followups` from `dev` at `ea7248b`. Worktree
`build/lanes/w5-owner-followups`. Three follow-ups of
`planning/lanes/HANDOFF-w5-owner-post.md` (its open items 4 and the read-back
question) and finding 5 of
`planning/evidence/deploy-cce4b11-2026-09-20.md`.

## 1. Read-back: a 240 moves the poster's pin, and only the poster's

`fn-own-outcome` (`books/owner.lisp`) renders the reply exactly as before,
from the connection as it was when the submission was taken, and then, when
the rendered completion is `:durable`, applies one `fn-own-advance` to that
connection — the same event the host's `(:advance id)` runs. `:refused` and
`:uncertain` move no pin.

New in `books/owner-invariants.lisp`:

- `fn-own-durable-outcome-repins-the-poster` (`:rule-classes nil`): under
  `fn-own-relation`, with the connection present and its submission in
  flight and the completion `:durable`, that connection's version and
  archive after the outcome are the committed view's. With K1
  (`fn-own-read-is-served-step-on-pinned-prefix`) that is the read-back: its
  next GROUP/ARTICLE is a served step over the prefix containing its own
  article.
- Local supports: `fn-own-advanced-session-is-bounded` (an advance is never
  refused for a bounded connection — the rebuilt session keeps the group and
  the cursor, and `fn-nntp-open-session` of any archive is a session),
  `fn-own-advance-repins-the-connection`, `fn-own-find-conn-of-replace-conn-same`,
  `fn-own-outcome-body-preserves-relation`.

**Statement changed, and why.** `fn-own-outcome-touches-only-its-connection`
said `(equal (fn-own-conns (cdr (fn-own-outcome ...))) (fn-own-conns o))` —
*no* connection touched. The new behaviour touches the poster's, so the
conjunct is now what the theorem's name always said: for `other ≠ id`,
`fn-own-find-conn other` is unchanged. Its second conjunct is untouched, and
no other keystone's statement moved. `fn-own-outcome-preserves-relation`
keeps its statement; its proof is now the body lemma plus
`fn-own-advance-preserves-relation`.

K1 covers either choice — it constrains what a connection reads *at its
pin*, not which pin it holds — so the choice is recorded in
`specs/nntp.md` (POST section, "Read-back") and `specs/node-functionality.md`
§2.1 rather than derived.

Witness: `tests/test_post.py`
`test_post_reaches_240_and_the_article_can_be_read_back` now reads back on
the poster's own socket (`211 2 1 2`, `STAT 2` → `223 2`), and
`test_a_reader_pinned_before_a_post_keeps_its_view` asserts the poster
advances while the early reader does not.

## 2. CAPABILITIES, the greeting and MODE READER

`fn-nntp-env` is four fields: `(:fn-nntp-env observation facts posting)`.
`fn-nntp-post-step` supplies the third from `(fn-inj-config-allow config)` —
the connection's own pinned configuration, the same bit it reads before
answering POST with 340 rather than 440 — so the advertisement is a promise
the server keeps (RFC 3977 §5.2.2). `fn-nntp-capability-lines` takes the bit
and inserts `POST` after `READER`; `fn-nntp-capabilities` and
`fn-nntp-mode-response` take it (§5.3.2: `200 posting allowed` /
`201 posting prohibited`); `fn-served-greeting` picks §5.1.1's code, so the
owner greets `200 fn-nntp experimental server ready` and the read-only
reader keeps its 201.

`*fn-nntp-caps*` is re-pinned from an `ld` of the edited
`books/nntp-responses.lisp`, with a second pin `*fn-nntp-caps-posting*` and
a separating assertion. **The old pin was stale**: it omitted the `HDR`
label the builder has been emitting, so that `assert-event` could not have
passed on any tree.

Edit for an includer: `fn-nntp-env` takes three arguments;
`fn-nntp-capabilities` and `fn-nntp-capability-lines` take the posting bit;
`fn-nntp-mode-response` takes `env` before `args`. Five test books and the
two `nntp-effects` / three `nntp-invariants` statements about those two
functions were threaded; nothing else changed.

## 3. The staging sweep

New `books/store-sweep.lisp` (prefix `fn-sn-`, Makefile root before
`books/store-observed`, with `tests/acl2/store-sweep-tests`). No owner code.

`fn-sn-sweep-staging (s observed held)` returns `(removals . s)`: the store
is returned unchanged, and a name is removed only when it is in the staging
namespace (`.stage-`), was observed, and is not one the live process holds —
and nothing at all is removed while the kernel holds an unresolved
publication (`fn-sn-sweep-enabledp`: `fn-sf-phase` is `:ready` and
`fn-sf-record-candidate` is nil, the same gate `fn-own-take-submission`
reads).

- Keystone `fn-sn-sweep-removes-only-unheld-staging-names`.
- `fn-sn-sweep-never-removes-a-final-namespace-name`: a completed
  publication's name is twenty decimal digits, which is not a staging name,
  so it can never be removed whatever the host enumerated.
- `-by-definition`, `:rule-classes nil`, cited by `:use`:
  `fn-sn-sweep-refuses-while-a-publication-is-unresolved`,
  `fn-sn-sweep-staging-keeps-the-store`, and the two preservation facts
  (`fn-sn-statep`, `fn-snt-relation`), which are that identity's corollaries
  and are not registry events.
- Teeth: `tests/acl2/store-sweep-tests.lisp` sweeps the deploy gate's own
  directory, keeps a held name, keeps a final-namespace name, and shows the
  gate refusing on two violating states under `with-guard-checking :none`.

Host: `host/store-node-host.lisp` `fn-store-sn-sweep-staging`;
`tools/run_store.py` `Acl2Store.sweep_staging`, `Store.sweep_staging`
(unlinks what the book named, then re-reports `self.orphans`), called from
`Store.recover` after the replay — which is the owner's reopen too, since
`run_owner.py` recovers through `Store.recover`. `Store.staging_orphans`
gained `raw=` so the sweep does not see the report's truncation marker.
Test: `tests/test_store_lifecycle.py`
`test_an_uncertain_publication_leaves_no_staging_orphan_after_recovery`.

## Open, recorded rather than weakened

1. The 240's ledger pair is still proved to be *a* pair consumed after the
   take with a record in the durable history, not the submission's own
   article (owner-post open item 1). Not attempted in this lane: it needs
   the record's Message-ID compared with `fn-own-sub-decision`'s, which
   means the book reading `fn-inj-decision-*` out of the stored record.
2. The sweep collects `.stage-` only. `.allocation-`, `.anchor-` and
   `.init-` orphans from interrupted frontier, anchor and init writes are
   still reported and not collected; each needs its own held-set argument
   from the host before it can be swept safely.
3. Owner-post open items 2, 3, 5 and 6 stand unchanged.

## Evidence

- ACL2, farm `run-20260920T050203Z-0904` on persvati (`--closure`,
  `--remote-root /home/ember/fn-lanes/w5-owner-followups`), evidence
  `build/acl2/certify-20260920T050207Z-2820274`, status **passed**, 17 books
  including `books/store-sweep` and `tests/acl2/store-sweep-tests` with their
  whole closure. Certificates installed in this worktree.
- ACL2, farm `run-20260920T050532Z-db74`, the nntp/served/owner closure
  (`--affected-by books/nntp-responses.lisp --affected-by books/owner.lisp
  --closure`): **submitted, still running when this lane's budget ran out**.
  Harvest it with `python3 tools/farm.py wait persvati --remote-root
  /home/ember/fn-lanes/w5-owner-followups run-20260920T050532Z-db74`. Local
  `ld` of the edited `books/nntp-responses.lisp` admitted every form and is
  where the two capability pins were quoted from; `books/store-sweep.lisp`
  and `tests/acl2/store-sweep-tests.lisp` were `ld`-clean before the submit.
  Nothing else in the chain has a local verdict — do not read this handoff
  as one.
- Python: `tests.test_store_lifecycle.StagingSweepTests` passes (15 s), which
  is finding 5 closed end to end. `tests/test_post.py` and
  `tests/test_owner.py` were edited for the read-back and the 200 greeting
  and were NOT run here (each owner start is minutes on this box); they are
  the next thing to run.
- `make check`: scaffold OK, ledger OK (149 pre-existing lint warnings,
  unchanged in kind).

Two host defects the lifecycle test found, both fixed in `4a0c412`: the
sweep ran while the file kernel was still `:recovering`, so its own gate
refused it (it now runs after the recovery barriers, where the phase is
`:ready`); and it joined the removal names with `fn-store-cfg-join-names`,
which encodes *strings* — a staging name is an octet list, so
`fn-store-sn-join-octet-names` is its joiner.

## Evidence, second pass (farm)

- `run-20260920T050532Z-db74` (nntp/served/owner closure, 48 roots):
  **47 certified, one failed** —
  `books/nntp-effects` **timed out at 1800.1 s** (evidence
  `build/acl2/certify-20260920T050536Z-2854073`, the log ends inside
  `FN-NNTP-EFFECTS-XOVER-RESPONSE`, a form this lane did not touch). The box
  was co-tenant to a second 12-job certification at the time. The plausible
  cost this lane added is upstream of it: `fn-nntp-capability-lines` built
  its answer as an `append` of a conditional, so every block-text obligation
  had to reason through the append. Fixed in `5bebaee` (one ground list per
  branch; emitted octets unchanged, held by the two `ld`-quoted pins) and
  resubmitted as `run-20260920T053849Z-9568`
  (`--closure books/nntp-effects`), **still running at the end of this
  lane's budget**. `books/nntp-effects` therefore has **no verdict**; every
  other root in the chain (nntp-responses, nntp, nntp-invariants, nntp-post,
  served, owner, owner-invariants, nntp-tests, nntp-teeth-tests,
  nntp-legacy-tests, nntp-reader-profile-tests, nntp-post-tests,
  served-tests, owner-tests and their closure) certified.
- Python on persvati in the certified remote root
  (`tests.test_post tests.test_owner tests.test_store_lifecycle
  tests.test_reader`, 31 tests, 171.9 s): **29 pass, 1 skip** (the nntplib
  probe; persvati's 3.13 has no `nntplib`), **1 fail**.

### Open defect this lane introduced, not yet closed

`tests.test_post.StorePostTests.test_a_reader_pinned_before_a_post_keeps_its_view`
fails at its **second** post through the same poster connection: expected
`240 article received OK`, received `441 posting failed; the a...`. The
first post, its 240, the poster's re-pin to `211 2 1 2` and both readers'
pins are all correct up to that point, and the single-post read-back test
(`test_post_reaches_240_and_the_article_can_be_read_back`) passes. So the
defect is in a **second** submission from a connection that has already been
re-pinned by a 240 — the suspect is the interaction of
`fn-own-advance`'s rebuilt session with the next POST on the same
connection, not the re-pin itself. Do not merge this lane before this is
diagnosed: either the second post is fixed, or `fn-own-outcome`'s advance is
removed and the read-back recorded open.

### `books/nntp-effects`: no verdict, and it is a wall clock, not a proof

`run-20260920T053849Z-9568` (`--closure books/nntp-effects`, after `5bebaee`)
certified its 16 closure books and **timed out again at 1800.2 s**
(`build/acl2/certify-20260920T053850Z-3202105`), at exactly the same point
as the first run: after `FN-NNTP-EFFECTS-XOVER-RESPONSE` completes, inside
the HDR block-text lemmas that follow it at `books/nntp-effects.lisp:948`
onwards (`fn-nntp-hdr-lines-for-numbers-are-block-text`,
`fn-nntp-hdr-numbered-line-is-block-text`,
`fn-nntp-hdr-labelled-line-is-block-text`). **That region is untouched by
this lane** — it mentions no capability line, no `fn-nntp-env` and no
posting bit, and the two forms this lane did change in that book
(`fn-nntp-effects-capabilities` at :846 and `fn-nntp-effects-mode-response`
at :1079) are respectively before and after it, the first of which passed.
persvati was carrying six concurrent ACL2 processes for other lanes, and
`FN_ACL2_TIMEOUT_SECONDS` is 1800 per invocation; the owner-post lane
certified this same book in `certify-20260920T025533Z-22858` on a quiet box.

So the honest reading is a per-invocation wall-clock cap on a contended box,
not a proof this lane broke — but **`books/nntp-effects` has no verdict on
this tree and must not be reported as certified**. The instrument is the
timeout, not a hint: resubmitted as `run-20260920T061124Z-7847`
(`--jobs 4 --timeout-seconds 5400 --closure books/nntp-effects`), pending.
If that run also stops inside the HDR block, the timeout is not the cause
and the block needs profiling on its own.

`5bebaee` stands on its own merits either way (a ground list per branch is
cheaper than an `append` of a conditional for every block-text obligation
above it) and changes no emitted octet.
