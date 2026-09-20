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
