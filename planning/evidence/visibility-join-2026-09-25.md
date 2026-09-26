# Visibility join: stored, visible and absent (2026-09-25)

Lane `lane/visibility-join`, from `dev` `483987b1`, under the Fable mandate
(§5.1, §11, §15 row "Lost reply followed by withdrawal"). Brief:
`build/coordinator/queue/w2-visibility-join.txt`. Rows: NNT-019, PRF-115,
SCN-060, PKT-164.

**What now works.** An agent or the web client that lost a POST reply settles
what the node accepted by itself: it re-sends the exact stored article under
the same Message-ID and the node answers from the Store, even after an
authorized cancel withdrew the article (a fresh reader gets `430 withdrawn`).
No second Message-ID and no second article number is ever made.
`docs/agents.md` no longer teaches that `430` means absent.

## The witness (step 1), natively

Developer image built from tree `061e8854` on hbox
(`/tank/fn/scratch/visibility-join/tree-061e8854`, script
`/tank/fn/scratch/visibility-join/vj-image.sh`, `systemd-run --user --scope -p
MemoryMax=24G`, build under `swarm-build`, `FN_OPENSSL_PREFIX=
/tank/fn/toolchains/openssl-3.5.8`). `validate --profile default`:
`roots=156 result=loaded`; 0 undefined lines.

- `build/fn-host-developer` `22e8285e3789da4b63efba9ba9213a840a5f779e68e445722d31d61bcbbbd711`
- `build/fn-host-developer.core` `0107785d773f0c7255d47f84ccde7836412a38b5e8e1d603c33357f6f3b7e79c`
- build log `dc75e9408d3c78e8b429daf7281d8e7214f3c1101488381874867a464abc476f`
- `tests.test_native_visibility_join` (2 tests OK, 6.0 s), log
  `build/lane/tests.test_native_visibility_join.log`
  `f5cbf08a668ec74de97a9b41eaa23d83145d9096a39cc392dfea5ed95f5a4a48` (left on hbox)

The sequence (`test_lost_reply_then_withdrawal_reconciles_to_already_stored`):
the owner runs with `FN_NATIVE_POST_FAULT=finish-durable:kill`, the cut after
the commit is durable and before the reply; `fn_client post --draft` gets
`340` and then nothing (exit 3, uncertain) and the owner dies with -9; the
same through `fn_web`'s outbox. After restart both targets answer `220`.
Principal `55..55` is enrolled and granted `cancel` over `fn.test`, and files a
signed cancel of each (`hybrid-author`). Observed:

| Step | Observation |
| --- | --- |
| fresh `ARTICLE <target>` (both) | `430 withdrawn` |
| `fn_client show <target>` | exit 1, `430 withdrawn -- not visible to this reader now; this is not evidence about acceptance`, `visibility: not-visible` |
| `fn_client reconcile DRAFT` | exit 0, `accepted`, `already-stored`; the node's line `441 posting failed; this article is already stored here` |
| `fn_web` POST `/reconcile` (after a web-client restart) | outbox `reconciliation` = accepted / already-stored; `result` still `uncertain` |
| transaction files before / after | 5 / 5 |
| `GROUP fn.test` before / after | `211 0 3 2 fn.test` both |
| second `reconcile` | exit 0, already-stored again |

With an authorization change
(`test_lost_reply_then_authorization_change_is_unresolved`): a protected node
(STARTTLS, `[auth] required`), login `vj-poster` posts under the same cut
(exit 3); the operator re-enrolls the login `--no-posting` and restarts;
`reconcile` logs in (`281`) and draws `440 posting not permitted for this
principal`: exit 4, `unresolved`; `show` still answers `220` (it was
accepted); transaction files 1 / 1.

**Reclaimed tombstone: not run natively (unexercised capability).** No host
verb reclaims an article on dev (`planning/now.md`, reclamation: the `store
reclaim` verb is open). The Store-level case is proved (below) and witnessed
in the test book on a reachable Store.

**Login rebinding:** not run. A login bound to a principal after the lost
reply is answered `441 ... this login posts only articles signed by its bound
principal` by the login gate, which runs before the Store's decision
(`fnn-owner-attempt-served`); by the client contract that is `unresolved`,
the same class as the `440` case run here.

## The contract (step 2), proved

Book `books/visibility-join.lisp`, tests `tests/acl2/visibility-join-tests.lisp`.

The subject is the host's decision. `host/native/owner.lisp`
`fnn-owner-attempt` asks `host/owner-host.lisp`
`fn-owner-existing-action-buffer`, whose decision is `fn-rclb-existing-action`
(`books/store-reclaim-buffer.lisp`), and returns `:duplicate`/`:conflict` as
its word before `fnn-advance-frontier` and `fn-owner-prepare-buffer`. The
carried-signature ingress `fnn-owner-attempt-transit` asks
`fn-owner-existing-action`, whose decision is `fn-rcl-existing-action`. Both
are stated.

- `fn-vj-a-completion-keeps-a-held-message-id-answered`:
  `(stringp msgid)` and `(fn-acceptedp msgid (fn-vj-articles s))` imply both
  `(fn-rclb-existing-action msgid fn-octets groups (fn-sn-finish s))` and
  `(fn-rcl-existing-action msgid payload groups (fn-sn-finish s))` are
  members of `(:duplicate :conflict)`. The withdrawing cancel is accepted by
  a `fn-sn-finish` (the owner's carried commit is `fn-ccar-sn-finish`,
  `fn-ccar-sn-finish-is-sn-finish`); withdrawal itself changes no Store
  state. From `fn-sn-finish-keeps-accepted-articles`.
- `fn-vj-reclamation-keeps-a-held-message-id-answered`: `(stringp msgid)`,
  `(fn-acceptedp msgid (fn-state-articles acc))` and
  `(equal (fn-vj-articles s2) (fn-state-articles (fn-rcl-reclaim-state acc r tomb)))`
  imply the same two memberships at `s2`. From
  `fn-rcl-reclaim-keeps-the-duplicate-history`.
- `fn-vj-a-held-message-id-is-answered-441`: with the owner's in-flight
  hypotheses of `fn-pb-same-article-is-answered-already-stored` (connection
  `id` exists, a submission in flight, it is `id`'s, no completion consumed),
  `(stringp msgid)` and the Message-ID held, `(car (fn-own-outcome o id
  (fn-rclb-existing-action ...)))` is one of `(fn-pb-served-reply o id
  :duplicate)` / `(... :conflict)`: the two 441 lines, never 240.
- Named `-by-definition`: `fn-vj-a-held-message-id-is-answered-by-definition`
  (the lookup is by Message-ID).

That the SAME source is `:duplicate` rather than `:conflict` across
reclamation is the existing `fn-rcl-existing-action-after-reclaim`, with its
SHA-256 collision disjuncts (collision, about 2^128 work, assumed not proved)
and its changed-injecting-agent disjunct. Across a completion it is the
definition (`fn-pb-existing-action-is-duplicate-iff-same-article-by-definition`)
and is witnessed; a general theorem would need Message-ID uniqueness in the
article list, which `fn-statep` does not carry (it carries number freshness).
Not claimed.

"Never allocates a number" is host control flow (the `case` in
`fnn-owner-attempt` returns before any reservation), observed natively
(transaction files and `GROUP` unchanged), not a theorem.

The theorem did hold at `483987b1`: no defect in the Store's decision. The
defect was the client contract and the docs.

**Teeth** (the test book; a reachable Store from `fn-sn-initial` by
`fn-sn-io` / `fn-spc-prepare` / `fn-sn-finish`: target T accepted, cancel C
naming T accepted by the completion the keystone is about; C3's withdrawal
record for a namespace grant over fn.test, built as
`control-visible-tests.lisp` builds it, makes T absent from
`fn-ctl-visible-articles` of the real article list; then T reclaimed to its
tombstone):

- completion keystone: witness (both entries, the live buffer run by
  `with-local-stobj`): same source `:duplicate`, changed source `:conflict`.
  Must-fail: not held (`<vj-absent@...>`, reachable); `stringp` removed
  (corrupted-state: a non-article at the head of the list).
- reclamation keystone: witness on the withdrawn-then-reclaimed Store: same
  source `:duplicate` by the tombstone digest, changed `:conflict`.
  Must-fail: not held; S2 not the reclaimed Store (the empty initial Store);
  `stringp` removed (corrupted-state).
- served reply: on `poster-bytes-tests`' `*pbt-owner*`, both Stores give
  `*pbt-duplicate-line*`, the changed source `*pbt-conflict-line*`.
  Must-fail per hypothesis: no connection `7`; nothing in flight; in flight
  for connection 3; a consumed completion; non-string Message-ID
  (corrupted-state); not held.

## Assurance chain

native entry `fnn-owner-attempt` (served POST, after the login gate, the
control filing and the carrier form) -> executed subject
`fn-rclb-existing-action` over the octet buffer (`fn-rclb-existing-action-is-
rcl-existing-action` under `fn-octets-p`) -> no representation change beyond
the buffer (the Store's article list is the list the owner holds) ->
maintained relation: "a held Message-ID stays held", preserved by every
`fn-sn-finish` (`fn-sn-finish-keeps-accepted-articles`) and by
`fn-rcl-reclaim-state`; established by the acceptance that first stored it
-> behavioural theorems above -> emitted line: `fn-own-outcome`'s 441 line ->
observed: `441 posting failed; this article is already stored here` on the
wire, settled `accepted` by the client.

## Runs

- persvati r1 `run-20260925T234337Z-1693` (2 jobs, 300 s, w25): 4 certified
  including the missing `store-node-retention` and `poster-bytes-tests`;
  `books/visibility-join` red at the completion keystone (a disabled
  `fn-vj-articles` against the expanded finish lemma). Manifest
  `planning/evidence/manifests/certify-20260925T234352Z-2671972.json`.
- persvati REPL session over the r1 cache: the three keystones and every
  test form admitted.
- persvati r2 `run-20260926T000228Z-6d61` (2 jobs, 300 s, w25): **2 of 2
  passed**; `books/visibility-join` 1.42 s, `tests/acl2/visibility-join-tests`
  1.62 s. Manifest
  `planning/evidence/manifests/certify-20260926T000258Z-2861655.json`.
- Python: `tests.test_fn_client` 43 OK (7 new), `tests.test_fn_web` 35 OK (3
  new; one assertion's wording moved with the contract, the regression it
  guards -- a lookup never changes the original -- kept).

## The clients (steps 3 and 4)

- `tools/fn_client.py`: `post --draft PATH` writes the exact lines and
  Message-ID (0600, atomic, fsync, directory fsync) before sending and the
  observed outcome after; an existing PATH is a usage error. `reconcile PATH`
  re-sends the lines under the same Message-ID: `240` accepted-now, the
  duplicate line already-stored (exit 0), the conflict line refused (1),
  anything else `unresolved` (exit 4, new). It refuses to re-send an accepted
  or refused original. Every reconciliation is appended; the original is
  never rewritten. `show` marks 423/430 `not-visible`.
- `tools/fn_web.py`: an uncertain result shows **unresolved** and a
  CSRF-checked POST `/reconcile` that re-sends the frozen lines; the answer is
  kept in the outbox record's `reconciliation`, beside `result`. The old page
  text "if the node serves it, it was accepted" is gone.
- `docs/agents.md`, `docs/human-web-client.md`, `specs/nntp.md` (NNT-019).

## PKT-164: a privileged identity query for the unresolved case

- **Trace.** Native authorization case above: the poster whose posting
  permission (or login binding) changed after a lost reply cannot re-submit;
  the gate answers first. Its reader lookup may be `430` (withdrawn) or `220`.
- **Constraints.** A lookup must not disclose content the asker may not read
  (withdrawn content stays withdrawn for readers); the Store's D25 answer
  compares the submitted source, so the asker must hold the exact source.
- **Default (what dev does now).** Unresolved; an operator can settle it
  with the Store's own inspection (`fn-host --fn store STORE inspect <msgid>`,
  as `tests/test_fn_web_native.py` uses it), which is an operator's
  authority, not a reader's.
- **Candidate.** Answer the D25 question before the login/posting gates for
  a resend under a held Message-ID (`already stored` / `different article`),
  returning nothing else. Disclosure: whoever holds the exact bytes learns the
  node holds them (and, for the conflict line, that some article holds the
  Message-ID, which `430` vs `423` already reveals). Authority: none beyond
  possession of the source.
- **Rejected alternative.** A new privileged `ACCEPTED <msgid>` query:
  new wire vocabulary, an authority row and a disclosure policy for little
  gain over the candidate.
- **Affected.** `fnn-owner-attempt-served` order (host), the login-binding
  keystone's composition (`books/login-binding.lisp`), NNT-013's text.
- **What continues without it.** Everything here: the client reports
  unresolved honestly.

## Not done, and why

- Native reclamation case: no host verb (above).
- The image of the final commit: books and host are unchanged after
  `061e8854` (later commits touch docs, registries, Python tests); the native
  module was re-run at the final tree with that image (see LANEDUMP / the
  final report for the SHA).
- `planning/ledger.*` regenerate on merge (not committed by the lane).
