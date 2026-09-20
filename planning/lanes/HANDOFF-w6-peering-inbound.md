# Handoff: w6/peering-inbound (packets K0 to K2, inbound half)

Branch `w6/peering-inbound` from `dev` at `cce4b11`, worktree
`build/lanes/w6-peering-inbound`. Spec: [`specs/peering.md`](../../specs/peering.md)
(the status section at its end is the per-keystone record and the list of
what differs from the design). Sibling `w5/owner-post` owns
`books/owner*.lisp` and the owner host: nothing there is edited; the owner's
transit port is a board proposal (below and on the board).

## What exists

| File | What |
| --- | --- |
| `books/config.lisp` (edit) | delta kinds `:set-peer` (9) and `:remove-peer` (10); `fn-cfg-rows-with-key`, `fn-cfg-rows-without-key`, `fn-cfg-rows-keyed-p`; `fn-cfg-set-peer`, `fn-cfg-remove-peer`; apply arms (upsert / drop the row group keyed by the peer name in the `peers` slot); reasons `:peer-rows-empty`, `:peer-rows-unkeyed`, `:no-such-peer`. Every existing statement kept. |
| `books/config-invariants.lisp` (edit) | two local row-list lemmas so `fn-cfg-apply-delta-preserves-valuep` covers the two new arms; statement unchanged. |
| `books/path.lisp` (new, `fn-path-`) | Path entries, `fn-path-identityp`, `fn-path-names-p` (RFC 5537 §3.6 loop test with the tail-entry and POSTED exclusions), `fn-path-diagnostic`, `fn-af-path-field-value`, `fn-path-date-presentp`. |
| `books/peer-config.lisp` (new, `fn-cfg-peer-`) | the opaque six-field record, `fn-cfg-peerp`, the row codec (`fn-cfg-peer-rows` / `fn-cfg-peer-of-rows`), `fn-cfg-peer-find`, `fn-cfg-set-peer-delta`, `fn-cfg-remove-peer-delta`; theorems `fn-cfg-set-peer-delta-is-admissible`, `fn-cfg-peer-rows-after-set-peer`, `fn-cfg-peer-find-after-remove-peer`, `fn-cfg-peer-deltas-change-only-peers`. |
| `books/peer-inbound.lisp` (new, `fn-peer-`) | `*fn-peer-decisions*`, `*fn-peer-reasons*`, the decision record, `fn-peer-history-hasp`, `fn-peer-stagedp`, `fn-peer-scope-groups`, `fn-peer-evidence`, `fn-peer-local-identity`, `fn-peer-decide-offer`, `fn-peer-decide-transfer`, `fn-peer-injection-arguments`, `fn-peer-transfer`, the transit submission record (`fn-peer-submissionp`), the transit session record (`fn-peer-sessionp`, `fn-peer-open-session`), the reply builders and both RFC tables with the explicit code classes (`fn-peer-offer-code`, `fn-peer-transit-code`, `fn-peer-not-now-is-a-retry-code`: 431/436 retry, 437/439 drop, never 400), `fn-peer-capability-lines`, `fn-peer-command`, `fn-peer-step`; keystones `fn-peer-step-effects-well-formed`, `fn-peer-step-preserves-consistent-session`, `fn-peer-step-submission-is-typed`, `fn-peer-transit-outcome-effects-well-formed`, `fn-peer-open-session-is-consistent`. |
| `books/peer-inbound-invariants.lisp` (new) | K1 `fn-peer-transfer-is-the-post-path`, `fn-peer-transfer-stages-only-scope-groups`, `fn-peer-scope-groups-are-live`, `fn-peer-refused-transfer-leaves-the-node` (by definition); K2 `fn-peer-loop-is-refused`; K3 `fn-peer-history-is-refused-at-offer`, `fn-peer-history-is-have-at-offer`, `fn-peer-history-is-refused-at-transfer`, `fn-peer-history-grows-under-transfer`. |
| `tests/acl2/peer-inbound-tests.lisp` (new) | record teeth, the CBOR round trip of a record carrying both peer deltas, replay to a configuration with two peers, `:remove-peer`, Path witnesses, and the transcripts: IHAVE accepted (335, article, submission, `fn-node-prepare` equality, 235 on `:durable`), loop refused (437 with reason; tail-entry and POSTED variants accepted), duplicate (435 / 438 / node unchanged), CHECK/TAKETHIS refused by groups (238, 439), uncertain TAKETHIS (`436 <msgid>` + close) and IHAVE (436 + close), deferred TAKETHIS (`436 <msgid>`, no close), deferred, inflight limit (436 / 431), not a peer (435 / 438), feed-only peer, no-date, mismatched Message-ID, MODE STREAM 203, CAPABILITIES with IHAVE and STREAMING, the reader's 502 and unchanged POST, malformed lines, the not-received article. |
| `books/nntp.lisp` (edit) | IHAVE / CHECK / TAKETHIS on a reader connection answer `502 transit is not permitted on this connection`. `tests/acl2/nntp-tests.lisp` pin updated from 500. |
| `books/served.lisp` (edit) | the connection's session is `fn-peer-sessionp`; `fn-served-dispatch` calls `fn-peer-step`; `fn-served-submit-effectp` accepts an injected or a transit submission; `fn-served-open` opens a reader (unchanged signature); `fn-served-open-peer archive line-limit body-limit config observation peer node cfg`; `fn-served-transit-outcome conn submission decision completion`; `fn-served-open-peer-is-a-connection`, `fn-served-transit-outcome-effects-are-typed`. Every existing keystone statement unchanged. |
| `Makefile`, `docs/prefixes.md` | roots after `nntp-post-tests`; rows for `fn-path-`, `fn-cfg-peer-`, `fn-peer-`, reserved `fn-feed-`. |

## The owner's transit port (proposal, exact forms)

1. At `(:open id peer)` with `peer` a configured name, the owner opens the
   connection with
   `(fn-served-open-peer archive line-limit body-limit config observation peer node cfg)`
   where `node` is `(fn-cnode-node cn)` and `cfg` is `(fn-cnode-config cn)`;
   `line-limit`/`body-limit` are the peer's `inbound-max-octets` (the wire cuts
   an oversize body; the decision names `:oversize` for the residue). A reader
   opens with `fn-served-open` as today.
2. On a `(:submit s)` effect with `(fn-peer-submissionp s)` (never
   `fn-inj-injectedp`; `fn-peer-submission-is-not-injected`), the owner
   computes `id = (fn-id-obligation-of msgid-octets subject-octets)` and
   `subject = (fn-id-subject-of-payload octets)` rendered as it does for POST,
   then `(mv node2 d) = (fn-peer-transfer node cfg (fn-peer-submission-peer s) (fn-peer-submission-msgid s) (fn-peer-submission-octets s) clock generation id subject)`,
   which is one `fn-node-prepare` on `:want` and the node unchanged otherwise
   (`fn-peer-transfer-is-the-post-path`, `fn-peer-refused-transfer-leaves-the-node`).
   Then the durable attempt as for POST (`fn-node-complete`), then
   `(fn-served-transit-outcome conn s d completion)` with `completion` one of
   `:durable`, `:refused`, `:uncertain`, or `nil` when `d` was not `:want`.
   On `:uncertain` the reply is 436 (both commands) with the close effect: the node is fenced. A `:defer` decision is 436 without a close; innfeed retries on 431/436 and drops on 437/439, so no "not now" ever maps to 437/439 or to 400.
3. Optionally, after a durable completion, re-pin the snapshot: reopen the
   session with `fn-peer-open-session` on the new node (the offer decision is
   advisory and re-checked at transfer, so this is a freshness improvement,
   not a correctness condition).

## What the feed lane (K2, `fn-feed-`) can assume

`fn-cfg-peerp` and its accessors (`fn-cfg-peer-outbound-groups`,
`fn-cfg-peer-streamingp`, `fn-cfg-peer-max-queue`, `fn-cfg-peer-backoff`,
`fn-cfg-peer-path-identity`); `fn-cfg-peer-find name (fn-cfg-peers (fn-cfg-value cfg))`;
`fn-path-names-p` and `fn-path-diagnostic` for the outbound loop check and
the §3.2.1 diagnostic; `fn-peer-evidence` as the evidence string of a
transit article (`"peer-transit:<peer>"`); `fn-peer-history-hasp`. The
`:remove-peer` feed-idle condition is the feed lane's owner-side check.

## Certification

Evidence directories under `build/acl2/` in this worktree (one ACL2 at a
time, `tools/certify_books.py --jobs 1`, ACL2 8.7, `FN_ACL2_TIMEOUT_SECONDS=1800`):
see the lane's final report and `planning/deputies/BOARD.md` entry for the
run ids and the per-root outcome.

## Open

- `fn-cfg-peer-of-rows-of-peer-rows` (general rows-to-record round trip) and its injectivity corollary: ground witnesses only.
- `fn-peer-accepted-article-is-acceptance-accepted` (K1 third statement),
  the outbound half of K2, `fn-peer-history-survives-reopen` (K4 restart),
  the general tail-entry lemma over `fn-path-names-p`: recorded in the spec
  status table.
- RFC 5537 §3.6 step 2 (date more than 24 h in the future): no certified
  RFC 5322 date-time reader; `:date-future` / `:no-clock` reserved.
- `verify-guards` for `fn-peer-decide-offer`, `fn-peer-decide-transfer`,
  `fn-peer-transfer`, `fn-peer-step` and the session recognizers (declared
  `:verify-guards nil`; callees are verified).
- The `cfg-gen` leading argument of the owner's `fn-cnode-prepare` is not in
  `fn-peer-injection-arguments` (the owner supplies it as for POST).
- `:set-peers` stays a delta kind beside `:set-peer`; retiring it is a
  config-lane decision.
- `books/owner*.lisp` and the host: not touched; `fn-own-read` still builds
  the served conn with three arguments (board note of w3/reader-profile).

## Per-root state, successor lane `w6/peering-inbound-2`

Branch `w6/peering-inbound-2`, worktree `build/lanes/w6-peering-inbound-2`,
from `dev` at `52eb0db` and merged with `dev` again at `cda964e`.
Certification on **persvati**, ACL2 8.7, `/home/ember/fn-lanes/w6-peering-inbound-2`.

| Root | State | Evidence |
| --- | --- | --- |
| `books/peer-config` | certified | `certify-20260920T192710Z-2288223` run set. Closed independently on `dev` too; this lane kept `dev`'s version and added two exported forward-chaining facts (below). |
| `books/peer-inbound` | **certified** | `certify-20260920T192710Z-2288223` |
| `books/peer-inbound-invariants` (K1, K2, K3) | **certified**, every statement unchanged | `certify-20260920T194848Z-2492799` |
| `tests/acl2/peer-inbound-tests` | **certified** | `certify-20260920T195156Z-2522463` |
| `books/served` | **certified** | `certify-20260920T194106Z-2419178` |
| `tests/acl2/served-tests` | **certified** | `certify-20260920T195046Z-2511951` |
| `books/owner`, `books/ideal` | **certified** | `certify-20260920T194347Z-2445219` |
| `books/owner-invariants`, `tests/acl2/owner-tests` | certified at `e8372fa` (`certify-20260920T203813Z-2981507`, `certify-20260920T204258Z-3028825`); at the merged HEAD they are blocked on `books/peer-feed-invariants` (below), not on anything here | |

### What was wrong, and what closed it

`books/peer-inbound` had never run past its includes, so the whole stack
above it -- `served`, `owner`, `ideal`, and the served host, which loads
them -- was dead. In order:

1. Two translate errors killed every definition. `fn-peer-decide-offer`
   called `fn-charge-for-payload` with `books/identity` in no book of the
   include closure; `fn-nntp-capability-lines` had gained a `postingp`
   argument on `dev`.
2. Six theorems. The two interesting ones are recorded below; the rest
   were rules that stopped matching because an accessor or an append had
   been opened under them.
3. Guard verification was **not** optional: `books/served.lisp`
   guard-verifies `fn-served-dispatch`, which calls `fn-peer-step`.
   `fn-peer-decide-offer`, `fn-peer-sessionp`, `fn-peer-open-session`,
   `fn-peer-delegate`, `fn-peer-command` and `fn-peer-step` are verified.
4. Four defects in `books/served`, three of them stale references the
   `dev` merge created and one a false theorem (below).

### Interface changes, all on the board

- `fn-peer-capability-lines record postingp` (was one argument);
  `fn-peer-command` passes `nil`, so a transit connection does not
  advertise POST. Witnessed both ways in the test book.
- `fn-peer-command` is `:guard (and (fn-peer-sessionp ps) (fn-peer-session-peer ps))`,
  which is what `fn-peer-step` establishes at the only call site.
- `books/peer-inbound` includes `books/identity` and exports one new
  forward-chaining rule, `fn-peer-session-consistentp-forward`.
- `books/peer-config` exports `fn-cfg-peer-find-is-a-peer` and
  `fn-cfg-peerp-inbound-fields`, both forward-chaining.

### One false theorem, repaired not weakened

`fn-served-submission-of-append` (`books/served.lisp`, w9/server-polish's,
and cited in `specs/nntp-audit.md`) was **false**: with
`left = ((:submit nil))` and `right = ((:submit 5))` both the left scan
and the appended scan yield `nil` while the right-hand side yields `5`.
It now carries `(fn-served-effectsp left)`; `fn-served-submit-effectp`
requires an `fn-inj-injectedp` or `fn-peer-submissionp` payload and
neither is `nil`, so on the only effect lists the served path produces
the equality holds. Discharged at its one use site from
`fn-served-step-effects-are-typed`.

### The owner predicate, and the two-node gate

`fn-own-conn-boundedp` (`books/owner.lisp`) tested `fn-post-sessionp` on a
session that has been a peer session since the inbound port -- two fields
against six -- so it was false on every connection `fn-own-open` builds.
The branches at `owner.lisp:657/695/724` were never taken (the owner never
re-pinned a connection and never enqueued a submission) and
`fn-own-relation`, which conjoins it through `fn-own-conn-okp`, was false
on every state holding a connection, so every theorem hypothesising it was
vacuous there. It now tests `fn-peer-sessionp` and reads the reader session
through `(fn-post-session-base (fn-peer-session-base ps))`; `fn-own-advance`
keeps the peer slots and rebuilds only the POST base through
`fn-peer-with-base`.

**Two-node gate, `planning/evidence/twonode-e8372fa-2026-09-20.md`
(persvati): 63 steps, 0 failed, 6 not exercised.** The run at `d8b1e8f`
had five failures -- both independence controls and the three crash and
recovery steps, all `server closed the connection` or `connection
refused` -- and every one of them was this predicate closing the
connection. The six that remain unexercised are the three feed steps
(`42` reread on B, `43` the second IHAVE drawing `435`, `44` the
Path-names-B refusal), their two setup steps (`35`, `37`, the peer
records) and `57 tcpcl exchange`. The feed five are unexercised because
the host opens every connection as a reader with `fn-served-open`, so
node B answers `IHAVE` with `502 transit is not permitted on this
connection` -- the model's correct reader answer, and an improvement on
the previous run's silence. Making them run is the owner's transit port
(`(:open id peer)` calling `fn-served-open-peer`), which is
w10/owner-feed's packet. **Nothing yet establishes that an article can
cross between two fn nodes.**

The gate was run at `e8372fa`, before the merge of `dev` that brought
w10/owner-feed in; at the merged HEAD `books/owner` does not certify, for
the reason below, so a rerun there would be red for a cause outside this
lane.

### Blocking someone else: `books/peer-feed-invariants`

The feed lane's book does not certify on dev, and `books/owner-feed`
includes it, so `books/owner`, `tests/acl2/owner-tests` and everything
above them cannot be read at the merged HEAD. Two failures:

1. `fn-feed-apply-record-preserves-peer` keeps every arm closed and so
   needs one `-preserves-peer` rewrite per arm, exactly as
   `-preserves-feedp` has; only `-preserves-feedp` existed. Six were added
   here (`give-up`, `restart`, `enqueue`, `done`, `back-off`, `lost`;
   `fn-feed-offer` and `fn-feed-send` return an `mv` and the dispatcher
   builds them inline, so they need none) and the theorem closes.
2. The next form, `fn-feed-selection-is-queued`, then fails on its own.
   Not touched; it is the feed lane's, and there is a board ASK.

### Guard verification is not optional below `fn-served-dispatch`

`books/served` guard-verifies `fn-served-dispatch`, which calls
`fn-peer-step`. A `:verify-guards nil` anywhere in that call graph makes
`books/served` uncertifiable and the served host unloadable. Verified:
`fn-peer-decide-offer`, `fn-peer-sessionp`, `fn-peer-open-session`,
`fn-peer-delegate`, `fn-peer-command`, `fn-peer-step`.

### Still open

- `books/owner-invariants`: `fn-own-open-session-boundedp` asks for
  `(fn-post-session-shapep (fn-peer-open-session archive nil nil nil))`.
  The connection's session is a peer session now, so `fn-own-conn-boundedp`
  must project it through `fn-peer-session-base` rather than the
  `fn-post-session-*` accessors. That is an owner-side semantic change and
  belongs to the owner lane, not a hint. `tests/acl2/owner-tests` is
  blocked on it.
- `verify-guards` of `fn-peer-session-consistentp`: it calls
  `fn-post-session-consistentp` (`books/nntp-post.lisp`), itself
  `:verify-guards nil`. Both are specification predicates that nothing on
  the served executable path calls.
- `fn-peer-transfer`, `fn-peer-decide-transfer` and
  `fn-peer-injection-arguments` stay `:verify-guards nil`: the owner, not
  the served path, calls them.
- The structured-evidence change (`(:peer-transit peer stamp)` in place of
  the string) is blocked on `fn-retain-admissiblep`'s `(stringp evidence)`
  requirement, `books/retention.lisp:380`. Cross-cluster.
- Everything the previous lane listed as open below is still open.

### Box notes

`ld` on hbox is `/tank/fn/acl2-8.7/saved_acl2`, not `$HOME/fn-tools/...`
(that path is persvati's, and exits 127 on hbox). A persvati run under
`--jobs 12` while the box was carrying six other closure certifications
lost `books/nntp-effects` to a dependency race -- `nntp-post` started
while `nntp-effects` was still certifying -- and cascaded "no certificate"
into six roots. `--jobs 6` did not reproduce it.

## Per-root state at handoff (HEAD after this commit; runs under `build/acl2/` in this worktree)

| Root | State | Evidence |
| --- | --- | --- |
| `books/config` | certified | `certify-20260920T030728Z-59872` |
| `books/path` | certified | `certify-20260920T031511Z-70354` (second run of that dir set) / re-run green in `certify-20260920T032008Z-76931` |
| `books/config-invariants`, `books/node-config`, `books/nntp-responses`, `books/nntp`, `books/nntp-overview`, `books/nntp-invariants`, `books/nntp-effects`, `books/nntp-post` | certified (the dispatcher's 502 branch; statements unchanged) | `certify-20260920T032353Z-96044` |
| `books/nntp-index`, `tests/acl2/nntp-index-tests`, `tests/acl2/nntp-post-tests`, `tests/acl2/nntp-reader-profile-tests`, `tests/acl2/nntp-teeth-tests` | certified | `certify-20260920T033720Z-32591` |
| `books/store-config`, `tests/acl2/config-tests`, `tests/acl2/nntp-tests` (502 pin) | certified | `certify-20260920T033902Z-34627` |
| `books/peer-config` | **open**: `ACL2 Error [Failure] in ( DEFTHM FN-CFG-SET-PEER-DELTA-IS-ADMISSIBLE` fails; last checkpoint: `1566-schemes.  However, one of these is flawed and so we are left with one 1567-viable candidate.   1568- 1569-We will induct according to a scheme suggested by (FN-CFG-ROWS-WITH-KEY A K), 1570-while accommodating (APPEND A B). 1571- 1572-These suggestions were produced using the :induction rules BINARY-APPEND 1573-and FN-CFG-ROWS-WITH-KEY.  If we let (:P A B K) denote *1 above then 1574-the induction scheme we'll use is 1575-(AND (IMPLIES (NOT (CONSP A)) (:P A B K)) 1576-     (IMPLIES (AND (CONSP A) -- 1592:Thus key checkpoint Goal is COMPLETED! 1593- ` | `certify-20260920T044850Z-38637` |
| `books/peer-inbound` | never certified (blocked on peer-config; its own forms have not been run past the include) | same run |
| `books/peer-inbound-invariants`, `tests/acl2/peer-inbound-tests` | never certified (blocked) | same run |
| `books/served` (edited), `tests/acl2/served-tests`, `books/ideal` | never certified on this branch (blocked on peer-inbound); `books/owner*` uncertified on dev already | same run |

Successor's first task: open `books/peer-config.lisp` in `ld` (driver: `(set-prover-step-limit 2000000)`, include `config`, `wildmat`, `path`), find the failing form named above, and fix it in place; the expected culprit is a lemma after the round-trip block that still opens the labels (disable `(:d fn-cfg-labelp)`, `fn-record-string-octets`, `fn-path-identityp`, `fn-wildmat-parse` in its hint, or make it local and ground). Then certify `peer-inbound`, `peer-inbound-invariants`, `peer-inbound-tests`, `served`, `served-tests`, `ideal` one at a time; the invariants' hints list the exact disables and may need `fn-peer-scope-groups` opened for K1's scope lemma.
