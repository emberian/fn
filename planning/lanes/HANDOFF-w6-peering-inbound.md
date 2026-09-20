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

## Per-root state, successor lane `w6/peering-inbound-2` (branch from `dev`
## at 52eb0db, merged `dev` again at cda964e; worktree
## `build/lanes/w6-peering-inbound-2`)

| Root | State | Evidence |
| --- | --- | --- |
| `books/peer-config` | certified | persvati `run-20260920T173911Z-6cf7`, `build/acl2/certify-20260920T173915Z-1242593`. Closed independently on `dev` as well (clock-seam lane); this lane merged `dev` and kept `dev`'s version. The failure was two missing facts, `(fn-record-ascii-stringp (fn-cfg-peer-name p))` and `(<= (len (fn-cfg-peer-rows p)) 1024)`, plus a hint that disabled `fn-cfg-labelp` as a whole symbol and so withdrew its executable counterpart. |
| `books/peer-inbound` | **all definitions admit**; open at the theorem `fn-peer-echo-reply-effects-well-formed` | hbox `run-20260920T183108Z-1096`, `/tank/fn/lanes/w6-peering-inbound-2/build/acl2/certify-20260920T183458Z-1061518` (pre-fix), then `ld` on hbox (`/tank/fn/acl2-8.7/saved_acl2`) |
| `books/peer-inbound-invariants`, `tests/acl2/peer-inbound-tests`, `books/served`, `tests/acl2/served-tests`, `books/owner`, `books/owner-invariants`, `tests/acl2/owner-tests`, `books/ideal` | blocked on `books/peer-inbound` (all fail with "no certificate on file") | same hbox run |

### What this lane fixed in `books/peer-inbound`

Two translate errors stopped every definition in the book, and with them
`books/served`, `books/owner` and the served host, whose `ld` loads them:

1. `fn-peer-decide-offer` called `fn-charge-for-payload`, which
   `books/identity` defines and which was in no book of the include closure.
   `(include-book "identity")` added (it includes only `books/frame`).
2. `fn-nntp-capability-lines` gained a `postingp` argument on `dev`.
   `fn-peer-capability-lines` takes it too and `fn-peer-command` passes
   `nil`: a transit connection reads only its session, carries no injection
   configuration, and so does not promise POST (RFC 3977 3.2.2/3.3.2
   advertise only what is served). **If the test book pins a CAPABILITIES
   transcript containing POST on a peer connection, that pin changes.**

### The one open form, with its exact remaining obligation

`fn-peer-echo-reply-effects-well-formed` (`books/peer-inbound.lisp`).
The `fn-nntp-response-textp` half is now discharged: the hint keeps the
append closed (`(:d binary-append)`, `(:d fn-nntp-string-octets)` withdrawn)
and cites `fn-nntp-response-text-of-append` and
`fn-nntp-printable-token-is-response-text`. The remaining checkpoint is

```
Subgoal 12'
(IMPLIES (AND (NOT (FN-NNTP-INITIAL-STATUS-LINEP (APPEND '(50 51 56 32) MSGID)))
              (FN-NNTP-PRINTABLE-TOKENP MSGID)
              (FN-AF-MESSAGE-IDP MSGID))
         (FN-NNTP-REPLYP (FN-NNTP-CRLF (APPEND '(50 51 56 32) MSGID))))
```

i.e. the RFC 3977 3.1 initial-line bound. What is needed is a length lemma
`(implies (fn-af-message-idp msgid) (<= (len msgid) <bound>))` (RFC 5536
bounds a Message-ID) and then `fn-nntp-initial-status-linep` of a
three-digit code, a space and that many octets. State it once,
`:rule-classes nil`, in the book that owns `fn-af-message-idp`
(`books/article-fields.lisp`) or locally here, and `:use` it.

### Box note

`ld` on hbox is `/tank/fn/acl2-8.7/saved_acl2`, not `$HOME/fn-tools/...`
(that path is persvati's). persvati was heavily contended during this lane
and one run lost `books/nntp-effects` to a dependency race under
`--jobs 12`, cascading "no certificate" failures into six roots; hbox
answered the same closure with `installed 188, uncached 52`.

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
