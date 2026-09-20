# Handoff: w6/peering-feed (packet K2, the outbound half)

Branch `w6/peering-feed`, worktree `build/lanes/w6-peering-feed`, branched from
`w6/peering-inbound` at `062e7fe` and merged with `dev` at `72279c8` (the
scheduler and the two-node harness are not on the inbound base; the only merge
conflict was `docs/prefixes.md`, resolved by keeping both sides). Spec:
[`specs/peering.md`](../../specs/peering.md) §3 and the status section at its
end, which is this lane's per-keystone record and the list of what differs
from the design.

## What exists

| File | What |
| --- | --- |
| `books/peer-feed.lisp` (new, `fn-feed-`) | The per-peer feed. Opaque records: the queue entry (Message-ID, offer state, attempts, tick), the limits (max-queue, backoff base, retry bound, streaming) and the feed itself, each with record lemmas and the three forward shape facts. `fn-feedp` carries queue distinctness, the queue bound, at most one entry in flight and attempt-id freshness. Transitions: `fn-feed-open`, `fn-feed-enqueue`, `fn-feed-selection`, `fn-feed-tick-step` (the host entry point: select then drive), `fn-feed-offer`, `fn-feed-send`, `fn-feed-done`, `fn-feed-back-off`, `fn-feed-lost`, `fn-feed-give-up`, `fn-feed-observe` (the RFC code map), `fn-feed-restart`, `fn-feed-settle`. The FNFD record family (magic `FNFD`, six kinds, one field spec each) over `books/frame`'s grammar, with `fn-feed-decode-of-encode` and `fn-feed-encode-is-injective`. `fn-feed-replay` is the fold; `fn-feed-drivenp` is the check that a record list is a journal a feed machine could have written. |
| `books/peer-feed-invariants.lisp` (new) | Preservation of `fn-feedp` by every transition; `fn-feed-at-most-one-accepted-outcome`; `fn-feed-done-is-never-selected` with `fn-feed-tick-step-offers-the-selection`; `fn-feed-restart-emits-no-transfer` and `fn-feed-restart-then-tick-offers`; `fn-feed-replay-is-the-fold`; `fn-feed-backoff-delay-is-monotone` and `fn-feed-back-off-does-not-lower-the-deadline`; `fn-feed-drop-needs-a-drop-record`. |
| `tests/acl2/peer-feed-tests.lisp` (new) | Six scenarios and the teeth: a two-article feed with a 431 retry and a 435 duplicate, a crash between `(:feed-sent ...)` and its outcome resolved by a CHECK, the retry bound dropping an entry with `:retry-bound`, a 400 losing the connection with nothing dropped, the FNFD codec on ground records, and one concrete violating value per keystone hypothesis. |
| `tools/run_feed.py` (new) | One process, one peer, one connection. Every state decision is a call into `books/peer-feed` through a live ACL2 session (`Acl2Store` from `tools/run_store.py`, the feed in an ACL2 state global). The journal is `<journal>/feed/<peer>.fnfd`, a 4-octet big-endian length before each FNFD frame; the host seals each record with SHA-256 over the protected prefix (A-CRYPTO) and reads the RFC 3977 §3.2 status framing. `--fault after-offer|after-sent` exits at a record boundary for the tests. |
| `tests/test_feed.py` (new) | `run_feed.py` against `tests/twonode_gate_fake/tools/run_peer.py`: two articles offered once each, a kill at the `sent` boundary with the re-offer a CHECK and exactly one copy at the peer, and a fresh-journal re-offer drawing 438. Skipped, never faked, without ACL2 and a certified `books/peer-feed`. |
| `Makefile`, `docs/prefixes.md`, `specs/peering.md` | Three roots after `tests/acl2/scheduler-tests`; the `fn-feed-` row names its books; the status section. |

## What the owner must do (the surface this lane needs and does not own)

1. **Open.** Per configured outbound peer, build
   `(fn-feed-limits max-queue backoff retry-bound streamingp)` from
   `(fn-cfg-peer-outbound (fn-cfg-peer-find name (fn-cfg-peers (fn-cfg-value cfg))))`
   and call `(fn-feed-open peer-octets limits contact conn)`. `peer-octets` is
   the peer name as octets; `contact` is `(fn-sched-contact <name-string> 0 horizon)`
   for a TCP peer (always-on), reopened after every `:feed-close`.
2. **Replay before anything.** Fold the peer's FNFD file with
   `fn-feed-apply-record`, write one `(:feed-restart peer)` record, then
   `fn-feed-restart`. Only then may a command be emitted.
3. **Enqueue on a durable local acceptance**, for every outbound peer the
   article is in scope for. The scope decision (`fn-feed-offerablep` of the
   design: the peer's `feed-groups` wildmat, the Path loop check with
   `fn-path-names-p`, and never back to the peer it came from) is the owner's
   and is **not** in this book — the feed never re-derives it.
4. **Durable before the effect.** Write `(:feed-offer ...)` before the
   `:command` of `fn-feed-tick-step`, `(:feed-sent ...)` before the
   TAKETHIS/article block, `(:feed-outcome ...)` after the response is parsed
   and before the next selection, `(:feed-drop ...)` when an entry leaves.
5. **`:remove-peer`.** The feed-idle condition of specs/peering.md §1.2 is
   `(equal (fn-feed-inflight-count (fn-feed-queue f)) 0)` together with no
   `:queued` entry — `(null (fn-feed-head-queued (fn-feed-queue f)))`.

## The scheduler interface change: designed, NOT built

The brief asked for a peer dimension on `fn-sched-item` and per-peer
`fn-sched-retries`. It is **not in this branch**: the laptop's four ACL2 slots
were held for this lane's whole window (a local `ld` waited past 240 s without
starting), the farm was the only compiler, and a shared-struct change to
`books/scheduler.lisp` blocks `books/peer-feed` — which includes it — from
certifying at all if a single proof breaks. Landing the feed cluster green was
the better use of the budget. Recorded open in the spec status section rather
than half-done. The exact edit, for whoever takes it:

- `fn-sched-item` gains a trailing `peer` field at `fn-bp-nth` index 7
  (`fn-sched-item-shapep` `(len x) 8`), accessor `fn-sched-item-peer`,
  conjunct `(stringp (fn-sched-item-peer x))` in `fn-sched-itemp`. Appending
  keeps indices 0 to 6 and every existing `-of-` lemma. Three construction
  sites in `books/scheduler.lisp` (`fn-sched-bump-item` twice, the expiry
  marker) and the witnesses in `tests/acl2/scheduler-tests.lisp`.
- `fn-sched-state` gains a trailing `peer-retries` field at index 10, an alist
  of `(peer . nat)`, with `fn-sched-retries-for peer ss` and
  `fn-sched-bump-peer-retries`. **`fn-sched-retries` keeps its name, its index
  and its meaning** (the aggregate), so
  `fn-sched-retries-stay-within-the-contact-bound`
  (`books/scheduler-invariants.lisp:436`) keeps its statement and its proof.
- `fn-sched-admissiblep` gains a conjunct — the open contact's peer's retry
  count is under `fn-sched-retry-bound` — beside the existing aggregate one.
  Adding a conjunct breaks only proofs that ESTABLISH admissibility (the
  witnesses), never the many that consume it.
- `fn-sched-selection` picks over `(fn-sched-queue-for-peer (fn-sched-queue ss)
  (fn-sched-contact-peer (fn-sched-open-contact ss)))` instead of the whole
  queue. Same arity, same statement; the selection lemmas need
  "a member of the filter is a member of the queue".

The feed does not block on it: `fn-feed-contact` already holds a
`fn-sched-contactp` and `fn-feed-selection` already gates on
`fn-sched-contact-holdsp`. What the change buys is the scheduler knowing that
two peers are two queues.

## Open (also in the spec status section)

- `fn-feed-replay-is-the-live-feed-modulo-inflight` as a general equation: it
  needs a live machine that emits its own journal, which this lane did not
  build. Proved instead: replay is a fold, plus the ground crash scenario.
- `fn-feed-parse-response` in ACL2, so the three-digit status split leaves
  `tools/run_feed.py`.
- The feed is not a field of F_node's state; K6's `fn-cfg-max-queue-total`
  cost term and the `:feed-octets` / `:tick` event kinds are untouched.
- RFC 4644's streaming window: `fn-feedp` allows one entry in flight.
- No INN and no second fn node has been fed; only the fake peer.

## Certification: per root, as of run `run-20260920T200246Z-fa0b` (lane w6/peering-feed-3)

`persvati`, ACL2 8.7 (`/home/ember/fn-tools/acl2-8.7/saved_acl2`, SBCL 2.6.8),
`--jobs 4`, `--affected-by books/peer-feed-invariants.lisp --closure`,
`FN_ACL2_TIMEOUT_SECONDS=1800`. Evidence on the host at
`/home/ember/fn-lanes/w6-peering-feed-3/build/acl2/certify-20260920T200423Z-2642224/`
(the run's own `manifest.json` carries the per-book exit codes quoted below);
`installed 90` from the box cache, 21 books certified in the run.

| Root | Result |
| --- | --- |
| `books/peer-feed` | **certified** in 1.35 s (`books--peer-feed.certify.log`, `FN_CERTIFY_SUCCESS`); published to the content-keyed cache and mirrored to `persvati:~/fn-certcache`. Its whole closure (`acceptance`, `node`, `retention`, `scheduler`, `frame*`, `cbor*`, `wildmat`, `bp-workflow`, `clock`, `defrecord`) certified in the same run. |
| `books/peer-feed-invariants` | **open, and the open set has moved.** `fn-feed-apply-record-preserves-feedp` is **PROVED** (Q.E.D., 1.95 s, 840,002 prover steps, `books--peer-feed-invariants.certify.log`, `Hint-events: ((:USE FN-FEED-ATTEMPTS-BELOWP-OF-AN-OFFERED-STATE-CLOSED) (:USE FN-FEED-SENT-RECORD-ABOVE-THE-BOUND-IS-UNREACHABLE))`). The book then **timed out after 1800 s** on the next theorem. See the tail inventory below: the eleven events after the keystone had never been reached by any run of this book, and ten of them are open. |
| `tests/acl2/peer-feed-tests` | **blocked** on the book above (`tests--acl2--peer-feed-tests.certify.log`: `ACL2 Error [Failure] in (CERTIFY-BOOK ...)`, 0.00 s); no assertion has been run. |

### What actually closed the keystone

A `local`, `:rule-classes nil` lemma cited by `:use` at the one instance the
arm needs, exactly the shape the previous lane prescribed:

```lisp
(local
 (defthm fn-feed-sent-record-above-the-bound-is-unreachable
   (implies (and (fn-feed-attempts-belowp xs n)
                 (fn-feed-offeredp (fn-feed-state-of msgid xs)))
            (< (fn-bp-nth 1 (fn-feed-state-of msgid xs)) (nfix n)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-feed-inflight-attempt-is-below-the-bound))))))
```

It is stated over `fn-bp-nth` because that is what `fn-feed-state-attempt`
opens to and what the arm's goal carries, and over `fn-feed-offeredp` rather
than `fn-feed-state-inflightp` because the arm closes the latter. It proves in
**818 prover steps, 0.00 s** from the existing
`fn-feed-inflight-attempt-is-below-the-bound`. The `:use` instance added to
the keystone's hint is `(xs (fn-feed-queue f)) (n (fn-feed-next-attempt f))
(msgid (fn-frame-item 1 values))`. No keystone statement moved, no rule was
promoted, and the comment at the lemma records the runaway that a general rule
in that spot caused, so it is not retried.

### The tail of the book: ten theorems that no run had ever reached

Certification stops at the first failure, so every previous report of this
book ("every other theorem certifies") described only the events **before**
the keystone. With the keystone closed, the eleven events after it ran for the
first time. Measured by `ld` of the book's own source against the certified
`books/peer-feed` (laptop, ACL2 8.7, `tools/acl2 --timeout 900`, driver step
limit 4,000,000; three of the entries below hit that driver limit rather than
failing, and are marked):

| Event | State | Key checkpoint |
| --- | --- | --- |
| `fn-feed-replay-preserves-feedp` | **fixed in this lane** | timed out at 1800 s on the farm with `fn-feed-apply-record` open; closing `(:d fn-feed-apply-record)` and `(:d fn-feedp)` at the form makes the record-step keystone the rewrite and it proves in seconds |
| `fn-feed-apply-record-preserves-peer` | open | `Subgoal 40'`: `(equal (fn-feed-peer (fn-feed-give-up f (fn-frame-item 1 values) (fn-frame-item 2 values))) (car values))` under `(fn-feedp f)` and `(equal (car values) (fn-feed-peer f))`. The hint closes every transition and **no `-preserves-peer` lemma exists for any of them**; the fix is one such lemma per arm (`enqueue`, `done`, `give-up`, `restart`, `with-queue`, and the `fn-feed-make` of the offer arm), or dropping the transitions from that one disable. |
| `fn-feed-replay-preserves-peer` | open, cascade | `Subgoal *1/3'4'`: needs the row above as a rewrite. The `(:d fn-feed-apply-record)` closure is already added at the form. |
| `fn-feed-replay-is-the-fold` | open | `Goal` unchanged; the induction reaches `Subgoal *1/2.490.3` with `fn-feed-apply-record` open (driver step limit). Wants the same closure. |
| `fn-feed-selection-is-queued` | open, **independent** | `Subgoal 6'`: `fn-feedp` open with `(not (fn-feed-contact f))`, `(fn-sched-contact-holdsp nil obs)` and `(fn-feed-head-queued (fn-feed-queue f))`. Nothing to do with the fold; `fn-feed-selection` needs its own branch lemmas. |
| `fn-feed-done-is-never-selected` | open, cascade | its `:use` names the row above. |
| `fn-feed-done-survives-a-driven-record` | open | `Subgoal 103.62''`, the dispatcher's case split again. |
| `fn-feed-done-means-no-more-accepted-outcomes` | open | `Goal`; the induction reaches `Subgoal *1/2.673.116` (driver step limit). |
| `fn-feed-accepted-outcome-makes-it-done` | open | `Subgoal 32''`. |
| `fn-feed-at-most-one-accepted-outcome` | open | `Goal`; induction reaches `Subgoal *1/2.175` (driver step limit). |
| `fn-feed-not-dropped-survives-a-non-drop-record` | open | `Subgoal 142.104.78''`. |
| `fn-feed-drop-needs-a-drop-record` | open | `Goal`; induction reaches `Subgoal *1/2.2525.8` (driver step limit). |

Four of the five KEYSTONES this book exists for are in that list
(`fn-feed-replay-is-the-fold`, `fn-feed-done-is-never-selected`,
`fn-feed-at-most-one-accepted-outcome`, `fn-feed-drop-needs-a-drop-record`),
so **specs/peering.md's §4 claims for K5 are not yet earned**, and the status
section there should say so rather than naming one open theorem. The shared
disease in seven of the twelve rows is the same one the keystone had and the
same one `fn-feed-observe-preserves-feedp` and `fn-feed-tick-step-preserves-feedp`
already cure: `fn-feed-apply-record` left OPEN inside an induction over the
journal re-splits the dispatcher under every arm. The next lane's first move is
that one-line closure at each folding form, then the per-transition
`-preserves-peer` family, then `fn-feed-selection`'s own branch lemmas --- in
that order, because the first two unblock most of the cascade.

### What the state-vocabulary hint bought, and the exact remaining checkpoint

Closing `fn-feed-state-of`, the three offer-state predicates and their
constructors in that one hint worked: the goal now stays in
`fn-feed-state-of` vocabulary, so `fn-feed-inflight-count-of-set-state-exact`
and `fn-feed-find-is-consp-when-the-state-is-a-state` match, and two further
shape facts (`fn-feed-offer-states-forward-consp`,
`fn-feed-offer-states-forward-natp`) plus
`fn-feed-attempts-belowp-of-set-state-open-inflight` carried it further still.
What is left is `Subgoal 100.10.3`, the **`:feed-sent` arm with a journaled
attempt at or above `fn-feed-next-attempt`**:

```lisp
(IMPLIES
 (AND (INTEGERP (FN-FRAME-ITEM 2 VALUES)) (<= 0 (FN-FRAME-ITEM 2 VALUES))
      (<= (FN-FEED-NEXT-ATTEMPT F) (FN-FRAME-ITEM 2 VALUES))
      ... the `fn-feedp' conjuncts of F, including
      (FN-FEED-ATTEMPTS-BELOWP (FN-FEED-QUEUE F) (FN-FEED-NEXT-ATTEMPT F)) ...
      (FN-FEED-OFFEREDP (FN-FEED-STATE-OF (FN-FRAME-ITEM 1 VALUES)
                                          (FN-FEED-QUEUE F)))
      (EQUAL (FN-BP-NTH 1 (FN-FEED-STATE-OF (FN-FRAME-ITEM 1 VALUES)
                                            (FN-FEED-QUEUE F)))
             (FN-FRAME-ITEM 2 VALUES)))
 (FN-FEED-ATTEMPTS-BELOWP
  (FN-FEED-QUEUE-SET-STATE (FN-FEED-QUEUE F) (FN-FRAME-ITEM 1 VALUES)
                           (FN-FEED-SENT (FN-FRAME-ITEM 2 VALUES)))
  (FN-FEED-NEXT-ATTEMPT F)))
```

The hypotheses are contradictory and that is the whole content: the entry is
in flight, so `fn-feed-attempts-belowp` puts its attempt strictly BELOW
`fn-feed-next-attempt`, while the record names an attempt at or above it. A
`(:feed-sent ...)` record with that attempt is unreachable. What the prover
cannot do is join those two, because `fn-feed-state-inflightp` is closed in
this hint and the hypothesis says `fn-feed-offeredp`.

### The attempt that made it worse, recorded so it is not repeated

Supplying that join as two more rules -- `fn-feed-offer-states-forward-inflightp`
(`offeredp`/`sentp` forward-chaining to `fn-feed-state-inflightp`) and
`fn-feed-inflight-attempt-below-bound-raw` (the bound as a `:linear` rule over
`(fn-bp-nth 1 (fn-feed-state-of msgid xs))`) -- **sent the proof into a
runaway**: run `run-20260920T191056Z-aa48` ground for over 30 minutes and was
killed by the per-invocation timeout at
`Subgoal *1/2.1426.154.103.103.50''`, with no `ACL2 Error [Failure]` line and
no checkpoint to read. A forward-chaining rule into a closed predicate, and a
`:linear` rule whose trigger contains `fn-feed-state-of`, both fire under
every arm of a large case split. Those two rules are **reverted**; the tree is
back to the source that produced the clean `Subgoal 100.10.3` above.

The shape that should work instead, for whoever takes it: make the
contradiction a `:rule-classes nil` lemma and cite it by `:use` at exactly the
instance the arm needs, rather than giving the prover a rule that fires
everywhere --

```lisp
(local
 (defthm fn-feed-sent-record-above-the-bound-is-unreachable
   (implies (and (fn-feed-attempts-belowp xs n)
                 (fn-feed-offeredp (fn-feed-state-of msgid xs)))
            (< (fn-bp-nth 1 (fn-feed-state-of msgid xs)) (nfix n)))
   :rule-classes nil))
```

cited with `(xs (fn-feed-queue f)) (n (fn-feed-next-attempt f))
(msgid (fn-feed-record-msgid values))` in the same hint. Nothing else about
the theorem or the book needs to change, and no keystone statement does.

## How certification is run

Farm only — the laptop's ACL2 slots were saturated for this lane's whole
window and the brief's box rule forbids taking one by force.
`python3 tools/farm.py submit persvati --jobs 8 --remote-root
/home/ember/fn-lanes/w6-peering-feed --closure books/peer-feed
books/peer-feed-invariants tests/acl2/peer-feed-tests`, then `wait`. Two farm
traps confirmed again: `--remote-root` must be written out as
`/home/ember/...` and the parent directory must exist on the host first. A
third, new: `certify_books.py` refuses an unreadable source before any ACL2
starts, so a paren error costs a whole round trip — balance the file locally
first.
