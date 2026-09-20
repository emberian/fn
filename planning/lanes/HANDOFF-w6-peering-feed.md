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

## Certification

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
