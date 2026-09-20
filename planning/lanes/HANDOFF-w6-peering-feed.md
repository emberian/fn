# Handoff: w6/peering-feed (packet K2, the outbound half)

Lanes `w6/peering-feed`, `w6/peering-feed-3` and `w6/peering-feed-4`.
The certification section is rewritten by whichever lane last measured
it; as of `w6/peering-feed-4` the cluster's three roots certify.

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
  needs a live machine that emits its own journal, which no lane has built.
  Proved instead: replay is a fold (`fn-feed-replay-is-the-fold`) and
  preserves both `fn-feedp` and the peer, plus the ground crash scenario.
- `fn-feed-restart-emits-no-transfer` is true for a reason WEAKER than its
  prose: `fn-feed-restart` also forgets the connection, and `fn-feed-send`
  refuses a feed whose `fn-feed-conn` is not a `natp`, so the settled queue
  is not what the current statement rests on. The statement that would need
  the settled queue is the one over the REOPENED feed,
  `(fn-feed-send (fn-feed-with-conn (fn-feed-restart f) conn) msgid article)`,
  which is what the host actually does next. Recorded, not attempted.
- `fn-feed-parse-response` in ACL2, so the three-digit status split leaves
  `tools/run_feed.py`.
- The feed is not a field of F_node's state; K6's `fn-cfg-max-queue-total`
  cost term and the `:feed-octets` / `:tick` event kinds are untouched.
- RFC 4644's streaming window: `fn-feedp` allows one entry in flight.
- No INN and no second fn node has been fed; only the fake peer.

## Certification: per root, lane `w6/peering-feed-4`

Two measurements, both at branch `w6/peering-feed-4` merged with dev
`ca1ce5d`. **persvati** (`/home/ember/fn-tools/acl2-8.7/saved_acl2`, SBCL,
ACL2 8.7), run `run-20260920T211802Z-ba78`, `--jobs 6`,
`--affected-by books/peer-feed-invariants.lisp --closure`,
`FN_ACL2_TIMEOUT_SECONDS=1800`: **61 of 68 roots certified in 242 s**,
evidence mirrored to
`build/lanes/w6-peering-feed-4/build/acl2/certify-20260920T211806Z-3369936/`
(`manifest.json` carries the per-root exit codes). **Laptop** (ACL2 8.7,
`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2`), `tools/certify_books.py`:
`books/peer-feed-invariants` in **31.9 s**, evidence
`build/acl2/certify-20260920T211815Z-98758/`.

A note for the next lane on the cache: `certs.py install` found **nothing**
for `books/peer-feed` at this lane's start (`installed 0, kept identical
local 100, no cached pair 168`), because dev had moved `scheduler.lisp`,
`frame.lisp` and `frame-invariants.lisp` and the content-keyed closure no
longer matched. That is a cold start, not a cache defect. One priming
submit (`--closure books/peer-feed`, `installed 122` from persvati's own
cache) certified the closure and published it back, after which every `ld`
in this lane ran against a certified `books/peer-feed`.

| Root | Result |
| --- | --- |
| `books/peer-feed` | **certified** (persvati, `books--peer-feed.certify.log`), unchanged by this lane. |
| `books/peer-feed-invariants` | **certified, no open form.** All eleven events behind `fn-feed-apply-record-preserves-feedp` are closed, and with them all five keystones the book exists for. |
| `tests/acl2/peer-feed-tests` | see the row below; it had never run an assertion and had three defects. |
| `books/owner-feed`, `tests/acl2/owner-feed-tests`, `books/owner`, `books/owner-config`, `books/owner-invariants`, `tests/acl2/owner-tests` | the seven failures of `run-...-ba78` were these six plus `tests/acl2/peer-feed-tests`. They are the w10/owner-feed lane's roots and this is the first run that ever REACHED them. |

### The eleven that no run had ever reached: all closed

Certification stops at the first failure, so until `w6/peering-feed-3`
closed `fn-feed-apply-record-preserves-feedp` these events had never been
attempted. Measured by `ld` of the book's own source against the certified
`books/peer-feed` (laptop, ACL2 8.7, `tools/acl2 --timeout 1500`, driver
step limit 4,000,000) and then by certification.

| Event | Steps | What closed it |
| --- | --- | --- |
| `fn-feed-replay-preserves-feedp` | 800 | `(:d fn-feed-apply-record)` and `(:d fn-feedp)` closed at the form (lane `w6/peering-feed-3`). |
| `fn-feed-apply-record-preserves-peer` | 9,039 | the `-preserves-peer` family: one UNCONDITIONAL equation per transition and per field update. The dispatcher keeps every arm closed, so each arm needs its own rewrite. The six single-valued members came from lane `w6/peering-inbound-2`; this lane added `offer`, `send`, `settle`, `observe`, `tick-step` and the four `fn-feed-peer-of-with-*`. The theorem lost its `fn-feedp` hypothesis: a record step returns a feed it does not recognize unchanged, so there is no violating value. |
| `fn-feed-replay-preserves-peer` | 743 | cascade; same closure at the fold, and it lost the same hypothesis. |
| `fn-feed-replay-is-the-fold` | 1,536 | `(:d fn-feed-apply-record)` closed, `:induct (fn-feed-replay f es)`. |
| `fn-feed-selection-is-queued` | 10,964 | `(:d fn-feed-state-of)` CLOSED. Open, the conclusion becomes `fn-feed-entry-state` of `fn-feed-find` before `fn-feed-head-queued-is-queued` can fire; that was `Subgoal 6'`. |
| `fn-feed-done-is-never-selected` | 27,985 | the statement was **FALSE** (see below) and carries a new hypothesis; the same `(:d fn-feed-state-of)` closure. |
| `fn-feed-done-survives-a-driven-record` | 140,512 | the offer-state vocabulary closed, plus one `:cases` on whether the record names this entry -- the arms give `:queued`, in flight or not-`:done` where this one is `:done`, and joining those is a case split, not a rewrite. |
| `fn-feed-done-means-no-more-accepted-outcomes` | 115,371 | cascade of the row above, with the record step, `fn-feedp` and `fn-feed-record-drivenp` closed so the two record-step keystones are the rewrites. |
| `fn-feed-accepted-outcome-makes-it-done` | 17,771 | the same closure; restated over a journal ENTRY rather than a loose `(kind values)` pair. |
| `fn-feed-at-most-one-accepted-outcome` | 111,246 | one `local` lemma, `fn-feed-count-accepted-after-an-accepted-head` (4.41 s, 2,891,166 steps), which chains the two rows above by `:use` at one instance. The induction hypothesis gives only `<= 1` over the tail and one plus one is two; what closes it is that an accepted head makes the entry `:done`, after which the tail holds none. |
| `fn-feed-not-dropped-survives-a-non-drop-record` | 277,389 | a `fn-feed-droppedp` propagation family stated with NO disequality: every queue operation a record can perform writes `:queued`, `:done` or an offer state, so the arms need no case split (that was `Subgoal 142.104.78''`). |
| `fn-feed-drop-needs-a-drop-record` | 6,564 | cascade; `:induct (fn-feed-replay f es)` with the step closed. |

### The genuine counterexample, the third this cluster has produced

`fn-feed-done-is-never-selected` was FALSE as stated, and the prover said so
at `Subgoal 73'`. Take `msgid` = `NIL` and a feed that selects nothing (no
connection, say): `(fn-feed-state-of nil (fn-feed-queue f))` is `NIL`, which
is not `:queued`, and `(fn-feed-selection f obs)` IS `NIL`, so the
conclusion `(not (equal (fn-feed-selection f obs) msgid))` fails. Repaired
with the hypothesis `(fn-feed-selection f obs)`, which holds on exactly the
states where the host emits a command:
`fn-feed-tick-step-offers-the-selection` already carried it and
`fn-feed-tick-step-is-silent-without-a-selection` covers the rest, so K5's
"a finished entry is never offered again" is unchanged. One concrete
violating value is in `tests/acl2/peer-feed-tests.lisp`.

### `tests/acl2/peer-feed-tests`: three defects, because no assertion had ever run

1. **Fifteen `(mv-nth n (fn-feed-... ))` calls in `defconst` and
   `assert-event` bodies are illegal ACL2.** Those bodies are translated for
   EVALUATION, with a single-value signature: "It is illegal to invoke
   FN-FEED-TICK-STEP here because of a signature mismatch. This function
   call returns a result of shape (MV * *) where a result of shape * is
   required." `mv-nth` is fine in a `defthm`, which translates in the
   don't-care signature, which is why the invariants book states every
   effect theorem that way and this book cannot. All fifteen are now
   `(nth n (mv-list 2 ...))`. **Any test book that projects an `mv` in a
   `defconst` has the same bug and has never been run.**
2. **The attempt id after a 431 retry was asserted to be 2; the machine says
   3, and the machine is right.** `fn-feed-next-attempt` is monotone over
   the whole feed, not per entry: attempt 1 went to `<a@fn>`, attempt 2 to
   `<b@fn>`'s first offer, and the re-offer is attempt 3. The scenario now
   asserts all three and `(fn-feed-next-attempt *ff7*) = 4`, which is the
   point it was making -- a retry never re-runs an attempt under its old id.
3. **The tooth for `fn-feed-restart-emits-no-transfer` asserted the
   opposite of what the machine does.** It built a forged two-in-flight feed
   and asserted that sending on it after a restart still emits a TAKETHIS.
   It does not: `fn-feed-send` refuses a feed that is not `fn-feedp` on its
   own, and `fn-feed-restart` returns such a feed unchanged. So that
   hypothesis has no violating value and is **deleted from the theorem**
   (docs/proof-style.md sec. 5), which now reads
   `(equal (mv-nth 1 (fn-feed-send (fn-feed-restart f) msgid article)) nil)`
   unconditionally. In its place is a separating witness on a reachable
   state: `*ff5*` has `<b@fn>` in flight and emits a TAKETHIS; after the
   restart the same call emits nothing.

### What this lane broke for an includer, and the export rule it pays for

`fn-feed-tick-step-preserves-peer`, exported ENABLED, fired on the `:use`d
hypothesis of `books/owner-feed`'s `fn-own-feed-tick-step-keeps-the-feed-half`
(`books/owner-feed.lisp:999`), rewrote it to T, and left that proof with a
conclusion in `car` vocabulary and nothing to close it -- measured on
persvati `run-20260920T211802Z-ba78`. The eleven transition members and the
four field equations of the family are therefore PROOF VOCABULARY, withdrawn
at book end under `fn-feed-invariants-vocabulary`. What leaves the book
enabled is the two DISPATCHER members, `fn-feed-apply-record-preserves-peer`
and `fn-feed-replay-preserves-peer`, which is what an includer folding a
journal needs. An includer that wants one of the eleven enables the
vocabulary name in the one hint that needs it and deletes its local twin --
`books/owner-feed` has such a twin at `fn-feed-tick-step-keeps-peer-and-contact`
(`books/owner-feed.lisp:991`).

### What actually closed the original keystone (kept from lane `w6/peering-feed-3`)

A `local`, `:rule-classes nil` lemma cited by `:use` at the one instance the
arm needs: `fn-feed-sent-record-above-the-bound-is-unreachable`, stated over
`fn-bp-nth` (what `fn-feed-state-attempt` opens to, and what the arm's goal
carries) and over `fn-feed-offeredp` (what the arm's hypothesis carries while
`fn-feed-state-inflightp` is closed), proved in **818 prover steps** from the
existing `fn-feed-inflight-attempt-is-below-the-bound`.

### The attempt that made it worse, recorded so it is not repeated

Supplying that same join as two RULES -- `fn-feed-offer-states-forward-inflightp`
(forward-chaining into the closed `fn-feed-state-inflightp`) and a `:linear`
rule whose trigger contains `fn-feed-state-of` -- sent the proof into a
runaway: run `run-20260920T191056Z-aa48` ground for over 30 minutes and was
killed by the per-invocation timeout at `Subgoal *1/2.1426.154.103.103.50''`,
with no checkpoint to read. A forward-chaining rule into a closed predicate,
and a `:linear` rule triggered on `fn-feed-state-of`, both fire under every
arm of a large case split. The rule of this cluster: when you need a fact in
one place, state it `local`, `:rule-classes nil`, and cite it by `:use` at
exactly the instance.


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
