# One letter through the system

Status: acceptance scenario and design exercise, not executed behavior. Machine-
readable cases are in the [scenario catalog](../tests/scenarios/catalog.json).

## Participants

`home`, `relay-a`, `relay-b`, and `destination` are independently writable nodes
in a closed test community. `letter-1` has a stable Message-ID, an immutable
source object, and membership in two configured local groups. Native signatures
exercise the selected D02 capability. No live hosts or real recipients are implied.

## The normal path and its interruptions

1. The author prepares the letter offline and preserves its Message-ID across
   retries. The source representation and provenance are explicit.
2. Home validates it, reserves the chosen retention/delivery capacity, and
   prepares one transaction for the content, both memberships, and obligations.
3. Crash before a complete durable commit: no partial membership or acceptance
   can be published. Orphan bytes may remain without becoming a visible article.
4. Retry and commit. Home publishes both memberships and emits success.
5. Lose the reply. Posting the same identity again produces no second membership
   or numbering allocation; the wire duplicate response follows the profile.
6. Home prepares a portable batch for relay-a, with content dependencies and
   scoped terms. Transfer pauses, resumes, and duplicates some chunks.
7. Relay-a persists content and its accepted obligation, then sends a matching
   receipt. Lose that receipt; replaying the transfer must not multiply effects.
8. Relay-a restarts after a long outage. Recovery restores its obligation and
   resource accounting. It can regenerate the required receipt.
9. Home records sufficient release evidence durably. It may discharge that
   forwarding obligation while its independent local archive pin remains.
10. Relay-a passes the batch through relay-b using carried media. Destination
    eventually imports overlapping batches in a different order.
11. Destination presents the article once in each selected local group. Its group
    numbers need not match home's. It records application acceptance separately
    from transport reception; no human-read claim follows.
12. Under explicitly selected policy, obligations are released. Compaction or GC
    preserves all remaining roots, numbering history, and required evidence.

## Negative branches

- A wrong-subject or old-incarnation receipt does not release a new obligation.
- A full node refuses an undertaking it cannot reserve; it does not acknowledge
  and then silently evict the letter.
- A clock jump cannot resolve a conflict or silently discharge a promise.
- A digest mismatch or missing dependency prevents complete publication.
- A source variant with different relay headers is not automatically a forgery;
  genuinely conflicting authorship remains visible as evidence under policy.
- Restoring an old node snapshot cannot silently issue a different event under
  an already used origin/incarnation/counter identity.
- A storage error after a write may leave an indeterminate commit. Mutations
  pause for recovery; a failed syscall does not prove the transaction is absent.

## Success criterion

The complete scenario has a trace connecting logical state, persistent bytes,
host events, and observed protocol replies. Each assertion identifies a requirement,
proof/test evidence, and external assumptions. Implement it progressively through
the [milestones](../planning/milestones.md), rather than labeling this narrative
itself a demonstrated end-to-end guarantee.

## The warranted lifecycle (GPT-6 section 9; row W6, 2026-09-29)

One cross-cutting lifecycle, stated as prefixes; for every prefix the
observable outcome, the retained evidence, the ownership state and the
resource charge, and who establishes it. Machine-readable: SCN-212. The
contract's terms are [the productive contract](productive-contract.md).
"Proved" names the theorem; "lane" names the live lane whose brief covers
it; "open" is owed and nobody's yet.

| # | prefix ends with | observable outcome | retained evidence | ownership state | resource charge | coverage |
|---|---|---|---|---|---|---|
| 1 | accept a post (valid, authorized, funded; the nine specified completions) | 240 on the wire (`*fn-pcx-240-line*`) | the record in `fn-sf-records`, its pair in the successes and the ledger | the identity bound; the article's number issued | the record's charge, the frontier and one history slot | proved: `fn-pcx-post-productive` PRF-1001, `fn-pcx-observer-240` PRF-1003; safety `fn-own-240-follows-consumed-completion` |
| 2 | lose its acknowledgement (the socket dies after the completion is consumed) | nothing at the client; if the host still renders, an uncertain that names `:effect-failed-after-publication` | unchanged from 1: the record stands | unchanged | unchanged (no refund for a lost reply) | proved: `fn-pcx-uncertain-has-a-named-cause` PRF-1002; the crash cut after publication: byte-model / `native_program_check` (every process-death cut a model crash point) |
| 3 | restart | the store reopens on the fenced prefix; no reply | the history replayed exactly (`fn-snrt-mixed-trace-ready-node-is-exact-replay`); numbers kept (`fn-ndur-` PRF-903) | the same identity binding after replay | the same charges after replay | proved (store); the configured open `fn-cpo-open-observed` is the host's subject; lane **store-lineage** (a fork of the same store after an empty suffix) |
| 4 | reconcile the original operation (the client retries the same Message-ID) | 441 duplicate by name; no second number | the binding that decides the duplicate (`fn-pidx-` PRF-191) | unchanged | no new charge; the refused submission may consume an allocator identity (a refusal's footprint, GPT-6 section 6) | proved: `fn-pidx-existing-action`, PRF-191; the operation identity across a restart: **open** (an idempotency token is not carried; the Message-ID is the reconciliation key) |
| 5 | read through the indexed view (ARTICLE by number, by Message-ID) | 220 and the article's octets | the pinned view's version; the catalog join (`fn-mpxt-` PRF-969/970) | reader pinned at a version at or after 1 | the pin holds the version below the reclaim floor (`fn-own-min-pinned`) | lane **paged-history-3** (the catalog equality, the writer's preservation); the productive read: **open** (productive-contract.md section 5) |
| 6 | two independent holds (local pin and forwarding obligation) | none | two retention pins with their evidence | the article held twice; neither discharge releases the other | the retained bytes charged once, the obligations twice | proved for the retention pins (`fn-retain-`, specs/retention.md); independent contributions to one aggregate: lane **incremental-finalize-3** (the finalize's resume, PRF-968); outbound local offer/send core progress PRF-1055/1062 with PRF-1056 quiet/refusal, union certification/native evidence pending |
| 7 | discharge one | none (a release event) | the release evidence, the surviving pin | held once | the released obligation's charge freed; bytes still charged | proved: release events (`fn-replay-apply-retention-event`, bp-release-tests); wrong-subject/old-incarnation receipts do not release (specs/bp-receipt.md) |
| 8 | compaction with the second hold outstanding | none; every reader's answer unchanged | the surviving pin, the record kept (a held article is never tombstoned) | held once | bytes still charged | store-reclaim-pack: well-formed and idempotent; the FUTURE-OBSERVATION equivalence (every continuation observes the same): lane **reclaim-equivalence** (W8) |
| 9 | discharge the other | none | the release evidence; the record now reclaimable | held by no one | obligations freed; bytes still charged until reclaim | proved (release); reclaimable-by-decision `fn-lgr-decide` is a construction theorem, not an execution one (GPT-6 section 1): **open** — the checkpoint written, installed, crash, reopen |
| 10 | reclaim the payload | ARTICLE 430 / 423 by name, never "not accepted" | the tombstone: identity, number, obligation fields kept; content bytes freed; transaction count NOT freed (resource-contract) | reclaimed, not absent: `accepted and legitimately reclaimed` distinct from `not accepted` | content bytes refunded; identity history still charged | store-reclaim-pack (fields, shape, idempotence); the five-way distinction at the reader (GPT-6 section 6) and the tombstone's answer on the served read: **open**; the history-lifetime policy for the identity history: **open** (decision needed) |
| 11 | retry the original operation again | 441 duplicate by name (the identity is retained through reclaim) | the tombstone's identity | unchanged | no allocation | **open**: that a reclaimed identity record still refuses the conflicting retry is exactly the case `Observe(Continue(S,E)) = Observe(Continue(C(S),E))` catches — lane **reclaim-equivalence**; until it lands, this is the sharpest unproved prefix |

Cuts during compaction and delayed I/O completion (GPT-6: "including cuts
during compaction and delayed I/O completion") are prefix 8 with a crash
point between any two of the pack's writes, and prefix 1 with any answer
delayed: the first is lane reclaim-equivalence's crash matrix (owed), the
second is covered by the fenced phases (`:fenced-frontier`, `:fenced-record`:
the host recovers, never finishes; `specs/store-node.md`) and by
PRF-1002's named causes.

The gap list, in one line each: (a) the productive read and the productive
inbound durable peer transfer (section 5 of the contract) remain open;
outbound local offer/requested-send core theorems PRF-1055/1056/1062 are
REPL-admitted with complete teeth, with union certification and matching native
evidence pending; (b)
operation reconciliation across a restart rests on the Message-ID, not an
operation identity; (c) the execution theorem for a reclaim decision
(checkpoint written, installed, crash, reopen) does not exist; (d) the
tombstone's answer on the served read must be "reclaimed", distinct from
"not accepted" and "unavailable", and is not yet a served-path theorem;
(e) the identity history has no lifetime policy (a decision); (f) prefix
11, the retry after reclaim, is the theorem lane reclaim-equivalence owes
and the one that makes compaction a semantic transition rather than an
optimization.
