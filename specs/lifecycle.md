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
