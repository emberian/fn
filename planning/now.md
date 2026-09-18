# Current work: first executable acceptance cycle

The full [decision workbook](decisions.md) is a backlog, not a questionnaire that
must be completed before coding. The current bounded experiment needs no further
product decisions. Open byte-format and cryptographic choices remain open.

## Outcome

Build and actually run a small ACL2 model of local acceptance: one immutable
article, two configured groups, one pending transaction, a retained archive pin,
and publication only after a matching abstract durable-completion event.
Exercise retries, wrong/stale completions, and indeterminate persistence results.
Obtain the first meaningful mechanically checked results if the toolchain can
be established. Report precisely which properties and guards were checked.

This is a portion of M1. A simulated durable-completion event is an environmental
contract, not a proof of filesystem durability. No cryptographic primitive,
native article serialization, NNTP wire codec, or public service is in this cycle.

## Swarm cycle authorized on 2026-09-18

| Role | Bounded responsibility |
| --- | --- |
| Luna | Executable ACL2 acceptance definitions and first theorem attempts |
| Terra | Reproducible ACL2 toolchain and truthful certification/test runner |
| Sol | Independent adversarial design and code/proof review |
| Astra | Integrate, resolve routine choices, check evidence, maintain project state |

One writer owns each implementation area. Review findings return to the owning
agent for repair. Completion requires actual execution evidence and review of
the resulting artifact; the existence of a theorem form is insufficient.

## Deliberate abstraction choices

- Exact Message-ID strings and payload octets; no native signing preimage yet.
- Configured local groups; a post naming an unknown group rejects atomically.
- Indefinite local archive pin, matching the selected D03 policy.
- One owner and one pending transaction; independent I/O is represented by events.
- Explicitly distinct prepared, committed, and uncertain states/results.
- No automatic expiry, release, or history pruning in this slice.

These choices bound the experiment; they do not freeze future persistent schemas
or the host integration ABI. An outcome/evidence link will be added here when the
cycle completes.

## Decisions to discuss next

Bring concrete examples instead of the entire backlog: first the immutable native
article/signature boundary (D01), then principal/key custody and rotation (D09).
Group encryption selection is a separate research/design track. Shared community
groups come first; MLS is one candidate, with no commitment to its architecture.
