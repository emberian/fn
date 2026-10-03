# Contributors' guide

For commands and the short development loop, start with
[CONTRIBUTING](CONTRIBUTING.md). This page explains the system boundaries and
how to interpret its current claims.

## What fn is building

fn combines an executable ACL2 semantic core, a specialized persistent store,
NNTP service and BP transport for disconnected operation. The broader direction
is a resource-accounted persistence and communication substrate for humans,
agents and other applications. The [architecture](docs/architecture.md) names
that destination; the [decisions](planning/decisions.md) distinguish agreed
directions from proposals and unresolved choices.

ACL2 owns semantic decisions: identities, bounds, framing, groups, charges and
reply outcomes. Native Common Lisp performs I/O and supplies observations. Moving
coordination, lifecycle and resource custody into explicit ACL2 machines is
active implementation work, not a claim that the entire host is already proved.
The host's realization of a machine and its physical assumptions need their own
connected evidence.

The important distinctions are preserved at every boundary:

- Durable acceptance comes from persisted state, not a socket write or transport
  acknowledgement. Refusal, uncertainty and acceptance remain different outcomes.
- Source bytes, content identity, Message-ID and local article number are
  different types. Preserve conflicting evidence and provenance.
- Stored-data limits come from the operator's supported profile. Work and
  allocation are bounded per step; exhausting a quantum yields or resumes.
- A served path carries its invariant rather than revalidating the whole state.
  Individual legacy paths and unfinished carrier work still need repair.
- Logical octet models, concrete runtime representations and persistent formats
  have separate contracts. Named refinements must connect the actual host-called
  implementation to the logical subject, including effects.

## Where to read and where to change

The [engineering map](docs/engineering.md) gives the subsystem reading order.
`books/` contains executable definitions and proofs; `host/` contains host
integration and native primitives; `specs/` contains contracts. `tools/` and
`tests/` contain executable development utilities and scenarios.

| Question | Location |
| --- | --- |
| Current state and limitations | [Now](planning/now.md), [current view](planning/current.md) |
| Connected capability work | [NSLICESQUEUE](NSLICESQUEUE.md) |
| Individual defects and residual obligations | [Repair ledger](planning/repair/STATUS.md), its JSON items |
| Required behavior | [Requirements](planning/requirements.json), linked specifications |
| Proof targets and scenarios | [Proof registry](planning/proofs.json), [scenario catalog](tests/scenarios/catalog.json) |
| Physical and resource assumptions | [Failure model](specs/failures.md), [resource contract](docs/resource-contract.md) |
| Current development coordination | [Workstreams](planning/overnight-2026-10-03.md) |

Read the latest state before relying on an older handoff. Generated reports can
lag source, and dated records remain evidence of their own coordinate. The
repair ledger records individual obligations; the capability queue groups them
into useful implementation families rather than one project per finding.

## Working with other contributors

Work in an isolated worktree from current `origin/dev`. Agree on shared
producer/consumer interfaces and one assembler for overlapping changes; current
ownership is in the workstreams and queue, not a permanent model or lane quota.
The integrator writes public `dev` during coordinated development. Push coherent
source promptly through that path, with unresolved proof and runtime work named;
reviews and checks follow without becoming an image-production gate.

Exercise judgment on design choices and explain consequential tradeoffs.
Ordinary engineering work has no mandatory coordinator/reviewer round count.
Ask for missing product intent or authorization when genuinely needed. Prefer
fixing forward; a necessary revert is a reasoned engineering decision, not a
forbidden operation or a substitute for investigating the failure. Never reset
another contributor's tree or remove their files or caches to reclaim space.

New registry IDs are claimed before use with `tools/next_id.py`; its `--help`
describes the kinds and claim/check commands. Keep the registry, specification
and scenario consistent. Generated files are regenerated rather than
hand-resolved. This preserves identity and evidence without making every
finding a separate ceremony.

## What a result establishes

A claim names its coordinate: source revision, logical admission or archived
certification, executed source process or tested image, and deployment. None
implies the others. Exact unchanged evidence can be reused; changed bytes need
matching evidence for the property being claimed.

A theorem's subject must be the actual called function, or have a named bridge
to it. Keystones ship with reachable positive and hypothesis-removal witnesses;
corrupted-state and mutation tests are labelled separately. No `skip-proofs`,
`defaxiom` or trust tag establishes completion. Trusted facilities and physical
assumptions remain explicit. See [proof strategy](docs/proofs.md) and
[AGENTS.md](AGENTS.md) for the detailed claim rules.

Use warm scoped sessions and selected consumer tests to find the next failure.
Certification, normal source execution, image construction and full operational
qualification answer different questions. Report what passed, failed or was
not run; keep unfinished family work in the existing ledger and queue. Current
whole-system realization, resource accounting and cross-layer integration still
have open obligations, even where individual consumers work.
