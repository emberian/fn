# Current work: native service composition and consolidation

Updated 2026-09-21. The goal remains the full selected two-peer v0 and v1/M6
scope in [milestones](milestones.md#release-shape-v0-and-v1). Component tests
and certificates do not establish that release. D07 requires a Python-free
node, operator CLI and runtime helpers; Python remains development tooling.

## Integrated and under validation

Main contains native owner/operator help/status/recover/run, feed intent and
resolution persistence, safe FNFD names and a total observation budget,
cross-session BP receive evidence, application journals, checkpoint/anchor
persistence, and selected initializer retry paths. The standalone store wrapper
calls a proved prepare refinement that omits per-prepare history replay;
shared-owner adoption is still being implemented. BP lifecycle append uses an
ACL2-owned namespace and carried frontier instead of rescanning retained files.
The listener's admitted loopback addresses now come from an ACL2 projection.

The frozen combined source is `03eb3ba3`, with retained persvati job
`run-20260921T095031Z-5cf4`. Certification, both same-origin image builds, scoped runtime suites and the
public operator loopback witness passed; see the [frozen evidence](evidence/native-owner-integrated-2026-09-21.md). Later main changes
are not part of that frozen source and must receive their own integration gate.
The earlier `76901c1` closure/build passed; its live listener wakeup defect was
repaired in the current frozen batch. Historical Python matrix disagreements
remain recorded and are not reclassified by component certificates.

## Parallel paths to the next service batch

[Active lane assignments](swarm-cycles.md#current-staffing-and-integration-checkpoint)
own these complete paths and their source-pinned evidence:

- Native local control/posting, authentication, outbound NNTP feed I/O and
  group/capacity administration, through the existing ACL2 policy and shared
  serialized owner. Control and BP submission share completion machinery;
  lifecycle hooks and orderly SIGTERM must compose without deadlocks.
- Native BP request intent through article acceptance, durable receipt decision
  and restart/lost-reply idempotence; carrier ACKs are not application acceptance.
- Actual BP lifecycle invariant/effects, shared immutable publication, checkpoint
  namespace/mismatch/fencing and initializer syscall/model correspondence.
- Shared-owner adoption of the prepare correspondence, followed by measured
  native service cost. Standalone measurements do not qualify concurrent service.

Root integrates coherent packets and uses both hbox and persvati with owned
closures and a frozen combined batch. Terra handles bounded implementation,
Sol substantial implementation/proof debugging, and Astra cross-project
convergence and difficult residual questions. Cross-model review runs in the
existing Claude tmux session on bounded source-pinned subjects; it is not a
serial approval gate.

## Assurance and consolidation

The [consolidation audit](duplication-audit-2026-09-21.md) records demonstrated
competing decisions, repeated scans and misleading contracts. Active repairs
include transaction/configuration namespace parsers and pre-allocation bounds,
native lifecycle shutdown and connection-local fault isolation. Initializer
expected-link classification and post-link uncertainty repairs are integrated.
Moving a semantic twin from Python to raw Lisp does not close it. A separate
logical specification and a proved efficient representation remain intentional.

Every new reachable behavior carries its caller, invariant, byte, crash and
resource obligations in the [registries](requirements.json), [proof targets](proofs.json)
and scenarios. Physical adapter correspondence, protected native transport,
complete operator/identity workflows, long-lived retention/release/restore,
full two-peer feature coverage and broader v1 work remain open. Preserve native
author signatures, exact source bytes with separate projections, indefinite
retention until authorized release, NNTP/CLI before web, and deferred private
group cryptography. D09/D11 proposals are not silently selected requirements.

Historical progress is retained in source-pinned evidence and
[milestone landing notes](milestones.md#earlier-landing-notes), not repeated here
as competing statements of current status. A scaffold pass is structural
validation; no component result is a mission-readiness claim.
