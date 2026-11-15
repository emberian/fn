# Selected recovery RELEASE settlement

Owner: Codex, `sol_release_trace/release_chronological_settlement`, 2026-11-15.
Source packet: `lane/assurance-release-settlement`; no ACL2 execution authorized.

The selected prefix-inventory applier and the actual suffix RELEASE reader share
one indexed target mutation. They retain distinct source authority and cursor
contracts. This decision follows root's approved root4 pending inventory and
explicit `EMPTY/CLAIMED/PERSISTED/SETTLED` evidence lifecycle.

`fn2-release-target-settlement-progress` consumes the canonical allocation-release
control, evidence and candidate aggregate, construction, allocator, edges,
operations and checkpoint tables. It derives actor and source generation from
the retained control, requires exact `PERSISTED` evidence and all three physical
proof claims, then checks the current target's old handle, retirement and covering
cut and its ownership ledger. It performs one canonical identity-index preparation
or probe step per invocation. Only an exact ready receipt permits
`fn2-alloc-identity-commit-free`, followed without yielding by exact ownership
live-bit cleanup and evidence `SETTLED` stamping. It leaves the controller and
all three physical proof edges intact; source-specific callers finish their own
continuations. The common return cursor is always zero.

The ordinary suffix wrapper additionally requires the actual stage8 installation
read context, containing commit greater than the selected base, and the original
member's retained offset bounds. Only that wrapper returns `replay-next` and idles
its control after success. The prefix applier must instead derive its queue row
and generation from the authenticated root4 inventory and require batch at or
below the selected cut. It must never fabricate suffix offsets or replay stage8.

The LIVE identity index is authoritative. Raw `fn2-alloc-free` is not a consumer
seam: prepare/probe/ready/commit must use the captured common source generation,
not checkpoint number, cut, allocator epoch or transient selected tag. Index and
ownership-ledger cleanup are one mutation boundary before any later allocation
can reuse the slot. Every target protector still vetoes settlement.

Actual boot protects all four retained bank closures before invoking the prefix
applier, and transfers the identity index to the suffix recovery actor afterward.
A selected phase4 freeze has a positive retained token; blanket negation of
`fn2-alloc-snapshot-activep` would make its settlement antecedent impossible. Live
checkpoint capture and selected cold recovery therefore have separate exact
source gates. Ordinary public frozen guards are unchanged.

The private primitives have no cost face. Actual selected-source/inventory joins
must dominate their callers before runtime stage8 can advance. Source controls
and synthetic local primitive witnesses do not establish that authority, native
crash correspondence, physical epoch reopening or checkpoint/FREE activation.
