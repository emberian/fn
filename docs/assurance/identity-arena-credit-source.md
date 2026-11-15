Overlay-owned arena credits: source-prepared

The first arena reserve belongs to its actual C overlay slot. Configuration
uses actual B row and overlay row counts: working1 + B drain groups + RELEASE1
+ O arena groups. The same layout functions supply initialization and consumer
checks. Configured old/partial layouts refuse; only genuinely unconfigured mode
uses ordinary pool reserve/release. No pool or overlay schema changes are made.

Actual idc-add-spare calls identity-arena-credit's reserve/start primitive. It
binds the slot's monotone pool credit nonce, redeems one arena, runs the real
ov-start/advance, and ends the reservation. An ov-start index refusal returns
the fresh unsubmitted lease and aborts empty before retry. Unexpected ownership
that cannot be returned is retained in a non-free C row and refused.

Cdrop and sealer-retire call the same return provider, validating actual row,
class, owner, group and nonce against immutable pool provenance. HELD does not
rearm quota or free the row. RETIRED ends ownership but depletes the group;
it is accepted cleanup, never replenishment. The actual scalar B-row count is
read from the initialized B child in C core wrappers, not supplied by actors.
Nine consumer functions/call classes are threaded by identity_arena_thread.py;
its original-source receipts and actual arity controls preserve literal frame
and function-name data. Existing public core function signatures stay unchanged.

P now protects O arena quotas, and F excludes those same arenas to avoid double
counting. The overlay-row admission floor comes from the declared POST schema
footprint plus actual nonempty NAME families. Actual node initialization controls
remain in the packet. The primitive unit uses an explicit small synthetic prefix
quota premise and synthetic sealer-eligible FROZEN phase; it proves no durable
publication or whole-profile capacity. It drives real spare/start/sealer cleanup,
real generic exhaustion, real query hold/release, actual generation retirement,
and exact stale/wrong-slot/old-layout/nonce-limit refusal controls. Assertions
are UNRUN. No compute was performed.

The current packet composes these named changes onto the actual DRAINING
sealer. Full source replay rejects changes to its visibility and held-return
ordering. NAME genesis and replay reserve through the same provider; constructor
controls check actual immutable arena provenance. Depleted or nonce-exhausted
FREE slots are skipped so another eligible slot can serve the actual stage call.

Source checks: five arena controls, four DRAINING projection controls, seven
cleanup projection controls and six DRAINING lifecycle controls pass. ACL2
assertions remain UNRUN. The inherited machines-c-bind macro has one unresolved
MV splice in the structural checker, present in its baseline.

Actual txn and authority callers retry :full as charged runnable work; they do
not park on generic pool availability. This packet does not prove that such a
retry eventually finds a slot. Independent transient upload admission and sealer
working/output admission remain open. Resident installed pages cannot replenish
credit at seal or checkpoint Fence; physical source adoption and exact cache
eviction remain separate consumers. Eager shared scratch initialization is a
separate, already integrated rolling packet and must be preserved on composition.
