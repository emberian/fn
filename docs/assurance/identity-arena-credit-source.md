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

Source checks: four arena program/arity/consumer controls; seven initializer
controls; three stream geometry and three original extraction controls; named
secrets scan0; parse/structural checks. The inherited machines-c-bind macro has
one unresolved MV splice in the shared structural checker, already present in
its baseline; this is not an expanded-output qualification. Closures: arena leaf
32, actual primitive unit121, init67, actual node initializer239.

Integration must preserve the newer sealer DRAINING/held-return protocol; the
older base's install-before-retire sequence alone does not safely resume a held
arena return. Only named provider/count/callsite changes should be composed onto
that protocol. Independent transient upload continuation credits, shared scratch
and sealer working/output admission remain required. Resident installed pages
cannot replenish credit at seal or checkpoint Fence; physical source adoption
and eventual exact cache eviction remain separate required consumers.
