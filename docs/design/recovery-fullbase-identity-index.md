# Full-base live identity index consumer

The actual full-base `fn2-recovery-install-adopt` derives its candidate position
from the recovery row. `fn2-recovery-adopt(id, generation, position, core)` binds
the existing index to that actual recovery kind/id/spawn generation; its source
generation is the same spawn generation. The actual FREE-only prepare path is
unchanged. Recovery cannot restart from DONE through prepare, so a continuation
cannot acquire authority for another spawn by supplying a source token.

The first position starts and clears the index one bucket per invocation. The
empty full-base terminal uses the same initializer. Every adoption then calls
`fn2-alloc-identity-adopt-progress` with the real tuple and the ordinary free-head
predecessor NONE. This reuses the shared prepare/probe/commit protocol. `:more`
retains the actual machine position; it does not enter replay. Chained extents
become ALLOCATED with their installed-root edge; payload extents become ALLOCATED
to the recorded owner; other positions remain quarantined with a recovery edge.
Their tuples stay indexed through those original private state/edge transitions.

The full-base terminal publishes the directory before replay while ACTIVE stays
one and epoch-begun stays zero. The old generic finish refuses ACTIVE before any
directory mutation. The added `fn2-boot-finalize-fullbase-index` helper is a
source seam for the owner's actual phase-zero boot finalizer: it rechecks the
completed boot Fence actor, terminal recovery row, processed highwater, full-base
source, exact index owner, idle/no-op continuation, and a strictly newer epoch.
It ends the index and calls the original begin-epoch in one nonyielding call.
Its ACTIVE-zero branch preserves fresh boot behavior. The outer phase-zero
branch hookup is owned by the boot integrator and is not included in this lane.

Two integration boundaries remain explicit:

- Unknown quarantined bytes retain the existing synthetic tuple `(0, position)`.
  Normal fresh allocation cannot produce epoch zero: initialization leaves
  epoch-begun zero, begin-epoch requires an increase over current zero, and
  reserve requires epoch-begun one. However, the actual persisted candidate
  decoder accepts any unsigned 60-bit epoch, including zero. No current source
  contract establishes disjoint namespaces for every accepted history. A known
  `(0, position)` elsewhere therefore conflicts with unknown quarantine and
  refuses recovery. The actual entry fixture retains this refusal. Supporting
  that history requires an explicit typed unknown-ownership design; uniqueness
  must not be relaxed or unknown rows omitted.
- The post-Fence helper requires the chosen epoch to exceed both the observed
  recovery maximum and allocator maximum. Boot epoch selection/hookup belongs
  to the boot owner. A selection that does not incorporate the observed maximum
  remains a refusal; this consumer does not silently end the index first.

`recovery-fullbase-index-unit` has six prepared actual-entry controls, including
real recovery preparation and shared adoption, exact duplicate and zero-epoch
collision refusals, stale generation, a real occupied protector edge, and the
empty terminal. Candidate/classification facts are explicit logical premises;
there is no persisted bytes, authenticated history, or completed boot claim.
Its local source closure is 360 books. Python source controls pass; ACL2
assertions, guards and composed post-Fence execution remain unrun.
