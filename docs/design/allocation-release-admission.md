# Authenticated outgoing RELEASE admission

`fn2-allocation-release-submit(kind, owner, generation, core)` consumes the
actual STAGED publication/retired-head capture. It selects a FREE ordinary B
row, reserves the dedicated initialized release credit group, and packs the
member itself through `fn2-allocation-release-pack-staged`. It accepts no
caller-provided lifecycle bytes or readiness flag. The group index is one
past the actual ordinary B drain groups; its single class demand comes from
the same member-capacity function used by the packer. Static profile P now
includes this workspace; F remains a separate service-fit calculation.

The producer invokes actual B START, derives the reserved journal tuple from
that row, and claims the descriptor, installation-journal and outgoing-journal
obligations before exposing the sole transaction member. It then closes the
workspace credit redemption and binds exact batch/event/workspace and writer
identity in WAITING. The batch stays closed to JOIN. Known unsubmitted START
refusal returns only the workspace and aborts its empty credit group, retaining
the staged source for exact same-batch retry. Unexpected START, evidence,
END or member failures retain ownership and stop uncertain. The selected writer
and workspace identities survive even a failure before START assigns its row.

The existing lifecycle dispatcher has a source-specific RELEASE adapter.
Its ordinary adapter refuses RELEASE. The actual adapter requires persisted
B flags and installed-root dispatch, the exact WAITING member/owner/writer,
all three owned evidence edges, canonical decoding and equality to the retained
source fields and descriptor hash. It marks PERSISTED; it performs no FREE,
release-pending transition or evidence discharge. Generic transaction admission
continues to reject RELEASE.

`fn2-allocation-release-poll` returns `:waiting` until exact accepted settlement
and PERSISTED are both established. The dedicated writer must also be past its
last member-byte consumer: completed notification with no pending operation or
fence, draining/free, or a strictly newer nonwrapping writer generation. Only
then does actual credited release free the workspace. Its historical slot and
generation remain recorded with `workspace-released = 1`; all evidence stays
owned. Refused, ambiguous, stale or failed-return paths retain ownership and
report uncertainty rather than rearming a nonce. Successful poll returns
`:persisted`, never physical reclamation permission.

These are connected source interfaces, not an executed durability witness.
The codec owner's whole-history fixture calls stage, submit, actual B drive,
poll, crash and cold verification. ACL2 admission, guard/cost composition and
that fixture's executable result remain pending. Runtime FREE stays disabled.
