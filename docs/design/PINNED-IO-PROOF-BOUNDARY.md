# Pinned I/O proof boundary

Source review of retirement slice `c68d8b006` found a missing proof interface:
`fn2-block-read-children` now delegates to the disabled
`fn2-pinned-block-io-children`, but its existing queue/history/operation
semantic proofs could only open the outer function. This patch supplies the
owning helper's contracts, then composes read and write wrappers through them.
It changes no preexisting runtime DEFUN, guard, measure, or result ABI.

The new identity event producer derives slot/generation-on-success from the
existing `fn2-env-op-reserve-ok-facts`, first through the actual common issue
pipeline, then the read/write action wrappers. It uses actual admitted formals
and the existing ABI validator. This eliminates the pinned helper's impossible
successful-issue/mismatched-candidate branch without weakening its existing
queue equation. The helper's full eight-result ABI is asserted explicitly:
code/slot/generation, pool, ops, control, extents, edges. Ops remains result 4;
new mutable carriers are results 6 and 7.

Existing `fn2-issue-wrapper-effect-events` and `fn2-issued-wrapper-events`
emit the helper's queue/row/history contracts. Both outer read/write wrappers
consume that interface with the helper closed. Existing `fn2-oss-child`
emits the corresponding operation-semantic contract, then both outer faces'
contracts. Allocation and pin-drop internals stay opaque in local proof
contexts. No alternate runtime pipeline or hand-written effect formula is
introduced.

The source lifetime review found acquisition before descriptor publication,
generation-matched release on primary read/write completion after pool
settlement and before operation recycling, retention on stopped/partially
issued paths, and rollback only for ordinary prepublication refusal. A cancel
secondary cell alone cannot release the pin. The tuple changes in core faces
and operation-semantic consumers keep the actual ops output position. This
is source analysis, not certification or completed lifecycle evidence.

Validation so far: structural reader, diff check, secrets scan, and exact
byte comparison of all preexisting literal DEFUNs in the two changed books.
No ACL2 or certification ran. The next author probe must admit the identity
chain and helper contracts against the actual pinned implementation before
replaying outer wrappers; it must preserve refusal equations and never add a
shape/semantic premise to an existing public effect statement. Completion,
failure/cancel, stale generation, ordinary refusal, and retained stopped
issuance controls remain necessary for the integrated lifecycle claim.

## Actual helper author gate (2026-11-15 UTC)

The retained Forge author world used authentic composed source
`754758bec14be936e5fb32ffcf430a90480638a1`, with the literal actual pinned and
outer read/write functions. Its three-root prerequisite union was
arm-issue-effects/read-pins/commit-geometry: 28 qualified cached books and FASLs,
plus four explicitly source-admitted books (commit-alloc, read-pins, format-base,
commit-geometry). No assembled core or full machines-b book was loaded.
Cache artifact set was
`821ce008b4eb5f9c5cf081712c35b76950e956379e20ef8b34310e82370fc434`,
with record launcher fingerprint
`8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`.

The unchanged pinned guard first exhausted 2,000,000 steps in 31.65 seconds.
Keeping table predicates/readers opaque while opening the allocation handle
check proves exactly that guard in 0.16 seconds / 5,736 steps. A macro-level
carrier hint does not cover WFP facts because carrier specs have their own nil
hint field. The repair therefore scopes the opaque theory around the complete
carrier family and helper effect family. No guard or theorem premise changes.

Successful individual author stages:

| Actual subject | Seconds | Prover steps |
| --- | ---: | ---: |
| Four explicit source prerequisites | 3.95 | 471,439 |
| Generic/read/write issue reservation identity | 1.37 | 187,706 |
| Pinned function original guard, repaired hint | 0.16 | 5,736 |
| All ten pinned carrier laws, full ABI assertion | 3.72 | 211,530 |
| Pinned identity, queue, rows, issued history | 0.94 | 161,298 |
| Actual outer read/write guards and carriers | 0.07 | 1,650 |
| Six outer read/write queue/rows/history laws | 0.12 | 1,415 |

Each proof was capped at 2M steps / 60 seconds in a retained world under
MemoryMax 4 GiB / swap 0 and an outer 600-second deadline. The initial CLI setup
refusal (incompatible cached-only plus explicit source flags) happened before
ACL2 start. The second supervisor intentionally retained its first guard-refusal
return code 1; later named RPC receipts record the repaired successful stages.
All recorded handles (outer 667676, server 667707, ACL2 group 667711) were
confirmed absent after explicit stop returned 0. Compute was released.

Receipts: Forge `/tmp/finish-pin-author-second.log`,
`/tmp/finish-pin-guard-repair3.log`, `/tmp/finish-pin-carriers-parts.log`,
`/tmp/finish-pin-helper-effects.log`, `/tmp/finish-pin-outer-bodies.log`,
and `/tmp/finish-pin-outer-effects.log`. Frozen source fragments and hashes are
in `/tmp/finish-pin-author/receipt.json`. This is a successful partial-source
helper author gate, not record certification. Full machines-b/current-core,
ops-semantic-steps composition, and lifecycle controls remain pending.

## Canonical module frontier (2026-11-15 UTC)

The next retained world used exact `347058fb0fc0e03d73a3506541b5fd5d64fdb218`
modules: machines-b closure 76, comprising 38 qualified cached books and 37
explicit source dependencies plus the target. No core/index was materialized.
Cache artifact set was `f0bb81b49866412fe610b27b83b1f247305eab13676897a11a2b56e23cd1ad2e`.

The initial whole-book format-events wrapper exhausted its aggregate 2M-step
budget, leaving only 3,884 steps for its final attempted theorem. Replaying exact
top-level events preserved each DEFLAYOUT's inner local scope and passed all
66 forms in 34.53 seconds / 5,405,639 total steps; the largest event was 392,836
steps. Books with top-level LOCAL events retained their complete book scope.

Two actual retirement row-frame proofs needed the observer kept opaque so the
existing allocator-account/retire row interface could match: retire family
0.78 seconds / 160,786 steps; install family 0.53 seconds / 109,365 steps.
The actual packer guard then exposed a missing codec-size upper bound. A total
coarse varint-size bound proved in 0.16 seconds / 803 steps; the actual retirement
codec's size-fits-field theorem proved in 0.20 seconds / 3,126 steps. The
original packer guard passed with explicit size arithmetic in 0.27 seconds /
7,588 steps; its unchanged carrier family subsequently passed using the named
size bound in 0.08 seconds / 10,322 steps. The source repair keeps the coarse
arithmetic lemma local and supplies the named size bound before the unchanged
packer definition. That final compact ordering still needs a fresh source
admission; the exploratory guard used explicit hints rather than that ordering.

Twelve source dependencies were admitted through format-check, whose scoped
book took 34.02 seconds / 1,705,198 steps. The outer deadline then stopped the
world cleanly (outer 686554, server 686587, ACL2 group 686588 all absent; stop
returned 0). Supervisor code 75 records the first source-wrapper refusal;
individual later RPC receipts carry subsequent passes. The next commit-geometry
send encountered the stopped world: this is not a commit-geometry proof failure.
No certification occurred. Twenty-five dependencies, machines-b itself, and the
canonical dispatcher/publish controls remain unrun in this scope.

Forge receipts are `/tmp/finish-pin-modules.log`,
`/tmp/finish-pin-modules-format-events.log`,
`/tmp/finish-pin-modules-continue2.log`, and named book/event logs under
`/tmp/finish-pin-modules/` and `/tmp/finish-pin-*.log`.
