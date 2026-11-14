# Successful fence return cuts

`tools/native_program_check.py --source-only --json` now carries a bounded
source witness for a fresh storage Fence with a captured snapshot, matching
slot/generation, no cancellation, a successful physical return and no lying
flush. It does not establish native/model refinement or execute a model proof.
The default gate still refuses incomplete cut mapping.

The actual worker calls `fn2-device-perform device job` between
`device-syscall` and `device-syscall-return`. The second cut precedes insertion
into the device completion queue. `fn2-n-storage-completions` checks the same
operation generation, then exposes `device-return` before decoding the raw
result and calling `fn2-n-complete`. Both return cuts therefore precede
normalization and terminal posting. They are not coordinates at
`fn2-sim-complete-result`, which immediately normalizes and posts.

`tools/served_storage_cut_check.py` checks complete worker/harvest blocks,
fixed enclosing AST positions, and argument/result flow. Its evidence records
actual function, AST path, contract and semantic role; it uses no line hashes.
The relation table must account for each callback and its derived physical
phase. Missing or terminal-post-attributed physical return cuts fail the source
audit. Disconnected or dead-branch copies cannot satisfy the checked positions.
This is a deliberately restrictive source slice; changing its control structure
requires reviewing the slice, not regenerating an acceptance hash.

The connected model slice is `fn2-sim-complete` → `fn2-sim-physical` →
`fn2-sim-physical-act` → `fn2-storage-fence-complete`, whose nonfailed/nonlying
branch commits the captured snapshot before returning storage and a raw code.
The corresponding unposted prefix ends before `fn2-sim-complete-result`.
Its source evidence includes that actual physical dispatcher, the snapshot
commit flag, durable-byte setter, raw result threading and the whole physical
to terminal suffix. Existing outer audit contracts retain the shared terminal
normalizer, posting ABI and crash-before-restart ordering.

That prefix is **unreachable-in-composition as an outer simulator scheduling
point**: successful `:ok` cannot take `:would-block`'s yielding branch, so
`fn2-sim-complete` continues directly to normalization and posting. Separately,
active=2/3 are Send release phases and are unreachable for the fresh Fence
incarnation under this domain. These facts do not make the host return cuts
unreachable. Calling internal simulator functions separately is not evidence
that the composed simulator can schedule a crash there.

Remaining work is explicit in the JSON: split physical return from posting in
the model schedule; establish initialization, operation incarnation, exact
effects and crash preservation; connect captured-snapshot coverage to the
native FIFO fence; qualify the FFI/OS contract; extend to reads, writes,
errors, cancellation and concurrent workers; and carry physical returns into
the trace/replay relation. Existing native SIGKILL controls do not discharge
those obligations or power-loss persistence assumptions.

Validation: `python3 -m unittest tests.test_served_native_program_check -q`
passes 23 focused controls, including omission, wrong phase, dead branch,
premature posting, disabled snapshot commit, Fence entering Send release and
model-yield mutations. The original source-only gate stays green; the default
completion gate stays red. No ACL2 certification or native campaign was run.
