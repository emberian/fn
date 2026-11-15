# Ordinary retirement dependency cut

The single generator in `books/retirement-coordinator.lisp` emits the actual
ordinary admit, submit, poll and persisted lifecycle operations. Its default
adapter releases the ordinary reserved workspace and refuses allocation and
checkpoint-installation records. It does not emit checkpoint producer helpers.

`books/checkpoint-lifecycle-coordinator.lisp` supplies an explicit source-time
adapter containing the original maintenance staging prelude, exact future
workspace return, staging identity check, and both persisted checkpoint installer
helpers. `machines-b` includes this extension; `commit` instantiates its wrappers
once. The common operation bodies remain in one generator. Token, owner,
containing batch/event, intent, persisted fence, completion and ambiguous failure
checks remain in that common body or the unchanged checkpoint helper expressions.
There is no runtime adapter switch or caller-supplied acceptance flag.

`tools/test_retirement_adapter.py` compares the checkpoint expansion against the
canonical event-tree digest of the actual pre-factor source at d2a1b7c0f
(the own-lane merge of admitted allocator source and integration 568724889). Nested event
`progn` is flattened; every operation expression and theorem statement must
otherwise match exactly. A second control checks that ordinary expansion emits
all four real operations, rejects both checkpoint record branches, uses ordinary
release, and contains no checkpoint helper calls. These are source controls, not
ACL2 admission or execution of submit/poll. Existing allocator, leaf and composed
retirement fixture assertions are unchanged.

Official `certify_books.local_closure` reports 19 local source books for
`books/retirement-coordinator` (system books excluded): alloc, blake3,
blake3-pool-spec, blake3-spec, columns, commit-alloc, declare, digests, format-base,
format-events, layout, operations, owed, owed-discharge, pool, profile, retirement,
retirement-coordinator, tuple. `tests/retirement-intent-leaf-unit` also has 19
local books, including its test root instead of the coordinator. The allocator
intent fixture retains its 7-book local closure. The checkpoint coordinator
extension has 48 local books.

This is a dependency-complete ordinary generator/codec slice. It is not yet a
checkpoint-free assembled machine: current `commit.lisp` directly includes
checkpoint-commit-leases, and current `machines-b` directly owns checkpoint
construction/tickets and other checkpoint-related children. Those independent
extension seams must be separated before claiming a small whole-core ordinary
closure. Existing full assembly continues to instantiate the checkpoint adapter.
No ACL2, native, remote, service or runtime qualification was run for this split.

## Stobj translation repair

The followup binds `fn2-core-stop` results before returning the core through
`mv`, including the cancellation branch whose final argument was an `if`.
The original pre-factor fingerprint remains recorded as
`PRE_FACTOR_EVENT_SHA256`; the additional normal-form fingerprint is derived
from that original tree at d2a1b7c0f. The source control permits only the explicit
core LET/return rewrite with no core reference in the scalar result expressions.
It does not replace the historical receipt with the repaired tree's digest.
