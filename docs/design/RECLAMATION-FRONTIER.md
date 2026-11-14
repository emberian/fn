# Persistent reclamation frontier

The current fn2 served machine does not implement persistent extent recycling.
`FN2-PERSISTENT-RECLAMATION-LIFETIME` in `books/owed-reclamation.lisp` records
that missing guarantee in the existing square registry. It deliberately has
no statement, proof or checker result. The product completion scope must
require this row with served subject `FN2-TURN`; an allocator-local theorem
does not establish that subject's lifetime guarantee.

## Existing mechanisms and their limits

`books/alloc.lisp` provides reserve, edge add/drop, retire, checkpoint advance,
release and relocate. Its release predicate checks retirement, checkpoint cut
and protection. `tests/alloc-unit.lisp` manually drives those operations and
feeds `sim/check-reclaim.lisp`, an independent event interpreter. Those are
useful allocator tests, not a served reclamation trace. The generic
`sim/check.lisp` dispatcher still answers `:not-yet` for reclamation.

The current non-proof books do not call `fn2-alloc-retire`,
`fn2-alloc-release`, `fn2-alloc-checkpoint-advance` or `fn2-alloc-relocate`
outside their definitions. `books/commit.lisp` does reserve extents and
maintain installed-root, prepared-successor and outstanding-I/O edges.
Cancelling an uncommitted reservation is distinct from retiring live data.
`fn2-rd-release` in `books/machines-c-read.lisp` releases query/range/read
rows; it does not release persistent allocations. Scheduler machine reclaim
and pool release likewise do not establish persistent extent recycling.

`docs/b-durability.md` identifies B6 checkpoint/cleaner machines as owed;
`books/checkpoint.lisp` and `books/cleaner.lisp` are absent. The legacy native
expiry/reclaim tests name absent `books/store-reclaim-pack.lisp`,
`books/owner-reclaim.lisp` and `host/native/checkpoint.lisp`. Their existence
is not evidence about the current fn2 served path.

This absence is not a demonstrated premature-reuse bug. Never reclaiming
committed extents can avoid reuse while still failing the product's capacity
and progress requirements.

## Integration contract

The next implementation must connect a bounded, resumable coordinator to the
served machine, rather than enabling release calls in isolation:

1. A read/borrow transition acquires its concrete extent and generation's
   protection before exposing bytes. Protection lasts through the promised
   read and every outstanding operation; completion and cancellation release
   precisely the holder's edge. Query-row release alone is insufficient.
2. Installed roots, every selectable checkpoint, recovery bases and candidates,
   prepared successors and custody obligations preserve their own protection
   through root replacement and recovery. These are distinct from read pins.
3. Retirement and checkpoint selection make release eligible, but eligibility
   does not make an extent reusable. The composed machine persists the release
   before FREE, models each death cut, and excludes stale-generation references
   after restart and reuse. Ambiguous persistence results require recovery.
4. Once the last actual protector disappears and the installed cut permits
   release, bounded steps eventually reclaim under stated scheduling and I/O
   assumptions. This progress obligation is separate from lifetime safety;
   no whole-store validation or arbitrary stored-data ceiling substitutes for it.

The first connected witness should hold a served read across retirement,
checkpoint installation and attempted release, assert the entire antecedent,
then finish the read and observe persisted release and generation-safe reuse.
Its removal control omits that live read's protection and reaches a stale read
or premature reuse in the same composed trace. Crash controls straddle release
persistence and reuse; a separate progress control detects permanent retention.

`tests/owed-reclamation-unit.lisp` exercises only the registry boundary: the
unbound requirement is valid, while fabricated proof and allocator-only check
attachments are refused. It is not a storage safety witness. The completion
gate owns the product scope and served-subject check; this lane adds no rival
completion inventory. Until the coordinator and witnesses exist, this row
must remain unbound and product completion must fail closed.
