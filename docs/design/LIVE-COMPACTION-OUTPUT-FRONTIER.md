# Live compaction output frontier

Source-only boundary at the live-capacity/adoption lane. Neither a larger
resident pool nor successful source-fit admission proves unlimited stored-data
progress. Live adoption remains inactive pending the actual query-parent joins.

`fn2-seal-build` / `fn2-seal-merge-next` feed the canonical served merge result to
`fn2-run-build-add`. On each needed page, `fn2-seal-take-page` reserves another
pool page and `fn2-seal-page` starts the run writer with a resident virtual unit.
`fn2-seal-cache` keeps every sealed page in `fn2-run-cache`. The new run becomes
LIVE only in `fn2-seal-install`; the existing bounded release then returns old
input pages, not the newly installed output. A merge over a large physical base
can therefore exhaust resident pages or direct-mapped cache rows before that
installation. The source-fit demand now requests real compaction after releasing
the cut, but does not remove this output dependency.

The actual checkpoint producer already supplies the required durable page
mechanism: `fn2-checkpoint-metadata-page` reserves one whole B extent before
`fn2-run-build-page-kind`; the existing page worker verifies/writes the actual
bytes; `fn2-checkpoint-metadata-promote` copies the verified commitment before
building a parent Ref. Its bounded working leases can then be reused. This is
the code to share, not a new merge or hash implementation.

The minimum connected producer interface must:

- Feed the existing sealer's actual per-schema merge/codec result into that B
  writer while retaining the exact HELD source cut and producer/grant owner.
- Bind each output page to its real allocator extent/epoch/allocation before
  header/Ref construction, and promote a child only after the real Write
  completion and retained verified hash.
- Return the original page lease through the canonical handback path, retaining
  only the typed Ref and commitment; never retain the full output in the resident
  cache merely to finish the tree.
- Handle the existing post-build Ribbon traversal without rereading evicted
  virtual cache pages: reuse the actual physical reader for owned completed
  construction Refs, or build the optional filter from the real merge stream.
- Publish the result through the actual checkpoint installation/Fence and C-base
  closure before exclusive source replacement; no ordinary allocator thaw or
  source-ready flag can substitute for it.

One useful integration is merging the actual held sources of a schema inside
root1 construction before its manifest emission. This can reuse the current
HELD construction ownership and physical writer. It also reduces catalog growth,
but must retain every original source identity for later retirement and use the
canonical merge policy (including folds/tombstones). The current one-root-per-
source capture cannot silently be reused as a many-input retirement ledger.

The N64/source36 control constructs actual metadata operations and registered
schemas with size-tier plans. It establishes the capacity/wake branch, not a
formatted-page, frontend-history or physical-compaction output witness.
