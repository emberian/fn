# s-xc2 round 7: atomic swap draft and missing exports

Not READY. The merge of origin/lane/p-xc-span@abb716d8f into
f60487b09 is conflict-free and remains uncommitted. Job A's requested removal
of the entire native backing array cannot be completed with the supplied
kind-2 export. No P-owned book has been edited locally.

## Supplied API and the uncovered callers

The draft raw path calls `fn-xc-init-windows`, creates `fn-xcw`, installs via
`fn-xc-install-window-bytes`, and calls `fn-xc-span-at` once per stretch with
FROM=0. There is no native raw candidate lookup or candidate loop. The three
requested span keystones and both initialization/installation keystones are
declared. `:duplicate` releases the uncached row without faulting.

`*fnn-extent-slots*` also holds kind-1 complete entry vectors and kind-3
decoded windows. `fn-xc-span-at` searches kind 2 only
(`books/extent-cache-span.lisp`, function `fn-xc-span-at`). The existing
decoded cache supplies PLAN=NIL. `fn-xcw-plan-octets` returns zero for that
plan, so routing its install to `fn-xc-install-window-bytes` would silently
copy no decoded bytes. `fn-xcw-store` excludes entry slots (SLOT < NE).
Thus this stobj is not a replacement for either remaining backing class.

The draft explicitly separates decoded installation into
`fnn-extent-decoded-window-cache-insert` and retains the old interface and
backing for it. This is a pending scope exception, not satisfaction of the
array-deletion requirement. S was asked whether to accept that temporary
separation or obtain the missing exports from P first. Until answered, the
atomic merge/host commit is withheld.

Memory note for N: raw windows move to eight eagerly allocated 256 KiB
`fn-xcw` rows (2 MiB), replacing lazy native raw-window backing. Decoded
backing remains in this draft; this is not yet the final memory inventory.

## Job B trace and statements before any new keystone

The current whole-entry hit already uses `fn-xc-lookup` in
`fnn-extent-entry`; there is no `find-if` over `*fnn-extent-cache*` in
`fnn-extent-entry-direct`. The latter is the miss/admission/retry path.

The supplied W2P `sprof.000.txt` is a flat profile: it reports
FNN-COLD-CALL at 31.1% total, NTH at 3.8% self, and %LOOKUP-SYMBOL at 1.3%
self. It does not establish that those samples were warm hits or give their
parent stacks. Current warm raw reads run `fn-xc-span-at` -> `fn-pwc-span-at`:
ledger/token/publication checks and copying, with no BLAKE3 invocation.
Hashing runs after a miss in `fnn-extent-window-run` -> `fn-ews-read` ->
`fn-b3x-words`. Whole-entry misses hash in `fnn-extent-read-verified`.
The earlier first-candidate false miss is removed by P's complete walk;
cache-capacity misses must still authenticate the newly read bytes.
No measured W2P reduction is claimed.

Concrete positional sites are `fnn-entry-guard`'s `(nth position args)` and
the plan fields in `fn-ews-capture-matches` / `fn-ews-boundp` on each digest
quantum. The symbol lookup site is `fnn-counterpart`'s
`(find-symbol (symbol-name name) "ACL2_*1*_ACL2")`, reached by the dispatcher
for counterpart entries. These are identified, not fixed by this draft.

Proposed missing core contracts, for S/P review before new proofs:

* A decoded cached-span export must walk all matching kind-3 candidates,
  derive bounds from the decoded window contract, return exactly the
  existing decoded span-at bytes, and touch only a successful slot.
  Installation must preserve that slot's actual decoded bytes; NIL raw
  plan must never authorize a zero-byte copy followed by a decoded hit.
* Entry backing needs an ACL2 representation/export that preserves the
  complete entry without introducing a fixed entry-size ceiling. Existing
  lookup identity, LRU, eviction and ledger-charge decisions stay ACL2's.
* Batch cache retirement must equal the existing ordered sequence of
  next-live/free operations for the supplied files, returning exactly their
  charged tokens; batch release must equal their ordered ledger evictions,
  retaining an explicit refusal instead of losing an unretired charge.

No new keystone or proof for these contracts has been introduced.

## Loop inventory before and after this draft

Unchanged: 129 sites against baseline 123. No ratchet was changed and no
loop was hidden in a helper to reduce the count.

| File | Functions / counted sites |
| --- | --- |
| extent.lisp | cache-take (2), window-run, executor-loop, executor-start, executor-stop, cache-release, entry-direct, lz-buffer-span, close (10 total) |
| extent-decoded.lisp | decoded-window-cache-run, decoded-window-run (2 total) |

The whole-entry retry is admission/eviction, not host descriptor selection.
Executor loops perform worker lifecycle and I/O; their removal requires
preserving actual completion and cancellation receipts. The decoded warm
loop requires the missing kind-3 export above. Full loop output is
`/tmp/s-xc2-r7-loops.log` on the laptop.

## Gates

`python3 tools/extract/world.py` ran; world rows were already current via
host/page-read-host.lisp's extent-cache-span include. The interface manifest
was regenerated with `FN_LAPTOP_OK=1 python3 tools/interface_emit.py --write`.

* host_check --load: exit 0, 58/58 raw files loaded, 0 findings. Bare ACL2
  fallback: 78 undefined world names, 28 world load-time calls, 46 other
  compiler warnings; certified umbrella equations were not evaluated.
* interface_emit --check: exit 0, 1845 declared / 1795 dispatched, 0 findings.
  One existing unresolved output-tariff keystone is reported, not a failure.
* keystone_emit --check: exit 0, 14 defkeystone forms in 4 books, 0 findings.
* Deleted-name rg: no matches (exit 1).
* Filtered extent pytest: 1 failed, 200 passed, 10 skipped, 38 subtests
  passed in 130.97s; `test_the_tree_is_at_its_baseline` fails at 129/123.
  The discovery's `check_control_unwind_effects.py` is a command-line script,
  not a pytest module: importing it consumes pytest's arguments. It was
  excluded after that collection error, and no unfiltered suite was run.
* Warm native tests: NOT PASSING. Source-event admission in the available
  older developer world timed out at 180s per test (2 errors / 360.240s).
  Installing the current 43-book certificate set on persvati succeeded
  (37 installed, 6 kept, 0 missing), but including it in that image conflicts
  with existing definitions (`*fn-cbor-max-uint64*`, ADT-INSTANCE-UNFOLD).
  Both certified-inclusion tests failed (2 failures / 2.173s). Fixing the
  fixture's initially unset connected book directory exposed that conflict.
  A subsequent source-admission attempt stalls proving fn-xc-span-at's
  guard in this older world; the diagnostic has its Subgoal 2 in
  `/tmp/s-xc2-r7-admit-debug.log` on persvati. Stopped only our own job,
  recorded PID 2001584. A compatible warm developer image is needed;
  no native evidence or W2L performance win is claimed.
* Current harness closure check: 1 passed, 2 skipped (the two native modules
  skip locally without FN_XC2_NATIVE_CORE), 1.04s.
* secrets_check: 15 named files, 0 secret-shaped values; diff --check clean.

Warm-read IDs: `tests.test_native_extent_cache_span.NativeExtentCacheSpanTests.test_warm_raw_extent_is_one_span_export_and_preserves_cold_miss`
and `tests.test_native_extent_decoded_span.NativeExtentDecodedSpanTests.test_actual_compressed_extent_span_matches_scalar_across_window`.

Exact native command (persvati, cwd `/home/ember/fn-gates/s-xc2-repl`):

```
FN_XC2_NATIVE_CORE=/home/ember/fn-gates/sxc-c3/native-sxc-9b6958f93/tree/build/fn-host-developer.core FN_XC2_SBCL=/tank/fn/sbcl/bin/sbcl timeout 400 python3 -m unittest tests.test_native_extent_cache_span tests.test_native_extent_decoded_span -v
```

The merge is deliberately pending: committing the retained decoded array
and old install interface as a completed Job A would violate the requested
atomic deletion. HEAD remains f60487b09; no round-7 commit and no push.

Verbatim final gate tails:

```
host_check --load: 58 of 58 raw files loaded in one bare acl2 in 3.9 s; 0 finding(s); 78 undefined names and 28 load-time calls belong to the certified world (not loaded here); 46 other compiler warnings
interface_emit: 1845 declared; 1795 of the raw host's 1795 dispatched entries; 24 extraction roots, 6 EXTRA; 0 finding(s)
keystone_emit: 14 defkeystone form(s) in 4 book(s), 0 finding(s)
loop_call_check: 129 host loops that call ACL2 or take a lock per iteration in 30 files (baseline 123)
1 failed, 200 passed, 10 skipped, 38 subtests passed in 130.97s (0:02:10)
Ran 2 tests in 2.173s
FAILED (failures=2)
1 passed, 2 skipped in 1.04s
```
