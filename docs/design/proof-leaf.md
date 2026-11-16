# Qualifying one ready leaf

`proof_repl qualify-leaf` replaces the repeated preflight/ENTRY/author/record
portion of the native leaf and groups/sealer scripts. It does not allocate a
host, start an external resource scope, schedule other roots, or retry failures.
The columns production script's deliberately multi-source stages remain explicit;
this command refuses an unqualified parent rather than silently replaying it.

Inside an already granted, externally timed Linux cgroup, with the pinned
`FN_ACL2` and `FN_CERT_CACHE` selected:

```sh
python3 tools/proof_repl.py qualify-leaf books/fnct-pool \
  --plan /tmp/current-source-plan.json \
  --output build/leaf-fnct-pool-attempt1 \
  --deadline "$EXISTING_CAMPAIGN_DEADLINE_EPOCH" \
  --memory-bytes 2147483648 --event-steps 2000000 --event-seconds 20
```

The plan has `source` (source revision label), `toolchain` (qualified fingerprint),
and `books`, mapping each closure book to its exact raw `sha256` and closure `key`.
`toolchain_identity` is also accepted for existing group/sealer plans. Exact
book bytes/keys, rather than a Git HEAD claim, bind an archived build tree.
The event limits are explicit per-run CLI inputs; 2M steps/20 seconds are defaults,
not a new project-wide policy. The canonical `acl2-projects` must already be staged. This tool never infers a
new resource grant or extends the caller's absolute deadline.

Each parent must have a compatible compiled cache entry with verified payloads
and matching book, closure-key, and exact raw source metadata. A comment-only
source mismatch is refused by this explicit raw-byte plan rather than silently
claimed as an exact match.
Existing `warm_entry_books` determines the definition-free minimal ENTRY from
only the target's **global direct imports**. LOCAL ancestors are required in
the cache but never forced into global scope. Strict `certs install-set
--dependencies-only` installs all parent artifacts without importing them.
The command runs `start --cached-only`, whole-book `send-range --ld-local`
(preserving direct LOCAL include events) with the caller's event limits,
then stops and checks its recorded
session handles before certification. `certify_books --incremental
--cached-parents` refuses any non-root miss after installation, before starting
ACL2; no parent source replay is allowed. Images are disabled. Actual record
manifest source/runner/toolchain checks and current cache payload checks finish
the operation.

The new output directory contains logs, exact child commands/PIDs, session
handles, ENTRY imports/exports, fixed deadline, and the actual manifest path.
First failure stops the sequence. Cleanup is restricted to the command's unique
session and child process groups; the caller still owns the outer cgroup and
must verify it is gone before releasing its resource ledger slot. A failed
cleanup is reported, never called a resource release. A later leaf invocation
uses a new output directory and the **same** campaign deadline.

Source controls: `python3 tests/test_proof_leaf.py`. These exercise orchestration
and refusal boundaries with fake proof APIs and real bounded Python children.
The actual cost20 pilot completed authoring and a new record publication under
a 2 GiB/swap0 scope; see [its receipt](receipts/native-leaf-cost20-pilot.json).
This validates the single-leaf lifecycle, not application or native runtime
behavior. Existing live campaigns are not changed by installing this command.
