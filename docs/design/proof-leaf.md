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
The canonical `acl2-projects` must already be staged. This tool never infers a
new resource grant or extends the caller's absolute deadline.

Each parent must have a compatible compiled cache entry with verified payloads.
Existing `warm_entry_books` determines the definition-free minimal ENTRY. The
command runs `start --cached-only`, whole-book `send-range --skip-includes
--ld-local` with original event limits, then stops and checks its recorded
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
and refusal boundaries with fake proof APIs; an actual capped pilot is still
required before replacing prepared live campaign scripts.
