# fn: recommended calls and next convergence — 2026-09-28

For ember and the coordinator. These are recommendations, not a record of decisions ember has already adopted.

## Review coordinate and scope

Source inspected: `2c46ce1c5b9cf21b02573b7f35c8a25a4559a54c` on `emberian/fn/dev`.
Final branch check: `ad8d3d34641440e1b56ee2b79854a8c5198d9303`; that subsequent commit changes only `planning/review-packet-2026-09-28.md`, adding the F8 breakdown and uncharged-connection term.

This review read selected source and evidence, not the whole repository. It did not run ACL2, rebuild images, or reproduce native performance and crash campaigns. It did execute the isolated extraction-gate witness supplied alongside this brief. Reported performance remains the repository's evidence, with its stated image and workload scope.

## Overall decision

Proceed with the page-backed owner and a maintained extracted-build target. Do not make the first production qualification simultaneously change the persistent-state authority boundary and the compiler/runtime boundary. This is a qualification order, not a request for another integration branch. Keep dev as the integration branch.

The next success is a page-backed owner whose accepted history, materialized image, log suffix, pinned views, and memory accounting compose. A fast prototype open and individually certified readers do not yet establish this.

## Immediate corrections

### 1. Make extraction qualification fail closed

At the inspected revision, `tools/extract/check.sh` runs the function-test binary without testing its exit status. Its final acceptance check only searches for `DIFFER|RAISE|HANG` output. `tools/extract/fcheck.py::cmd_report` accepts an empty log, reporting zero executed vectors. The supplied isolated witness runs the unchanged final shell gate and extracted report functions with a stand-in binary that exits 73 before producing results; the gate prints PASS and exits zero.

Check every child status explicitly; compare produced cases against an expected manifest; require complete, nonzero case execution; reject truncated or duplicate case IDs and missing completion markers. Make machine-readable reports carry explicit failure status. Test the gate by killing each stage, emptying/truncating its output, removing a vector file, corrupting an expected result, and inducing a mismatch. Do not rely on shell `set -e` alone, especially across pipelines. This finding does not establish that any previously recorded successful run failed; it establishes that the gate cannot reject an important failure class.

### 2. Correct the format-9 import claim

`books/store-format-9-records.lisp::fn-f9r-step` explicitly refuses signed topic anchor/admission records as `:signed-format-9-identity`. The packet's “every format-9 kind” claim is too broad. State the supported migration domain and preflight an archive before touching live state.

## Memory and zero-copy calls

Use reservation credits acquired before allocation, not maximum-article-size reservation for every idle connection, and not RSS sampling as admission authority. Measurements tune estimates and safety margins; they do not retroactively authorize allocations.

Use pooled bounded chunks with per-request logical ownership. Transfer the same credit with the buffer from ingress to prepared submission to outstanding durable I/O and finally retained/cache ownership. Do not free the credit just because a client timed out: a worker or submitted syscall may still own the memory.

Budget fixed runtime use, resident/pinned pages, dirty pages, active input, output, parser/decompressor and crypto scratch, foreign-library allocations, stacks, GC headroom, and completion/recovery reserves. An overdraft is acceptable only as a separately funded bounded reserve, not a claim that observed spare memory will remain available. Cache credit is reclaimable only after actual eviction/unpinning.

For unknown-length NNTP input, combine bounded growth with a safe completion path: enough reserved capacity to finish at least the admitted work, or a reserved staging path. Do not admit many partial uploads that collectively hold all buffers while each needs more to finish.

Keep F8's old reserved-memory verdict visible. Define separate virtual-address-space and accountable physical-memory measures. Recommended small-node successor target: a 256 MiB accountable service envelope and <=128 MiB working-set target under an explicitly named small profile and active-request mix. This is a target, not evidence that the current runtime meets it. Larger stores/profiles get explicit cache and concurrency budgets rather than full-history heap reservations.

## Representation and page-store calls

Continue the abstract stobj with a ghost history and concrete image-plus-suffix. Do not wait for a general defadt backend. The arena-store-5 inventory says 94 syntactic readers, most relations, about 30 executed readers; classify them by count, indexed access, bounded cursor, fold, append/prefix, and snapshot operation. Prove reusable access-pattern refinements and specialize them, rather than create a twin for every caller.

`fn-hrecs`' correspondence currently projects concrete state; the meaningful history relation is `fn-hrecs-faithful`. Keep that distinction explicit. Establish it at real image adoption, full replay, import, and recovery; preserve it at mutation, fill, and eviction. Do not make the host assume the relation it is supposed to establish.

Arena-store-5 explicitly leaves matching two durable writes to the host. Matching counts is not matching history. A selected manifest/root must bind the materialized image to the exact log prefix, schema/codec interpretation and store identity. Test equal-count/different-history pairs and individually valid objects from different generations.

A finite page-count retry fuel proves neither bounded service latency nor compatibility with eviction. Page faults must become asynchronous requests outside the owner mutex, with operation/root generation, expected page identity, and a pinned continuation. A timeout does not turn missing data into article absence. For a bounded cache, preserve the active read's required pages or prove a progress measure that tolerates eviction.

Near-zero open defers validation; state exactly which damage can be discovered at first touch. Keep an explicit full integrity-scan operation. Report ready time, cold first-query cost, and full scan separately.

## Extraction calls

Authorize the implementation and qualification work. Keep an ACL2/SBCL reference build; introduce extracted read-only service, then a writable build after state-and-effect/crash differentials cover its actual host closure. A named A-EXTRACT assumption is not discharged by calling a differential its witness.

Maintain a frozen extraction manifest: admitted world, roots, resolved attachments, target data model, erased checks, runtime shims, compiler options, and foreign-library identities. Reject unsupported forms. Keep entry guards where callers are not proved to satisfy them, and preserve evaluation order, aliasing discipline, protected stobj updates, arithmetic boundaries and error behavior.

Compare durable effects and subsequent states, not only reply transcripts. Exercise malformed inputs, stobj/state transitions, missing pages, failures, restarts, key changes, concurrent completion and real filesystem operations. A second backend helps detect backend defects but shares frontend risks. CakeML reduces the backend/compiler part of the trusted chain; it does not automatically verify ACL2-to-CakeML translation or fn's FFI.

Optimize the existing Chicken path first: finite keyword dispatch, small fixed-record accessors, safe representation specialization and selective inlining. Judge the 3.4x gap on real workloads and target memory budgets, not only small in-process transcripts. Do not start another backend merely to avoid profiling the current one.

## Migration calls

Use BLAKE3 for new fn-defined hashing as decided. Separate new storage framing/page digests from old portable identities embedded in signed statements. Preserve old immutable evidence under its original interpretation, with narrow legacy verification or an explicitly refused migration domain. Do not silently rewrite signed references or require other authors' private keys.

Preserve cancellation authority through protected secret/key-epoch backup where possible; losing old Cancel-Lock capability is an operational choice, not a necessary consequence of changing the Store digest. Preserve stable principals and credential bindings rather than automatically replacing an identity because a default derivation changed.

`store-export.lisp` says feed journals and BP spools do not travel. Re-peering is not evidence that outstanding delivery obligations survive. Require draining, obligation transfer, or an explicit authorized waiver before retiring the old node.

Adopt previous-layout archive compatibility as a useful baseline, but include semantic/event/hash dependencies, not merely decoding the old tuple. An upgrade-equivalent digest is evidence only for its declared projection; it does not prove equivalent authorization, retention, cancellation or recovery behavior.

## F4 calls

Keep the existing safety rule: positive acceptance follows the actual durability completion. A time alarm changes admission and notification, not whether a pending write succeeded.

Suggested qualification targets, not achieved numbers: local cached health/inspection p99 <=250 ms and <=1 s in the injected-disk-stall campaign; bounded warm reads <=1 s; cold reads have a separately declared dependency timeout (initial target 5 s); disk slow threshold D=5 s; unresolved-write notification at H=30 s plus <=1 s notification slack under the stated host scheduling assumptions. The design document currently gives H=60 s, so choosing 30 s is an explicit default change, not a description of current behavior.

Keep request outcomes separate from late device completion. No second client reply, no early release of I/O-owned resources, and no stale completion applied to a new generation. A durable timeout notification must not wait for the same disk that has stalled. Health distinguishes process liveness, read readiness, write readiness and unresolved durable operations.

## Generators, proof cost and Python

Priority: definterface plus the logic/exec split pilot; one profile source; defevent; then narrow defadt generation from stable hand-derived instances. Generate mechanistic representation/codec obligations, not purported authority or history correctness from field shapes. Expand defkeystone where it removes real duplication, not to every helper lemma.

Use stable abstract interfaces and attachment/implementation books. Merely renaming files logic/exec does not stop recertification if their include closures still contain implementation changes. Keep exported rules minimal, localize aggressive rules, and profile tau, elaboration, loading and rewriting separately. The near-5-second rule needs an aggregate/critical-path budget too: thousands of sub-threshold regressions are not free.

Retire the Python host with its dependencies, consolidate the native harness, and replace duplicated Lisp parsers/macro interpreters with trusted-world exports. Keep independent protocol/crypto checkers and real OS/network/crash tests. Fundamentals F1–F8 do not replace the v0 protocol conformance matrix unless each displaced obligation has another owner. A theorem generator does not by itself replace reachability or host-binding checks. Generated tests and generated implementation can share the same mistake.

## Scale, dictionaries, operations and release

Use 1k–100k curves for iteration, but require a real held-out 1M run before advertising 1M support. GC/cache/COW/growth thresholds can invalidate a confident fit. Test across resize thresholds, with a bounded cache, old pinned readers, sustained checkpoints and reclamation, and cold first reads.

Bao is most attractive for genuinely partial/resumable large transfers, not as a new prerequisite for ordinary whole-article reads. Compression dictionaries can help small similar messages: persist dictionary bytes as immutable digest-identified dependencies, durable before reference, retained through snapshots/export/recovery. Test unseen corpora, bounded decompression memory and missing-dictionary refusal. Do not treat the codec's small dictionary ID as a cryptographic identity.

Keep the user-selected release sequence; use the explicit sequence manifest, not numeric version comparisons. The first tag should promise the actually qualified NNTP/BP/persistence/resource profile. Keep F8 unmet unless ember explicitly adopts a revised metric/profile. Do not require general defadt or CakeML before a useful tag; do require no known silent loss, covered admission and credible recovery on the advertised build.

For external trust, prioritize a separately operated peer with independent keys, narrow peering authority, documented cancel/moderation and retention behavior, restore rehearsal, and clear compatibility/support information. No deployment or cutover is authorized by this review.

## Highest-priority integrated campaign

Exercise a pinned old reader, new accepted writes, a snapshot publication, cache pressure/eviction, a delayed page read or durability completion, and recovery after a crash in the same scenario. Include swapped equal-count snapshots and old-format evidence. Require that accepted history remains accepted, damage is never ordinary absence, uncertainty is never retroactively refusal, and no live/fallback root loses a page.

The main risk is an unclosed composition between locally correct components. The next convergence should make that composed boundary true and observable, not merely add more locally green helpers.
