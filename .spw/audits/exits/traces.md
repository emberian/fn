# Exit trace ledger

Consumer source base: 3f39e6df98b3d87881e43200bba9334e47e1af4b. Code lane: codex/horse-exits. Workbench infrastructure is excluded.

## EX01 — journal cleanup stranded suffix (repaired, actual-source tested)

Terminal subjects: host/native/owner.lisp `fnn-owner-feed-close-all`, `fnn-owner-feed-open-all`, `fnn-owner-feed-open-missing`.

Counterexample: three journal rows a,b,c; close(a) signals. Previous close-all exited before b,c and never cleared cache. During open rollback, successfully opened a,b followed by failed open(c); close(b) signals and replaces the original opening/replay fault while a remains open.

Repair: `fnn-owner-feed-close-entries` attempts every independent close and retains the first cleanup condition. Close-all clears exhausted custody rows and then signals that first condition. Opening rollback attempts all closes and re-signals the original fault. Per-journal close invalidates its FD slot before physical close, so no retry against a reused FD.

Check: `sbcl --script tests/native_feed_cleanup_source.lisp` passes complete production definition extraction with injected first/two close errors and identity checks on primary conditions. This is source execution of host cleanup, not ACL2 certification or image qualification.

## Pull/catch-up terminal traces (inspected)

`fnn-pull-flight-finish` -> dispose local capture/cold/await and TLS/socket -> ACL2 session-close-effects (journal publication) -> log -> cursor-cache publication -> scheduler finish. The cache does not advance if the journal close effect fails. `fnn-pull-journal-append` write/fsync failures close journal and signal indeterminate; no false refusal. Post-barrier failures are definite faults preserving persisted cursor.

`fnn-pull-worker` unwind -> every flight dispose -> every cached FNPL/FNCU close. Each independent cleanup is attempted; primary body condition wins. `fnn-pull-service-close` wakes blocked sockets, joins worker, then unregisters runtime. Full cleanup debt semantics on an ACL2 close escape remain runtime-owned for cross-check.

## Service fencing (inspected)

`fnn-owner-stop-service-locked` installs stopping/exit escalation before lifecycle drain, signals clients/committer/commit waiters in unwind cleanup. ANSWERING sockets remain spared for owed uncertain reply. Socket shutdown wakes blocked I/O without FD reuse; cached FD's worker closes it. The exit lattice prevents graceful stop masking later uncertainty.

## Workbench recipes

Observed: `npm --prefix .spw/_workbench run spw -- roots` resolves the outer mounted-consumer manifest and names consumer @spw and infrastructure @workbench separately. CLI emits Node module.register deprecation warning; navigation still succeeds. Parse/query checks follow as map grows. Entries horse owns shared manifest/index.

## Remaining coverage

NNTP output/refund and EOF, Web terminal branches, BP acceptance/ACK separation, store/checkpoint terminal barriers, shutdown/restart and reclaim are still open inspection scope. Known startup baseline and already-repaired actor/Web/decoded cleanup are cross-linked to current owners rather than recorded as new defects.

## EX02 / EX03 / EX04 — physical close failure hidden by terminal helpers

EX02: `fnn-bps-read-route-table` previously skipped Store cleanup after feed cleanup error and replaced body error. It now consumes `fnn-unwind-cleanups`.

EX03: `fnn-owner-install` rollback attempts feed and Store cleanup independently, preserves primary initialization failure, and retains the actual service/Store carrier if either cleanup fails. Operator owns settlement's fallback from nil explicit service to the actual retained carrier (a startup `t` reservation is not a Store).

EX04: `fnn-store-close` previously suppressed active-log close and spare cleanup failures; `fnn-owner-store-settlement` then observed `:closed`. Close now attempts spare/log/unlock/lock close independently, fences on failure and records sticky `close-debt` holding log, lock descriptor identity and first condition. Repeated close re-signals debt, never retries consumed descriptors or claims settled. Spare close/unlink failures retain the original spare metadata in `spare-close-debt` and signal instead of disappearing. History agreed this scope.

Shared macro contract: `fnn-unwind-cleanups` preserves normal multiple values; runs every cleanup; signals first cleanup error after normal return; preserves actual nonlocal body escape including `throw`; secondary cleanup error is diagnosed. A handled body condition is a normal return, so later cleanup failure remains visible. Unlike recording every signaled condition with handler-bind, this tracks actual completion.

Checks: `sbcl --script tests/native_feed_cleanup_source.lisp`, `tests/native_store_cleanup_source.lisp`, `tests/native_owner_install_cleanup_source.lisp`. Actual complete production definitions loaded; injected spare close, unlink, active-log close, unlock, lock close, startup failure, and normal/throw/handled-condition macro behavior passed. Startup fixture supplies only early-fault prerequisites, so compiler reports later uncalled symbols; this is scoped actual-source coverage, not whole startup or saved-image qualification.

Workbench coordinate: 651b535b5171e9ed419570f4cd64b53914094433. Observed `select .spw/audits/exits/index.spw --selector navigable --summary` resolves four PathRefs; tool/root ownership remain correctly separated.

## Native terminal boundary coverage (inspected, no new qualification claim)

| Exit | Backward obligation / forward effect | Source subject | Status |
| --- | --- | --- | --- |
| NNTP EOF/cancel | Mark done prevents scheduling; abandon awaiting publication, cold read; return response window/output/unpin; close core/exposure; independently TLS/zlib/socket cleanup; debt retains failed receipts | `fnn-mux-finish` (host/native/mux.lisp) | Inspected full definition; Runtime owns debt mechanism |
| NNTP logical close | Drop only matching connection/pin/staged pending/queued requests; immutable committed Store retained; connection credit released, commit/open/sealed credit separate | `fn-owner-callback-close` -> `fn-ocfg-close` -> `fn-own-close`, `fn-mca-close` | Inspected full executable definitions |
| Output physical refund | Output drain/discard is separate from physical dependency completion; closed+output-returned+no-dependencies needed for terminal physical receipt | `fnn-owner-output-close`, `fnn-owner-output-maybe-physical-locked` | Inspected; no empty-slot equals physical-return shortcut |
| Web cancel/shutdown | Semantic disposal claimed only after exact job returned; revoke aliases before response window/unpin/core close; cleanup debt blocks semantic-ended | `fnn-web-dispose-semantic`, `fnn-web-discard-response` | Runtime's landed graph-discard repair present in base; inspected |
| BP transport socket return | Once-only close consumes socket slot; only :closed observation returns grant; ambiguous close signals indeterminate and keeps grant | `fnn-bp-session-close` | Inspected full definition |
| BP private context return | Finished alone insufficient: source-pending/root/token/held messages/tx arrays must meet ACL2 release-ready; then clear callback/context aliases before grant observation | `fnn-bp-session-release-context` | Inspected full definition; BP transport owner |
| BP received acceptance | Persist kind5/conflict14 -> persistence-result machine -> callback disposition; accepted requests later rescan; uncertain fences; refused tracked distinctly | `fnn-bps-receive` | Inspected full definition |
| BP final ACK | ACL2 delivery-plan selects held final ACK; accepted/refused flush corresponding plan; uncertainty fences and never flushes acceptance ACK | `fnn-tcl-settle-delivery` | Inspected full definition |
| Immutable publication | ACL2 stage/write->file barrier->link->directory barrier; final-name visibility after error is not durability; post-authority unlink/fsync cannot downgrade accepted result | `fnn-immutable-publish-effect` | Inspected full definition; physical fd-close debt outside Store terminal remains a separate question |
| Store open/recovery failure | Cleanup must preserve primary failure and convey actual Store close uncertainty even before owner-install receives Store | `fnn-open-live-store`, `fnn-acquire` | Newly identified EX03 deeper residual; coordinating Operator |

CLI friction: `tree @spw` only enumerates .spw files; linked Markdown ledgers are discoverable through PathRef/select, not tree's file count. This distinction is useful: store semantic navigation cards in Spw and detailed executable traces in linked Markdown.

EX03 deeper gap repaired by fe5ead1b3: `fnn-acquire` and `fnn-open-live-store` consume common failed-open close preserving the primary error. `fnn-owner-install` binds a scoped custody callback around the initial open; a failed physical rollback delivers the actual Store to an existing minimal retained-service carrier before original error escape. Operator's complementary settlement fallback is 1e9eb6f52. Source fixtures also cover this exact callback through actual owner-install.

Archived source witnesses: `planning/evidence/horse-exits-2026-10-03/source-cleanup.json`, hash4600ec439de67d221de64b3574115b8301df30c508bea560030f57e85693f041, sourcefe5ead1b3. Three fixtures passed; no ACL2/saved-image claim. Integration owns coherent module load because Store/log structs gained terminal debt fields.

Additional inspected leaves: `fn-own-close` removes only matching queued/inflight submission descriptors and connection; committed Store/view/ledger survive. `fn-mca-close` resizes only connection-key credit to zero, leaving committer :open and :sealed ownership. `fnn-remote-receive-installed` reaches `fnn-remote-installed-entry`, whose current unavailable preflight does not invoke BODY or consume suffix; remote transport remains inactive, not claimed as operational. `fnn-command-compact` and `fnn-command-reclaim` only return success after checkpoint/drop/reclaim steps; physical close is later independent cleanup. `fnn-clone-activate` validates reopened durable rollover before removing activation fence; fence removal fsync error is explicit indeterminate. Wider CLI direct unwind cleanup still can replace a primary body error with physical close error; retained authority fix addresses actual owner startup, not every CLI error message.
