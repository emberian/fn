# Native empirical workloads

Owner: Codex GPT-6.1-Sol empirical deputy, 2026-10-03. Technical contracts
belong to Groundwork; Integration schedules images and expensive runs. This
matrix describes finite experiments, not proof or deployment qualification.

| Workload | Real consumer / oracle | Measurements and discriminating checks | State |
| --- | --- | --- | --- |
| Mixed POST, warm/fresh TCP/slow ARTICLE, live checkpoint/reclaim, reopen | `tools/native_mixed_workload.py`; native `Client`, injected-source comparison, actual `STAT` numbers | Paired same image/profile/seed, actor latencies and progress, sampled owner RSS/HWM/FD/store peaks; exact source preservation and exact served bytes/numbers across restart; four outcome classes | SCN-1083: historical45e paired and current1a946 baseline exact correctness passed; current4.198s total, quiet reclaim credit-refused16,680,640. Currentad8 matched funded baseline/slow pair passed:48accepted/36reads/all48exacthashes+numbersreopen percase, final actual custody dualreceipts/drain checked, sampledRSS~570MiB/fd23. Explicitmaintenance excluded; successful maintenance progress remains open |
| Reclaim capture before independent OVER response ownership | `tools/resilience/adapters/reclaim_hold.py`; actual hold/settle/defer/install markers, client bytes | Existing native response ownership boundary; observed hold prevents swap, settlement permits progress; physical sector release unclaimed | Ready existing consumer, image run scheduled after mixed smoke |
| Issued read cancellation, file retirement, delayed completion | `tools/resilience/adapters/page_io.py`; image-owned token/answer labels and client bytes; `tests/test_native_page_io.py` actual fd and job-return observations | Held token cancelled, late answer discarded, old file closes only after settlement; productive retained read; CID reuse requires its own witness | New developer-only fd/admit/capture/job-result/physical-return/settle/close observations feed existing finite native schedules; ad8da41/core14ab00 finite native normal held-read2.546s and cancellation/retirement/stale/duplicate40.981s passed with0skips, using archived old fixture assertions. Successful raw trace bytes were not retained; new result-label/complete-byte/shutdown fixtures remain pending. Finite non-wait E regions and captured actual executor identities now feed the bounded collector; normal held-read fixture consumes its opaque readout; prepared held-SIGTERM fixture checks actual join call/return and exact reopened bytes. Normal and cancellation/stale/duplicate fixtures compare complete captured native replies during service and after reopen; their strengthened selection is pending. Literal stored :job-result is distinct from device :io-complete. COMPLETE is only collector-prefix status. Full certified HM comparison remains unavailable pending physical wait/pin/remaining O edges, literal condition boundary and matching model/native dependency digests |
| Actual actor child creation and failed joins | `tests/native_actor_envelope_raw.sh`; real SBCL threads and native envelope hooks | Timeout/failed join retains child, cleanup cannot run under live borrow, duplicate return cannot refill, post-create failure retains parked child | Runtime source ready; combined-image consumer pending |
| Funded syncer interruption/recovery | Native syncer job + typed `fn-ros-install-syncer`/physical join | Retain exactly the captured job through interruption and pending join; funding and operation settlement are separate observations | ad8da41/core14ab00 actual funded mux POST/stop/fresh ARTICLE passed2.732s0skips; exact issue token/opgen independently physical+outcome receipts and final typed/native drain asserted. Successful receipt bytes not retained; strengthened complete-byte/reopen keeper fixture pending. No full user-bank enforcement claim |
| Sparse NEWNEWS over >8 rows and tombstones under competing work | Actual served metadata scan/cursor plus complete client reply | Complete sparse match set and no tombstoned payload I/O; separate metadata progress from payload reads | SCN-1085: historical45e and current1a946 whole-scan bridge exact reply/progress/reopen passed; current4.829s total, offline expiry2accepted/live reclaim credit-refused8,098,624. Per-command I/O attribution and new bounded cursor image remain open |
| Peer interruption and recovery | Existing native BP node/contact adapters, ACL2-generated bundle/request bytes | Pre-connect failure versus post-connect uncertainty; durable held work survives restart; only exact application receipt releases custody | SCN-001: historical45e receipt-held death preflight native retention-refused before nodes/fault. Existing native producer reused and literal MID transport repaired; source/request/journal archived. Focused native undertaking/carry fixtures now use real same-image NNTP accepted source and core inspect; their current grant/reopen execution remains pending. Current retention producer and DTN image rerun owed |
| Restartable application report/reply and saved-delivery recovery | `tests.test_native_consumer_exchange` plus real `tools/fn_consumer.py`/independent verifier/SQLite/native consumer position | Preserve exact saved cursor/report through projection-process failure; commit/reply/ACK only after actual application transition; owner restart and reply correlation | fc6 app/ad8 kernel selected case failed native bootstrap UNCERTAIN3 before report/agents/projection cut; owner fenced on rejected record placement.7 interface blobs equal, composed producer compatibility not established. Exact logs/source filed; rejected record bytes unavailable after fixture cleanup. Groundwork/Lieutenant diagnose before any rerun |
| Crash schedules for post/recovery/checkpoint | `tools/resilience/adapters/native_cuts.py`; actual image cuts and scan | Preserve every previously acknowledged article, classify lost replies separately, check exact bytes/memberships after repeat recovery | SCN-003: historical log-written→recover-barrier-1 actual deaths, exact recovery/read/retry passed in 7.54s; atomic-memberships pending. Early cut selection preserves selected validation. Retired per-file mock families excluded |
| 1k→100k curves | Existing `tools/scale_curve.py`, `fixtures.py`, ACL2 `synth_log_store.py` | Matched profile/heap/cache/host conditions; post, read, maintenance, open and resource curves; no 1M execution | After smoke and image convergence, Integration budgets selected probes |

The mixed runner writes `plan.json`, sealed `journal.jsonl`, `summary.json`,
`manifest.json`, and owner diagnostic streams outside the store. A plan fixes
per-actor requests and phase barriers; the event journal captures the realized
OS concurrency. Replaying the plan does not promise identical interleaving.
Fresh TCP is labelled cold connection, never cold filesystem cache. Delayed
line consumption is a slow client, never evidence that a kernel write blocked.
Baseline and perturbation use separately initialized scratch stores; neither
touches a live node or a registered fixture in place.

Manifest image launcher/core/runtime digests and supplied image-source revision
are distinct from harness-source revision and input hashes. Diagnostics cannot
establish durable promises: accepted client replies and recovered exact content
do that for the observed schedule. Checkpoint log markers establish that the
requested maintenance actually ran, not its durability by themselves. Store
allocation and descriptor peaks are sampled at 100 ms, owner process only;
shorter spikes and separate control-client processes are outside that measure.
Null metrics are unavailable, never zero. Percentiles are descriptive for the
sample count, not distribution or latency guarantees.

Archive completed run bytes under a named `planning/evidence/` coordinate with
`tools/evidence_store.py put`; commit the resulting index lines, not logs. Keep
this matrix and SCN-1083 scope aligned when execution exposes missing consumers.

Current-source continuation, 2026-10-03: SCN-1129 adds a decoder-specific
pending-read hold. The legacy PageIO selector cannot demonstrate this branch:
actual typed decoded jobs previously bypassed its hold entirely. The new
connected selector preserves an actual compressed article, admits competing
POST/DATE while its physical read remains held, then observes literal cancel,
read return, physical return and independent release before exact reopen.
Actual SBCL physical seam passes with a real fd/syscall; connected native run
is pending current host entry and Root's real pre-open default pool producer.
No old image or raw recording fixture verdict is transferred to that outcome.
