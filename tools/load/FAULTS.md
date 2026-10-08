# Fault corpus: externally visible properties

F1 through F6 drive a private shipped image through NNTP and the operator
control socket. F1/F2/F4 load developer hooks before starting the image; no
cell edits store bytes. F7/F8/F9 remain explicitly not implemented, with their
properties and owners in workloads.json.
No cell qualifies power loss. The product's claimed write-ordering assumption
is **fdatasync durability of the store filesystem**; abort/SIGKILL tests process
death only. A surviving OS can retain unsynced writes.

The deputy runs these on a build box, in its own scratch, detached under
`timeout` with a PID file (and `swarm-build` on hbox). Use the existing driver's
`run --cell F2 --image IMAGE --out OUTPUT --work SCRATCH --keep` interface.
Do not use its `box` command from this lane. No deploy or live-node path is used.

Every fault-client command has an operation ID, argument digest, monotonic
send time, final reply line and one outcome: `not-attempted`,
`attempted-uncertain`, or `completed`. An incomplete multiline reply is
uncertain even after its status line; POST's 340 is intermediate, never its
completion. Send exceptions are conservatively uncertain because a partial
send may have reached the owner. Closing a client emits no unrecorded QUIT.
Control operations record their complete output and exit status too.

`faults.violations` names the property, original history length, shrunk history
and rerun budget consumption; `faults.outcomes` counts all three outcomes.
The shrinker tries prefix/suffix/chunk deletion on fresh private stores,
preserving operation order. A budget-exhausted history is the shortest found,
not a claimed global minimum. A completed ddmin is one-deletion minimal.
A missing required observation never supplies a passing zero-violations bar.

| Cell | Required externally visible result | Control and finite scope |
| --- | --- | --- |
| F1 | P4-RECLAIM, P2-IDENTITY: a cold-read completion after cache reuse across publication returns its accepted octets (`faults.digest`) or a named refusal, never another article's bytes. | Separate E (entry) and W (window) trials, each with 25 distinct 512 KiB articles, checkpoint then restart, cache restricted to one entry. Hold the first entry cache store / cache-eligible window release; concurrently request checkpoint/publication and 24 other cold reads, then release. Each route requires publication, file-drop calls, actual eviction and reuse during the hold; otherwise that route is not measured. Both routes must qualify to supply the cell's zero-violation bars. |
| F4 | P2-IDENTITY: under saturation and across restart, every existing Message-ID resolves to original octets, absent IDs are absent, and neither same-byte nor changed-byte reposts are accepted. | Up to 1,048,576 candidates, ACL2 tag oracle in batches of 4,096; 2,304 present candidates and 32 absent candidates sharing eight low tag bits, plus 62 IDs with a 128-character shared prefix and wide fan-out. STAT/ARTICLE on every ID before and after restart. Requires unplaced > 0 in both epochs. |
| F2 | P1-DURABLE: every read 240 survives, Path/Xref excepted. P2-IDENTITY: only attempted IDs/octets exist, uncertain POSTs whole or absent. P5-RECOVERY: clean recovery after two process deaths reaches LISTENING and accepts a POST within 60 s. | 100 POSTs at intended 20/s with one requested publication; count boundary calls, then sample first/middle/last of each, 16 shrink reruns per finding. Full LIST ACTIVE/LISTGROUP/ARTICLE inventory, including numeric and Message-ID lookup routes. |
| F6 | P8-CLIENTS: fragmented/pipelined GROUP, ARTICLE, HEAD, STAT, POST+body, and invalid command have the same replies as the unfragmented reference; invalid command is refused by name; another client meets a 10 s deadline. | Every split of the reference transcript is eligible; 64 evenly spaced splits including the endpoints when long. One variant changes exposure-connections to 32 after ARTICLE's status line. Fresh-store RSS must stay within 16 MiB of reference. 16 shrink reruns. |
| F5 | P8-CLIENTS: four fast clients' GROUP/STAT/2 KiB ARTICLE p99 stays within 2x solo; RSS growth is at most four x 512 KiB; a send refusal is logged by name. | Four 512 KiB readers, SO_RCVBUF=4096, one-byte recv then 10 ms sleep; eight queued ARTICLEs each to exhaust socket queues. Four fast clients, POST at intended 5/s; 10 s solo, 40 s stress; at least 200 samples for each p99. Owner cache cold after restart, filesystem cache untouched. Eight shrink reruns. |
| F3 | P4-RECLAIM: resumed ARTICLE replies are accepted octets (Path/Xref excepted) or named refusals, never other content. | Four held 512 KiB ARTICLEs; checkpoint/publication, expiry policy and installed live reclaim, then a different POST before resume. Requires actual reclaimed articles, not a no-op pass. Eight shrink reruns. |

Finite F5/F6 RSS envelopes are bounded experiments, not proofs of bounded RSS
for every possible client sequence. F9 is the unimplemented long-run slope cell.

F2's hook uses `sb-int:encapsulate`, with `FN_LOAD_CRASH_AT=function:k`.
`FN_LOAD_CRASH_COUNT=path` appends per-function cumulative counts in the
reference. `FN_LOAD_CRASH_GO=path` arms only after LISTENING, excluding initial
open. The second start omits that gate and uses `*:1` to abort at the first
candidate boundary reached during recovery. `FN_LOAD_CRASH_RECORD` is a
pre-created side file: the hook appends function/count, flushes, calls
`sb-posix:fsync`, then `(sb-ext:exit :code 86 :abort t)`. No hook-witness file
means the intended cut was not established. Zero reference calls and unreached
sample hits remain not measured. The clean third start removes all arming vars.

Boundary entries are fnn-durable-barrier, fnn-log-fdatasync,
fnn-checkpoint-yield (each arena/history batch), fnn-checkpoint-write-arena-steps,
fnn-checkpoint-write-steps, fnn-state-checkpoint-install and
fnn-owner-publish-captured. The hooked shipped image must retain those names;
missing names fail hook loading instead of silently reducing coverage.

The current external publication verb is `operator CONFIG store checkpoint`
(`books/native-operator.lisp`), as in phase_publish_live; there is no store
`publish` verb in this tree. F3 uses `store reclaim` with `[resources]
reclaim_live = true` and `retention expire fn.test purge 30`. It requires the
`RECLAIM installed records=... reclaimed=N` witness with N positive.

Box-only checks: load/encapsulate these forms in each shipped image; confirm
reference boundary reachability and both death witnesses; run inventory after
recovery; measure the p99/RSS/send-refusal windows; observe actual publication,
reclaim and held-reader bytes. Laptop tests validate orchestration primitives
and data, not those runtime claims. See specs/failures.md and the existing
native crash-model/torn-journal campaigns for the separate model correspondence.

F1's `f1-delay.lisp` uses `FN_LOAD_F1_ARM`, `FN_LOAD_F1_RELEASE` and
`FN_LOAD_F1_WITNESS` paths, `FN_LOAD_F1_ROUTE` (`E`, the default, or `W`),
`FN_LOAD_F1_N` (armed call number; W counts cache-eligible calls only),
`FN_LOAD_F1_SECONDS` (maximum hold) and `FN_LOAD_F1_CACHE` (test cache size,
never larger than the image's allowance, including zero). E holds before
`fnn-extent-cache-store(file eoff elen trailer octets &optional token)`;
the token is forwarded unchanged, including NIL in offline mode. Its
`fnn-extent-cache-forget(entries)` wrapper counts removed entries rather than
returned tokens, so offline evictions count too. A successful competing store
must consume a position vacated during the hold to count as reuse. W holds
before `fnn-extent-window-release(worker token &optional cachep)` only with
cachep and a positive cache limit; `fnn-extent-window-cache-insert` records
returned eviction tokens and inserts that replaced an occupied position.

Witness rows are `held ROUTE FUNCTION N`, `token ROUTE TOKEN`, and
`released ROUTE FUNCTION INSTALLS DROPS EVICTIONS REUSES` (or `timeout` with
the same counts). Counts cover only the hold: the held call's own installation
after release cannot qualify. W also records `pool W funded|unfunded` from
the actual `fnn-extent-pool-funded-p` decision. Results and traces retain the
raw witness, function, counts, per-route coverage and missing-evidence reason.
Torn, mismatched and timeout rows cannot supply a release witness.

W uses the default startup configuration in this tree:
`fnn-owner-page-read-startup` calls `fn-owner-page-read-install-default`, which
calls `fn-owner-page-read-install-baseline` and supplies the data needed for
`:funded-pool` in `fn-owner-page-read-direct-mode`. The five `[resources]`
keys `cold_heap_octets`, `cold_workers`, `cold_descriptors`, `cold_read_ids`
and `cold_file_ids` are parsed by `books/native-config.lisp`, but an explicit
cold policy is refused as `:unpriced-complete-cold-profile` by
`fn-prstartup-default-plan` in `books/page-read-startup.lisp`; they are not
an enable switch. Leave them absent. If the running image does not observe
a funded default pool, W is NOT-MEASURED with that reason, never forced by
changing a pool mode in the hook. A funded pool alone does not prove the
response-capture window route was reached: the hold witness is still required.

The harness releases on setup failure too, and collects the held and competing
replies after release. It never unlocks an owner or extent mutex. Entry callers
hold the extent mutex; `fnn-owner-cold-window-result-locked` calls window release
with the owner mutex held. Either can prevent this interleaving, yielding
NOT-MEASURED. Publication completed only after release cannot qualify.

F4's `f4-index.lisp` observes the live catalog at
`fnn-owner-read-buffer-fill`, under the owner mutex. `FN_LOAD_F4_REQUEST` is a
numbered `tags START COUNT` or `health` request, and `FN_LOAD_F4_RESPONSE`
contains its matching number, decimal rows and a final `done`. No Lisp reader
parses that file. Tags come from `fn-mlh-tag-of` using the live table; the key
never leaves the image. Health records `fn-mlh-build-health` and checks it
against `fn-cat$c-index-health`. Refused candidate POSTs become additional
absent probes. A saturated admission refusal does not imply unplaced rows:
if the image prevents all such rows, this trial remains not measured. These
are finite search/workload bounds, not new admission limits.

F1/F4 save observed wire histories and hook evidence in reference traces,
marked nonsequential because the wire replay format cannot reproduce file
trigger timing. Findings explicitly say `not-replayed`; these cells do not
claim a minimized counterexample. Missing hook functions, candidate exhaustion,
unreached hold/reuse and missing saturation remain named not-measured outcomes.
Box runs must confirm encapsulation reachability, the live stobj accessors and
health equivalence, publication during the hold, and the resulting NNTP bytes.

F7 remains not implemented: the g41/dev store has no persisted Message-ID
index; open rebuilds fn-cei and the catalog msgid table from checkpoint records
(`books/store-checkpoint-open.lisp:206`). It waits for paged checkpoint/catalog
adoption (`s-pck-2c-host`, `PCK-ADOPT`).
