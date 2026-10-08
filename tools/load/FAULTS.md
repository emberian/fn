# Fault corpus: externally visible properties

F2, F6, F5 and F3 drive a private shipped image through NNTP and the operator
control socket. They do not edit the image or store bytes. F1/F4/F7/F8/F9 are
explicitly not implemented, with their properties and owners in workloads.json.
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
