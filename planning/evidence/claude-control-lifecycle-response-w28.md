# Root disposition: native control lifecycle review

The [independent source review](claude-control-lifecycle-review-w28.md)
examines `866223f1`; it is not a runtime result or a review of later main.
It ran in the existing Claude Code tmux session. Root checked the named callers
and assigned the following repairs to the native control/lifecycle lane while
other implementation continued.

F1 is a concrete ownership defect: distinct Store writer locks cannot serialize
one explicitly shared control socket pathname. Before removing a stale socket,
the process needs ownership of that endpoint, not merely its own Store. A
connect probe alone races concurrent startup. Merely requiring a path below
the Store does not prove uniqueness when Store roots can nest. The repair must
include a two-store/same-endpoint refusal witness and preserve the first owner's
endpoint and routing.

F2 was appropriately reported as an unexecuted interleaving concern. Source
inspection by the owner lane confirmed the same ownership pattern in both
control and NNTP workers: the worker caches a raw descriptor while the stop
thread can close it. Shutdown followed immediately by close still permits
reuse before the worker's final I/O. The intended correction is shutdown-only
in stop, final close by the worker, and joining workers before releasing shared
resources. A controlled witness is assigned; no stress-test failure is claimed.

The report's clean observations are scoped inspection, not proofs. Its test-cut
environment variable observation is not a defect: the existing deliberate cut
is part of fault-injection infrastructure. No new approval or serial review
gate follows from this report. Repairs and their exact runtime evidence remain
separate until integrated.
