# Native I/O review: root disposition

The [independent report](claude-native-io-seam-review.md) is archived unchanged.
It inspected integration `406578c` and owner candidate `d47212d`, in the real
interactive `fn-claude-review` tmux session. The intended broader duplication
pass converged on the raw I/O boundary; root and the CLI lane cover the other
surfaces in the [consolidation audit](../duplication-audit-2026-09-21.md).
This response records source checks and assignments, not completed fixes.

| Finding | Disposition |
| --- | --- |
| F1: configuration enumeration errors become empty history | The error/empty conflation is real in `37ec36b`'s `fnn-config-record-names`. Assigned to the native initializer lane with a second-enumeration failure test. The report's stronger fresh-data-loss argument is **not established**: `fnn-publish-initial-file` already calls `fnn-fsync-file` on the staged contents before linking them, so skipping a later repeat file barrier does not by itself show that fresh contents were never fenced. Error classification and host/model trace divergence still require repair. |
| F2: reader condition subtype collapse | Confirmed by the native handler ordering. Assigned to native I/O progress work, preserving per-connection and global-fault distinctions. Root also found an earlier classification loss: `fnn-call` turns an ACL2 execution error into `fnn-refuse`, and core-result shape checks do likewise. Repair that boundary as well; a successfully returned semantic refusal is different from a failed core call. |
| F3: writable owner catches uncertainty as a generic connection error | Confirmed in the report's exact `d47212d` source. The active successor already has an explicit indeterminate clause calling `fnn-owner-fence-service`; its tests and integrated evidence are still required. A `fnn-store-fault` remains a subtype caught by the generic clause in the inspected successor, so owner convergence is checking the separate fault contract. The report's suggested connection-fault transition alone would not establish a global uncertainty fence. |
| F4: socket zero progress / EINTR | The source asymmetry is real. Assigned to native I/O progress with deterministic zero/partial/EINTR cases, EOF preservation and a deadline that does not reset indefinitely on retries. Do not claim that every injected result is naturally reachable on every supported platform. |

The report's cleared items are source-review observations, not qualified
platform or formal correctness results. Its JSON discussion concerns superseded
metadata code and creates no new repair requirement. No additional review gate
is required: land each coherent tested repair and record its actual scope.
