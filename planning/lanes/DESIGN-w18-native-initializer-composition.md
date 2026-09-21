# W18 native initializer composition

This packet extends the reviewed W14 fresh path only where current native
`store init` actually continues after an immutable-link `EEXIST`.  The host
subject is `fnn-command-init` -> `fnn-initialize` -> `fnn-acquire` in
`host/native/io.lisp`.  It does not state a full physical correspondence,
all-opening-path claim, or a recovery-sweep correspondence.

| Observed native branch | Host result | Executable byte-model subject | Runtime witness |
| --- | --- | --- | --- |
| Fresh root and metadata | accepted after all fresh cuts | `fn-bsi-current-init-program` | existing W14 fresh/restart cases |
| Valid existing config and frontier | accepted; each immutable root link returns real `EEXIST`, then existing bytes are loaded | `fn-bsi-existing-init-program` | repeat `store init`, then new-process `recover` |
| History file durable, frontier absent after SIGKILL | retry accepts the existing config link, creates the missing frontier, then recovers | `fn-bsi-history-retry-program` | SIGKILL at `init-config-history-fenced`, fresh-process retry and recover |
| Second initializer owns no lock | refused before metadata publication | no byte-store mutation; flock is a transient ownership boundary | held real `writer.lock`, then a later successful init |
| Link error other than `EEXIST` | uncertain; final-name effect may have been issued | ordinary `:link` error stops, including `(:eio . :issued)` | executable model negative witness; no platform-EIO claim |
| A history file appears after empty enumeration | uncertain; the host preserves it for recovery | intentionally outside the accepted retry programs | source branch only |

`(:link-eexist ...)` is a byte-store program step that calls the existing
`fn-bs-link` transition.  It continues only when that transition returns
`:eexist`; `:ok` is an unexpected success and every other result remains an
error.  This represents the actual native `link(2)` result before the staged
candidate cleanup, rather than a static list asserting an unspecified retry.

The existing/retry programs begin after directory/lock validation.  Those
checks either have no byte-store mutation or hold/release a transient lock; the
programs do not claim to model all `lstat`, `open`, flock, or external-writer
interleavings.  A SIGKILL is process death, not a physical power-loss model.
