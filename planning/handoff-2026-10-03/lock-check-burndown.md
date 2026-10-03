# Lock-check burndown (generated 2026-10-03 from lane/lock-check fb4423550; tools/lock_discipline_check.py --json)

Shrink the baseline as defects land: fix, run `python3 tools/lock_discipline_check.py --write-baseline`. That
command refuses to raise any row. Then commit tools/lock_discipline_baseline.json with the fix.
`make check-fast` fails on any NEW finding. It also fails on a STALE row, meaning a baseline row whose finding
has gone away until you lower it.

Each key below is the baseline row: `rule|function|key`. Line numbers are at fb4423550 (dev 4aa332295).

There are two R7 kinds:
- `swallow:` a handler consumes a fault or an indeterminate without fencing.
- `overfence:` connection-local conditions (socket errors, refusals, connection faults) reach the fence, so a
  client/peer event stops the node.
- (`unfenced-gated`: a gated body can signal a fault/indeterminate outside fnn-owner-shared-action-locked.)

There are two R10 kinds:
- `ignored-close`: a close is wrapped in ignore-errors.
- `foreign-close`: the function closes an fd it did not open, and no close row declares the site.

A legitimate site is closed by a DECLARATION in tools/lock_discipline_contracts.json, with its why, not by a
baseline row:
- `failure_scopes` (private / result / converts / fence);
- `close_sites`;
- `exceptions`.

## R7: 88 findings (FAILURE-SCOPE (and HOST-LIFECYCLE for the over-fence rows: a client/peer event stops the node))

### host/native/owner.lisp (34)
- :892 `fnn-owner-feed-append` -- handler clause error consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-owner-feed-append|swallow:error:fault,indet`]
- :904 `fnn-owner-feed-append` -- handler clause ignore-errors consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-owner-feed-append|swallow:ignore-errors:fault,indet`]
- :1398 `fnn-owner-space-event` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-space-event|swallow:ignore-errors:fault`]
- :1764 `fnn-owner-fault-service` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-fault-service|unfenced-gated`]
- :1786 `lambda@host/native/owner.lisp:1784` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|lambda@host/native/owner.lisp:1784|swallow:ignore-errors:fault`]
- :1914 `fnn-owner-abandon-connection` -- handler clause fnn-store-error consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-abandon-connection|swallow:fnn-store-error:fault`]
- :2069 `fnn-owner-attempt` -- handler clause fnn-store-indeterminate consumes ['indet'] without routing it to the fence  [key `R7|fnn-owner-attempt|swallow:fnn-store-indeterminate:indet`]
- :2233 `fnn-owner-attempt-transit` -- handler clause fnn-store-indeterminate consumes ['indet'] without routing it to the fence  [key `R7|fnn-owner-attempt-transit|swallow:fnn-store-indeterminate:indet`]
- :2662 `fnn-owner-consumer-entropy-observation` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-consumer-entropy-observation|swallow:error:fault`]
- :3097 `fnn-owner-commit-start-locked` -- handler clause fnn-store-indeterminate consumes ['indet'] without routing it to the fence  [key `R7|fnn-owner-commit-start-locked|swallow:fnn-store-indeterminate:indet`]
- :3198 `fnn-owner-commit-release-member` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-commit-release-member|swallow:ignore-errors:fault`]
- :3349 `lambda@host/native/owner.lisp:3345` -- handler clause serious-condition consumes ['fault'] without routing it to the fence  [key `R7|lambda@host/native/owner.lisp:3345|swallow:serious-condition:fault`]
- :3633 `fnn-owner-commit-pipeline` -- handler clause fnn-store-indeterminate consumes ['indet'] without routing it to the fence  [key `R7|fnn-owner-commit-pipeline|swallow:fnn-store-indeterminate:indet`]
- :3690 `fnn-owner-committer-loop` -- handler clause fnn-store-error consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-owner-committer-loop|swallow:fnn-store-error:fault,indet`]
- :4323 `fnn-owner-cold-settle` -- handler clause serious-condition consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-cold-settle|swallow:serious-condition:fault`]
- :4327 `fnn-owner-cold-settle` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-cold-settle|swallow:ignore-errors:fault`]
- :4332 `fnn-owner-cold-reap` -- handler clause fnn-store-error routes connection-local ['refusal'] to the fence (a client/peer event stops the node)  [key `R7|fnn-owner-cold-reap|overfence:fnn-store-error:refusal`]
- :4696 `fnn-owner-retire-refuse` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-retire-refuse|swallow:error:fault`]
- :4944 `fnn-owner-release-extents` -- handler clause serious-condition consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-release-extents|swallow:serious-condition:fault`]
- :4967 `fnn-owner-release-extents` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-release-extents|unfenced-gated`]
- :4981 `fnn-owner-release-extents` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-release-extents|unfenced-gated`]
- :5054 `fnn-owner-publish-captured` -- handler clause serious-condition consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-publish-captured|swallow:serious-condition:fault`]
- :5095 `fnn-owner-publish-captured` -- handler clause (or fnn-store-io-refusal fnn-store-indeterminate) consumes ['indet'] without routing it to the fence  [key `R7|fnn-owner-publish-captured|swallow:(or fnn-store-io-refusal fnn-store-indeterminate):indet`]
- :5134 `fnn-owner-publish-captured` -- handler clause serious-condition consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-publish-captured|swallow:serious-condition:fault`]
- :5135 `fnn-owner-publish-captured` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-publish-captured|unfenced-gated`]
- :5212 `fnn-owner-maybe-publish-quantum` -- gated body (class :control) can signal ['fault', 'indet'] outside the shared-action fence  [key `R7|fnn-owner-maybe-publish-quantum|unfenced-gated`]
- :5394 `fnn-owner-export-captured` -- handler clause serious-condition consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-export-captured|swallow:serious-condition:fault`]
- :5465 `fnn-owner-reclaim-dry-run` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-reclaim-dry-run|unfenced-gated`]
- :5506 `fnn-owner-reclaim-dry-run` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-reclaim-dry-run|unfenced-gated`]
- :5593 `fnn-owner-reclaim-intern` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-reclaim-intern|unfenced-gated`]
- :5651 `fnn-owner-reclaim-pass` -- gated body (class :control) can signal ['fault', 'indet'] outside the shared-action fence  [key `R7|fnn-owner-reclaim-pass|unfenced-gated`]
- :5745 `fnn-owner-reclaim-pass` -- gated body (class :control) can signal ['fault', 'indet'] outside the shared-action fence  [key `R7|fnn-owner-reclaim-pass|unfenced-gated`]
- :5797 `fnn-owner-reclaim-pass` -- gated body (class :control) can signal ['fault'] outside the shared-action fence  [key `R7|fnn-owner-reclaim-pass|unfenced-gated`]
- :5917 `fnn-owner-maybe-reopen-log` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-maybe-reopen-log|swallow:error:fault`]

### host/native/mux.lisp (16)
- :249 `fnn-mux-tls-log` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-tls-log|swallow:ignore-errors:fault`]
- :254 `fnn-mux-tls-log` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-tls-log|swallow:ignore-errors:fault`]
- :281 `fnn-mux-finish` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-finish|swallow:ignore-errors:fault`]
- :289 `fnn-mux-finish` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-finish|swallow:ignore-errors:fault`]
- :294 `fnn-mux-finish` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-finish|swallow:ignore-errors:fault`]
- :539 `fnn-mux-z-in` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-z-in|swallow:ignore-errors:fault`]
- :792 `fnn-mux-handshake-release` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-handshake-release|swallow:ignore-errors:fault`]
- :801 `fnn-mux-handshake-refused` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-handshake-refused|swallow:ignore-errors:fault`]
- :850 `fnn-mux-start-waiting-handshake` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-start-waiting-handshake|swallow:ignore-errors:fault`]
- :854 `fnn-mux-start-waiting-handshake` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-start-waiting-handshake|swallow:ignore-errors:fault`]
- :1123 `fnn-mux-dispatch` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-dispatch|swallow:ignore-errors:fault`]
- :1140 `fnn-mux-timers` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-timers|swallow:ignore-errors:fault`]
- :1194 `fnn-mux-take-inbox` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-take-inbox|swallow:ignore-errors:fault`]
- :1219 `fnn-mux-take-arrived` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-take-arrived|swallow:ignore-errors:fault`]
- :1270 `fnn-mux-iterate` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-iterate|swallow:ignore-errors:fault`]
- :1328 `fnn-mux-stop-loop` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-mux-stop-loop|swallow:ignore-errors:fault`]

### host/native/pull-service.lisp (8)
- :229 `fnn-pull-journal-append` -- handler clause error consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-pull-journal-append|swallow:error:fault,indet`]
- :248 `fnn-pull-journal-append` -- handler clause ignore-errors consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-pull-journal-append|swallow:ignore-errors:fault,indet`]
- :308 `fnn-pull-profile` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-pull-profile|swallow:error:fault`]
- :348 `fnn-pull-round` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-pull-round|swallow:error:fault`]
- :365 `fnn-pull-round` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-pull-round|swallow:error:fault`]
- :430 `fnn-pull-round` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-pull-round|swallow:error:fault`]
- :453 `fnn-pull-round` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-pull-round|swallow:ignore-errors:fault`]
- :552 `fnn-pull-worker-guarded` -- handler clause serious-condition routes connection-local ['refusal', 'socket'] to the fence (a client/peer event stops the node)  [key `R7|fnn-pull-worker-guarded|overfence:serious-condition:refusal,socket`]

### host/native/control.lisp (4)
- :123 `fnn-control-send-reply` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-control-send-reply|swallow:error:fault`]
- :269 `fnn-control-handle-client` -- handler clause fnn-store-fault consumes ['fault'] without routing it to the fence  [key `R7|fnn-control-handle-client|swallow:fnn-store-fault:fault`]
- :269 `fnn-control-handle-client` -- handler clause fnn-store-indeterminate consumes ['indet'] without routing it to the fence  [key `R7|fnn-control-handle-client|swallow:fnn-store-indeterminate:indet`]
- :480 `fnn-control-accept-loop` -- handler clause sb-bsd-sockets:socket-error routes connection-local ['socket'] to the fence (a client/peer event stops the node)  [key `R7|fnn-control-accept-loop|overfence:sb-bsd-sockets:socket-error:socket`]

### host/native/io.lisp (4)
- :1005 `fnn-journal-write` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-journal-write|swallow:error:fault`]
- :1032 `fnn-log-write-item` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-log-write-item|swallow:error:fault`]
- :1144 `fnn-log-line` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-log-line|swallow:error:fault`]
- :3184 `fnn-checkpoint-revision` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-checkpoint-revision|swallow:ignore-errors:fault`]

### host/native/bp-control.lisp (3)
- :112 `fnn-bpnc-handle` -- handler clause fnn-store-fault consumes ['fault'] without routing it to the fence  [key `R7|fnn-bpnc-handle|swallow:fnn-store-fault:fault`]
- :112 `fnn-bpnc-handle` -- handler clause fnn-store-indeterminate consumes ['indet'] without routing it to the fence  [key `R7|fnn-bpnc-handle|swallow:fnn-store-indeterminate:indet`]
- :152 `fnn-bpnc-handle` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-bpnc-handle|swallow:ignore-errors:fault`]

### host/native/heap.lisp (3)
- :66 `fnn-heap-read-small` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-heap-read-small|swallow:error:fault`]
- :214 `fnn-heap-history-observation` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-heap-history-observation|swallow:error:fault`]
- :240 `fnn-heap-history-octets` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-heap-history-octets|swallow:error:fault`]

### host/native/tcpcl.lisp (3)
- :336 `fnn-tcl-source-tick` -- handler clause error consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-tcl-source-tick|swallow:error:fault,indet`]
- :417 `fnn-tcl-act` -- handler clause error consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-tcl-act|swallow:error:fault,indet`]
- :556 `fnn-tcl-session` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-tcl-session|swallow:ignore-errors:fault`]

### host/native/web-host.lisp (3)
- :107 `fnn-web-feed` -- handler clause fnn-store-error consumes ['fault', 'indet'] without routing it to the fence  [key `R7|fnn-web-feed|swallow:fnn-store-error:fault,indet`]
- :135 `fnn-web-close` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-web-close|swallow:ignore-errors:fault`]
- :137 `fnn-web-close` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-web-close|swallow:ignore-errors:fault`]

### host/native/bp-listener-control.lisp (2)
- :52 `fnn-bplc-drive` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-bplc-drive|swallow:error:fault`]
- :66 `fnn-bplc-drive` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-bplc-drive|swallow:error:fault`]

### host/native/bp-service.lisp (2)
- :532 `fnn-bps-send-effect-next` -- handler clause (or fnn-os-error sb-bsd-sockets:socket-error fnn-store-er... consumes ['indet'] without routing it to the fence  [key `R7|fnn-bps-send-effect-next|swallow:(or fnn-os-error sb-bsd-sockets:socket-error fnn-store-er...:indet`]
- :1016 `fnn-bps-publish-generation` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-bps-publish-generation|swallow:ignore-errors:fault`]

### host/native/feed-service.lisp (2)
- :175 `fnn-feed-auth-profile` -- handler clause fnn-store-fault consumes ['fault'] without routing it to the fence  [key `R7|fnn-feed-auth-profile|swallow:fnn-store-fault:fault`]
- :565 `fnn-feed-worker-guarded` -- handler clause fnn-store-error routes connection-local ['refusal'] to the fence (a client/peer event stops the node)  [key `R7|fnn-feed-worker-guarded|overfence:fnn-store-error:refusal`]

### host/native/admin.lisp (1)
- :178 `fnn-owner-refresh-config-cache` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-owner-refresh-config-cache|swallow:error:fault`]

### host/native/bp-node.lisp (1)
- :197 `fnn-bpnode-app-result` -- handler clause fnn-store-indeterminate consumes ['indet'] without routing it to the fence  [key `R7|fnn-bpnode-app-result|swallow:fnn-store-indeterminate:indet`]

### host/native/immutable-publish.lisp (1)
- :115 `fnn-immutable-publish-effect` -- handler clause ignore-errors consumes ['fault'] without routing it to the fence  [key `R7|fnn-immutable-publish-effect|swallow:ignore-errors:fault`]

### host/native/signatures.lisp (1)
- :274 `fnn-hsig-observe-raw` -- handler clause error consumes ['fault'] without routing it to the fence  [key `R7|fnn-hsig-observe-raw|swallow:error:fault`]

## R10: 41 findings (HOST-LIFECYCLE (FAILURE-SCOPE where the close is on a durable path))

### host/native/io.lisp (21)
- :1062 `fnn-log-writer-loop` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-log-writer-loop|ignored-close:fnn-close`]
- :1120 `fnn-log-swap-fd` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-log-swap-fd|ignored-close:fnn-close`]
- :2419 `fnn-initialize` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-initialize|foreign-close:fnn-close`]
- :2458 `fnn-store-close` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-store-close|ignored-close:fnn-close`]
- :2463 `fnn-store-close` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-store-close|foreign-close:fnn-close`]
- :3123 `fnn-record-filesystem-at-init` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-record-filesystem-at-init|foreign-close:fnn-close`]
- :4494 `fnn-publication-unlock` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-publication-unlock|foreign-close:fnn-close`]
- :6713 `fnn-log-recover` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-log-recover|foreign-close:fnn-close`]
- :7082 `fnn-log-open-read-only` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-log-open-read-only|foreign-close:fnn-close`]
- :7286 `fnn-log-discard-spare` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-log-discard-spare|ignored-close:fnn-close`]
- :7320 `fnn-log-prepare-spare` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-log-prepare-spare|ignored-close:fnn-close`]
- :7369 `fnn-log-rotate` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-log-rotate|ignored-close:fnn-close`]
- :7374 `fnn-log-rotate` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-log-rotate|ignored-close:fnn-close`]
- :7389 `fnn-log-rotate` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-log-rotate|foreign-close:fnn-close`]
- :7508 `fnn-log-scan-segments` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-log-scan-segments|foreign-close:fnn-close`]
- :7536 `fnn-log-read-closed-segment` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-log-read-closed-segment|foreign-close:fnn-close`]
- :7565 `fnn-log-read-active-segment` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-log-read-active-segment|foreign-close:fnn-close`]
- :7958 `fnn-log-write-history` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-log-write-history|foreign-close:fnn-close`]
- :8149 `fnn-command-log-scan-store` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-command-log-scan-store|foreign-close:fnn-close`]
- :8177 `fnn-command-log` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-command-log|foreign-close:fnn-close`]
- :8197 `fnn-command-log` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-command-log|foreign-close:fnn-close`]

### host/native/owner.lisp (4)
- :836 `fnn-owner-feed-close` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-owner-feed-close|foreign-close:fnn-close`]
- :887 `fnn-owner-feed-open` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-owner-feed-open|ignored-close:fnn-close`]
- :5838 `fnn-owner-journal-open` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-owner-journal-open|ignored-close:fnn-close`]
- :5889 `fnn-owner-journal-close` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-owner-journal-close|foreign-close:fnn-close`]

### host/native/bp.lisp (2)
- :165 `fnn-bp-sequence-lock` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-bp-sequence-lock|ignored-close:fnn-close`]
- :214 `fnn-bp-reserve-sequence` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-bp-reserve-sequence|foreign-close:fnn-close`]

### host/native/control-transport.lisp (2)
- :57 `fnn-control-acquire-lease` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-control-acquire-lease|ignored-close:fnn-close`]
- :66 `fnn-control-release-lease` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-control-release-lease|ignored-close:fnn-close`]

### host/native/pull-service.lisp (2)
- :141 `fnn-pull-journal-open` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-pull-journal-open|ignored-close:fnn-close`]
- :194 `fnn-catchup-journal-open` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-catchup-journal-open|ignored-close:fnn-close`]

### host/native/tcpcl.lisp (2)
- :244 `fnn-tcl-spool-acquire` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-tcl-spool-acquire|ignored-close:fnn-close`]
- :249 `fnn-tcl-spool-release` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-tcl-spool-release|ignored-close:fnn-close`]

### host/native/workflow.lisp (2)
- :20 `fnn-app-journal-close` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-app-journal-close|ignored-close:fnn-close`]
- :42 `fnn-app-journal-lock` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-app-journal-lock|ignored-close:fnn-close`]

### host/native/auth-admin.lisp (1)
- :537 `fnn-native-auth-admin-execute` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-native-auth-admin-execute|foreign-close:fnn-close`]

### host/native/bp-control.lisp (1)
- :16 `fnn-bpnc-release-lease` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-bpnc-release-lease|foreign-close:fnn-close`]

### host/native/bp-service.lisp (1)
- :105 `fnn-bps-release` -- fnn-close of a descriptor this function did not open and no close row declares  [key `R10|fnn-bps-release|foreign-close:fnn-close`]

### host/native/immutable-publish.lisp (1)
- :111 `fnn-immutable-publish-effect` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-immutable-publish-effect|ignored-close:fnn-close`]

### host/native/operator-live.lisp (1)
- :142 `fnn-operator-execute-run` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-operator-execute-run|ignored-close:fnn-close`]

### host/native/operator.lisp (1)
- :286 `fnn-operator-log-tail` -- fnn-close inside ignore-errors: an ambiguous close is swallowed  [key `R10|fnn-operator-log-tail|ignored-close:fnn-close`]

## What the check cannot see: coverage list for the COMPOSITION host model (books/host-model*.lisp, fn-hm-)

These are defects of this week that the syntactic check does not and cannot flag. Each needs a model
label/schedule (MODEL) or an executed witness (HARNESS: tools/resilience driven by HM labels). The host model
should name, for each one, the label or theorem that covers it.

| Defect | Where | Why the check is blind | Needs |
|---|---|---|---|
| r71 F3 | mux.lisp:635 fnn-mux-step | A valid cold-line prefix in a TLS record is misclassified as a fault. This is a value/protocol predicate (positive progress with no submission), not a lock, lease or handler shape. | MODEL: the continuation vocabulary; a trace witness (DATE / cold ARTICLE / DATE in one TLS record). |
| r71 F11 | mux.lisp:1182 fnn-mux-timers | Busy-poll: the idle timer's FIRE predicate and SCHEDULE predicate differ. Comparing two predicates semantically is outside the check. | MODEL: the timer as an event with one eligibility source (Astra R9-later); the idle half `fn-exp-idle`/`entry-last` too. |
| r71 F13 | mux.lisp:1389 fnn-mux-adopt | Accepted-but-unadmitted sockets have no capacity bound. Admission arithmetic is not syntax. | MODEL: admission capacity as a resource in the HM's H component (reservation before retention). |
| r71 F14 | owner.lisp:4300 cold-result-locked | Unbounded work inside a "bounded" quantum. Cost is not a lock rule. | def-entry `:cost` with a VISIT bound; cost companion theorem (A6). |
| r71 F15 | owner.lisp:2015 prepare-refusal-word | The host decides the outcome mapping. This is a decision-ownership rule, not concurrency. | An ACL2 conversion entry ("ACL2 owns the word"). |
| r71 F16 | owner.lisp:4862 | Unused wrapper and stale comment. | Dead-code tooling (reach/host_callers), not the model. |
| S001 | io.lisp:5714 fnn-accept-observe | accept returns NIL on EAGAIN and NIL is adopted. This is input validation of a runtime return value. (The R4 no-handler finding on the extra accept threads covers only its other half.) | HARNESS: an accept/reset witness; MODEL: an accept label whose result is typed. |
| S010 | TLS + cold page | A pipelined TLS client stops the node when a later line needs an uncached page. Same class as r71 F3. | As r71 F3. |
| S015 | owner.lisp stop-service-locked | "First stop wins" drops a later uncertain outcome, so the exit code is 0. The ordering of two terminal outcomes is semantic. | MODEL: terminal outcome as a lattice (uncertain dominates); a schedule: graceful stop, then failed barrier. |
| S028 | control reply | The reply says REFUSED for an OS error after the owner faulted itself. This is outcome-class agreement across a boundary. (R7 does flag control.lisp:269 swallowing fault/indet; the misreported WORD is not syntax.) | MODEL: outcome classes as Obs (A1); harness check of exit code vs. owner state. |
| r71 F9 / B2 | mux.lisp:1393 | Adopt after the final drain. R8 flags the SHAPE (a push with no lifecycle check). It cannot prove the race present or absent. | HANDOFF protocol (Astra 6.1) plus the forced adopt-before/after-stop schedules. |

Partial coverage worth stating to the model lane:
- R9 accepts every mux-loop wait at the gate (`fnn-owner-gate-enter`). So r71 F7's ":control settlement behind
  a barrier" is caught only through the executor-wait and log-await-sync leaves, not through the gate wait. The
  gate's admission order under an in-flight barrier is a MODEL obligation (fn-ocs-next).
- R2 follows the ACL2 closure path-insensitively. A reached realizer is "may block", not "does block on this
  command/profile". Astra wants native witnesses for the cold routes (r67 F2's OVER route especially).
