# W14 native fresh-initializer fidelity

Baseline: native codec commit `37ec36b`; the compared executable model is the
already-reviewed `fn-bsi-current-init-program` from the fresh-initializer
packet (`dd97ade`).  This packet does not merge or restate that model.

`fnn-command-init` calls `fnn-initialize` and then `fnn-acquire`
(`host/native/io.lisp:1176-1182`).  The table records the successful **fresh**
initializer path only.  It is source correspondence evidence, not a K0 claim
or a proof about an existing store.

| Native source operation | Model step and following cut |
| --- | --- |
| `fnn-safe-directory(root, t)`: `mkdir`, `fsync(parent)` | `:mkdir :parent "store" :root`; `init-root-mkdir`; `:fsync-dir :parent`; `init-root-parent-fenced` |
| `fnn-open-lock(..., create=t)`: `open(O_CREAT)` | `:create :root "writer.lock"`; `init-lock-created` |
| `fnn-safe-directory` for `transactions`, `staging`, `config` | the corresponding `:mkdir` and `init-*-mkdir`, then `:fsync-dir :root` and `init-*-parent-fenced` pairs |
| each `fnn-publish-initial-file` for config, history, frontier | `:create`, `:write-all`, `:fsync-file`, `:link`, `:fsync-dir :root`, `:unlink`, each with its `init-config-`, `init-history-`, or `init-frontier-` cut |
| explicit `fnn-fsync-dir(config)` after history | `:fsync-dir :config`; `init-config-history-fenced` |
| final three regular-file barriers and transaction/root/parent directory barriers | the five matching `init-final-*`, `init-transactions-fenced`, `init-root-fenced`, and `init-parent-fenced` cuts |

The native metadata and history bytes come from `fnn-metadata-*-frame` and
`fnn-bridge-config-initial`, which call the ACL2 bridge.  The test seam does
not construct or compare those values.

The normal image has no initializer fault hook.  The bounded implementation
adds `FN_NATIVE_INIT_FAULT`, a developer/test-only environment seam that names
one table cut and selects either `:eio` or `:kill`.  It calls the existing
`fnn-at` only after the named native syscall returns.  `:kill` sends SIGKILL to
the native process, so cleanup handlers do not run; the next command is a
new-process `recover`, not an in-process exception retry.  Targeted tests use
the pre-lock and config-history-directory cuts, and check a normal fresh init
followed by an independent-process restart.  The source-map test checks the
complete label set against the model labels.

`fnn-config-record-names` previously converted any directory-enumeration OS
error to an empty list.  This packet propagates that error.  A separate,
pre-enumeration test control drives the **second** initializer enumeration to
EIO and proves that init faults rather than silently skipping final
configuration-record barriers.  It is not a byte-model cut and is kept out of
the exact model-label set.

Open: `_safe_directory` existing/read-validation branches; existing
`writer.lock`; `EEXIST`/load branches of each initial publication; all
platform crash outcomes after a SIGKILL; and general preservation/recovery K0.
Those paths do not meet this packet's fresh-input precondition and are not
called successful retries here.

The frozen native differential also reported a missing-`staging/` restart
outcome that disagreed with Python.  Current source has `fnn-acquire` call
`fnn-safe-directory(staging)` without `create`, which should fault; this packet
does not relabel that existing/restart divergence as fresh initialization.
It remains a separate source/image reproduction and recovery-policy item.
