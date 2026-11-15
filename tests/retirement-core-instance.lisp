; Actual A/B core and commit callbacks, without the simulator, executor,
; checkpoint builders or boot workers. This is a qualification entrypoint;
; it does not supply C's successor publication/replay attachments or run arms.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/machines-all")
(include-book "../books/machine-dispatch")
(include-book "../books/checkpoint-catalog-kind")
(include-book "../books/runs-served")
(include-book "../books/accounts-core")

; Same instance and callback generators, in their existing assembly order.
(fn2-machine-index-events)
(in-theory (disable fn2-machine-local-id))
(fn2-machine-directory-events)
(fn2-core-events)
(fn2-core-init-events)
(fn2-account-events)
(fn2-machine-access-events)
(fn2-machine-row-events :a)
(fn2-machine-row-events :b)
(fn2-machine-admission-events)
(fn2-scribe-events)
(fn2-commit-hook-events)
(fn2-commit-events)
(fn2-commit-events-1t)

; The actual persisted dispatcher is generated directly from the same
; checkpoint adapter used by production's final callback section. Its guards
; still require publish phase, installed containing batch, deps/log/fence,
; exact member/workspace/envelope, and ordinary intent before retirement.
(fn2-checkpoint-retirement-install-events)
