; A5r: the served core on a configured listener, for H's Node backend and
; the nntp natives (layer doc 4.1.4). Started as `tools/acl2 < fn2/tests/native-serve.lsp`
; with FN2_LISTENER_PORT (and optionally FN2_LISTENER_ADDRESS, a dotted quad;
; default 127.0.0.1) in the environment, which set the served profile's
; :listener-port / :listener-address; FN2_LISTENER_PATH sets :listener-path,
; the owner-only Unix socket beside it. Prints fn1's ready line
; `LISTENING <port>` once bound (port 0 reports the kernel's ephemeral port),
; serving the simulator session's profile and seeded store (sim-session.lsp:
; reading over local.test with three articles and local.empty),
; then `LISTENING-LOCAL <path>` when the Unix socket is bound,
; serves until SIGTERM or SIGINT (the sticky signal stops the core), then
; prints `STOPPED <reason>` and exits 0; a refused configuration exits 2 with
; `REFUSED <word>`. FN2_ENVELOPE_TRACE=N records a boundary trace of N
; entries and checks ENVELOPE's legality (item 1) at stop: `ENVELOPE <verdict>`.
(in-package "ACL2")
(include-book "fn2/sim/check-envelope")
(ld "fn2/tests/sim-session.lsp")
; ENVELOPE's replay of the session from the same seeded store
(defun fn2-nserve-replay (trace profile seeds)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (verdict caps fn2-core)
      (let ((fn2-core (fn2-init-executor profile :echo nil fn2-core)))
        (mv-let (code fn2-core) (fn2-cs-seed-all seeds 1 fn2-core)
          (declare (ignore code))
          (fn2-env-steps trace 0 nil nil nil fn2-core)))
      (list verdict caps))))
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
:q
(load "fn2/host/ffi.lisp")
(load "fn2/host/adapter.lisp")
(load "fn2/host/native-serve-raw.lisp")
(sb-ext:exit :code (fn2-nserve-main))
