; From worktree root; command and PID-file discipline are in the LD file.
(in-package "ACL2")
(set-gag-mode :goals)
(set-inhibit-output-lst '(proof-tree prove))
(include-book "fn2/books/crash-model")
(include-book "fn2/sim/storage")
(include-book "fn2/sim/prng")
(include-book "fn2/tests/crash-model-differential")
; Session-only compiled evaluation, following sim-layer-a-a4-driver.lsp.
; No book bypasses admission or installs a trust tag.
:q
(handler-case
    (progn
      (assert (fn2-diff-negative-teeth))
      (assert (fn2-diff-live-tear-regression))
      (assert (fn2-diff-stale-cache-regression))
      (assert (fn2-diff-storage-controls))
      (assert (time (fn2-diff-run)))
      (assert (time (fn2-diff-benchmark64)))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "B1 DIFFERENTIAL FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
