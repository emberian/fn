; Run after qualifying the current CNS contract/unit/counterexample closure:
;   FN_ACL2=... tools/acl2 --timeout 240 < tests/cns-draining-controls.lsp
; The raw adversary is ephemeral and restores every changed definition.
(in-package "ACL2")
(include-book "tests/cns-draining-count-counterexample")
(set-guard-checking nil)
:q
(handler-case
    (progn
      (load "tests/cns-draining-shared-control.lsp")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "CNS-INDEPENDENT FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
