; Exact sole live configuration accessor, factored from owner-host.
(in-package "ACL2")
(include-book "owner-state-accessors")
(include-book "owner-config-selector")
(include-book "config")
(defun fn-owner-config (fn-owner-st)
  ; The one live configuration.  No host global shadows this value: every
  ; caller reads the generation replayed into and published by fn-ocfg.
  (declare (xargs :stobjs (fn-owner-st) :guard (fn-owner-boundp fn-owner-st)))
  (fn-ocfg-config (fn-owner-ocfg fn-owner-st)))
