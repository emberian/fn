; The cost rows of the host lease's dispatched entries
; (books/runtime-contract-host-lease.lisp; tools/cost_obligations.py reads them):
; each entry's visit twin derived from its executed body, partial over the
; callees named :unaccounted.  No :visits bound is declared: the claim is
; `derived'.
(in-package "ACL2")
(include-book "image-world")
(include-book "def-cost")
(include-book "runtime-contract-host-lease")

(def-cost fn-hld-init
  :unaccounted (fn-hl-rtc-config fn-rtc-st-cfg-okp fn-hll-x-init true-list-fix fn-hld-fuel fn-hld-settle mv-nth))

(def-cost fn-hld-begin
  :unaccounted (expt fn-rtc-inc-roomp fn-rtc-kind-out-p fn-rtc-s-inc fn-rtc-kind-op fn-hll-x-step* true-list-fix fn-hld-fuel fn-hld-settle mv-nth fn-rtc-x-slots-exhaustedp))

(def-cost fn-hld-workspace
  :unaccounted (fn-rtc-nbufs))

(def-cost fn-hld-window-base
  :unaccounted (fn-rtc-buf-base))

(def-cost fn-hld-quantum
  :unaccounted (fn-rtc-nbufs fn-rtc-x-live-p fn-rtc-kind-out-p fn-rtc-buf-cap fn-hld-copy fn-rtc-x-request mv-nth))

(def-cost fn-hld-sent
  :unaccounted (fn-rtc-outcomep fn-hll-x-step* mv-nth true-list-fix fn-hld-fuel fn-hld-settle))

(def-cost fn-hld-end
  :unaccounted (fn-rtc-x-request mv-nth true-list-fix fn-hld-fuel fn-hld-settle))
