; The cost rows of the pool OVER's dispatched entries
; (books/over-render-plan.lisp; tools/cost_obligations.py reads them):
; each entry's visit twin derived from its executed body, partial over the
; callees named :unaccounted. No :visits bound is declared: the claim is
; `derived'.
(in-package "ACL2")
(include-book "def-cost")
(include-book "over-render-plan")

(def-cost fn-ovr-lease-quantum
  :unaccounted (fn-rtc-nbufs fn-rtc-x-live-p fn-rtc-kind-out-p fn-rtc-buf-cap fn-ovr-quantum fn-rtc-x-request mv-nth))

(def-cost fn-ovr-plan-cursor
  :unaccounted (fn-ovr-rest-cursor))

(def-cost fn-ovr-plan-next
  :unaccounted (fn-ovr-rest-cursor fn-ovr-rest-next))
