; The cost of the log walk's host entries (landing 2b(a), 2026-10-10): the
; count steps, the cursor, the slice and the descriptor that
; host/native/io.lisp fnn-log-stream-segment calls per entry and per record.
; The cursor (fn-lgb-span) is costed whole; the slice is partial over the
; window copy's fixnum type checks; the descriptor over the trailer
; attachment; the steps over the decision, the trailer and the txid fold.
(in-package "ACL2")
(include-book "image-world")
(include-book "def-cost")
(include-book "store-log-walk-once")

(def-cost fn-lgb-span)
(def-cost fn-lgb-slice-acc :unaccounted (unsigned-byte-p))
(def-cost fn-lgb-slice :unaccounted (expt unsigned-byte-p))
(def-cost fn-lgb-descriptor :unaccounted (fn-arx-attach-trailers-buffer))
(def-cost fn-lgb-next-record
  :unaccounted (mv-nth unsigned-byte-p fn-arx-attach-trailers-buffer))
(def-cost fn-lgw-step-buf-count
  :unaccounted (fn-lgb-decide-count mv-nth fn-lgb-broken fn-lgb-trailer fn-lgb-next-fold-spans))
(def-cost fn-lgw-step-buf-nf-count
  :unaccounted (fn-lgb-decide-count mv-nth fn-lgb-broken fn-lgb-trailer))

(def-cost-check fn-lgb-span)
(def-cost-check fn-lgb-slice-acc)
(def-cost-check fn-lgb-slice)
(def-cost-check fn-lgb-descriptor)
(def-cost-check fn-lgb-next-record)
(def-cost-check fn-lgw-step-buf-count)
(def-cost-check fn-lgw-step-buf-nf-count)
