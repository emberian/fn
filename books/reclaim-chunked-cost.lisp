; The cost of the reclaim pass's accumulator entries (the reclaim carry,
; 2026-10-10): the fresh stobj fn-rcwacc that host/native/owner.lisp
; fnn-owner-reclaim-pass creates for passes 2 and 3, its init, the per-chunk
; canonical and prediction steps, and the finish.
(in-package "ACL2")
(include-book "image-world")
(include-book "def-cost")
(include-book "reclaim-chunked-seal")
; Each wrapper is costed partial over the value function it stores
; (books/reclaim-chunked-walk.lisp, reclaim-chunked-seal.lisp: the R4
; equations make the stobj run that value fold); the creator is costed whole.

(def-cost create-fn-rcwacc)
(def-cost fn-rcwacc-init :unaccounted (fn-rcw-acc-init))
(def-cost fn-rcwacc-canon-step :unaccounted (fn-rcw-canon-acc-step))
(def-cost fn-rcwacc-predict-step :unaccounted (fn-rcw-predict-acc-step))
(def-cost fn-rcwacc-finish :unaccounted (fn-rcw-acc-finish))

(def-cost-check create-fn-rcwacc)
(def-cost-check fn-rcwacc-init)
(def-cost-check fn-rcwacc-canon-step)
(def-cost-check fn-rcwacc-predict-step)
(def-cost-check fn-rcwacc-finish)
