; Live registration of the B-owned future working leases.
(in-package "ACL2")
(include-book "checkpoint-future-working")
(include-book "core-children")
(fn2-book-layer :b)

(defcorechild fn2-core-checkpoint-future fn2-checkpoint-future
 :init (fn2-checkpoint-future-init 1 fn2-checkpoint-future) :profilep t
 :why "The master-owned future working bundle is admitted before the held C cut.")

(defcorechild fn2-core-checkpoint-future-windows fn2-checkpoint-future-windows
 :init (fn2-checkpoint-future-windows-init *fn2-checkpoint-future-window-count* fn2-checkpoint-future-windows) :profilep t
 :why "One staging, four reusable journal and three anchor leases retain exact borrower generations.")
