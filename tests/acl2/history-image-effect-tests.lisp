(in-package "ACL2")
(include-book "../../books/history-image-effect-boundary")
; Exact signed syscall observations: complete, short, error and stale-plan.
; Full current funded-controller positive fixture belongs to the joined
; writer trajectory and is not replaced by a fabricated grant here.
(assert-event
 (and (equal (fn-hie-outcome 16384 16384 :ok) :ok)
      (equal (fn-hie-outcome 16384 16383 :ok) :uncertain)
      (equal (fn-hie-outcome 32 -1 :error) :uncertain)
      (equal (fn-hie-outcome 32 32 :error) :uncertain)))
(assert-event
 (and (equal (fn-hie-plan nil nil 7 nil) '(:refused :image-effect))
      (equal (fn-hie-read-count nil nil 7 nil 64 :ok) 0)
      (equal (fn-hie-observation nil nil 7 nil 16384 :ok nil)
             '(:refused :image-effect))))
