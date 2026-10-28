(in-package "ACL2")
(include-book "fn2/tests/check-history-unit")
(assert-event
 (mv-let (positive np) (fn2-history-unit-recovery-count *fn2-history-unit-positive* t)
  (mv-let (negative nn) (fn2-history-unit-action-count *fn2-history-unit-negative*)
   (mv-let (recovery nr) (fn2-history-unit-recovery-count *fn2-history-unit-recovery-negative* nil)
    (prog2$
     (cw "HISTORY UNIT baseline positive=~x0/~x1 action-refusals=~x2/~x3 recovery-rejections=~x4/~x5 verdict=~x6~%"
         positive np negative nn recovery nr
         (if (and (= positive np) (= negative nn) (= recovery nr)) :pass :fail))
     (and (< 0 np) (< 0 nn) (< 0 nr) (= positive np) (= negative nn) (= recovery nr)))))))
(good-bye)
