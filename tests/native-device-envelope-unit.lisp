; Dependency/registration gate only. The actual initialized whole-trace
; witness is the selected native control-death campaign, still pending.
(in-package "ACL2")
(include-book "../sim/native-device-envelope")
(include-book "native-device-bindings-unit")

; The actual consumer calls this ordered join before reading the logical loan.
; Whole initialized replay remains the separate native campaign obligation.
(assert-event
 (let* ((a *fn2-nde-write-take*)
        (b (update-nth 1 5 a))
        (records '((:submit 1 (17 5 7 :write 100 3 (8 9 10)))
                   (:submit 2 (17 4 7 :write 100 3 (8 9 10))))))
  (and (fn2-nde-submit-join-p b records '(1 2) (list a) :fdatasync)
       (not (fn2-nde-submit-join-p a records '(1 2) (list b) :fdatasync)))))
(assert-event
 (and (fn2-nde-submit-join-p *fn2-nde-write-take* nil nil nil :fdatasync)
      (fn2-nde-submit-join-p *fn2-nde-write-take* nil nil '((:ack 1)) :fdatasync)
      (not (fn2-nde-submit-join-p *fn2-nde-write-take* nil '(1) nil :fdatasync))
      (not (fn2-nde-submit-join-p *fn2-nde-write-take* nil nil '((:ack 1) (:turn 0)) :fdatasync))))
