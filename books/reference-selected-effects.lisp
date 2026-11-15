; Operationally selected machine callback with explicit semantic FIFO effects.
; The source seal states which dispatcher program is modeled. It never
; equates constrained machine stubs to their executable attachments.
(in-package "ACL2")
(include-book "reference-selected-dispatcher")
(include-book "reference-effect-timer-leaves")

(fn2-reference-effect-lower fn2-selected-machine-run
 :shape-leaves ((fn2-corep . fn2-ref-effect-corep-shape)
                (fn2-core-wfp . fn2-ref-effect-core-wfp-shape)
                (fn2-cns-wait-expired-p . fn2-ref-effect-cns-wait-expired-p-shape)
                (fn2-tls-expired-p . fn2-ref-effect-tls-expired-p-shape))
 :frame-leaves ((fn2-core-record-enqueue . fn2-ref-effect-record-enqueue-frame)
                (fn2-cns-arm-wait-timer . fn2-ref-effect-cns-arm-wait-timer-frame)
                (fn2-cns-clear-wait-timer . fn2-ref-effect-cns-clear-wait-timer-frame)
                (fn2-tls-arm-timer . fn2-ref-effect-tls-arm-timer-frame)
                (fn2-tls-clear-timer . fn2-ref-effect-tls-clear-timer-frame)))

; Recheck AFTER constructing the effectful program. Guard/body/ABI or
; attachment drift is a source failure, never a new proof assumption.
(fn2-reference-selected-check fn2-selected-machine-run-binding)
