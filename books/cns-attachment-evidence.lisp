; Actual served CNS selected tuple; no logical equality to constrained stubs.
(in-package "ACL2")
(include-book "assembly-attach")
(include-book "attachment-validation")
(defconst *fn2-av-cns-pairs*
 '((fn2-cns-run-stub . fn2-cns-run)
   (fn2-machine-observe-fn2-cns-stub . fn2-machine-observe-fn2-cns)
   (fn2-cns-arm-charge-ok-p-stub . fn2-cns-arm-charge-ok-p)
   (fn2-cns-arm-bound-stub . fn2-cns-arm-bound)))
(assert-event (fn2-av-packet *fn2-av-cns-pairs* (w state)))
; These caller obligations are derived from actual admitted logical bodies,
; preserving branch conditions and lambda bindings. No authored domain list.
(make-event (value (fn2-av-caller-event 'fn2-machine-run *fn2-av-cns-pairs*
                   'fn2-cns-selected-run-caller-domain (w state))))
(make-event (value (fn2-av-caller-event 'fn2-machine-observe-route-fn2-cns *fn2-av-cns-pairs*
                   'fn2-cns-selected-observe-caller-domain (w state))))
(make-event (value (fn2-av-caller-event 'fn2-machine-arm-charge-ok-p *fn2-av-cns-pairs*
                   'fn2-cns-selected-charge-caller-domain (w state))))
(make-event (value (fn2-av-caller-event 'fn2-machine-arm-bound *fn2-av-cns-pairs*
                   'fn2-cns-selected-bound-caller-domain (w state))))
