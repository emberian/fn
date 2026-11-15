; Existing generator decisions: numeric expansion unchanged; byte-based
; taken ranges resolve only through the same child-registry class resolver.
; These are prepared generator controls, not runtime upload TAKE witnesses.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../books/machine-arms")
(assert-event
 (fn2-machine-taken-ranges-p '((:chunk-window :slot c0 :gen g0 :class 1)) '(c0 g0)))
(assert-event
 (fn2-machine-taken-ranges-p '((:chunk-window :slot c0 :gen g0 :class (:bytes 17440))) '(c0 g0)))
(assert-event
 (fn2-machine-taken-ranges-p '((:chunk-window :slot c0 :gen g0 :class (:bytes *fn2-test-window-bytes*))) '(c0 g0)))
(assert-event
 (not (fn2-machine-taken-ranges-p '((:chunk-window :slot c0 :gen g0 :class (:bytes -1))) '(c0 g0))))
(assert-event
 (equal (fn2-machine-taken-reserves '((:chunk-window :slot c0 :gen g0 :class 1)) 0 'test-kind 'installed 'parked)
  '(mv-let (code0 slot0 pgen0 fn2-core)
    (fn2-core-reserve 1 test-kind target gen fn2-core)
    (if (not (eq code0 :ok))
     (let ((fn2-core parked)) (mv :pool *fn2-none* 0 fn2-core)) installed))))
(assert-event
 (equal (fn2-arms-registry-reserves '((:chunk-window :slot c0 :gen g0 :class (:bytes *fn2-test-window-bytes*)))
                                  0 'installed 'refused)
  '(mv-let (code0 slot0 pgen0 fn2-pool)
    (fn2-pool-reserve (fn2-pool-class-for *fn2-test-window-bytes* fn2-pool) kind target gen fn2-pool)
    (if (not (eq code0 :ok)) refused installed))))
; The unsupported core-only path must reject rather than emit a list as a
; runtime class argument. Actual child registries use the resolver above.
(must-fail
 (assert-event
  (fn2-machine-taken-reserves '((:chunk-window :slot c0 :gen g0 :class (:bytes 17440)))
                              0 'test-kind 'installed 'parked)))
