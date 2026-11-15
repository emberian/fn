; Fixed representation work of the actual guarded publication callbacks.
; Same categories as canonical consume: typed payload bytes, native metadata
; GET/SET and bounded literal spine probes. SUM includes all short-circuit
; alternatives. This is a source binding, not a physical/extraction theorem.
(in-package "ACL2")
(include-book "checkpoint-directory-consume-work")
(fn2-book-layer :c)
(defconst *fn2-live-work-snapshot-owner* 6)
(defconst *fn2-live-work-source-owner* 12)
(defconst *fn2-live-work-manifest-owner* (+ 16 6 3))
(defconst *fn2-live-work-build-owner* (+ 13 6))
(defconst *fn2-live-work-event-owner* (+ 21 6 6))
; BODY-invoked fixed MK shape (10 columns), row and digest workspace.
(defconst *fn2-live-work-mk-ready* (+ 2 (* 2 10) 1 19))
(defconst *fn2-live-work-frontier* (+ 16 6 *fn2-live-work-mk-ready* 16))
(defconst *fn2-live-work-event-roots* (* 2 9))
(defconst *fn2-live-work-event-done*
 (+ 15 *fn2-live-work-event-owner* *fn2-live-work-frontier* *fn2-live-work-event-roots*))
(defconst *fn2-live-work-production-roots* (* 6 7))
(defconst *fn2-live-work-source*
 (+ 40 *fn2-live-work-source-owner* *fn2-live-work-manifest-owner*
    *fn2-live-work-build-owner* *fn2-live-work-event-done*
    *fn2-directory-consume-slot-carried-steps* 21 6 *fn2-live-work-production-roots*))
(defconst *fn2-live-work-catalog* (+ 25 *fn2-live-work-source*))
(defconst *fn2-live-work-exclusive* (+ 8 2))
(defconst *fn2-live-work-readiness-current* (+ 19 7 *fn2-live-work-exclusive*))
(defconst *fn2-live-work-readiness-geometry* (+ 7 7 48))
(defconst *fn2-live-work-readiness-complete*
 (+ 6 *fn2-live-work-readiness-current* *fn2-live-work-readiness-geometry*))
(defconst *fn2-live-work-common*
 (+ *fn2-live-work-catalog* 28 *fn2-live-work-exclusive*
    *fn2-live-work-readiness-complete* *fn2-directory-consume-authority-complete-steps*))
; Two event-root member probes plus end; authority origin/state list probes.
(defconst *fn2-live-work-spines* (+ (* 3 3) (+ 2 1) (+ 4 1)))
; Actual SAME-emitter gate: 42/43 inputs and 2/4 mutable child stores.
(defconst *fn2-checkpoint-live-promotion-steps*
 (+ 99 *fn2-live-work-common* *fn2-live-work-spines* 42 2))
(defconst *fn2-checkpoint-live-reopen-steps*
 (+ 158 *fn2-live-work-common* *fn2-live-work-spines* 43 4))
(assert-event (equal *fn2-live-work-common* 502))
(assert-event (equal *fn2-checkpoint-live-promotion-steps* 662))
(assert-event (equal *fn2-checkpoint-live-reopen-steps* 724))
; Controller ARMWORK and resolved independent/combined work admission are a
; separate composition gate; these constants alone do not establish that gate.
