; Cap refusal is tested before an intentionally observable mutation body.
(in-package "ACL2")
(include-book "../books/executor")
(include-book "../sim/check-work")

(defun fn2-work-control-refusal (bytes steps descriptors fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((id 0))
    (fn2-machine-with-work bytes steps descriptors
      (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-observation* fn2-core)))
        (fn2-machine-result 0 1 0 nil fn2-core)))))
(defun fn2-work-control-case (bytes steps descriptors fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (phase (fn2-machine-phase 0 fn2-core))
       ((mv b s d runnable fn2-core)
        (fn2-work-control-refusal bytes steps descriptors fn2-core)))
    (mv (and (equal (list b s d runnable) '(0 1 0 t))
             (equal phase (fn2-machine-phase 0 fn2-core))
             (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*)
             (equal (fn2-exec-queued fn2-core) 0)) fn2-core)))
(defun fn2-work-cap-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
   (mv-let (ok fn2-core)
     (b* (((mv b fn2-core) (fn2-work-control-case 4097 1 0 fn2-core))
          ((mv s fn2-core) (fn2-work-control-case 0 33 0 fn2-core))
          ((mv d fn2-core) (fn2-work-control-case 0 1 5 fn2-core))
          ((mv used-bytes used-steps used-descriptors runnable fn2-core)
           (fn2-work-control-refusal 4096 32 4 fn2-core)))
       (mv (and b s d
                (equal (list used-bytes used-steps used-descriptors runnable) '(0 1 0 nil))
                (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-machine-observation*))
           fn2-core))
     ok)))
(assert-event (fn2-work-cap-control))

; Exact boundary of the unchanged H*24 + K*4129 turn allowance. The real
; concrete loop must yield before issuing a listener descriptor at exhaustion.
(assert-event
 (and (fn2-turn-work-room-p 4 8 0 0 0)
      (fn2-turn-work-room-p 4 8 0 28999 0)
      (not (fn2-turn-work-room-p 4 8 0 29000 0))))
(defun fn2-work-turn-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
   (mv-let (ok fn2-core)
     (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
          (fn2-core (fn2-exec-set-turn-bytes 29000 fn2-core))
          ((mv status obs visits actions fn2-core)
           (fn2-concrete-loop 12 4 8 8 0 0 0 fn2-core)))
       (mv (and (eq status :more) (= obs 0) (= visits 0) (= actions 0)
                (= (fn2-exec-queued fn2-core) 0)
                (= (fn2-exec-turn-bytes fn2-core) 29000)
                (fn2-exec-runnable-p fn2-core)) fn2-core))
     ok)))
(assert-event (fn2-work-turn-control))
(value-triple (cw "R5b WORK CONTROLS: caps/yield, visible bytes/descriptors/observations, turn allowance PASS~%"))

; Per-record caps alone used to admit this over-budget combined turn.
(assert-event
 (let ((h '(0 0 0 0 4096 24 0 0 4294967295 0 0 0 0 0 0 0 0 0 0))
       (r '(1 0 0 0 4096 32 0 0 4294967295 0 0 0 0 0 0 0 0 0 0)))
   (equal (fn2-check-work (list h h h h r r r r r r r r)
                          0 4 8 0 *fn2-profile-tiny*)
          '(:fail :turn-work-cost))))
