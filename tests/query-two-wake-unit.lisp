; Actual core composition: cancellation/DONE must not overwrite an ordinary
; wake already posted for a different live row. This is a seam fixture, not
; a claim that an NNTP transaction reaches a particular cancellation branch.
(in-package "ACL2")
(include-book "../books/executor")
(include-book "query-reference-unit")

(defun fn2-qtw-queues (owner sibling principal fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-sched (fn2-core-sched fn2-core))) (view)
  (list (fn2-sched-in-queue owner fn2-sched) (fn2-sched-in-queue sibling fn2-sched)
        (fn2-sched-countsi principal fn2-sched) (fn2-sched-headsi principal fn2-sched)
        (fn2-sched-tailsi principal fn2-sched) (fn2-sched-next owner fn2-sched)
        (fn2-sched-prev sibling fn2-sched)) view))

(defun fn2-qtw-trace (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-trace (fn2-core-trace fn2-core))) (view)
  (let ((n (fn2-trace-count fn2-trace)))
   (list n (fn2-trace-lost fn2-trace)
     (if (< 0 n) (fn2-trace-kind 0 fn2-trace) 0)
     (if (< 0 n) (fn2-trace-machine 0 fn2-trace) 0)
     (if (< 0 n) (fn2-trace-principal 0 fn2-trace) 0))) view))

; Fill a one-row diagnostic ring using a completed real query, then pop
; its actual enqueue. The next query must still schedule when its trace
; record overwrites this already retained record and increments LOST.
(defun fn2-qtw-prime (done slot gen owner generation principal fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv started fn2-core)
       (fn2-identity-decide-start 0 slot gen 0 1 slot gen 1
        *fn2-cns-kind* owner generation fn2-core))
      ((mv ended fn2-core)
       (if done (fn2-qru-drive 64 0 fn2-core) (fn2-successor-release 0 fn2-core)))
      ((mv popped id fn2-core) (fn2-exec-pop principal fn2-core)))
   (mv (and (eq started :ok) (equal ended (if done :stored :ok))
            (eq popped :ok) (equal id owner)) fn2-core)))

(defun fn2-qtw-body (done capacity same fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((profile (put-assoc-equal :trace-capacity capacity
                (put-assoc-equal :trace t
                 (put-assoc-equal :t 4 (put-assoc-equal :cns 2
                  (put-assoc-equal :pool-classes '((16 . 4096)) *fn2-profile-tiny*))))))
      (supported (fn2-core-profilep profile))
      (fn2-core (fn2-core-init profile fn2-core))
      ((mv c0 owner generation fn2-core)
       (fn2-machine-take-fn2-cns *fn2-none* *fn2-none* 0 1 0 0 4 *fn2-none* 0 fn2-core))
      ((mv c1 sibling & fn2-core)
       (fn2-machine-take-fn2-cns *fn2-none* *fn2-none* 0 2 0 0 4 *fn2-none* 0 fn2-core))
      ((unless (and supported (eq c0 :ok) (eq c1 :ok))) (mv nil fn2-core))
      (principal (fn2-machine-principal-slot owner fn2-core))
      (slot (fn2-cns-row-ws-slot owner fn2-core))
      (gen (fn2-cns-row-ws-gen owner fn2-core))
      ((mv filled fn2-core) (fn2-qru-fill 33 7 slot gen 0 *fn2-cns-kind* owner fn2-core))
      ((mv primed fn2-core)
       (if (equal capacity 1)
           (fn2-qtw-prime done slot gen owner generation principal fn2-core)
         (mv t fn2-core)))
      ((mv started fn2-core)
       (fn2-identity-decide-start 0 slot gen 0 1 slot gen 1
        *fn2-cns-kind* owner generation fn2-core))
      (empty (fn2-qtw-queues owner sibling principal fn2-core))
      ; Use the existing callback handoff, not a fabricated directory write.
      (intended (if same owner sibling))
      (fn2-core (fn2-machine-wake-row intended fn2-core))
      ((mv result fn2-core)
       (if done (fn2-qru-drive 64 0 fn2-core) (fn2-successor-release 0 fn2-core)))
      (middle (fn2-qtw-queues owner sibling principal fn2-core))
      (ordinary (fn2-machine-wake-id fn2-core))
      (trace (fn2-qtw-trace fn2-core))
      ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
      ; The ordinary intent still enters through the actual executor seam.
      (fn2-core (fn2-exec-wake wake fn2-core))
      (both (fn2-qtw-queues owner sibling principal fn2-core))
      (fn2-core (fn2-core-scheduler-wake owner fn2-core))
      (once (fn2-qtw-queues owner sibling principal fn2-core))
      (qstate (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core))) (state)
               (list (fn2-id-decides-qmask 0 fn2-id-decides)
                     (fn2-id-decides-qwake 0 fn2-id-decides)) state)))
  (mv (and (eq filled :ok) primed (eq started :ok)
           (equal principal (fn2-machine-principal-slot sibling fn2-core))
           (equal (take 3 empty) '(0 0 0))
           (equal result (if done :stored :ok))
           (equal middle (list 1 0 1 owner owner *fn2-none* *fn2-none*))
           (equal ordinary intended) (equal wake intended)
           (equal both (if same (list 1 0 1 owner owner *fn2-none* *fn2-none*)
                         (list 1 1 2 owner sibling sibling owner)))
           (equal once both) (equal qstate '(0 0))
           (equal (fn2-qru-count slot fn2-core) 0)
           (equal trace (list 1 (if (equal capacity 1) 1 0)
                              *fn2-trace-kind-enqueue* owner principal))
           (not (fn2-core-stopped-p fn2-core))) fn2-core)))

(defun fn2-qtw-result (done capacity same)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core) (fn2-qtw-body done capacity same fn2-core) answer)))

; Both distinct and identical ordinary/query wake owners enter through the
; actual composition. An identical owner stays one FIFO entry after the
; ordinary handoff is consumed. The full ring changes evidence loss only.
(assert-event
 (and (fn2-qtw-result nil 8 nil) (fn2-qtw-result t 8 nil)
      (fn2-qtw-result nil 1 nil) (fn2-qtw-result t 1 nil)
      (fn2-qtw-result nil 8 t) (fn2-qtw-result t 8 t)
      (fn2-qtw-result nil 1 t) (fn2-qtw-result t 1 t)))
