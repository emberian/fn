; Reachable witnesses and teeth for the host-called outbound lifecycle step.
(in-package "ACL2")
(include-book "../../books/bp-node-machine-codec")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

(defconst *bpnm-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpnm-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpnm-config* (fn-bpn-config *bpnm-local* 3600000 2 32 1048576))
(defconst *bpnm-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnm-adu* '(104 101 108 108 111))
(defconst *bpnm-work* '(119 111 114 107 45 49))
(defconst *bpnm-attempt* '(97 116 116 101 109 112 116 45 49))
(defconst *bpnm-route*
  (list :route '(49 50 55 46 48 46 48 46 49) 4556
        '(100 116 110 58 47 47 102 110 45 97 47) 10 1024 1048576))

(assert-event (fn-bpn-configp *bpnm-config*))
(assert-event (fn-bpn-routep *bpnm-route*))

(defconst *bpnm-s0* (fn-bpn-initial-machine-state *bpnm-config* 4 1048576))
(defconst *bpnm-enqueue*
  (list :enqueue *bpnm-work* *bpnm-attempt* 0 7 *bpnm-route*
        *bpnm-peer* *bpnm-adu* *bpnm-obs*))
(defconst *bpnm-a0* (fn-bpn-step *bpnm-s0* *bpnm-enqueue*))

; Queue acceptance is withheld until the queued record is durable.
(assert-event (equal (car (car (fn-bpn-answer-effects *bpnm-a0*))) :persist))
(assert-event (not (fn-bpn-effect-kind-memberp
                    :bundle-queue-accepted (fn-bpn-answer-effects *bpnm-a0*))))
(defconst *bpnm-r0* (third (car (fn-bpn-answer-effects *bpnm-a0*))))
(assert-event (fn-bpn-lifecycle-recordp *bpnm-r0*))
(assert-event (equal (fn-bpn-lifecycle-record-unframe
                      (fn-bpn-lifecycle-record-frame *bpnm-r0*))
                     *bpnm-r0*))

; The publication operation is authorized only for the exact token and record
; currently pending in the host-called machine state.  Lock ownership and a
; physically absent canonical next name are explicit premises.
(defconst *bpnm-publication-operation*
  (fn-bpn-lifecycle-publication-authorize
   (fn-bpn-answer-state *bpnm-a0*) 0 *bpnm-r0* t t))
(assert-event
 (fn-bpn-lifecycle-publication-operationp *bpnm-publication-operation*))
(assert-event
 (equal (fn-bpn-lifecycle-publication-operation-token
         *bpnm-publication-operation*)
        0))
(assert-event
 (equal (fn-bpn-lifecycle-publication-operation-record
         *bpnm-publication-operation*)
        *bpnm-r0*))
(assert-event
 (equal (fn-bpn-lifecycle-publication-operation-publication
         *bpnm-publication-operation*)
        (fn-jpub-initial t)))
(assert-event
 (not (fn-bpn-lifecycle-publication-operationp
       (fn-bpn-lifecycle-publication-authorize
        (fn-bpn-answer-state *bpnm-a0*) 0 *bpnm-r0* nil t))))
(assert-event
 (not (fn-bpn-lifecycle-publication-operationp
       (fn-bpn-lifecycle-publication-authorize
        (fn-bpn-answer-state *bpnm-a0*) 0 *bpnm-r0* t nil))))
(must-fail
 (assert-event
  (fn-bpn-lifecycle-publication-operationp
   (fn-bpn-lifecycle-publication-authorize
    (fn-bpn-answer-state *bpnm-a0*) 0 *bpnm-r0* t nil))))

(defconst *bpnm-a1*
  (fn-bpn-step (fn-bpn-answer-state *bpnm-a0*) '(:persist-result 0 :durable)))
(defconst *bpnm-s1* (fn-bpn-answer-state *bpnm-a1*))
(assert-event (fn-bpn-effect-kind-memberp
               :bundle-queue-accepted (fn-bpn-answer-effects *bpnm-a1*)))

; Lifecycle filenames use the Store transaction decimal codec, and recovery
; accepts only a contiguous ACL2-generated namespace.  Hidden stages remain
; bounded, explicit evidence rather than silently disappearing from the plan.
(defconst *bpnm-name0* "00000000000000000000.fnb")
(defconst *bpnm-name1* "00000000000000000001.fnb")
(defconst *bpnm-name2* "00000000000000000002.fnb")
(assert-event (equal (fn-bpn-lifecycle-record-name 0) *bpnm-name0*))
(defconst *bpnm-namespace-plan*
  (fn-bpn-lifecycle-namespace-plan
   (list ".interrupted-stage" *bpnm-name0* *bpnm-name1*)))
(assert-event (fn-bpn-lifecycle-namespace-planp *bpnm-namespace-plan*))
(assert-event
 (equal (fn-bpn-lifecycle-plan-record-names *bpnm-namespace-plan*)
        (list *bpnm-name0* *bpnm-name1*)))
(assert-event
 (equal (fn-bpn-lifecycle-plan-hidden-stages *bpnm-namespace-plan*)
        '(".interrupted-stage")))
(assert-event
 (equal (fn-bpn-lifecycle-plan-next-token *bpnm-namespace-plan*) 2))

; A corrupt spelling and a gap are rejected before any frame is read.
(assert-event
 (equal (car (fn-bpn-lifecycle-namespace-plan
              '("00000000000000000000.fnB")))
        :fault))
(assert-event
 (equal (car (fn-bpn-lifecycle-namespace-plan
              (list *bpnm-name0* *bpnm-name2*)))
        :fault))
(must-fail
 (assert-event
  (fn-bpn-lifecycle-namespace-planp
   (fn-bpn-lifecycle-namespace-plan
    (list *bpnm-name0* *bpnm-name2*)))))

; Exact duplicate means the same durable object binding.  Contrary route or
; bytes under the same work/attempt/generation key is a refusal.
(assert-event (fn-bpn-effect-kind-memberp
               :bundle-queue-accepted
               (fn-bpn-answer-effects (fn-bpn-step *bpnm-s1* *bpnm-enqueue*))))
(defconst *bpnm-conflict*
  (list :enqueue *bpnm-work* *bpnm-attempt* 0 7
        (list :route '(108 111 99 97 108 104 111 115 116) 4557
              '(100 116 110 58 47 47 102 110 45 97 47) 10 1024 1048576)
        *bpnm-peer* *bpnm-adu* *bpnm-obs*))
(assert-event (fn-bpn-effect-kind-memberp
               :bundle-queue-refused
               (fn-bpn-answer-effects (fn-bpn-step *bpnm-s1* *bpnm-conflict*))))

; An imprecise wall reading cannot expire this retained bundle: expiry follows
; the monotonic Bundle Age anchor.  A sufficiently later monotonic reading
; persists :expired while keeping the exact wire bytes in the job record.
(defconst *bpnm-untrusted-wall* (fn-clock-observation 1001 999999999 999999999 t))
(assert-event
 (null (fn-bpn-answer-effects
        (fn-bpn-step *bpnm-s1* (list :clock *bpnm-untrusted-wall*)))))
(defconst *bpnm-expired-obs* (fn-clock-observation 4000002 0 0 nil))
(defconst *bpnm-expiring*
  (fn-bpn-step *bpnm-s1* (list :clock *bpnm-expired-obs*)))
(assert-event (equal (car (third (car (fn-bpn-answer-effects *bpnm-expiring*))))
                     :expired))
(defconst *bpnm-expired*
  (fn-bpn-step (fn-bpn-answer-state *bpnm-expiring*)
               '(:persist-result 1 :durable)))
(defconst *bpnm-expired-job*
  (fn-bpn-find-job (list *bpnm-work* *bpnm-attempt* 0)
                   (fn-bpn-machine-state-jobs
                    (fn-bpn-answer-state *bpnm-expired*))))
(assert-event (equal (fn-bpn-job-status *bpnm-expired-job*) :expired))
(assert-event
 (equal (fn-bpn-job-wire *bpnm-expired-job*)
        (fn-bpn-job-wire
         (fn-bpn-find-job (list *bpnm-work* *bpnm-attempt* 0)
                          (fn-bpn-machine-state-jobs *bpnm-s1*)))))

; Contact alone proposes a durable attempting record; only its completed
; barrier produces the exact-wire convergence-layer send effect.
(defconst *bpnm-a2* (fn-bpn-step *bpnm-s1* (list :contact *bpnm-peer* t)))
(defconst *bpnm-r1* (third (car (fn-bpn-answer-effects *bpnm-a2*))))
(assert-event (equal (car *bpnm-r1*) :attempting))
(assert-event
 (not (fn-bpn-lifecycle-publication-operationp
       (fn-bpn-lifecycle-publication-authorize
        (fn-bpn-answer-state *bpnm-a0*) 0 *bpnm-r1* t t))))

; Decoded record tokens must agree with their canonical observed filenames.
; Swapping the token-1 record under the token-0 name is a reachable namespace
; corruption witness, not merely a malformed-frame case.
(defconst *bpnm-lifecycle-recovery*
  (fn-bpn-lifecycle-recovery
   (list ".interrupted-stage" *bpnm-name0* *bpnm-name1*)
   (list *bpnm-r0* *bpnm-r1*)))
(assert-event (equal (car *bpnm-lifecycle-recovery*) :ready))
(assert-event
 (equal (fn-bpn-lifecycle-recovery-stages *bpnm-lifecycle-recovery*)
        '(".interrupted-stage")))
(assert-event
 (equal (car (fn-bpn-lifecycle-recovery
              (list *bpnm-name0*) (list *bpnm-r1*)))
        :fault))
(must-fail
 (assert-event
  (equal (car (fn-bpn-lifecycle-recovery
               (list *bpnm-name0*) (list *bpnm-r1*)))
         :ready)))
(assert-event (not (fn-bpn-effect-kind-memberp
                    :cl-send (fn-bpn-answer-effects *bpnm-a2*))))
(defconst *bpnm-a3*
  (fn-bpn-step (fn-bpn-answer-state *bpnm-a2*) '(:persist-result 1 :durable)))
(assert-event (fn-bpn-effect-kind-memberp :cl-send
                                           (fn-bpn-answer-effects *bpnm-a3*)))
(assert-event
 (equal (fifth (car (fn-bpn-answer-effects *bpnm-a3*)))
        (fn-bpn-job-wire
         (fn-bpn-find-job (list *bpnm-work* *bpnm-attempt* 0)
                          (fn-bpn-machine-state-jobs *bpnm-s1*)))))

; An outage is a transport observation.  It first persists :requeued and the
; job remains retained; it never becomes an archive/application receipt.
(defconst *bpnm-a4*
  (fn-bpn-step (fn-bpn-answer-state *bpnm-a3*)
               (list :forward-result (list *bpnm-work* *bpnm-attempt* 0)
                     :uncertain)))
(defconst *bpnm-r2* (third (car (fn-bpn-answer-effects *bpnm-a4*))))
(assert-event (equal (car *bpnm-r2*) :requeued))
(defconst *bpnm-a5*
  (fn-bpn-step (fn-bpn-answer-state *bpnm-a4*) '(:persist-result 2 :durable)))
(assert-event
 (equal (fn-bpn-job-status
         (fn-bpn-find-job (list *bpnm-work* *bpnm-attempt* 0)
                          (fn-bpn-machine-state-jobs
                           (fn-bpn-answer-state *bpnm-a5*))))
        :queued))
(assert-event (not (fn-bpn-effect-kind-memberp
                    :release (fn-bpn-answer-effects *bpnm-a5*))))

; Restart of the prefix cut after :attempting requeues the exact same peer,
; route and wire.  This is the crash boundary the native service exercises.
(defconst *bpnm-restart*
  (fn-bpn-step *bpnm-s0* (list :restart (list *bpnm-r0* *bpnm-r1*) :ready)))
(defconst *bpnm-restarted-job*
  (fn-bpn-find-job (list *bpnm-work* *bpnm-attempt* 0)
                   (fn-bpn-machine-state-jobs
                    (fn-bpn-answer-state *bpnm-restart*))))
(assert-event
 (fn-bpn-lifecycle-recovery-agrees-with-statep
  *bpnm-lifecycle-recovery* (fn-bpn-answer-state *bpnm-restart*)))
(assert-event (equal (fn-bpn-job-status *bpnm-restarted-job*) :queued))
(assert-event (equal (fn-bpn-job-route *bpnm-restarted-job*) *bpnm-route*))
(assert-event
 (equal (fn-bpn-job-wire *bpnm-restarted-job*)
        (fn-bpn-job-wire
         (fn-bpn-find-job (list *bpnm-work* *bpnm-attempt* 0)
                          (fn-bpn-machine-state-jobs *bpnm-s1*)))))

(defthm fn-bpn-reachable-restart-keeps-exact-send-context
  (and (equal (fn-bpn-job-status *bpnm-restarted-job*) :queued)
       (equal (fn-bpn-job-route *bpnm-restarted-job*) *bpnm-route*)
       (equal (fn-bpn-job-wire *bpnm-restarted-job*)
              (fn-bpn-job-wire
               (fn-bpn-find-job (list *bpnm-work* *bpnm-attempt* 0)
                                (fn-bpn-machine-state-jobs *bpnm-s1*))))))

; A write whose completion is ambiguous fences mutation until replay.
(defconst *bpnm-uncertain*
  (fn-bpn-step (fn-bpn-answer-state *bpnm-a0*)
               '(:persist-result 0 :uncertain)))
(assert-event (equal (fn-bpn-machine-state-fenced
                      (fn-bpn-answer-state *bpnm-uncertain*)) t))
(assert-event
 (null (fn-bpn-answer-effects
        (fn-bpn-step (fn-bpn-answer-state *bpnm-uncertain*)
                     (list :contact *bpnm-peer* t)))))

; Missing sequence recovery fences lifecycle replay before any queued job can
; be resumed, even if the lifecycle records themselves are intact.
(defconst *bpnm-sequence-fault*
  (fn-bpn-step *bpnm-s0* (list :restart (list *bpnm-r0*) :fault)))
(assert-event (equal (fn-bpn-machine-state-fenced
                      (fn-bpn-answer-state *bpnm-sequence-fault*)) t))

; Tooth for fn-bpn-step-emits-no-release's effect-list hypothesis: the
; separating value contains an actual :release effect and is not an accepted
; machine effect list.
(assert-event (not (fn-bpn-effect-listp '((:release work-1)))))
(must-fail
 (assert-event
  (not (fn-bpn-effect-kind-memberp :release '((:release work-1))))))

; Namespace capacity remains owned by the called fn-bpn-propose path.  A
; machine recovered at the record frontier refuses without emitting :persist.
(defconst *bpnm-full-state*
  (fn-bpn-state-with *bpnm-s0* nil nil nil nil
                     *fn-bpn-machine-max-records*))
(defconst *bpnm-full-answer*
  (fn-bpn-step *bpnm-full-state* *bpnm-enqueue*))
(assert-event
 (fn-bpn-effect-kind-memberp
  :bundle-queue-refused (fn-bpn-answer-effects *bpnm-full-answer*)))
(assert-event
 (not (fn-bpn-effect-kind-memberp
       :persist (fn-bpn-answer-effects *bpnm-full-answer*))))
