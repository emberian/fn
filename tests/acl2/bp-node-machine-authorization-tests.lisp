; Reachable witnesses and hypothesis teeth for PRF-046.
(in-package "ACL2")
(include-book "../../books/bp-node-machine-authorization")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpna-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpna-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpna-config* (fn-bpn-config *bpna-local* 3600000 2 32 1048576))
(defconst *bpna-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpna-adu* '(104 101 108 108 111))
(defconst *bpna-work* '(119 111 114 107 45 49))
(defconst *bpna-attempt* '(97 116 116 101 109 112 116 45 49))
(defconst *bpna-key* (list *bpna-work* *bpna-attempt* 0))
(defconst *bpna-route*
  (list :route '(49 50 55 46 48 46 48 46 49) 4556
        '(100 116 110 58 47 47 102 110 45 97 47) 10 1024 1048576))
(defconst *bpna-enqueue*
  (list :enqueue *bpna-work* *bpna-attempt* 0 7 *bpna-route*
        *bpna-peer* *bpna-adu* *bpna-obs*))

(defconst *bpna-s0* (fn-bpn-initial-machine-state *bpna-config* 4 1048576))
(defconst *bpna-a0* (fn-bpn-step *bpna-s0* *bpna-enqueue*))
(defconst *bpna-s-pending-queue* (fn-bpn-answer-state *bpna-a0*))
(defconst *bpna-r0* (third (car (fn-bpn-answer-effects *bpna-a0*))))
(defconst *bpna-a1*
  (fn-bpn-step *bpna-s-pending-queue* '(:persist-result 0 :durable)))
(defconst *bpna-s-queued* (fn-bpn-answer-state *bpna-a1*))
(defconst *bpna-a2*
  (fn-bpn-step *bpna-s-queued* (list :contact *bpna-peer* t)))
(defconst *bpna-s-pending-attempt* (fn-bpn-answer-state *bpna-a2*))
(defconst *bpna-r1* (third (car (fn-bpn-answer-effects *bpna-a2*))))
(defconst *bpna-a3*
  (fn-bpn-step *bpna-s-pending-attempt* '(:persist-result 1 :durable)))
(defconst *bpna-s-attempting* (fn-bpn-answer-state *bpna-a3*))
(defconst *bpna-a4*
  (fn-bpn-step *bpna-s-attempting*
               (list :forward-result *bpna-key* :uncertain)))
(defconst *bpna-s-pending-requeue* (fn-bpn-answer-state *bpna-a4*))
(defconst *bpna-r2* (third (car (fn-bpn-answer-effects *bpna-a4*))))
(defconst *bpna-a5*
  (fn-bpn-step *bpna-s-pending-requeue* '(:persist-result 2 :durable)))
(defconst *bpna-s-requeued* (fn-bpn-answer-state *bpna-a5*))

; The non-degenerate path crosses each persistence boundary before the host
; observes queue acceptance, exact-wire send, and transport loss/requeue.
(assert-event (fn-bpn-lifecycle-invariantp *bpna-s0*))
(assert-event (fn-bpn-lifecycle-invariantp *bpna-s-pending-queue*))
(assert-event (fn-bpn-lifecycle-invariantp *bpna-s-queued*))
(assert-event (fn-bpn-lifecycle-invariantp *bpna-s-pending-attempt*))
(assert-event (fn-bpn-lifecycle-invariantp *bpna-s-attempting*))
(assert-event (fn-bpn-lifecycle-invariantp *bpna-s-pending-requeue*))
(assert-event (fn-bpn-lifecycle-invariantp *bpna-s-requeued*))
(assert-event
 (equal (nth 5 (car (fn-bpn-answer-effects *bpna-a1*))) :durable))
(assert-event
 (equal (car (car (fn-bpn-answer-effects *bpna-a3*))) :cl-send))
(assert-event
 (not (fn-bpn-effect-kind-memberp :release
                                  (fn-bpn-answer-effects *bpna-a5*))))
(assert-event
 (not (fn-bpn-effect-kind-memberp :receipt-prepare
                                  (fn-bpn-answer-effects *bpna-a5*))))

; Correct idempotence is separate from new durable acceptance and is grounded
; in the exact already-retained job.
(defconst *bpna-duplicate* (fn-bpn-step *bpna-s-queued* *bpna-enqueue*))
(assert-event
 (equal (nth 5 (car (fn-bpn-answer-effects *bpna-duplicate*))) :duplicate))

; A crash after the durable :attempting record and before a transport result
; requeues the same exact send context.  The theorem subject is fn-bpn-step.
(defconst *bpna-restart-after-lost-send*
  (fn-bpn-step *bpna-s0*
               (list :restart (list *bpna-r0* *bpna-r1*) :ready)))
(defconst *bpna-original-job*
  (fn-bpn-find-job *bpna-key* (fn-bpn-machine-state-jobs *bpna-s-queued*)))
(defconst *bpna-restarted-job*
  (fn-bpn-find-job
   *bpna-key*
   (fn-bpn-machine-state-jobs
    (fn-bpn-answer-state *bpna-restart-after-lost-send*))))

(defthm fn-bpn-reachable-lost-send-restart-keeps-exact-context
  (and (fn-bpn-lifecycle-invariantp
        (fn-bpn-answer-state *bpna-restart-after-lost-send*))
       (equal (fn-bpn-job-status *bpna-restarted-job*) :queued)
       (equal (fn-bpn-job-peer *bpna-restarted-job*)
              (fn-bpn-job-peer *bpna-original-job*))
       (equal (fn-bpn-job-route *bpna-restarted-job*)
              (fn-bpn-job-route *bpna-original-job*))
       (equal (fn-bpn-job-bundle *bpna-restarted-job*)
              (fn-bpn-job-bundle *bpna-original-job*))
       (equal (fn-bpn-job-wire *bpna-restarted-job*)
              (fn-bpn-job-wire *bpna-original-job*))
       (equal (fn-bpn-job-age-anchor *bpna-restarted-job*)
              (fn-bpn-job-age-anchor *bpna-original-job*))
       (equal (fn-bpn-job-sequence *bpna-restarted-job*)
              (fn-bpn-job-sequence *bpna-original-job*))))

; Tooth for the input lifecycle invariant.  This remains a well-formed
; machine state, but token 4097 is beyond the maintained replay namespace.
(defconst *bpna-over-token*
  (fn-bpn-state-with *bpna-s0* nil nil nil nil 4097))
(assert-event (fn-bpn-machine-statep *bpna-over-token*))
(assert-event (not (fn-bpn-lifecycle-invariantp *bpna-over-token*)))
(local
 (must-fail
  (defthm fn-bpn-tooth-step-without-input-invariant
    (fn-bpn-lifecycle-invariantp
     (fn-bpn-answer-state
      (fn-bpn-step *bpna-over-token*
                   (list :contact *bpna-peer* nil)))))))

; Build an applicable 4097-record restart history: queue token 0, then
; alternate attempting and requeued records for the same retained job.
(defun fn-bpn-test-alternating-records (count token attemptingp)
  (declare (xargs :guard t :verify-guards nil :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (if attemptingp
         (list :attempting token *bpna-work* *bpna-attempt* 0)
       (list :requeued token *bpna-work* *bpna-attempt* 0
             :failed :requeued))
     (fn-bpn-test-alternating-records
      (1- count) (1+ token) (not attemptingp)))))

(defconst *bpna-overlong-records*
  (cons *bpna-r0* (fn-bpn-test-alternating-records 4096 1 t)))
(defconst *bpna-overlong-restart-event*
  (list :restart *bpna-overlong-records* :ready))
(assert-event (not (fn-bpn-machine-eventp *bpna-overlong-restart-event*)))
(assert-event
 (not (fn-bpn-lifecycle-invariantp
       (fn-bpn-answer-state
        (fn-bpn-step *bpna-s0* *bpna-overlong-restart-event*)))))
(local
 (must-fail
  (defthm fn-bpn-tooth-step-without-bounded-event
    (fn-bpn-lifecycle-invariantp
     (fn-bpn-answer-state
      (fn-bpn-step *bpna-s0* *bpna-overlong-restart-event*))))))

; A merely typed pending value can pair a queued record with a send.  The old
; machine invariant accepts it; the new relation rejects it, and a durable
; result demonstrates the unauthorized send that the premise prevents.
(defconst *bpna-queue-pending*
  (fn-bpn-machine-state-pending *bpna-s-pending-queue*))
(defconst *bpna-fake-send-pending*
  (fn-bpn-make-pending
   (fn-bpn-pending-token *bpna-queue-pending*)
   (fn-bpn-pending-record *bpna-queue-pending*)
   (list (list :cl-send *bpna-route* *bpna-peer* *bpna-key* '(1 2 3)))
   (fn-bpn-pending-refusal-effect *bpna-queue-pending*)
   (fn-bpn-pending-uncertainty-effect *bpna-queue-pending*)))
(defconst *bpna-fake-send-state*
  (fn-bpn-state-with
   *bpna-s-pending-queue*
   (fn-bpn-machine-state-jobs *bpna-s-pending-queue*)
   (fn-bpn-machine-state-contacts *bpna-s-pending-queue*)
   *bpna-fake-send-pending* nil 0))
(defconst *bpna-fake-send-answer*
  (fn-bpn-step *bpna-fake-send-state* '(:persist-result 0 :durable)))
(assert-event (fn-bpn-machine-invariantp *bpna-fake-send-state*))
(assert-event (not (fn-bpn-lifecycle-invariantp *bpna-fake-send-state*)))
(assert-event
 (fn-bpn-effect-kind-memberp :cl-send
                             (fn-bpn-answer-effects *bpna-fake-send-answer*)))
(local
 (must-fail
  (defthm fn-bpn-tooth-send-without-pending-authorization
    (equal (fn-cbor-ag-car
            (fn-bpn-pending-record *bpna-fake-send-pending*))
           :attempting))))

; The converse mismatch makes an attempting record release a fabricated
; durable queue acknowledgement, separating the acceptance theorem's premise.
(defconst *bpna-attempt-pending*
  (fn-bpn-machine-state-pending *bpna-s-pending-attempt*))
(defconst *bpna-fake-accept-pending*
  (fn-bpn-make-pending
   (fn-bpn-pending-token *bpna-attempt-pending*)
   (fn-bpn-pending-record *bpna-attempt-pending*)
   (list (list :bundle-queue-accepted *bpna-work* *bpna-attempt* 0 7 :durable))
   (fn-bpn-pending-refusal-effect *bpna-attempt-pending*)
   (fn-bpn-pending-uncertainty-effect *bpna-attempt-pending*)))
(defconst *bpna-fake-accept-state*
  (fn-bpn-state-with
   *bpna-s-pending-attempt*
   (fn-bpn-machine-state-jobs *bpna-s-pending-attempt*)
   (fn-bpn-machine-state-contacts *bpna-s-pending-attempt*)
   *bpna-fake-accept-pending* nil 1))
(defconst *bpna-fake-accept-answer*
  (fn-bpn-step *bpna-fake-accept-state* '(:persist-result 1 :durable)))
(assert-event (fn-bpn-machine-invariantp *bpna-fake-accept-state*))
(assert-event (not (fn-bpn-lifecycle-invariantp *bpna-fake-accept-state*)))
(assert-event
 (fn-bpn-effect-kind-memberp
  :bundle-queue-accepted (fn-bpn-answer-effects *bpna-fake-accept-answer*)))
(local
 (must-fail
  (defthm fn-bpn-tooth-acceptance-without-pending-authorization
    (equal (fn-cbor-ag-car
            (fn-bpn-pending-record *bpna-fake-accept-pending*))
           :queued))))
