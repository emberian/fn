; Teeth for bp-node-progress-premises: a reachable state with a live session
; and a held row keeps the served step's guard premises through a host
; step, and each hypothesis of fn-bpnp-step-preserves-guard-premises has a
; concrete case where dropping it breaks the conclusion.
(in-package "ACL2")
(include-book "../../books/bp-node-progress-premises")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpsp-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpsp-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpsp-dest* (cons :dtn '(47 47 98 112 45 100 101 115 116 47)))
(defconst *bpsp-config* (fn-bpn-config *bpsp-local* 3600000 2 32 1048576))
(defconst *bpsp-sender-config*
  (fn-bpn-config *bpsp-sender* 3600000 2 32 1048576))
(defconst *bpsp-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bpsp-ingress*
  (list :cl (cons 0 1) 1 *bpsp-sender* '(115 101 110 100 101 114) 0))
(defconst *bpsp-bundle*
  (fn-bpn-send-bundle *bpsp-sender-config* *bpsp-dest*
                      (make-list 64 :initial-element 66)
                      8 *bpsp-observation*))
(defconst *bpsp-wire* (fn-bpb-encode *bpsp-bundle*))

; Open: the cold initial state recovered by the host's boot event.
(defconst *bpsp-raw* (fn-bpnf-initial-state *bpsp-config* 8 1048576))
(defconst *bpsp-boot-event*
  (fn-bpnf-family-recover-auto-event *bpsp-raw* nil :ready nil))
(defconst *bpsp-s0*
  (fn-bpnf-answer-state (fn-bpnp-step *bpsp-raw* *bpsp-boot-event*)))

; One durable receive installs a held row through the served step.
(defconst *bpsp-receive-event*
  (fn-bpnf-receive-wire-event-value
   (fn-bpnf-receive-wire-event
    *bpsp-config* *bpsp-wire* *bpsp-observation* *bpsp-ingress*)))
(defconst *bpsp-proposed* (fn-bpnp-step *bpsp-s0* *bpsp-receive-event*))
(defconst *bpsp-persist* (car (fn-bpnf-answer-effects *bpsp-proposed*)))
(defconst *bpsp-persist-event*
  (list :persist-result (fn-bpn-nth 1 *bpsp-persist*)
        (fn-bpn-nth 2 *bpsp-persist*) :durable))
(defconst *bpsp-s1*
  (fn-bpnf-answer-state
   (fn-bpnp-step (fn-bpnf-answer-state *bpsp-proposed*) *bpsp-persist-event*)))

; A session to the destination opens through the served step.
(defconst *bpsp-session* (cons 1 1))
;; The routed session (spec 4.6): the host opens an outbound session only to
;; the boundary the route table names, and a :session without VIA offers
;; nothing.  This fixture's table sends dtn://bp-dest/ to the boundary "relay".
(defconst *bpsp-via*
  (list :via "relay" (fn-record-string-octets "dtn://relay/")
        (list (fn-bprt-route 100 "dtn://bp-dest/" "relay" "dtn://relay/" 4556))))
(defconst *bpsp-session-event*
  (list :session *bpsp-dest* *bpsp-session* t 32768 *bpsp-observation* *bpsp-via*))
(defconst *bpsp-s2*
  (fn-bpnf-answer-state (fn-bpnp-step *bpsp-s1* *bpsp-session-event*)))

(assert-event
 (and (fn-bpnp-host-eventp *bpsp-boot-event*)
      (fn-bpnp-host-eventp *bpsp-receive-event*)
      (fn-bpnp-host-eventp *bpsp-persist-event*)
      (fn-bpnp-host-eventp *bpsp-session-event*)
      (fn-bpnp-step-guard-premisesp *bpsp-s0*)
      (fn-bpnp-step-guard-premisesp *bpsp-s1*)
      (equal (len (fn-bpnf-held-list *bpsp-s2*)) 1)
      (equal (fn-bpnp-sessions *bpsp-s2*)
             (list (fn-bpnp-session *bpsp-dest* *bpsp-session* 32768)))))

; Reachable witness: the progress event proposes a transit dispatch of the
; held row.  Premises hold before and after, and the step did work.
(defconst *bpsp-routes* (list (list *bpsp-dest* *bpsp-dest*)))
(defconst *bpsp-progress-event*
  (list :progress *bpsp-local* *bpsp-observation* *bpsp-routes* 1))
; The dispatch frame digest is an attachment, so the step runs in make-event.
(make-event
 `(defconst *bpsp-s3-answer*
    ',(fn-bpnp-step *bpsp-s2* *bpsp-progress-event*)))
(defconst *bpsp-s3* (fn-bpnf-answer-state *bpsp-s3-answer*))
(assert-event
 (and (fn-bpnp-step-guard-premisesp *bpsp-s2*)
      (fn-bpnp-host-eventp *bpsp-progress-event*)
      (fn-bpnp-step-guard-premisesp *bpsp-s3*)
      (equal (car (car (fn-bpnf-answer-effects *bpsp-s3-answer*)))
             :persist-dispatch)
      (equal (fn-bpn-nth 3 (fn-bpnf-issued *bpsp-s3*)) :dispatch)
      (equal (fn-bpnp-sessions *bpsp-s3*) (fn-bpnp-sessions *bpsp-s2*))
      (equal (len (fn-bpnf-held-list *bpsp-s3*)) 1)))

; Hypothesis (fn-bpnp-host-eventp event).  A :session event whose MRU is 0
; is not a host event; logically stepped, it installs a malformed session
; row, so the premises fail afterwards.
(defconst *bpsp-bad-session-event*
  (list :session *bpsp-dest* *bpsp-session* t 0 *bpsp-observation* *bpsp-via*))
(make-event
 `(defconst *bpsp-bad-event-after*
    ',(with-guard-checking
       :none
       (fn-bpnf-answer-state (fn-bpnp-step *bpsp-s2* *bpsp-bad-session-event*)))))
(assert-event
 (and (fn-bpnp-step-guard-premisesp *bpsp-s2*)
      (not (fn-bpnp-host-eventp *bpsp-bad-session-event*))
      (not (fn-bpnp-session-listp (fn-bpnp-sessions *bpsp-bad-event-after*)))
      (not (fn-bpnp-step-guard-premisesp *bpsp-bad-event-after*))))
(must-fail
 (assert-event (fn-bpnp-step-guard-premisesp *bpsp-bad-event-after*)))

; Hypothesis (fn-bpnp-step-guard-premisesp st), one case per conjunct.  The
; host event is the reachable progress event above.
(defconst *bpsp-bad-sessions*
  (fn-bpnp-with-runtime
   *bpsp-s2*
   (cons (fn-bpnp-session *bpsp-dest* *bpsp-session* 0)
         (fn-bpnp-sessions *bpsp-s2*))
   (fn-bpnp-pending-image *bpsp-s2*)))
(defconst *bpsp-bad-held*
  (update-nth 2 (cons (car (fn-bpnf-held-list *bpsp-s2*)) :tail) *bpsp-s2*))
(defconst *bpsp-bad-base*
  (update-nth 1 (update-nth 6 (1+ *fn-bpn-machine-max-records*)
                            (fn-bpnf-base *bpsp-s2*))
              *bpsp-s2*))

(make-event
 `(defconst *bpsp-bad-sessions-after*
    ',(with-guard-checking
       :none
       (fn-bpnf-answer-state (fn-bpnp-step *bpsp-bad-sessions* *bpsp-progress-event*)))))
(assert-event
 (and (fn-bpnp-host-eventp *bpsp-progress-event*)
      (not (fn-bpnp-session-listp (fn-bpnp-sessions *bpsp-bad-sessions*)))
      (fn-bpn-machine-invariantp (fn-bpnf-base *bpsp-bad-sessions*))
      (true-listp (fn-bpnf-held-list *bpsp-bad-sessions*))
      (not (fn-bpnp-step-guard-premisesp *bpsp-bad-sessions*))
      (not (fn-bpnp-step-guard-premisesp *bpsp-bad-sessions-after*))))
(must-fail
 (assert-event (fn-bpnp-step-guard-premisesp *bpsp-bad-sessions-after*)))

(make-event
 `(defconst *bpsp-bad-held-after*
    ',(with-guard-checking
       :none
       (fn-bpnf-answer-state (fn-bpnp-step *bpsp-bad-held* *bpsp-progress-event*)))))
(assert-event
 (and (fn-bpnp-host-eventp *bpsp-progress-event*)
      (not (true-listp (fn-bpnf-held-list *bpsp-bad-held*)))
      (fn-bpn-machine-invariantp (fn-bpnf-base *bpsp-bad-held*))
      (fn-bpnp-session-listp (fn-bpnp-sessions *bpsp-bad-held*))
      (not (fn-bpnp-step-guard-premisesp *bpsp-bad-held*))
      (not (fn-bpnp-step-guard-premisesp *bpsp-bad-held-after*))))
(must-fail
 (assert-event (fn-bpnp-step-guard-premisesp *bpsp-bad-held-after*)))

(make-event
 `(defconst *bpsp-bad-base-after*
    ',(with-guard-checking
       :none
       (fn-bpnf-answer-state (fn-bpnp-step *bpsp-bad-base* *bpsp-progress-event*)))))
(assert-event
 (and (fn-bpnp-host-eventp *bpsp-progress-event*)
      (not (fn-bpn-machine-invariantp (fn-bpnf-base *bpsp-bad-base*)))
      (true-listp (fn-bpnf-held-list *bpsp-bad-base*))
      (fn-bpnp-session-listp (fn-bpnp-sessions *bpsp-bad-base*))
      (not (fn-bpnp-step-guard-premisesp *bpsp-bad-base*))
      (not (fn-bpnp-step-guard-premisesp *bpsp-bad-base-after*))))
(must-fail
 (assert-event (fn-bpnp-step-guard-premisesp *bpsp-bad-base-after*)))
