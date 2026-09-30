; Source-only negative receive fixture. Local durable authority input remains
; private even when the transport channel has an admitted network principal.
(in-package "ACL2")
(include-book "bp-session-admission-tests")
(include-book "../../books/consumer-authority-codec")
(include-book "../../books/bp-node-progress-guards")
(include-book "../../books/codec-attach")
(defconst *bpca-event* '(:consumer-authority 0 1 0 (:authority-begin (65) 0 1 7)))
(defconst *bpca-bytes* (fn-cac-encode *bpca-event*))
(defconst *bpca-local* (cons :dtn (fn-record-string-octets "//local/")))
(defconst *bpca-config* (fn-bpn-config *bpat-eid* 3600000 2 32 1048576))
(defconst *bpca-clock* (fn-clock-observation 1000 0 0 nil))
(defconst *bpca-ingress*
  (list :cl '(0 . 1) 1 *bpat-eid*
        (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal *bpat-cfg* *bpat-channel* *bpat-eid*)) 7))
(defconst *bpca-bundle*
  (fn-bpn-send-bundle *bpca-config* *bpca-local* *bpca-bytes* 7 *bpca-clock*))
(defconst *bpca-held*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bpca-ingress*)
               (fn-bpb-bundle-id *bpca-bundle*) 0 *bpca-ingress* nil nil
               *bpca-bundle* (fn-bpb-encode *bpca-bundle*)
               nil '(:dispatch-pending) nil nil nil nil 0))
(assert-event
 (and (fn-cac-eventp *bpca-event*)
      (equal (fn-cac-decode-exact *bpca-bytes*) (list :ok *bpca-event*))
      (fn-cfgp *bpat-cfg*)
      (equal (fn-bpaj-session-principal *bpat-cfg* *bpat-channel* *bpat-eid*)
             (list :admitted (fn-record-string-octets "peer") 7))
      (fn-bpnf-cl-ingressp *bpca-ingress*)
      (fn-bpnf-heldp *bpca-held*)
      (equal (fn-bpah-held-class *bpca-held*) :local-authority-private)
      (equal (fn-bpnp-local-class *bpca-held*) :local-authority-private)
      (not (member-equal (fn-bpnp-local-class *bpca-held*) '(:request :receipt)))))
(defconst *bpca-raw*
 (fn-bpnf-initial-state (fn-bpn-config *bpca-local* 3600000 2 32 1048576) 8 1048576))
(defconst *bpca-boot*
 (fn-bpnf-family-recover-auto-event *bpca-raw* nil :ready nil))
(make-event `(defconst *bpca-s0*
 ',(fn-bpnf-answer-state (fn-bpnp-step *bpca-raw* *bpca-boot*))))
(defconst *bpca-receive*
 (fn-bpnf-receive-wire-event-value
  (fn-bpnf-receive-wire-event
   (fn-bpn-config *bpca-local* 3600000 2 32 1048576)
   (fn-bpb-encode *bpca-bundle*) *bpca-clock* *bpca-ingress*)))
(make-event `(defconst *bpca-proposed* ',(fn-bpnp-step *bpca-s0* *bpca-receive*)))
(make-event `(defconst *bpca-settle*
 ',(let ((effect (car (fn-bpnf-answer-effects *bpca-proposed*))))
    (list :persist-result (fn-bpn-nth 1 effect) (fn-bpn-nth 2 effect) :durable))))
(make-event `(defconst *bpca-s1*
 ',(fn-bpnf-answer-state (fn-bpnp-step (fn-bpnf-answer-state *bpca-proposed*) *bpca-settle*))))
(defconst *bpca-progress* (list :progress *bpca-local* *bpca-clock* nil 7))
(make-event `(defconst *bpca-disposition* ',(fn-bpnp-step *bpca-s1* *bpca-progress*)))
(assert-event
 (and (fn-bpn-machine-statep (fn-bpnf-base *bpca-s1*))
      (fn-bpnp-session-listp (fn-bpnp-sessions *bpca-s1*))
      (true-listp (fn-bpnf-held-list *bpca-s1*))
      (fn-bpnp-host-eventp *bpca-progress*)
      (equal (len (fn-bpnf-held-list *bpca-s1*)) 1)
      (equal (fn-bpnp-local-class (car (fn-bpnf-held-list *bpca-s1*))) :local-authority-private)
      (equal (fn-bpnf-answer-effects *bpca-disposition*)
       (list (list :progress-unsupported (fn-bpnp-wait-key (car (fn-bpnf-held-list *bpca-s1*))))))))
