; Literal actual producer and typed recovery witnesses.
(in-package "ACL2")
(include-book "../../books/bp-handoff-producer-shape")
(include-book "../../books/bp-node-rotation")

(defconst *fn-bphsp-local* (cons :dtn '(47 47 108 111 99 97 108 47)))
(defconst *fn-bphsp-sender* (cons :dtn '(47 47 115 101 110 100 101 114 47)))
(defconst *fn-bphsp-config*
  (fn-bpn-config *fn-bphsp-sender* 3600000 2 32 1048576))
(defconst *fn-bphsp-bundle*
  (fn-bpn-send-bundle *fn-bphsp-config* *fn-bphsp-local*
    (fn-bpa-encode
     (fn-bpa-make-request "w" "s" "dtn://sender/" "dtn://local/"
                          "p" "i" "c" "t" '(88 13 10)))
    8 (fn-clock-observation 1000 0 0 nil)))
(defconst *fn-bphsp-ingress*
  (list :cl (cons 0 1) 1 *fn-bphsp-sender* '(115 101 110 100 101 114) 0))
(defconst *fn-bphsp-held*
  (fn-bpnf-held (fn-bpnf-ingress-principal *fn-bphsp-ingress*)
    (fn-bpb-bundle-id *fn-bphsp-bundle*) 0 *fn-bphsp-ingress*
    nil nil *fn-bphsp-bundle* (fn-bpb-encode *fn-bphsp-bundle*)
    nil nil nil '(:dispatch-pending) nil nil 0))
(defconst *fn-bphsp-record*
  (fn-bpah-delivery-record 0 1 0
    (fn-bpp-primary-identity (fn-bpb-bundle-primary *fn-bphsp-bundle*))
    :request-accepted '(114 101 99 101 105 112 116)))

(assert-event
 (mv-let (ok updated handoff)
     (fn-bpah-apply-delivery *fn-bphsp-record* (list *fn-bphsp-held*))
   (declare (ignore updated))
   (and ok (fn-bphs-held-sourcesp (list *fn-bphsp-held*))
        (fn-bpah-delivery-recordp *fn-bphsp-record*)
        (fn-bpah-delivery-matches-heldp *fn-bphsp-record* *fn-bphsp-held*)
        (consp handoff)
        (fn-bphs-handoffp handoff))))

; Direct positive anchor retains the actual producer's returned value, so
; a constantly false grammar cannot satisfy this fixture.
(defconst *fn-bphsp-produced-handoff*
  (mv-let (ok updated handoff)
      (fn-bpah-apply-delivery *fn-bphsp-record* (list *fn-bphsp-held*))
    (declare (ignore ok updated))
    handoff))
(assert-event
 (and (consp *fn-bphsp-produced-handoff*)
      (fn-bphs-handoffp *fn-bphsp-produced-handoff*)
      (fn-bphs-handoffs-p (list *fn-bphsp-produced-handoff*))))

; Malformed data is distinct from a healthy producer trajectory.
(assert-event
 (and (not (fn-bphs-handoffp :bpck-unknown-symbol-witness))
      (not (fn-bphs-handoffs-p '(:bpck-unknown-symbol-witness)))))

; Healthy producer -> CK7 -> actual recovery remains accepted. Complete
; recovery guard premises and installed handoff are checked explicitly.
(assert-event
 (mv-let (ok updated handoff)
     (fn-bpah-apply-delivery *fn-bphsp-record* (list *fn-bphsp-held*))
   (declare (ignore updated))
   (let* ((base (fn-bpn-initial-machine-state *fn-bphsp-config* 4 1048576))
          (st (fn-bpnf-state base nil nil nil nil nil nil 0 0))
          (ck (fn-bpnr-checkpoint 1 nil (list handoff) nil 0 0))
          (event (append
                   (fn-bpnr-recover-auto-event st nil :ready nil (list :selected ck))
                   '((:initialize))))
          (direct (fn-bpnf-recover-fnbs-step st (nth 1 event) (nth 2 event)
                    (nth 3 event) (nth 4 event)))
          (answer (fn-bpnp-step st event)))
     (and ok (fn-bphs-held-sourcesp (list *fn-bphsp-held*))
          (fn-bpah-delivery-recordp *fn-bphsp-record*)
          (fn-bphs-handoffp handoff) (fn-bpnr-checkpointp ck)
          (fn-bpn-machine-statep base)
          (fn-bpnp-session-listp (fn-bpnp-sessions st))
          (true-listp (fn-bpnf-held-list st))
          (fn-bpnp-host-eventp event)
          (equal (car (car (fn-bpnf-answer-effects direct))) :restart-ready)
          (fn-bphs-handoffs-p (fn-bpnf-handoffs (fn-bpnf-answer-state direct)))
          (equal (fn-bpnf-answer-effects answer) '((:restart-ready 0)))
          (equal (fn-bpnf-handoffs (fn-bpnf-answer-state answer)) (list handoff))))))
