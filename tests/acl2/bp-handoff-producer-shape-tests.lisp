; Literal actual producer and typed recovery witnesses.
(in-package "ACL2")
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
