(in-package "ACL2")
(include-book "../../books/bp-app-handoff")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpah-local* (cons :dtn '(47 47 114 101 99 101 105 118 101 114 47)))
(defconst *bpah-peer* (cons :dtn '(47 47 115 101 110 100 101 114 47)))
(defconst *bpah-config* (fn-bpn-config *bpah-peer* 3600000 2 32 1048576))
(defconst *bpah-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpah-adu* (fn-bpa-encode
  (fn-bpa-make-request "w" "s" "dtn://sender/" "dtn://receiver/"
                       "p" "i" "c" "t" '(88 13 10))))
(defconst *bpah-bundle*
  (fn-bpn-send-bundle *bpah-config* *bpah-local* *bpah-adu* 7 *bpah-obs*))
(defconst *bpah-ingress*
  (list :cl (cons 1 1) 1 *bpah-peer*
        (fn-record-string-octets "dtn://sender/") 0))
(defconst *bpah-held*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bpah-ingress*)
                 (fn-bpb-bundle-id *bpah-bundle*) 0 *bpah-ingress*
                 nil nil *bpah-bundle* (fn-bpb-encode *bpah-bundle*)
                 nil nil nil '(:dispatch-pending) nil nil 0))
(defconst *bpah-state*
  (fn-bpnf-state (fn-bpn-initial-machine-state *bpah-config* 4 1048576)
                 (list *bpah-held*) nil nil nil nil nil 1 1))

(assert-event (fn-bpnf-heldp *bpah-held*))
(assert-event (equal (fn-bpah-held-class *bpah-held*) :request))
(assert-event (equal (fn-bpah-view-class
                      (fn-bpah-pending-view *bpah-state* *bpah-local*))
                     :request))
(assert-event (null (fn-bpah-pending-view *bpah-state* *bpah-peer*)))
(assert-event (null (fn-bpah-pending-view
                     (fn-bpnf-state (fn-bpnf-base *bpah-state*) nil nil nil
                                    nil nil nil 1 1)
                     *bpah-local*)))
(must-fail
 (assert-event (fn-bpah-local-pendingp *bpah-held* *bpah-peer*)))

; The receipt names the remote work peer, while its return carrier is
; addressed to the local node.  Requiring the receipt peer field to equal
; the return carrier destination would refuse an authorized two-node reply.
(defconst *bpah-receipt-adu*
  (fn-bpa-encode
   (fn-bpa-make-receipt "r" "w" "s" "dtn://receiver/"
                        "dtn://receiver/" "p" "i" "c" "t")))
(defconst *bpah-receipt-view*
  (list :delivery '("principal" "bundle") :receipt *bpah-receipt-adu*
        (list :cl (cons 2 1) 1 *bpah-local*
              (fn-record-string-octets "receiver-peer") 7)
        nil "dtn://receiver/" "dtn://sender/"))
(defconst *bpah-receipt-cfg*
  (fn-cfg-make 7
    (fn-cfg-value-make nil 0 nil nil nil
      (list (fn-cfg-row-make "receiver-peer" "path-identity"
                             "receiver.example.invalid" 0)
            (fn-cfg-row-make "receiver-peer" "auth-principal"
                             "bp-only-no-nntp-principal" 0)
            (fn-cfg-row-make "receiver-peer" "bp-trust" "network" 0)
            (fn-cfg-row-make "receiver-peer" "transport-bp"
                             "dtn://receiver/" 0)) nil)))
(defconst *bpah-request-view*
  (update-nth 4
    (list :cl (cons 1 1) 1 *bpah-peer*
          (fn-record-string-octets "sender-peer") 7)
    (fn-bpah-pending-view *bpah-state* *bpah-local*)))
(defconst *bpah-request-cfg*
  (fn-cfg-make 7
    (fn-cfg-value-make nil 0 nil nil nil
      (list (fn-cfg-row-make "sender-peer" "path-identity"
                             "sender.example.invalid" 0)
            (fn-cfg-row-make "sender-peer" "auth-principal"
                             "bp-only-no-nntp-principal" 0)
            (fn-cfg-row-make "sender-peer" "bp-trust" "network" 0)
            (fn-cfg-row-make "sender-peer" "transport-bp"
                             "dtn://sender/" 0)) nil)))
(assert-event
 (fn-bpah-request-trustedp *bpah-request-view* *bpah-request-cfg*))
(assert-event
 (not (fn-bpah-request-trustedp
       (update-nth 4 (list :cl (cons 1 1) 1 *bpah-peer* nil 0)
                   *bpah-request-view*)
       *bpah-request-cfg*)))
(assert-event
 (not (fn-bpah-request-trustedp
       *bpah-request-view* (fn-cfg-make 8 (fn-cfg-value *bpah-request-cfg*)))))
(assert-event
 (fn-bpah-receipt-trustedp *bpah-receipt-view* *bpah-receipt-cfg*))
(must-fail
 (assert-event
  (fn-bpah-receipt-trustedp
    *bpah-receipt-view* (fn-cfg-make 8 (fn-cfg-value *bpah-receipt-cfg*)))))
(must-fail
 (assert-event
  (fn-bpah-receipt-trustedp
   (update-nth 6 "dtn://other/" *bpah-receipt-view*)
   *bpah-receipt-cfg*)))

; A fragment whose own payload is a well-formed request is still only a
; fragment carrier.  The host-called pending selector must never dispatch it.
(include-book "../../books/bp-fragment")
(defconst *bpah-partial-primary*
  (fn-bpf-fragment-block (fn-bpb-bundle-primary *bpah-bundle*)
                         0 (+ 1 (len *bpah-adu*))))
(defconst *bpah-partial-bundle*
  (fn-bpb-make-bundle *bpah-partial-primary*
                      (fn-bpb-bundle-blocks *bpah-bundle*)
                      (fn-bpb-bundle-payload *bpah-bundle*)))
(defconst *bpah-partial-held*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bpah-ingress*)
                 (fn-bpb-bundle-id *bpah-partial-bundle*) 0 *bpah-ingress*
                 nil nil *bpah-partial-bundle*
                 (fn-bpb-encode *bpah-partial-bundle*)
                 nil nil nil '(:dispatch-pending) nil nil 0))
(defconst *bpah-partial-state*
  (fn-bpnf-state (fn-bpnf-base *bpah-state*)
                 (list *bpah-partial-held*) nil nil nil nil nil 1 1))
(assert-event (fn-bpb-bundlep *bpah-partial-bundle*))
(assert-event (fn-bpnf-heldp *bpah-partial-held*))
(assert-event (equal (fn-bpah-held-class *bpah-partial-held*) :request))
(assert-event (fn-bpp-fragmentp (fn-bpp-flags *bpah-partial-primary*)))
(assert-event (null (fn-bpah-pending-view *bpah-partial-state* *bpah-local*)))
(assert-event
 (not (fn-bpah-request-trustedp
       (fn-bpah-pending-view *bpah-partial-state* *bpah-local*)
       *bpah-request-cfg*)))
(must-fail
 (assert-event (equal (fn-bpah-view-class
                       (fn-bpah-pending-view *bpah-partial-state*
                                              *bpah-local*))
                      :request)))
(must-fail
 (assert-event
  (fn-bpah-request-trustedp
   (fn-bpah-pending-view *bpah-partial-state* *bpah-local*)
   *bpah-request-cfg*)))

; D23: the host's decision line, and a receipt carried by a relay whose
; boundary lists the receiver's EID, judged under the receiver's own
; enrollment.
(assert-event
 (equal (fn-bpah-source-decision-line *bpah-request-view* *bpah-request-cfg*)
        "direct principal=sender-peer"))
(assert-event
 (equal (fn-bpah-source-decision-line
         *bpah-request-view* (fn-cfg-make 8 (fn-cfg-value *bpah-request-cfg*)))
        "refused reason=generation"))
(defconst *bpah-relay-rows*
  (list (fn-cfg-row-make "relay" "path-identity" "relay.example.invalid" 0)
        (fn-cfg-row-make "relay" "auth-principal"
                         "bp-only-no-nntp-principal" 0)
        (fn-cfg-row-make "relay" "bp-trust" "network" 0)
        (fn-cfg-row-make "relay" "transport-bp" "dtn://relay/" 0)))
(defconst *bpah-relay-carries*
  (list (fn-cfg-row-make "relay" "bp-boundary-carries" "dtn://receiver/" 0)))
(defun bpah-cfg-with (rows)
  (fn-cfg-make 7 (fn-cfg-value-make nil 0 nil nil nil
                   (append (fn-cfg-peers (fn-cfg-value *bpah-receipt-cfg*))
                           rows) nil)))
(defconst *bpah-carried-receipt-view*
  (update-nth 4 (list :cl (cons 2 2) 1 *bpah-local*
                      (fn-record-string-octets "relay") 7)
              *bpah-receipt-view*))
(assert-event
 (fn-bpah-receipt-trustedp *bpah-carried-receipt-view*
                           (bpah-cfg-with (append *bpah-relay-rows*
                                                  *bpah-relay-carries*))))
(assert-event
 (equal (fn-bpah-source-decision-line
         *bpah-carried-receipt-view*
         (bpah-cfg-with (append *bpah-relay-rows* *bpah-relay-carries*)))
        "carried carrier=relay author=receiver-peer"))
(must-fail
 (assert-event
  (fn-bpah-receipt-trustedp *bpah-carried-receipt-view*
                            (bpah-cfg-with *bpah-relay-rows*))))
(assert-event
 (equal (fn-bpah-source-decision-line *bpah-carried-receipt-view*
                                      (bpah-cfg-with *bpah-relay-rows*))
        "refused reason=source-not-carried"))
