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
                             "dtn://receiver/" 0)) nil nil nil nil)))
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
                             "dtn://sender/" 0)) nil nil nil nil)))
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
                           rows) nil nil nil nil)))
(defconst *bpah-carried-receipt-view*
  (update-nth 4 (list :cl (cons 2 2) 1 *bpah-local*
                      (fn-record-string-octets "relay") 7)
              *bpah-receipt-view*))
;; D23 second half: carrying the receiver's EID is not release authority.
;; The relay carries dtn://receiver/ but does not release for it: its
;; receipt is not trusted.  With a releases-for row it is.
(must-fail
 (assert-event
  (fn-bpah-receipt-trustedp *bpah-carried-receipt-view*
                            (bpah-cfg-with (append *bpah-relay-rows*
                                                   *bpah-relay-carries*)))))
(defconst *bpah-relay-releases*
  (list (fn-cfg-row-make "relay" "bp-boundary-releases-for"
                         "dtn://receiver/" 0)))
(assert-event
 (fn-bpah-receipt-trustedp *bpah-carried-receipt-view*
                           (bpah-cfg-with (append *bpah-relay-rows*
                                                  *bpah-relay-carries*
                                                  *bpah-relay-releases*))))
; The release list alone suffices for the receipt gate; the carried list
; alone does not.
(assert-event
 (fn-bpah-receipt-trustedp *bpah-carried-receipt-view*
                           (bpah-cfg-with (append *bpah-relay-rows*
                                                  *bpah-relay-releases*))))
(assert-event
 (equal (fn-bpah-release-line
         *bpah-carried-receipt-view*
         (bpah-cfg-with (append *bpah-relay-rows* *bpah-relay-carries*)))
        "carried-not-released carrier=relay issuer=dtn://receiver/"))
(assert-event
 (equal (fn-bpah-release-line
         *bpah-carried-receipt-view*
         (bpah-cfg-with (append *bpah-relay-rows* *bpah-relay-carries*
                                *bpah-relay-releases*)))
        "listed-issuer carrier=relay issuer=dtn://receiver/"))
(assert-event
 (equal (fn-bpah-release-line *bpah-carried-receipt-view*
                              (bpah-cfg-with *bpah-relay-rows*))
        "issuer-not-released carrier=relay issuer=dtn://receiver/"))
(assert-event
 (equal (fn-bpah-release-line *bpah-receipt-view* *bpah-receipt-cfg*)
        "self-issued carrier=receiver-peer issuer=dtn://receiver/"))
; fn-bpah-unauthorized-issuer-never-authorizes-receipt: teeth -- with the
; release row the issuer is authorized and the receipt is trusted, so the
; conclusion fails without the hypothesis.
(must-fail
 (assert-event
  (not (fn-bpah-receipt-trustedp
        *bpah-carried-receipt-view*
        (bpah-cfg-with (append *bpah-relay-rows* *bpah-relay-releases*))))))
; Author publication: the receiver's own enrollment, not the relay's.
(assert-event
 (fn-bpah-author-publication-authorizedp
  (bpah-cfg-with *bpah-relay-rows*)
  (fn-bpaj-principal-id (fn-record-string-octets "receiver-peer")) 7
  (fn-bpaj-source-eid "dtn://receiver/")))
(assert-event
 (not (fn-bpah-author-publication-authorizedp
       (bpah-cfg-with (append *bpah-relay-rows* *bpah-relay-carries*))
       (fn-bpaj-principal-id (fn-record-string-octets "relay")) 7
       (fn-bpaj-source-eid "dtn://receiver/"))))
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

; D23 durable provenance.  A delivered receipt's held row: its kind-5
; ingress (received from the relay at generation 7), its bundle's source
; (claimed dtn://receiver/), and its kind-7 marker carrying ACL2's release
; verdict.  Each fact has its own accessor.
(defconst *bpah-receipt-bundle*
  (fn-bpn-send-bundle *bpah-config* *bpah-local* *bpah-receipt-adu* 9
                      *bpah-obs*))
(defconst *bpah-relay-ingress*
  (list :cl (cons 2 2) 1 *bpah-local* (fn-record-string-octets "relay") 7))
(defun bpah-delivered-receipt (verdict status)
  (fn-bpnf-held (fn-record-string-octets "relay")
                (fn-bpb-bundle-id *bpah-receipt-bundle*) 0
                *bpah-relay-ingress* nil nil *bpah-receipt-bundle*
                (fn-bpb-encode *bpah-receipt-bundle*)
                nil
                (list :delivered status (fn-bpah-release-detail verdict))
                nil '(:dispatch-done) nil nil 0))
(defconst *bpah-listed* (bpah-delivered-receipt :listed-issuer
                                                :receipt-accepted))
(defconst *bpah-unreleased*
  (bpah-delivered-receipt :carried-not-released :receipt-refused))
(assert-event
 (equal (fn-bpah-held-received-from *bpah-listed*)
        (list :received-from
              (fn-bpaj-principal-id (fn-record-string-octets "relay"))
              (fn-bpaj-eid-text *bpah-local*) 7)))
(assert-event
 (equal (fn-bpah-held-claimed-source *bpah-listed*)
        (fn-bpaj-source-eid "dtn://sender/")))
(assert-event (equal (fn-bpah-held-verdict *bpah-listed*) :listed-issuer))
(assert-event (equal (fn-bpah-held-verdict *bpah-unreleased*)
                     :carried-not-released))
(assert-event
 (equal (fn-bpah-held-policy-row *bpah-listed*)
        (fn-cfg-row-make "relay" "bp-boundary-releases-for"
                         "dtn://sender/" 0)))
(assert-event (null (fn-bpah-held-policy-row *bpah-unreleased*)))
; Every verdict name decodes back to its verdict.
(assert-event
 (equal (fn-bpah-release-verdict-of-name "obligation-mismatch"
                                         *fn-bpah-release-verdicts*)
        :obligation-mismatch))
(defun bpah-all-round-trip (vs)
  (if (consp vs)
      (and (equal (fn-bpah-release-verdict-of-name
                   (fn-bpah-release-verdict-name (car vs))
                   *fn-bpah-release-verdicts*)
                  (car vs))
           (bpah-all-round-trip (cdr vs)))
    t))
(assert-event (bpah-all-round-trip *fn-bpah-release-verdicts*))
; The detail is a valid kind-7 detail (non-empty, at most 256 octets).
(assert-event (<= (len (fn-bpah-release-detail :obligation-mismatch)) 256))

;; PRF-136: fn-bpah-local-pendingp-has-a-nonfragment-header.  Witness: the
;; pending request carrier is local-pending and its header is a non-fragment
;; block.  Without the hypothesis: the held fragment carrier is heldp and its
;; header is a fragment's, so the conclusion fails (and the definition
;; refuses it, which the executable body now reads from the header alone).
(assert-event
 (and (fn-bpah-local-pendingp *bpah-held* *bpah-local*)
      (fn-bpnf-held-nonfragment-headerp *bpah-held*)))
(assert-event
 (and (fn-bpnf-heldp *bpah-partial-held*)
      (not (fn-bpah-local-pendingp *bpah-partial-held* *bpah-local*))
      (not (fn-bpnf-held-nonfragment-headerp *bpah-partial-held*))))
