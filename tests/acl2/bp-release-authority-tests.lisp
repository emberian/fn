; D23 release authority: witnesses and teeth for books/bp-release-authority.
; Home node A (dtn://home/) holds work-1 for the receiver B (dtn://receiver/),
; whose receipts arrive either directly from B's boundary ("receiver-peer")
; or through the relay boundary "relay".
(in-package "ACL2")
(include-book "../../books/bp-release-authority")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The held obligation: an outstanding, pinned, delivered work-1.
(defconst *bra-groups* '("fn.letters"))
(defconst *bra-node*
  (fn-node-complete
   (fn-node-prepare (fn-node-initial-state *bra-groups* 16) 9
                    "<bra@example.invalid>" '(72 105 13 10) *bra-groups*
                    "archive-bra" "subject-bra" "operator-release" 4 841000000)
   0 9 :durable))
(defconst *bra-config*
  (fn-bp-make-config "dtn://home/" "dtn://receiver/" "policy-1"
                     "dtn://receiver/" 1000 "home-incarnation-1"
                     "authorization-context-1"))
(defconst *bra-enqueued*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue (fn-bp-initial-state *bra-node* *bra-config*)
                           10 0 "work-1" "<bra@example.invalid>"
                           "forward-1" "policy-1" "terms-1")
    10 0 :durable)))
(defconst *bra-wf*
  (fn-bp-observe-transport
   (fn-bp-result-state
    (fn-bp-complete
     (fn-bp-prepare-attempt (fn-bprl-undertake *bra-enqueued* "work-1" 3)
                            11 0 "work-1" "attempt-0")
     11 0 :durable))
   "work-1" "attempt-0" 0 :delivered))
(assert-event (fn-bp-work-outstandingp
               (fn-bp-find-work "work-1" (fn-bp-state-works *bra-wf*))))
(assert-event (fn-bprl-work-pinnedp
               *bra-wf* (fn-bp-find-work "work-1" (fn-bp-state-works *bra-wf*))))

(defun bra-receipt (work subject terms)
  (fn-bpa-encode
   (fn-bpa-make-receipt "receipt-1" work subject "dtn://receiver/"
                        "dtn://receiver/" "policy-1" "home-incarnation-1"
                        "authorization-context-1" terms)))
(defconst *bra-exact* (bra-receipt "work-1" "subject-bra" "terms-1"))

; -----------------------------------------------------------------------------
; Configuration at A: B's own boundary, and the relay.
(defun bra-boundary (name eid port)
  (list (fn-cfg-row-make name "path-identity"
                         (string-append name ".example.invalid") 0)
        (fn-cfg-row-make name "auth-principal" "bp-only-no-nntp-principal" 0)
        (fn-cfg-row-make name "transport-bp" eid 0)
        (fn-cfg-row-make name "bp-trust" "network" 0)
        (fn-cfg-row-make name "bp-boundary-listener" "127.0.0.1" port)
        (fn-cfg-row-make name "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make name "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make name "bp-boundary-originators" "all-co-resident" 0)))
(defconst *bra-carries*
  (list (fn-cfg-row-make "relay" "bp-boundary-carries" "dtn://receiver/" 0)))
(defconst *bra-releases*
  (list (fn-cfg-row-make "relay" "bp-boundary-releases-for"
                         "dtn://receiver/" 0)))
(defun bra-cfg (rows)
  (fn-cfg-make 7 (fn-cfg-value-make
                  nil 0 nil nil nil
                  (append (bra-boundary "receiver-peer" "dtn://receiver/" 4601)
                          (bra-boundary "relay" "dtn://relay/" 4602)
                          rows) nil)))
(defconst *bra-carried-cfg* (bra-cfg *bra-carries*))
(defconst *bra-released-cfg* (bra-cfg (append *bra-carries* *bra-releases*)))
(assert-event (fn-cfgp *bra-carried-cfg*))
(assert-event (fn-cfgp *bra-released-cfg*))

(defun bra-view (class adu from)
  (list :delivery '("k" "b") class adu
        (list :cl (cons 3 1) 1 (cons :dtn (fn-record-string-octets "//relay/"))
              (fn-record-string-octets from) 7)
        nil "dtn://receiver/" "dtn://home/"))
(defconst *bra-relayed* (bra-view :receipt *bra-exact* "relay"))
(defconst *bra-direct* (bra-view :receipt *bra-exact* "receiver-peer"))

; -----------------------------------------------------------------------------
; Reachable witnesses.
; 1. The relay carries B's EID but does not release for it: the gate refuses,
;    no record, the obligation stays pinned.  ACL2's reason says so.
(assert-event (fn-bpaj-origin-carriage-permittedp
               *bra-carried-cfg* (fn-record-string-octets "relay") 7
               (fn-bpaj-source-eid "dtn://receiver/")))
(assert-event (not (fn-bpah-receipt-trustedp *bra-relayed* *bra-carried-cfg*)))
(assert-event (null (fn-bpah-receipt-release-record
                     *bra-relayed* *bra-carried-cfg* *bra-wf*)))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-relayed* *bra-carried-cfg* *bra-wf*)
                     :carried-not-released))
; 2. With the release row, the exact receipt releases work-1, and only it.
(defconst *bra-record*
  (fn-bpah-receipt-release-record *bra-relayed* *bra-released-cfg* *bra-wf*))
(assert-event
 (equal *bra-record*
        '(:receipt-intent 12 0 "receipt-1" "work-1" "subject-bra"
          "dtn://receiver/" "dtn://receiver/" "policy-1" "home-incarnation-1"
          "authorization-context-1" "terms-1")))
(assert-event (car (fn-bprl-apply-journal-record *bra-wf* *bra-record*)))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-relayed* *bra-released-cfg* *bra-wf*)
                     :listed-issuer))
; 3. B's own boundary delivering B's receipt needs no release row.
(assert-event (fn-bpah-receipt-release-record
               *bra-direct* *bra-carried-cfg* *bra-wf*))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-direct* *bra-carried-cfg* *bra-wf*)
                     :self-issued))
; 4. A listed issuer naming another work, subject or terms releases nothing.
(defun bra-other (work subject terms)
  (fn-bpah-receipt-release-record
   (bra-view :receipt (bra-receipt work subject terms) "relay")
   *bra-released-cfg* *bra-wf*))
(assert-event (null (bra-other "work-2" "subject-bra" "terms-1")))
(assert-event (null (bra-other "work-1" "subject-other" "terms-1")))
(assert-event (null (bra-other "work-1" "subject-bra" "terms-2")))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      (bra-view :receipt (bra-receipt "work-1" "subject-other"
                                                      "terms-1") "relay")
                      *bra-released-cfg* *bra-wf*)
                     :obligation-mismatch))

; -----------------------------------------------------------------------------
; Teeth: one must-fail per hypothesis.

; fn-bpah-unauthorized-issuer-releases-nothing: an authorized issuer does
; release.
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-relayed* *bra-released-cfg* *bra-wf*))))
; fn-bpah-carrier-without-release-row-releases-nothing, per hypothesis:
; with the carrier's own transport-bp row for the issuer (the direct case),
; and with a releases-for row, the receipt releases.
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-direct* *bra-carried-cfg* *bra-wf*))))
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-relayed* *bra-released-cfg* *bra-wf*))))
; fn-bpah-released-receipt-names-exactly-its-obligation: without a record
; the issuer need not be authorized.
(must-fail
 (assert-event (fn-bpah-release-issuer-authorizedp
                *bra-carried-cfg* (fn-record-string-octets "relay") 7
                (fn-bpaj-issuer-eid "dtn://receiver/"))))
; fn-bpah-receipt-naming-other-terms-releases-nothing: when the receipt
; names the obligation exactly, it releases.
(must-fail
 (assert-event (null (bra-other "work-1" "subject-bra" "terms-1"))))

; fn-bpah-request-trust-ignores-release-rows.  A request carried by the
; relay claiming B is trusted the same with or without the release row.
(defconst *bra-request* (bra-view :request '(0) "relay"))
(assert-event (fn-bpah-request-trustedp *bra-request* *bra-carried-cfg*))
(assert-event (fn-bpah-request-trustedp *bra-request* *bra-released-cfg*))
; A release row alone grants no request trust.
(assert-event (not (fn-bpah-request-trustedp *bra-request*
                                             (bra-cfg *bra-releases*))))
; Teeth, per hypothesis: differing in a non-release row, in generation, or
; in well-formedness changes the answer.
(must-fail
 (assert-event (equal (fn-bpah-request-trustedp *bra-request*
                                                *bra-released-cfg*)
                      (fn-bpah-request-trustedp *bra-request*
                                                (bra-cfg *bra-releases*)))))
(must-fail
 (assert-event (equal (fn-bpah-request-trustedp *bra-request*
                                                *bra-released-cfg*)
                      (fn-bpah-request-trustedp
                       *bra-request*
                       (fn-cfg-make 8 (fn-cfg-value *bra-released-cfg*))))))
(must-fail
 (assert-event (equal (fn-bpah-request-trustedp *bra-request*
                                                *bra-released-cfg*)
                      (fn-bpah-request-trustedp
                       *bra-request*
                       (fn-cfg-make 7 (fn-cfg-value-make
                                       '(junk) 0 nil nil nil
                                       (fn-cfg-peers
                                        (fn-cfg-value *bra-released-cfg*))
                                       nil))))))
