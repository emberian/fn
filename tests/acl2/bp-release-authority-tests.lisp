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
                          rows) nil nil nil)))
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
                     *bra-relayed* *bra-carried-cfg* *bra-wf* nil nil)))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-relayed* *bra-carried-cfg* *bra-wf* nil nil)
                     :carried-not-released))
; 2. With the release row, the exact receipt releases work-1, and only it.
(defconst *bra-record*
  (fn-bpah-receipt-release-record *bra-relayed* *bra-released-cfg* *bra-wf* nil nil))
(assert-event
 (equal *bra-record*
        '(:receipt-intent 12 0 "receipt-1" "work-1" "subject-bra"
          "dtn://receiver/" "dtn://receiver/" "policy-1" "home-incarnation-1"
          "authorization-context-1" "terms-1")))
(assert-event (car (fn-bprl-apply-journal-record *bra-wf* *bra-record*)))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-relayed* *bra-released-cfg* *bra-wf* nil nil)
                     :listed-issuer))
; 3. B's own boundary delivering B's receipt needs no release row.
(assert-event (fn-bpah-receipt-release-record
               *bra-direct* *bra-carried-cfg* *bra-wf* nil nil))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-direct* *bra-carried-cfg* *bra-wf* nil nil)
                     :self-issued))
; 4. A listed issuer naming another work, subject or terms releases nothing.
(defun bra-other (work subject terms)
  (fn-bpah-receipt-release-record
   (bra-view :receipt (bra-receipt work subject terms) "relay")
   *bra-released-cfg* *bra-wf* nil nil))
(assert-event (null (bra-other "work-2" "subject-bra" "terms-1")))
(assert-event (null (bra-other "work-1" "subject-other" "terms-1")))
(assert-event (null (bra-other "work-1" "subject-bra" "terms-2")))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      (bra-view :receipt (bra-receipt "work-1" "subject-other"
                                                      "terms-1") "relay")
                      *bra-released-cfg* *bra-wf* nil nil)
                     :obligation-mismatch))

; -----------------------------------------------------------------------------
; Teeth: one must-fail per hypothesis.

; fn-bpah-unauthorized-issuer-releases-nothing: an authorized issuer does
; release.
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-relayed* *bra-released-cfg* *bra-wf* nil nil))))
; fn-bpah-carrier-without-release-row-releases-nothing, per hypothesis:
; with the carrier's own transport-bp row for the issuer (the direct case),
; and with a releases-for row, the receipt releases.
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-direct* *bra-carried-cfg* *bra-wf* nil nil))))
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-relayed* *bra-released-cfg* *bra-wf* nil nil))))
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
                                       nil nil nil))))))

; -----------------------------------------------------------------------------
; Signed receipts (lane signed-receipts).  B's hybrid principal P and its two
; keys are enrolled in A's keyring; A's own boundary for B
; ("receiver-peer") names P as its receipt signer.  The signatures and the
; host's observations are abstract (A-CRYPTO): these witnesses exercise the
; decision, not Ed25519 or ML-DSA-65.
(defconst *bra-principal* (make-list 32 :initial-element 7))
(defconst *bra-ed-key* (make-list 32 :initial-element 1))
(defconst *bra-ml-key* (make-list 1952 :initial-element 2))
(defconst *bra-keys* (list (cons :ed25519 *bra-ed-key*)
                           (cons :ml-dsa-65 *bra-ml-key*)))
; Attachments (the statement codec) run in make-event, not in defconst.
(make-event
 `(defconst *bra-snapshots*
    ',(list (fn-hsig-keyring-event 1 1 1 1 *bra-principal* *bra-keys*))))
(assert-event (equal (fn-bpah-receipt-signer-keys *bra-snapshots*
                                                  *bra-principal*)
                     *bra-keys*))
(defconst *bra-ed-sig* (make-list 64 :initial-element 3))
(defconst *bra-ml-sig* (make-list 3309 :initial-element 4))
(defun bra-signed (adu)
  (fn-bpsr-encode (fn-bpsr-make adu *bra-principal* *bra-ed-sig*
                                *bra-ml-sig*)))
(defconst *bra-signed-exact* (bra-signed *bra-exact*))
; The frame round-trips and carries the exact ADU.
(assert-event (equal (fn-bpsr-decode *bra-signed-exact*)
                     (fn-bpsr-make *bra-exact* *bra-principal* *bra-ed-sig*
                                   *bra-ml-sig*)))
(assert-event (equal (fn-bpsr-adu-octets *bra-signed-exact*) *bra-exact*))
(assert-event (null (fn-bpsr-decode *bra-exact*)))
; The preimage is the article scheme's subject body under the receipt tag,
; and binds the requester.
(assert-event (consp (fn-bpsr-signed-preimage *bra-principal* *bra-keys*
                                              "dtn://home/" *bra-exact*)))
(assert-event (not (equal (fn-bpsr-signed-preimage *bra-principal* *bra-keys*
                                                   "dtn://home/" *bra-exact*)
                          (fn-bpsr-signed-preimage *bra-principal* *bra-keys*
                                                   "dtn://other/" *bra-exact*))))

(defconst *bra-signer-row*
  (fn-cfg-row-make "receiver-peer" "bp-boundary-receipt-signer"
                   (fn-record-octets-string (fn-stx-hex-octets *bra-principal*))
                   0))
(defconst *bra-require-row*
  (fn-cfg-row-make "relay" "bp-boundary-require-signed-receipts" "yes" 0))
; The lab's A: the relay carries B, no release row, require-signed-receipts.
(defconst *bra-signed-cfg*
  (bra-cfg (list* *bra-signer-row* *bra-require-row* *bra-carries*)))
(assert-event (fn-cfgp *bra-signed-cfg*))
(defconst *bra-signed-view* (bra-view :receipt *bra-signed-exact* "relay"))
(defconst *bra-good-obs* (list *bra-ml-key* :verified :verified))
(defconst *bra-bad-obs* (list *bra-ml-key* :refused :refused))
(make-event
 `(defconst *bra-plan*
    ',(fn-bpah-receipt-signature-plan *bra-signed-view* *bra-snapshots*)))
(assert-event (equal (cdr *bra-plan*)
                     (list *bra-ed-key* *bra-ml-key*
                           (list (cons :ed25519 *bra-ed-sig*)
                                 (cons :ml-dsa-65 *bra-ml-sig*)))))
(assert-event (equal (car *bra-plan*)
                     (fn-bpsr-signed-preimage *bra-principal* *bra-keys*
                                              "dtn://home/" *bra-exact*)))

; 5. The signed receipt releases work-1 through a relay that is neither B
;    nor lists B, under require-signed-receipts.
(make-event
 `(defconst *bra-signed-record*
    ',(fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg*
                                      *bra-wf* *bra-snapshots*
                                      *bra-good-obs*)))
(assert-event (equal *bra-signed-record* *bra-record*))
(assert-event (not (fn-bpah-release-issuer-authorizedp
                    *bra-signed-cfg* (fn-record-string-octets "relay") 7
                    (fn-bpaj-issuer-eid "dtn://receiver/"))))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-signed-view* *bra-signed-cfg* *bra-wf*
                      *bra-snapshots* *bra-good-obs*)
                     :signed-issuer))
(assert-event (equal (fn-bpah-receipt-release-line
                      *bra-signed-view* *bra-signed-cfg* *bra-snapshots*
                      *bra-good-obs*)
                     "signed-issuer carrier=relay issuer=dtn://receiver/"))
; 6. Its signature failing (the lab's flipped bytes: both primitives
;    refuse) releases nothing, even from B itself or a listed relay.
(assert-event (null (fn-bpah-receipt-release-record
                     *bra-signed-view* *bra-signed-cfg* *bra-wf*
                     *bra-snapshots* *bra-bad-obs*)))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-signed-view* *bra-signed-cfg* *bra-wf*
                      *bra-snapshots* *bra-bad-obs*)
                     :signature-refused))
(assert-event (null (fn-bpah-receipt-release-record
                     (bra-view :receipt *bra-signed-exact* "receiver-peer")
                     (bra-cfg (list *bra-signer-row*)) *bra-wf*
                     *bra-snapshots* *bra-bad-obs*)))
(assert-event (null (fn-bpah-receipt-release-record
                     *bra-signed-view*
                     (bra-cfg (list* *bra-signer-row* *bra-releases*))
                     *bra-wf* *bra-snapshots* *bra-bad-obs*)))
; 7. Signed fields that differ from the obligation release nothing.
(defun bra-signed-other (work subject terms)
  (fn-bpah-receipt-release-record
   (bra-view :receipt (bra-signed (bra-receipt work subject terms)) "relay")
   *bra-signed-cfg* *bra-wf* *bra-snapshots* *bra-good-obs*))
(assert-event (null (bra-signed-other "work-2" "subject-bra" "terms-1")))
(assert-event (null (bra-signed-other "work-1" "subject-other" "terms-1")))
(assert-event (null (bra-signed-other "work-1" "subject-bra" "terms-2")))
; 8. The signer is the issuer's own enrollment, never the carrier's: the
;    same principal named on the relay's boundary verifies nothing; nor
;    does a principal this Store has not enrolled.
(defconst *bra-carrier-signer-cfg*
  (bra-cfg (list* (fn-cfg-row-make "relay" "bp-boundary-receipt-signer"
                                   (fn-record-octets-string
                                    (fn-stx-hex-octets *bra-principal*)) 0)
                  *bra-require-row* *bra-carries*)))
(assert-event (null (fn-bpah-receipt-release-record
                     *bra-signed-view* *bra-carrier-signer-cfg* *bra-wf*
                     *bra-snapshots* *bra-good-obs*)))
(assert-event (null (fn-bpah-receipt-release-record
                     *bra-signed-view* *bra-signed-cfg* *bra-wf*
                     nil *bra-good-obs*)))
; 9. The delegation profile: a bare receipt through a listed relay releases
;    whoever wrote it (witness 2); the same bare receipt under
;    require-signed-receipts releases nothing, listed or direct.
(defconst *bra-flagged-released-cfg*
  (bra-cfg (list* *bra-require-row* (append *bra-carries* *bra-releases*))))
(assert-event (null (fn-bpah-receipt-release-record
                     *bra-relayed* *bra-flagged-released-cfg* *bra-wf*
                     nil nil)))
(assert-event (equal (fn-bpah-receipt-release-verdict
                      *bra-relayed* *bra-flagged-released-cfg* *bra-wf*
                      nil nil)
                     :signature-required))

; Teeth for the signed-receipt keystones, one per hypothesis.
; fn-bpah-signed-receipt-releases-through-any-carrier:
;   signed -- the bare receipt through the same relay does not release what
;   the signed one does;
(must-fail
 (assert-event (equal (fn-bpah-receipt-release-record
                       *bra-relayed* *bra-signed-cfg* *bra-wf*
                       *bra-snapshots* *bra-good-obs*)
                      (fn-bprl-receipt-auto-record *bra-wf* *bra-exact* t))))
;   verified -- with failing observations the record differs;
(must-fail
 (assert-event (equal (fn-bpah-receipt-release-record
                       *bra-signed-view* *bra-signed-cfg* *bra-wf*
                       *bra-snapshots* *bra-bad-obs*)
                      (fn-bprl-receipt-auto-record *bra-wf* *bra-exact* t))))
;   shape -- a view whose bundle source is not the receipt's issuer.
(must-fail
 (assert-event
  (equal (fn-bpah-receipt-release-record
          (list :delivery '("k" "b") :receipt *bra-signed-exact*
                (fn-bpn-nth 4 *bra-signed-view*) nil "dtn://relay/"
                "dtn://home/")
          *bra-signed-cfg* *bra-wf* *bra-snapshots* *bra-good-obs*)
         (fn-bprl-receipt-auto-record *bra-wf* *bra-exact* t))))
; fn-bpah-unverified-signed-receipt-releases-nothing: verified releases; a
; bare receipt from B directly releases.
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-signed-view* *bra-signed-cfg* *bra-wf*
                      *bra-snapshots* *bra-good-obs*))))
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-direct* *bra-carried-cfg* *bra-wf*
                      *bra-snapshots* *bra-bad-obs*))))
; fn-bpah-receipt-signature-needs-both-observations: refused observations
; are not verified.
(must-fail
 (assert-event (fn-bpah-receipt-signature-verifiedp
                *bra-signed-cfg* *bra-snapshots* 7
                (fn-bpaj-issuer-eid "dtn://receiver/") "dtn://home/"
                (fn-bpsr-decode *bra-signed-exact*)
                (list *bra-ml-key* :verified :refused))))
; fn-bpah-trusted-bare-receipt-releases: signed, flagged and untrusted
; receipts each differ from the bare workflow answer.
(must-fail
 (assert-event (equal (fn-bpah-receipt-release-record
                       *bra-signed-view* *bra-signed-cfg* *bra-wf*
                       *bra-snapshots* *bra-good-obs*)
                      (fn-bprl-receipt-auto-record
                       *bra-wf* *bra-signed-exact* t))))
(must-fail
 (assert-event (equal (fn-bpah-receipt-release-record
                       *bra-relayed* *bra-flagged-released-cfg* *bra-wf*
                       nil nil)
                      (fn-bprl-receipt-auto-record *bra-wf* *bra-exact* t))))
(must-fail
 (assert-event (equal (fn-bpah-receipt-release-record
                       *bra-relayed* *bra-carried-cfg* *bra-wf* nil nil)
                      (fn-bprl-receipt-auto-record *bra-wf* *bra-exact* t))))
; fn-bpah-required-signature-refuses-bare-receipts: without the flag the
; listed bare receipt releases; signed under the flag releases.
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-relayed* *bra-released-cfg* *bra-wf* nil nil))))
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-signed-view* *bra-signed-cfg* *bra-wf*
                      *bra-snapshots* *bra-good-obs*))))
; The unsigned keystones' new hypothesis (not signed): a signed receipt
; through the relay without any row releases.
(must-fail
 (assert-event (null (fn-bpah-receipt-release-record
                      *bra-signed-view* (bra-cfg (list* *bra-signer-row*
                                                        *bra-carries*))
                      *bra-wf* *bra-snapshots* *bra-good-obs*))))
