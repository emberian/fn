; One explicitly configured loopback boundary.  Every co-resident process is
; named in this profile; a claimed TCPCL EID cannot create a principal alone.
(in-package "ACL2")
(include-book "../../books/bp-session-admission")

(defconst *bpat-eid* (cons :dtn (fn-record-string-octets "//peer/")))
(defconst *bpat-other-eid* (cons :dtn (fn-record-string-octets "//other/")))
(defconst *bpat-channel* (list :tcp4 '(127 0 0 1) 4556 '(127 0 0 1)))
(defconst *bpat-rows*
  (list (fn-cfg-row-make "peer" "path-identity" "peer.example.invalid" 0)
        (fn-cfg-row-make "peer" "auth-principal" "bp-only-no-nntp-principal" 0)
        (fn-cfg-row-make "peer" "transport-bp" "dtn://peer/" 0)
        (fn-cfg-row-make "peer" "bp-trust" "network" 0)
        (fn-cfg-row-make "peer" "bp-boundary-listener" "127.0.0.1" 4556)
        (fn-cfg-row-make "peer" "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make "peer" "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make "peer" "bp-boundary-originators"
                         "all-co-resident" 0)))
(defconst *bpat-cfg*
  (fn-cfg-make 7 (fn-cfg-value-make nil 0 nil nil nil *bpat-rows* nil nil)))
(defconst *bpat-no-trust*
  (fn-cfg-make 7 (fn-cfg-value-make nil 0 nil nil nil
                                  (append (take 3 *bpat-rows*)
                                          (cddddr *bpat-rows*)) nil nil)))

(assert-event (fn-cfgp *bpat-cfg*))
(assert-event (fn-bpp-eidp *bpat-eid*))
(assert-event
 (equal (fn-bpaj-session-principal *bpat-cfg* *bpat-channel* *bpat-eid*)
        (list :admitted (fn-record-string-octets "peer") 7)))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal *bpat-cfg* *bpat-channel* *bpat-other-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal *bpat-no-trust* *bpat-channel* *bpat-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          (fn-cfg-make 7
            (fn-cfg-value-make nil 0 nil nil nil
              (cddr *bpat-rows*) nil nil))
          *bpat-channel* *bpat-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          *bpat-cfg* (list :tcp4 '(127 0 0 1) 4556 '(127 0 0 2))
          *bpat-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          (fn-cfg-make 7
            (fn-cfg-value-make nil 0 nil nil nil
              (cons (fn-cfg-row-make "peer" "bp-trust" "network" 0)
                    *bpat-rows*) nil nil))
          *bpat-channel* *bpat-eid*))
        nil))
; An announced EID cannot disambiguate two profiles on one observed channel.
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          (fn-cfg-make 7
            (fn-cfg-value-make nil 0 nil nil nil
              (append *bpat-rows*
                (list (fn-cfg-row-make "other" "path-identity"
                                       "other.example.invalid" 0)
                      (fn-cfg-row-make "other" "auth-principal"
                                       "bp-only-no-nntp-principal" 0)
                      (fn-cfg-row-make "other" "transport-bp" "dtn://other/" 0)
                      (fn-cfg-row-make "other" "bp-trust" "network" 0)
                      (fn-cfg-row-make "other" "bp-boundary-listener"
                                       "127.0.0.1" 4556)
                      (fn-cfg-row-make "other" "bp-boundary-source"
                                       "127.0.0.1" 0)
                      (fn-cfg-row-make "other" "bp-boundary-translation"
                                       "none" 0)
                      (fn-cfg-row-make "other" "bp-boundary-originators"
                                       "all-co-resident" 0))) nil nil))
          *bpat-channel* *bpat-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          (fn-cfg-make 7
            (fn-cfg-value-make nil 0 nil nil nil
              (append *bpat-rows*
                (list (fn-cfg-row-make "other" "path-identity"
                                       "other.example.invalid" 0)
                      (fn-cfg-row-make "other" "auth-principal"
                                       "bp-only-no-nntp-principal" 0)
                      (fn-cfg-row-make "other" "transport-bp" "dtn://peer/" 0)
                      (fn-cfg-row-make "other" "bp-trust" "network" 0)
                      (fn-cfg-row-make "other" "bp-boundary-listener"
                                       "127.0.0.1" 4556)
                      (fn-cfg-row-make "other" "bp-boundary-source"
                                       "127.0.0.1" 0)
                      (fn-cfg-row-make "other" "bp-boundary-translation"
                                       "none" 0)
                      (fn-cfg-row-make "other" "bp-boundary-originators"
                                       "all-co-resident" 0))) nil nil))
          *bpat-channel* *bpat-eid*))
        nil))

; D23: the carried-source decision.  "peer" is the neighbour; it carries
; dtn://x/, and "x" is x's own enrollment (a different listener port).
(include-book "std/testing/must-fail" :dir :system)
(defconst *bpat-x-rows*
  (list (fn-cfg-row-make "x" "path-identity" "x.example.invalid" 0)
        (fn-cfg-row-make "x" "auth-principal" "bp-only-no-nntp-principal" 0)
        (fn-cfg-row-make "x" "transport-bp" "dtn://x/" 0)
        (fn-cfg-row-make "x" "bp-trust" "network" 0)
        (fn-cfg-row-make "x" "bp-boundary-listener" "127.0.0.1" 4999)
        (fn-cfg-row-make "x" "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make "x" "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make "x" "bp-boundary-originators" "all-co-resident" 0)))
(defconst *bpat-carries-x*
  (list (fn-cfg-row-make "peer" "bp-boundary-carries" "dtn://x/" 0)))
(defun bpat-cfg (rows)
  (fn-cfg-make 7 (fn-cfg-value-make nil 0 nil nil nil rows nil nil)))
(defconst *bpat-carried-cfg*
  (bpat-cfg (append *bpat-rows* *bpat-carries-x* *bpat-x-rows*)))
(defconst *bpat-unenrolled-cfg* (bpat-cfg (append *bpat-rows* *bpat-carries-x*)))
(defconst *bpat-uncarried-cfg* (bpat-cfg (append *bpat-rows* *bpat-x-rows*)))
(defconst *bpat-p* (fn-record-string-octets "peer"))
(defconst *bpat-x* (fn-record-string-octets "x"))
(assert-event (fn-cfgp *bpat-carried-cfg*))
(assert-event (fn-cfgp *bpat-unenrolled-cfg*))
(assert-event (fn-cfgp *bpat-uncarried-cfg*))
; The neighbour is still admitted on its own channel; x's boundary is on
; another listener and does not make the peer's channel ambiguous.
(assert-event
 (equal (fn-bpaj-session-principal *bpat-carried-cfg* *bpat-channel* *bpat-eid*)
        (list :admitted *bpat-p* 7)))
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-p* 7
                                         "dtn://peer/")
        (list :direct *bpat-p*)))
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-p* 7
                                         "dtn://x/")
        (list :carried *bpat-p* *bpat-x*)))
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-x* 7
                                         "dtn://x/")
        (list :direct *bpat-x*)))
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-uncarried-cfg* *bpat-p* 7
                                         "dtn://x/")
        '(:refused :source-not-carried)))
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-unenrolled-cfg* *bpat-p* 7
                                         "dtn://x/")
        '(:refused :carried-source-unenrolled)))
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-p* 8
                                         "dtn://x/")
        '(:refused :generation)))
; A carried row names what the neighbour may carry, not what x may carry:
; x is a direct boundary and carries nothing.
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-x* 7
                                         "dtn://peer/")
        '(:refused :source-not-carried)))

; Teeth.  fn-bpaj-carried-decision-is-the-authors-direct-decision without
; its hypothesis: a refused decision names no author with a direct decision.
(must-fail
 (assert-event
  (fn-bpaj-current-peer-eidp
   *bpat-unenrolled-cfg*
   (fn-bpaj-source-decision-principal
    (fn-bpaj-carried-source-decision *bpat-unenrolled-cfg* *bpat-p* 7
                                     "dtn://x/"))
   7 "dtn://x/")))
; fn-bpaj-unlisted-source-is-not-trusted: with the neighbour's own
; transport row, or with its carries row, the source is trusted.
(must-fail
 (assert-event
  (not (fn-bpaj-source-decision-trustedp
        (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-p* 7
                                         "dtn://peer/")))))
(must-fail
 (assert-event
  (not (fn-bpaj-source-decision-trustedp
        (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-p* 7
                                         "dtn://x/")))))
; fn-bpaj-carried-unenrolled-source-is-refused, one case per hypothesis.
(defun bpat-unenrolledp (cfg principal generation)
  (equal (fn-bpaj-carried-source-decision cfg principal generation "dtn://x/")
         '(:refused :carried-source-unenrolled)))
(assert-event (bpat-unenrolledp *bpat-unenrolled-cfg* *bpat-p* 7))
(must-fail (assert-event   ; not a configuration
            (bpat-unenrolledp
             (fn-cfg-make 7 (fn-cfg-value-make '(junk) 0 nil nil nil
                              (append *bpat-rows* *bpat-carries-x*) nil nil))
             *bpat-p* 7)))
(must-fail (assert-event (bpat-unenrolledp *bpat-unenrolled-cfg* *bpat-p* 8)))
(must-fail (assert-event (bpat-unenrolledp *bpat-uncarried-cfg* *bpat-p* 7)))
(must-fail (assert-event (bpat-unenrolledp *bpat-carried-cfg* *bpat-p* 7)))

; D23 second half: typed identities, origin carriage and the release list.
; "peer" carries dtn://x/ and, in the released configuration, also lists
; dtn://x/ as a release issuer.  The two lists are separate row kinds and
; their accessors return separate identity domains.
(defconst *bpat-releases-x*
  (list (fn-cfg-row-make "peer" "bp-boundary-releases-for" "dtn://x/" 0)))
(defconst *bpat-released-cfg*
  (bpat-cfg (append *bpat-rows* *bpat-carries-x* *bpat-releases-x*
                    *bpat-x-rows*)))
(defconst *bpat-release-only-cfg*
  (bpat-cfg (append *bpat-rows* *bpat-releases-x* *bpat-x-rows*)))
(assert-event (fn-cfgp *bpat-released-cfg*))
(assert-event (fn-cfgp *bpat-release-only-cfg*))
(assert-event
 (equal (fn-bpaj-boundary-carried-sources *bpat-released-cfg* *bpat-p*)
        (list (fn-bpaj-source-eid "dtn://x/"))))
(assert-event
 (equal (fn-bpaj-boundary-release-issuers *bpat-released-cfg* *bpat-p*)
        (list (fn-bpaj-issuer-eid "dtn://x/"))))
(assert-event
 (null (fn-bpaj-boundary-release-issuers *bpat-carried-cfg* *bpat-p*)))
(assert-event (fn-bpaj-source-eidp (fn-bpaj-source-eid "dtn://x/")))
(assert-event (not (fn-bpaj-source-eidp (fn-bpaj-issuer-eid "dtn://x/"))))
(assert-event (not (fn-bpaj-issuer-eidp (fn-bpaj-source-eid "dtn://x/"))))
(assert-event (not (fn-bpaj-principal-idp (fn-bpaj-source-eid "dtn://x/"))))
; Neighbour admission is the session admission.
(assert-event
 (fn-bpaj-neighbor-admittedp *bpat-carried-cfg* *bpat-channel* *bpat-eid*))
; Origin carriage reads the carried list and takes only a source EID.
(assert-event
 (fn-bpaj-origin-carriage-permittedp *bpat-carried-cfg* *bpat-p* 7
                                     (fn-bpaj-source-eid "dtn://x/")))
(assert-event
 (not (fn-bpaj-origin-carriage-permittedp *bpat-carried-cfg* *bpat-p* 7
                                          (fn-bpaj-issuer-eid "dtn://x/"))))
(assert-event
 (not (fn-bpaj-origin-carriage-permittedp *bpat-release-only-cfg* *bpat-p* 7
                                          (fn-bpaj-source-eid "dtn://x/"))))
; The release list reads its own rows and takes only an issuer EID.
(assert-event
 (fn-bpaj-release-issuer-listedp *bpat-released-cfg* *bpat-p* 7
                                 (fn-bpaj-issuer-eid "dtn://x/")))
(assert-event
 (not (fn-bpaj-release-issuer-listedp *bpat-carried-cfg* *bpat-p* 7
                                      (fn-bpaj-issuer-eid "dtn://x/"))))
(assert-event
 (not (fn-bpaj-release-issuer-listedp *bpat-released-cfg* *bpat-p* 7
                                      (fn-bpaj-source-eid "dtn://x/"))))
; A release row grants no carriage: with only a release row the source is
; not carried (fn-bpaj-release-row-is-not-carriage, reachable witness).
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-release-only-cfg* *bpat-p* 7
                                         "dtn://x/")
        '(:refused :source-not-carried)))
; Teeth for fn-bpaj-release-row-is-not-carriage: with the carries row the
; conclusion fails.
(must-fail
 (assert-event
  (not (fn-bpaj-origin-carriage-permittedp
        *bpat-released-cfg* *bpat-p* 7 (fn-bpaj-source-eid "dtn://x/")))))
; fn-bpaj-carried-decision-requires-origin-carriage: a direct decision is
; not a carriage permission (the hypothesis matters).
(must-fail
 (assert-event
  (fn-bpaj-origin-carriage-permittedp *bpat-carried-cfg* *bpat-p* 7
                                      (fn-bpaj-source-eid "dtn://peer/"))))
; fn-bpaj-source-decision-ignores-release-rows, witness: adding the release
; row changes no decision.
(assert-event
 (equal (fn-bpaj-carried-source-decision *bpat-released-cfg* *bpat-p* 7
                                         "dtn://x/")
        (fn-bpaj-carried-source-decision *bpat-carried-cfg* *bpat-p* 7
                                         "dtn://x/")))
; Teeth, one per hypothesis: configurations that differ in a non-release
; row, in generation, or in well-formedness decide differently.
(must-fail
 (assert-event
  (equal (fn-bpaj-carried-source-decision *bpat-released-cfg* *bpat-p* 7
                                          "dtn://x/")
         (fn-bpaj-carried-source-decision *bpat-release-only-cfg* *bpat-p* 7
                                          "dtn://x/"))))
(must-fail
 (assert-event
  (equal (fn-bpaj-carried-source-decision *bpat-released-cfg* *bpat-p* 7
                                          "dtn://x/")
         (fn-bpaj-carried-source-decision
          (fn-cfg-make 8 (fn-cfg-value *bpat-released-cfg*)) *bpat-p* 7
          "dtn://x/"))))
(must-fail
 (assert-event
  (equal (fn-bpaj-carried-source-decision *bpat-released-cfg* *bpat-p* 7
                                          "dtn://x/")
         (fn-bpaj-carried-source-decision
          (fn-cfg-make 7 (fn-cfg-value-make '(junk) 0 nil nil nil
                           (append *bpat-rows* *bpat-carries-x*
                                   *bpat-x-rows*) nil nil))
          *bpat-p* 7 "dtn://x/"))))
