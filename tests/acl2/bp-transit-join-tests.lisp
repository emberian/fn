; The BP request's immutable article and the NNTP transit Store projection
; are distinct on a reachable Path-bearing request.  The same peer table and
; transfer decision are used; a BP-only boundary grants no inbound scope.
(in-package "ACL2")
(include-book "../../books/bp-transit-join")
(include-book "../../books/owner-invariants")
(include-book "../../books/codec-attach")
(include-book "peer-inbound-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *btj-peer*
  (fn-cfg-peer-make "dtnB" "dtnb.example" '(:bp "dtn://b/")
                    '("fn.letters" 32768 16) nil
                    '(:principal "bp-only-no-nntp-principal")))
(defconst *btj-boundary-rows*
  (list (fn-cfg-row-make "dtnB" "bp-trust" "network" 0)
        (fn-cfg-row-make "dtnB" "bp-boundary-listener" "127.0.0.1" 4556)
        (fn-cfg-row-make "dtnB" "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make "dtnB" "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make "dtnB" "bp-boundary-originators"
                         "all-co-resident" 0)))
(defconst *btj-cfg*
  (fn-cfg-make 1
    (fn-cfg-apply-delta
      (fn-cfg-value *pt-cfg*) 1 *fn-cfg-default-stamp*
      (fn-cfg-set-peer "dtnB"
        (append (fn-cfg-peer-rows *btj-peer*) *btj-boundary-rows*)))))
(defconst *btj-ingress*
  (list :cl (cons 1 1) 1 (cons :dtn (pt-o "//b/"))
        (pt-o "dtnB") 1))
(make-event
 `(defconst *btj-subject*
    ',(fn-record-octets-string (fn-id-text (fn-id-subject-of-payload *pt-a1*)))))
(defconst *btj-request*
  (fn-bpa-make-request "work-btj" *btj-subject* "dtn://b/" "dtn://local/"
                       "policy" "incarnation" "auth" "terms" *pt-a1*))
(defconst *btj-request-octets* (fn-bpa-encode *btj-request*))
(make-event
 `(defconst *btj-plan*
    ',(fn-bpaj-transit-plan *pt-node0* *btj-cfg* *btj-ingress* "dtn://b/"
                              *btj-request-octets* *pt-obs*)))

(assert-event (fn-cfgp *btj-cfg*))
(assert-event (fn-bpa-requestp *btj-request*))
(assert-event (equal (car *btj-plan*) :submit))
(assert-event (equal (fn-bpaj-nth 1 *btj-plan*) "dtnB"))
(assert-event (equal (fn-bpaj-nth 3 *btj-plan*) *pt-a1*))
(assert-event (equal (fn-bpaj-transit-stored-octets *btj-plan*)
                     (fn-peer-relayed-octets *btj-cfg* "dtnB" *pt-a1*)))
(assert-event (not (equal (fn-bpaj-transit-stored-octets *btj-plan*)
                          *pt-a1*)))
(must-fail
 (assert-event (equal (fn-bpaj-transit-stored-octets *btj-plan*)
                      *pt-a1*)))
(make-event
 `(defconst *btj-intent*
    ',(fn-bpaj-transit-intent-from-plan
       *btj-cfg* "bundle-btj" *btj-request-octets* 1 0
       :accepted *btj-plan*)))
(assert-event (fn-bpaj-transit-intentp *btj-intent*))
(assert-event (equal (fn-bpaj-nth 2 *btj-intent*) *btj-request-octets*))
(assert-event (equal (fn-bpaj-nth 9 *btj-intent*)
                     (fn-bpaj-transit-stored-octets *btj-plan*)))
(assert-event (not (fn-bpaj-transit-intentp
                    (update-nth 9 *pt-a1* *btj-intent*))))
(must-fail
 (assert-event (fn-bpaj-transit-intentp
                (update-nth 9 *pt-a1* *btj-intent*))))
(assert-event
 (equal (fn-bpaj-transit-plan
         *pt-node0* *btj-cfg*
         (update-nth 4 nil *btj-ingress*) "dtn://b/"
         *btj-request-octets* *pt-obs*)
        '(:refused :no-principal)))
(defconst *btj-no-inbound-peer*
  (fn-cfg-peer-make "dtnB" "dtnb.example" '(:bp "dtn://b/") nil nil
                    '(:principal "bp-only-no-nntp-principal")))
(defconst *btj-no-inbound-cfg*
  (fn-cfg-make 1
    (fn-cfg-apply-delta
      (fn-cfg-value *pt-cfg*) 1 *fn-cfg-default-stamp*
      (fn-cfg-set-peer "dtnB"
        (append (fn-cfg-peer-rows *btj-no-inbound-peer*)
                *btj-boundary-rows*)))))
(assert-event
 (equal (fn-bpaj-transit-plan
         *pt-node0* *btj-no-inbound-cfg* *btj-ingress* "dtn://b/"
         *btj-request-octets* *pt-obs*)
        '(:refused :no-inbound)))

; The BP-origin event enters the real owner transit queue without inventing
; an NNTP connection.  A premature :durable word is still uncertain.
(defconst *btj-owner*
  (fn-own-observe (fn-own-start
                   (fn-sn-initial '("fn.letters" "fn.test") 10) 4)
                  *pt-obs*))
(assert-event
 (equal (fn-own-bp-transit-submit-result
         *btj-owner* *btj-cfg* "dtnB" *pt-id1* *pt-a1*
         (fn-bpaj-nth 8 *btj-plan*) (fn-bpaj-nth 9 *btj-plan*))
        :submitted))
(defconst *btj-queued*
  (fn-own-bp-transit-submit
   *btj-owner* *btj-cfg* "dtnB" *pt-id1* *pt-a1*
   (fn-bpaj-nth 8 *btj-plan*) (fn-bpaj-nth 9 *btj-plan*)))
(assert-event (fn-own-relation *btj-owner*))
(assert-event (fn-own-relation *btj-queued*))
(must-fail
 (assert-event
  (fn-own-relation
   (fn-own-bp-transit-submit
    (update-nth 4 -1 *btj-owner*) *btj-cfg* "dtnB" *pt-id1* *pt-a1*
    (fn-bpaj-nth 8 *btj-plan*) (fn-bpaj-nth 9 *btj-plan*)))))
(assert-event (fn-own-bp-transit-submissionp
               (car (fn-own-queue *btj-queued*))))
(defconst *btj-taken* (fn-own-take-submission *btj-queued*))
(assert-event (fn-own-bp-transit-submissionp
               (fn-own-inflight *btj-taken*)))
(assert-event
 (equal (fn-own-bp-transit-outcome-result *btj-taken* :durable)
        :uncertain))
(assert-event
 (not (fn-own-inflight
       (fn-own-bp-transit-outcome *btj-taken* :uncertain))))
(assert-event (fn-own-relation *btj-taken*))
(assert-event
 (fn-own-relation
  (fn-own-bp-transit-outcome *btj-taken* :uncertain)))
(must-fail
 (assert-event
  (fn-own-relation
   (fn-own-bp-transit-outcome
    (update-nth 4 -1 *btj-taken*) :uncertain))))
(must-fail
 (assert-event
  (equal (fn-own-bp-transit-outcome-result *btj-taken* :durable)
         :accepted)))

; -----------------------------------------------------------------------------
; D23: a relay boundary that carries dtn://b/.  "relay" is the TCPCL
; neighbour; "dtnB" is the author's own enrollment (the witness above).
(defconst *btj-relay-peer*
  (fn-cfg-peer-make "relay" "relay.example" '(:bp "dtn://relay/")
                    nil nil '(:principal "bp-only-no-nntp-principal")))
(defconst *btj-relay-rows*
  (list (fn-cfg-row-make "relay" "bp-trust" "network" 0)
        (fn-cfg-row-make "relay" "bp-boundary-listener" "127.0.0.1" 4557)
        (fn-cfg-row-make "relay" "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make "relay" "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make "relay" "bp-boundary-originators"
                         "all-co-resident" 0)))
(defconst *btj-carries-b*
  (list (fn-cfg-row-make "relay" "bp-boundary-carries" "dtn://b/" 0)))
(defun btj-with-relay (value rows)
  (fn-cfg-apply-delta value 1 *fn-cfg-default-stamp*
    (fn-cfg-set-peer "relay"
      (append (fn-cfg-peer-rows *btj-relay-peer*) *btj-relay-rows* rows))))
; Relay carries b and b is enrolled here: the reachable D23 configuration.
(defconst *btj-carried-cfg*
  (fn-cfg-make 1 (btj-with-relay (fn-cfg-value *btj-cfg*) *btj-carries-b*)))
; Relay without the carried row (b still enrolled).
(defconst *btj-uncarried-cfg*
  (fn-cfg-make 1 (btj-with-relay (fn-cfg-value *btj-cfg*) nil)))
; Relay carries b, but b is enrolled nowhere at this node.
(defconst *btj-unenrolled-cfg*
  (fn-cfg-make 1 (btj-with-relay
                  (fn-cfg-apply-delta (fn-cfg-value *pt-cfg*) 1
                                      *fn-cfg-default-stamp*
                                      (fn-cfg-remove-peer "dtnB"))
                  *btj-carries-b*)))
; Relay carries b; b has a peer record with transport dtn://b/ but no BP
; trust profile, so it is not an enrollment either.
(defconst *btj-untrusted-author-cfg*
  (fn-cfg-make 1 (btj-with-relay (fn-cfg-value *pt-cfg*) *btj-carries-b*)))
(defconst *btj-relay-ingress*
  (list :cl (cons 1 2) 1 (cons :dtn (pt-o "//relay/")) (pt-o "relay") 1))
(defconst *btj-bad-relay-ingress* (update-nth 2 -1 *btj-relay-ingress*))
(defun btj-view (ingress)
  (list :delivery '(k) :request *btj-request-octets* ingress
        '(id) "dtn://b/" "dtn://local/"))
(defun btj-decision (cfg ingress)
  (fn-bpaj-carried-source-decision
   cfg (fn-bpnf-ingress-principal ingress) (fn-bpn-nth 5 ingress) "dtn://b/"))
(defun btj-plan (cfg ingress)
  (fn-bpaj-transit-plan *pt-node0* cfg ingress "dtn://b/"
                        *btj-request-octets* *pt-obs*))

(assert-event (fn-cfgp *btj-carried-cfg*))
(assert-event (fn-cfgp *btj-uncarried-cfg*))
(assert-event (fn-cfgp *btj-unenrolled-cfg*))
(assert-event (fn-cfgp *btj-untrusted-author-cfg*))
(assert-event (fn-bpnf-cl-ingressp *btj-relay-ingress*))
(assert-event (not (fn-bpnf-cl-ingressp *btj-bad-relay-ingress*)))
(assert-event (equal (fn-bpnf-ingress-principal *btj-bad-relay-ingress*)
                     (pt-o "relay")))

; Reachable witness for the carried keystone: every hypothesis holds, the
; decision is carried with author dtnB, and the carried plan is the direct
; plan: a :submit under dtnB with dtnB's inbound scope.
(assert-event (equal (btj-decision *btj-carried-cfg* *btj-relay-ingress*)
                     (list :carried (pt-o "relay") (pt-o "dtnB"))))
(assert-event (equal (fn-bpnf-ingress-principal *btj-ingress*) (pt-o "dtnB")))
(assert-event (equal (fn-bpn-nth 5 *btj-ingress*)
                     (fn-bpn-nth 5 *btj-relay-ingress*)))
(assert-event (equal (btj-decision *btj-carried-cfg* *btj-ingress*)
                     (list :direct (pt-o "dtnB"))))
(assert-event (fn-bpah-request-trustedp (btj-view *btj-relay-ingress*)
                                        *btj-carried-cfg*))
(assert-event (equal (btj-plan *btj-carried-cfg* *btj-relay-ingress*)
                     (btj-plan *btj-carried-cfg* *btj-ingress*)))
(assert-event (equal (car (btj-plan *btj-carried-cfg* *btj-relay-ingress*))
                     :submit))
(assert-event (equal (fn-bpaj-nth 1 (btj-plan *btj-carried-cfg*
                                              *btj-relay-ingress*))
                     "dtnB"))
(assert-event
 (equal (fn-bpah-source-decision-line (btj-view *btj-relay-ingress*)
                                      *btj-carried-cfg*)
        "carried carrier=relay author=dtnB"))
(assert-event
 (equal (fn-bpah-source-decision-line (btj-view *btj-ingress*)
                                      *btj-carried-cfg*)
        "direct principal=dtnB"))
; The carrier's own scope never enters: the relay has no inbound groups, and
; a request judged under the relay would be refused :no-inbound.
(assert-event (not (fn-cfg-peer-inbound
                    (fn-cfg-peer-find "relay" (fn-cfg-peers
                                               (fn-cfg-value
                                                *btj-carried-cfg*))))))

; Teeth for fn-bpaj-carried-request-is-judged-as-the-authors-direct-request,
; one per hypothesis; each case keeps the other hypotheses.
; (1) carried ingress not a CL ingress: the decision is still carried, but
;     the host view is refused while the direct one is trusted.
(assert-event (equal (car (btj-decision *btj-carried-cfg*
                                        *btj-bad-relay-ingress*))
                     :carried))
(must-fail
 (assert-event (fn-bpah-request-trustedp (btj-view *btj-bad-relay-ingress*)
                                         *btj-carried-cfg*)))
; (2) direct ingress not a CL ingress.
(must-fail
 (assert-event
  (equal (fn-bpah-view-source-decision
          (btj-view (update-nth 2 -1 *btj-ingress*)) *btj-carried-cfg*)
         (list :direct (pt-o "dtnB")))))
; (3) decision not carried (relay does not carry b): the author is nil and
;     no direct view is decided under it.
(assert-event (equal (btj-decision *btj-uncarried-cfg* *btj-relay-ingress*)
                     '(:refused :source-not-carried)))
(must-fail
 (assert-event
  (equal (fn-bpah-view-source-decision
          (btj-view (update-nth 4 nil *btj-ingress*)) *btj-uncarried-cfg*)
         (list :direct nil))))
; (4) direct ingress names the carrier, not the author.
(must-fail
 (assert-event
  (equal (fn-bpah-view-source-decision
          (btj-view *btj-relay-ingress*) *btj-carried-cfg*)
         (list :direct (pt-o "dtnB")))))
; (5) direct ingress at another generation.
(must-fail
 (assert-event
  (equal (fn-bpah-view-source-decision
          (btj-view (update-nth 5 2 *btj-ingress*)) *btj-carried-cfg*)
         (list :direct (pt-o "dtnB")))))

; fn-bpaj-unlisted-carried-request-is-refused: reachable witness and teeth.
(assert-event (not (fn-bpah-request-trustedp (btj-view *btj-relay-ingress*)
                                             *btj-uncarried-cfg*)))
(assert-event (equal (btj-plan *btj-uncarried-cfg* *btj-relay-ingress*)
                     '(:refused :no-principal)))
(assert-event
 (equal (fn-bpah-source-decision-line (btj-view *btj-relay-ingress*)
                                      *btj-uncarried-cfg*)
        "refused reason=source-not-carried"))
; (1) with the neighbour's own transport row for the source (direct).
(must-fail
 (assert-event (not (fn-bpah-request-trustedp (btj-view *btj-ingress*)
                                              *btj-uncarried-cfg*))))
; (2) with the carries row (the relay carries b, and b is enrolled).
(must-fail
 (assert-event (not (fn-bpah-request-trustedp (btj-view *btj-relay-ingress*)
                                              *btj-carried-cfg*))))

; fn-bpaj-carried-unenrolled-request-is-refused: reachable witness and teeth.
(assert-event (fn-bpaj-carrier-rows
               (fn-cfg-peers (fn-cfg-value *btj-unenrolled-cfg*))
               (fn-cfg-peers (fn-cfg-value *btj-unenrolled-cfg*))
               (pt-o "relay") "dtn://b/"))
(assert-event (not (fn-bpaj-source-enrolled-anywherep
                    (fn-cfg-peers (fn-cfg-value *btj-unenrolled-cfg*))
                    "dtn://b/")))
(assert-event (equal (fn-bpah-view-source-decision
                      (btj-view *btj-relay-ingress*) *btj-unenrolled-cfg*)
                     '(:refused :carried-source-unenrolled)))
(assert-event (equal (btj-plan *btj-unenrolled-cfg* *btj-relay-ingress*)
                     '(:refused :no-principal)))
(defun btj-unenrolledp (cfg ingress)
  (equal (fn-bpah-view-source-decision (btj-view ingress) cfg)
         '(:refused :carried-source-unenrolled)))
(assert-event (btj-unenrolledp *btj-untrusted-author-cfg* *btj-relay-ingress*))
(assert-event (not (fn-bpah-request-trustedp (btj-view *btj-relay-ingress*)
                                             *btj-untrusted-author-cfg*)))
; (1) not a CL ingress.
(must-fail (assert-event (btj-unenrolledp *btj-unenrolled-cfg*
                                          *btj-bad-relay-ingress*)))
; (2) a malformed configuration with the same rows and generation.
(defconst *btj-malformed-cfg*
  (fn-cfg-make 1 (fn-cfg-value-make '(junk) 0 nil nil nil
                   (fn-cfg-peers (fn-cfg-value *btj-unenrolled-cfg*)) nil nil nil)))
(assert-event (not (fn-cfgp *btj-malformed-cfg*)))
(must-fail (assert-event (btj-unenrolledp *btj-malformed-cfg*
                                          *btj-relay-ingress*)))
; (3) another generation.
(must-fail (assert-event (btj-unenrolledp *btj-unenrolled-cfg*
                                          (update-nth 5 2 *btj-relay-ingress*))))
; (4) the neighbour does not carry the source.
(must-fail (assert-event
            (btj-unenrolledp
             (fn-cfg-make 1 (btj-with-relay (fn-cfg-value *pt-cfg*) nil))
             *btj-relay-ingress*)))
; (5) the source is enrolled here.
(must-fail (assert-event (btj-unenrolledp *btj-carried-cfg*
                                          *btj-relay-ingress*)))
; Two boundaries enrolled for one source name no author.
(defconst *btj-ambiguous-cfg*
  (fn-cfg-make 1
    (fn-cfg-apply-delta (fn-cfg-value *btj-carried-cfg*) 1
                        *fn-cfg-default-stamp*
      (fn-cfg-set-peer "dtnB2"
        (append (fn-cfg-peer-rows
                 (fn-cfg-peer-make "dtnB2" "dtnb2.example" '(:bp "dtn://b/")
                                   nil nil
                                   '(:principal "bp-only-no-nntp-principal")))
                (list (fn-cfg-row-make "dtnB2" "bp-trust" "network" 0)))))))
(assert-event (fn-cfgp *btj-ambiguous-cfg*))
(assert-event (btj-unenrolledp *btj-ambiguous-cfg* *btj-relay-ingress*))
