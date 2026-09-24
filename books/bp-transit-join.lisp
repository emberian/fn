; Finite request-side transit contract.  The application request remains the
; immutable received object; the Store article is the existing peer transit
; projection.  A later FNRJ record pins both before any Store attempt.
(in-package "ACL2")
(include-book "bp-app-handoff")
(include-book "peer-inbound-invariants")
(set-verify-guards-eagerness 0)

; The peer a request is judged under (D23): the neighbour for a direct
; request, the author's own enrollment for a carried one, never the carrier.
(defun fn-bpaj-ingress-peer (cfg ingress source-eid)
  (declare (xargs :guard t))
  (if (fn-bpnf-cl-ingressp ingress)
      (let ((decision (fn-bpaj-carried-source-decision
                       cfg (fn-bpnf-ingress-principal ingress)
                       (fn-bpn-nth 5 ingress) source-eid)))
        (if (fn-bpaj-source-decision-trustedp decision)
            (fn-record-octets-string
             (fn-bpaj-source-decision-principal decision))
          nil))
    nil))

(defun fn-bpaj-transit-msgid (article-octets)
  (declare (xargs :guard t))
  (let* ((parsed (fn-article-parse article-octets))
         (article (if (fn-article-result-okp parsed)
                      (fn-article-result-article parsed) nil))
         (check (if (fn-article-syntax-p article)
                    (fn-af-relayed-article-check article) nil)))
    (if (equal (fn-af-status-kind check) :ok)
        (fn-peer-check-msgid check)
      nil)))

(defun fn-bpaj-transit-plan
    (node cfg ingress source-eid request-octets clock)
  (declare (xargs :guard t))
  (let* ((peer (fn-bpaj-ingress-peer cfg ingress source-eid))
         (request (fn-bpaj-request request-octets))
         (article (and request (fn-bpa-request-article request)))
         (msgid (and article (fn-bpaj-transit-msgid article)))
         (stored (and peer article (fn-peer-relayed-octets cfg peer article)))
         (subject-id (and stored (fn-id-subject-of-payload stored)))
         (subject (and subject-id
                       (fn-record-octets-string (fn-id-text subject-id))))
         (id (and msgid subject-id
                  (fn-record-octets-string
                   (fn-id-text (fn-id-obligation-of msgid subject-id))))))
    (if (not peer) (list :refused :no-principal)
      (if (not (and request msgid (fn-bpaj-request-subjectp request)))
          (list :refused :request)
        (let* ((decision (fn-peer-decide-transfer
                          node cfg peer msgid article clock id subject))
               (args (fn-peer-injection-arguments
                      node cfg peer msgid article
                      (fn-cfg-generation cfg) id subject clock)))
          (case (fn-peer-decision-kind decision)
            (:want
             (list :submit peer msgid article (nth 2 args)
                   (nth 3 args) (nth 6 args) (nth 7 args)
                   id subject))
            (:have
             (list :have peer msgid article (nth 2 args)
                   (nth 3 args) (nth 6 args) (nth 7 args)
                   id subject))
            (:defer (list :busy (fn-peer-decision-reason decision)))
            (otherwise (list :refused (fn-peer-decision-reason decision)))))))))

(defun fn-bpaj-transit-stored-octets (plan)
  (declare (xargs :guard t))
  (if (member-equal (car plan) '(:submit :have))
      (fn-bpaj-nth 4 plan) nil))

; The durable v3 context must bind the *stored* projection, not replay an old
; config against the raw request to rediscover it.  The raw ADU and article
; remain distinct and can still be used for the receipt's original subject.
; The called peer projection itself is certified by
; fn-peer-injection-arguments-payload-unfolds in peer-inbound-invariants.
; A finite witness in bp-transit-join-tests checks that this plan selects that
; projection on a Path-bearing request and separates it from the raw ADU.

(defun fn-bpaj-transit-intent-from-plan
    (cfg inbound-id request-octets generation txid result plan)
  (declare (xargs :guard t))
  (let* ((peer (fn-bpaj-nth 1 plan))
         (record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (r (list :request-transit-intent inbound-id request-octets
                  generation txid result peer
                  (fn-cfg-policy (fn-cfg-value cfg) "path-identity")
                  (and record (fn-cfg-peer-path-identity record))
                  (fn-bpaj-transit-stored-octets plan))))
    (and (member-equal (car plan) '(:submit :have))
         (fn-bpaj-transit-intentp r) r)))

;; -----------------------------------------------------------------------------
;; D23 over the functions the host calls.  host/native/bp-node.lisp's
;; `fnn-bpnode-request-result' asks `fn-owner-bp-request-trustedp' and
;; `fnn-bpnode-receipt-result' asks `fn-owner-bp-receipt-trustedp'
;; (host/bp-native-app-host.lisp: `fn-bpah-request-trustedp' and
;; `fn-bpah-receipt-trustedp' over the live owner configuration); the Store
;; plan is `fn-bpaj-transit-plan', called by `fn-owner-app-plan-install' with
;; the view's ingress (element 4) and source EID (element 6).  The views below
;; have the shape `fn-bpah-pending-view' builds.

(local (defthm fn-bpaj-transit-plan-reads-ingress-only-through-peer
  (implies (equal (fn-bpaj-ingress-peer cfg a src)
                  (fn-bpaj-ingress-peer cfg b src))
           (equal (fn-bpaj-transit-plan node cfg a src req clock)
                  (fn-bpaj-transit-plan node cfg b src req clock)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpaj-transit-plan)
                                             (theory 'minimal-theory))))))

(local (defthm fn-bpaj-carried-source-is-a-string
  (implies (and (fn-cfgp cfg)
                (fn-bpaj-carrier-rows (fn-cfg-peers (fn-cfg-value cfg))
                                      (fn-cfg-peers (fn-cfg-value cfg))
                                      principal source))
           (stringp source))
  :hints (("Goal" :in-theory (e/d (fn-cfg-labelp fn-record-ascii-stringp)
                                  (fn-bpaj-carrier-rows fn-cfgp
                                   fn-bpaj-carried-source-is-a-label))
           :use fn-bpaj-carried-source-is-a-label))))

(local (defthm fn-bpaj-carried-ingress-peer-is-the-authors
  (let* ((d (fn-bpaj-carried-source-decision
             cfg (fn-bpnf-ingress-principal carried)
             (fn-bpn-nth 5 carried) src))
         (author (fn-bpaj-source-decision-principal d)))
    (implies (and (fn-bpnf-cl-ingressp carried)
                  (fn-bpnf-cl-ingressp direct)
                  (equal (car d) :carried)
                  (equal (fn-bpnf-ingress-principal direct) author)
                  (equal (fn-bpn-nth 5 direct) (fn-bpn-nth 5 carried)))
             (equal (fn-bpaj-ingress-peer cfg carried src)
                    (fn-bpaj-ingress-peer cfg direct src))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpaj-carried-decision-is-the-authors-direct-decision
                            (principal (fn-bpnf-ingress-principal carried))
                            (generation (fn-bpn-nth 5 carried))
                            (source src)))
           :in-theory (e/d (fn-bpaj-ingress-peer)
                           (fn-bpaj-carried-decision-is-the-authors-direct-decision
                            fn-bpaj-carried-source-decision
                            fn-bpnf-cl-ingressp fn-bpnf-ingress-principal))))))

; KEYSTONE (D23: a carried request from an allowlisted, enrolled source is
; accepted exactly as a direct one).  When the delivering neighbour's
; decision is `:carried' with author A, a delivery of the same bundle
; directly from A (an ingress naming A at the same generation) is decided
; `:direct' under A, both host trust checks answer the same, and the Store
; plan is the same plan: the peer, inbound scope and transfer decision are
; A's, and the carrier's enrollment does not enter.  The receipt gate is not
; part of this: a carried receipt is judged by the release question
; (bp-release-authority), which the carried list does not answer.
(defthm fn-bpaj-carried-request-is-judged-as-the-authors-direct-request
  (let* ((d (fn-bpaj-carried-source-decision
             cfg (fn-bpnf-ingress-principal carried)
             (fn-bpn-nth 5 carried) src))
         (author (fn-bpaj-source-decision-principal d))
         (cview (list :delivery key class adu carried id src dst))
         (dview (list :delivery key class adu direct id src dst)))
    (implies (and (fn-bpnf-cl-ingressp carried)
                  (fn-bpnf-cl-ingressp direct)
                  (equal (car d) :carried)
                  (equal (fn-bpnf-ingress-principal direct) author)
                  (equal (fn-bpn-nth 5 direct) (fn-bpn-nth 5 carried)))
             (and (equal (fn-bpah-view-source-decision dview cfg)
                         (list :direct author))
                  (fn-bpah-request-trustedp (update-nth 2 :request cview) cfg)
                  (equal (fn-bpah-request-trustedp cview cfg)
                         (fn-bpah-request-trustedp dview cfg))
                  (equal (fn-bpaj-transit-plan node cfg carried src req clock)
                         (fn-bpaj-transit-plan node cfg direct src req
                                               clock)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpaj-carried-decision-is-the-authors-direct-decision
                            (principal (fn-bpnf-ingress-principal carried))
                            (generation (fn-bpn-nth 5 carried))
                            (source src))
                 (:instance fn-bpaj-carried-source-is-a-string
                            (principal (fn-bpnf-ingress-principal carried))
                            (source src))
                 fn-bpaj-carried-ingress-peer-is-the-authors
                 (:instance fn-bpaj-transit-plan-reads-ingress-only-through-peer
                            (a carried) (b direct)))
           :in-theory (e/d (fn-bpah-view-source-decision
                            fn-bpah-request-trustedp
                            fn-bpn-nth)
                           (fn-bpaj-carried-ingress-peer-is-the-authors
                            fn-bpaj-transit-plan-reads-ingress-only-through-peer
                            fn-bpaj-ingress-peer
                            fn-bpaj-carried-decision-is-the-authors-direct-decision
                            fn-bpaj-carried-source-is-a-string
                            fn-bpaj-current-peer-eidp fn-bpaj-carrier-rows
                            fn-bpaj-enrolled-source-names
                            fn-bpnf-cl-ingressp fn-bpnf-ingress-principal
                            fn-bpaj-transit-plan fn-cfgp
                            fn-bpa-decode-exact fn-bpa-result-okp
                            fn-bpa-receiptp fn-bpa-result-message
                            fn-bpa-receipt-issuer fn-bpa-receipt-peer-eid))))
  :rule-classes nil)

; D23: a source the neighbour neither is nor carries.  Its boundary has no
; transport-bp row and no carries row for the source; neither host trust
; check admits the delivery and the Store plan is refused, so the host
; returns `:request-refused' before opening FNRJ or Store
; (host/native/bp-node.lisp `fnn-bpnode-request-result').
(defthm fn-bpaj-unlisted-carried-request-is-refused
  (let* ((principal (fn-bpnf-ingress-principal ingress))
         (rows (fn-cfg-peers (fn-cfg-value cfg)))
         (name (fn-record-octets-string principal))
         (view (list :delivery key class adu ingress id src dst)))
    (implies (and (not (fn-bpaj-boundary-rowp rows name "transport-bp" src 0))
                  (not (fn-bpaj-boundary-rowp rows name "bp-boundary-carries"
                                               src 0)))
             (and (not (fn-bpah-request-trustedp view cfg))
                  (equal (fn-bpaj-transit-plan node cfg ingress src req clock)
                         '(:refused :no-principal)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpaj-unlisted-source-is-not-trusted
                            (principal (fn-bpnf-ingress-principal ingress))
                            (generation (fn-bpn-nth 5 ingress))
                            (source src)))
           :in-theory (e/d (fn-bpah-view-source-decision
                            fn-bpah-request-trustedp
                            fn-bpaj-ingress-peer fn-bpaj-transit-plan
                            fn-bpn-nth)
                           (fn-bpaj-unlisted-source-is-not-trusted
                            fn-bpaj-carried-source-decision
                            fn-bpaj-source-decision-trustedp
                            fn-bpaj-boundary-rowp
                            fn-bpnf-cl-ingressp fn-bpnf-ingress-principal
                            fn-record-octets-string
                            fn-bpa-decode-exact fn-bpa-result-okp
                            fn-bpa-receiptp fn-bpa-result-message
                            fn-bpa-receipt-issuer fn-bpa-receipt-peer-eid))))
  :rule-classes nil)

; D23: a carried source this node has not enrolled.  The neighbour is a
; current carrier of the source, and no boundary here is enrolled with it as
; its transport-bp EID.  The decision is the named refusal, not trusted
; under the carrier, and the Store plan is refused.
(defthm fn-bpaj-carried-unenrolled-request-is-refused
  (let* ((principal (fn-bpnf-ingress-principal ingress))
         (rows (fn-cfg-peers (fn-cfg-value cfg)))
         (view (list :delivery key class adu ingress id src dst)))
    (implies (and (fn-bpnf-cl-ingressp ingress)
                  (fn-cfgp cfg)
                  (equal (fn-bpn-nth 5 ingress) (fn-cfg-generation cfg))
                  (fn-bpaj-carrier-rows rows rows principal src)
                  (not (fn-bpaj-source-enrolled-anywherep rows src)))
             (and (equal (fn-bpah-view-source-decision view cfg)
                         '(:refused :carried-source-unenrolled))
                  (not (fn-bpah-request-trustedp view cfg))
                  (equal (fn-bpaj-transit-plan node cfg ingress src req clock)
                         '(:refused :no-principal)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpaj-carried-unenrolled-source-is-refused
                            (principal (fn-bpnf-ingress-principal ingress))
                            (generation (fn-bpn-nth 5 ingress))
                            (source src))
                 (:instance fn-bpaj-carried-source-is-a-string
                            (principal (fn-bpnf-ingress-principal ingress))
                            (source src)))
           :in-theory (e/d (fn-bpah-view-source-decision
                            fn-bpah-request-trustedp
                            fn-bpaj-ingress-peer fn-bpaj-transit-plan
                            fn-bpn-nth)
                           (fn-bpaj-carried-unenrolled-source-is-refused
                            fn-bpaj-carried-source-is-a-string
                            fn-bpaj-carried-source-decision
                            fn-bpaj-carrier-rows
                            fn-bpaj-source-enrolled-anywherep fn-cfgp
                            fn-bpnf-cl-ingressp fn-bpnf-ingress-principal
                            fn-bpa-decode-exact fn-bpa-result-okp
                            fn-bpa-receiptp fn-bpa-result-message
                            fn-bpa-receipt-issuer fn-bpa-receipt-peer-eid))))
  :rule-classes nil)

; D23: release rows are not carriage.  The transit plan's principal is the
; same under two configurations at one generation that agree once
; `bp-boundary-releases-for' rows are dropped (bp-session-admission's
; `fn-bpaj-source-decision-ignores-release-rows').
(defthm fn-bpaj-ingress-peer-ignores-release-rows
  (implies (and (equal (fn-cfgp cfg1) (fn-cfgp cfg2))
                (equal (fn-cfg-generation cfg1) (fn-cfg-generation cfg2))
                (equal (fn-bpaj-without-release-rows
                        (fn-cfg-peers (fn-cfg-value cfg1)))
                       (fn-bpaj-without-release-rows
                        (fn-cfg-peers (fn-cfg-value cfg2)))))
           (equal (fn-bpaj-ingress-peer cfg1 ingress src)
                  (fn-bpaj-ingress-peer cfg2 ingress src)))
  :hints (("Goal" :in-theory (e/d (fn-bpaj-ingress-peer)
                                  (fn-bpaj-carried-source-decision
                                   fn-bpaj-source-decision-ignores-release-rows
                                   fn-bpaj-without-release-rows))
           :use ((:instance fn-bpaj-source-decision-ignores-release-rows
                            (principal (fn-bpnf-ingress-principal ingress))
                            (generation (fn-bpn-nth 5 ingress))
                            (source src))))))
