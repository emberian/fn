; Finite request-side transit contract.  The application request remains the
; immutable received object; the Store article is the existing peer transit
; projection.  A later FNRJ record pins both before any Store attempt.
(in-package "ACL2")
(include-book "bp-app-handoff")
(include-book "peer-inbound-invariants")
(set-verify-guards-eagerness 0)

(defun fn-bpaj-ingress-peer (cfg ingress source-eid)
  (declare (xargs :guard t))
  (if (and (fn-bpnf-cl-ingressp ingress)
           (fn-bpaj-current-peer-eidp
            cfg (fn-bpnf-ingress-principal ingress)
            (fn-bpn-nth 5 ingress) source-eid))
      (fn-record-octets-string (fn-bpnf-ingress-principal ingress))
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
