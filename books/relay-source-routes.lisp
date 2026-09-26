; fn: relaying cannot change who wrote an article -- the routes (PRF-127).
;
; books/relay-source.lisp proves the parser join: for every article the
; parser accepts, fn-hc-authored-source is a function of the octets with
; Path and Xref stripped (fn-rs-authored-source-is-the-walk).  This book
; composes it with the transit representation and the two transfer
; decisions the host calls:
;
;   - fn-peer-relayed-octets, which host/owner-host.lisp fn-owner-take
;     stages for an NNTP transit article, keeps the authored source
;     whenever the parser accepts both (fn-rs-relaying-keeps-the-authored-
;     source, with fn-peer-relayed-octets-change-only-path-and-xref);
;   - a transfer fn-peer-decide-transfer wants is one the parser accepts
;     before and after the Path update, so the payload
;     fn-peer-injection-arguments stages keeps the authored source with no
;     further hypothesis (fn-rs-a-wanted-transfer-keeps-the-authored-source);
;   - a BP request fn-bpaj-transit-plan submits, which
;     host/bp-native-app-host.lisp fn-owner-app-plan-install calls, stores
;     octets whose authored source is the request article's
;     (fn-rs-a-bp-transit-keeps-the-authored-source).

(in-package "ACL2")
(include-book "relay-source")
(include-book "bp-transit-join")

; -----------------------------------------------------------------------------
; The keystone at the representation: B's stored octets have A's authored
; source whenever both parse.  The subject is fn-peer-relayed-octets, which
; host/owner-host.lisp fn-owner-take stages for a transit article.

(defthm fn-rs-relaying-keeps-the-authored-source
  (implies (and (fn-article-result-okp (fn-article-parse octets))
                (fn-article-result-okp
                 (fn-article-parse (fn-peer-relayed-octets cfg peer octets))))
           (equal (fn-hc-authored-source
                   (fn-article-result-article
                    (fn-article-parse (fn-peer-relayed-octets cfg peer octets))))
                  (fn-hc-authored-source
                   (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal" :in-theory (union-theories '(fn-peer-relayed-octets-change-only-path-and-xref)
                                             (theory 'minimal-theory))
           :use ((:instance fn-rs-authored-source-is-the-walk (y octets))
                 (:instance fn-rs-authored-source-is-the-walk
                  (y (fn-peer-relayed-octets cfg peer octets)))))))

; -----------------------------------------------------------------------------
; The transfer decision wants an article only when the parser accepts it
; before and after the Path update, so the two hypotheses above are what
; the node already checks.

(defthm fn-rs-a-transfer-is-wanted-only-if-both-parse
  (implies (not (and (fn-article-result-okp (fn-article-parse octets))
                     (fn-article-result-okp
                      (fn-article-parse (fn-peer-relayed-octets cfg peer octets)))))
           (not (equal (fn-peer-decision-kind
                        (fn-peer-decide-transfer node cfg peer msgid octets clock id subject))
                       :want)))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-transfer fn-peer-decision fn-peer-decision-kind)
                                  (fn-article-parse fn-peer-relayed-octets fn-article-syntax-p
                                   fn-af-relayed-article-check fn-peer-history-hasp fn-path-names-p
                                   fn-peer-scope-groups fn-peer-stagedp fn-retain-admissiblep
                                   fn-af-message-idp fn-af-message-id-equalp fn-path-date-presentp
                                   fn-cfg-peer-find fn-af-status-kind fn-peer-check-msgid fn-peer-check-groups
                                   fn-charge-for-payload fn-peer-evidence fn-af-path-field-value
                                   fn-peer-local-identity)))))

(defthm fn-rs-a-wanted-transfer-keeps-the-authored-source
  (let ((stored (nth 2 (fn-peer-injection-arguments node cfg peer msgid octets
                                                    generation id subject clock))))
    (implies (equal (fn-peer-decision-kind
                     (fn-peer-decide-transfer node cfg peer msgid octets clock id subject))
                    :want)
             (and (fn-article-result-okp (fn-article-parse octets))
                  (fn-article-result-okp (fn-article-parse stored))
                  (equal (fn-hc-authored-source
                          (fn-article-result-article (fn-article-parse stored)))
                         (fn-hc-authored-source
                          (fn-article-result-article (fn-article-parse octets)))))))
  :hints (("Goal" :in-theory (union-theories '(fn-rs-relaying-keeps-the-authored-source
                                               fn-peer-injection-arguments-payload-unfolds)
                                             (theory 'minimal-theory))
           :use (fn-rs-a-transfer-is-wanted-only-if-both-parse))))

; -----------------------------------------------------------------------------
; The BP route: a request the planner submits (host/bp-native-app-host.lisp
; fn-owner-app-plan-install) is stored as the relayed octets of the request's
; article, and both parse; so the stored authored source is the article's.

(local
 (defthm fn-rs-a-submitted-transit-plan-unfolds
   (let ((plan (fn-bpaj-transit-plan node cfg ingress source-eid request-octets clock))
         (article (fn-bpa-request-article (fn-bpaj-request request-octets))))
     (implies (equal (car plan) :submit)
              (and (fn-article-result-okp (fn-article-parse article))
                   (fn-article-result-okp
                    (fn-article-parse
                     (fn-peer-relayed-octets cfg (fn-bpaj-ingress-peer cfg ingress source-eid) article)))
                   (equal (fn-bpaj-transit-stored-octets plan)
                          (fn-peer-relayed-octets cfg (fn-bpaj-ingress-peer cfg ingress source-eid) article)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-bpaj-transit-plan fn-bpaj-transit-stored-octets)
                                   (fn-article-parse fn-peer-relayed-octets fn-peer-decide-transfer
                                    fn-peer-injection-arguments fn-hc-authored-source
                                    fn-bpaj-ingress-peer fn-bpaj-request fn-bpa-request-article
                                    fn-bpaj-transit-msgid fn-id-subject-of-payload (:e fn-id-subject-of-payload)
                                    fn-id-obligation-of fn-id-text fn-record-octets-string
                                    fn-bpaj-request-subjectp fn-cfg-generation fn-article-result-okp
                                    fn-article-result-article))))))

(defthm fn-rs-a-bp-transit-keeps-the-authored-source
  (let ((plan (fn-bpaj-transit-plan node cfg ingress source-eid request-octets clock))
        (article (fn-bpa-request-article (fn-bpaj-request request-octets))))
    (implies (equal (car plan) :submit)
             (and (fn-article-result-okp (fn-article-parse article))
                  (fn-article-result-okp
                   (fn-article-parse (fn-bpaj-transit-stored-octets plan)))
                  (equal (fn-hc-authored-source
                          (fn-article-result-article
                           (fn-article-parse (fn-bpaj-transit-stored-octets plan))))
                         (fn-hc-authored-source
                          (fn-article-result-article (fn-article-parse article)))))))
  :hints (("Goal" :in-theory (union-theories '(fn-rs-relaying-keeps-the-authored-source)
                                             (theory 'minimal-theory))
           :use (fn-rs-a-submitted-transit-plan-unfolds))))
