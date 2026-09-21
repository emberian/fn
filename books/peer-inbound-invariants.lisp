; fn: the inbound peering keystones (specs/peering.md section 4, K1 and K2,
; and the offer/transfer half of K4, which planning calls this wave's K3).
;
; Every statement here is about the functions the served path and the owner
; call: fn-peer-transfer (the owner's transit port), fn-peer-decide-transfer
; and fn-peer-decide-offer (books/peer-inbound.lisp).  The hypotheses are the
; carried invariants or nothing; a hypothesis the theorem does not need is
; deleted and the deletion is recorded in the spec's status section.

(in-package "ACL2")
(include-book "peer-inbound")

(local (in-theory (enable fn-peer-vocabulary fn-path-vocabulary)))

; -----------------------------------------------------------------------------
; K1. Peering refines acceptance

; The node a transit transfer produces is the node the post path produces on
; the arguments ACL2 computes from the same octets.  No hypothesis: the
; function is that call by construction, so the statement carries none, and
; fn-node-statep enters only through fn-node-prepare's own refusal of a
; non-state (fn-node-prepare-preserves-state, books/node-invariants.lisp).
(defthm fn-peer-transfer-is-the-post-path
  (implies (equal (fn-peer-decision-kind
                   (fn-peer-decide-transfer node cfg peer msgid octets clock
                                            id subject))
                  :want)
           (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock
                                              generation id subject))
                  (let ((a (fn-peer-injection-arguments node cfg peer msgid octets
                                                        generation id subject)))
                    (fn-node-prepare node (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                                     (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a)))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer)
                                  (fn-peer-decide-transfer
                                   fn-peer-injection-arguments
                                   fn-node-prepare)))))

; A transfer the decision refuses, defers or already has leaves the node
; exactly as it was.  -by-definition: the branch test is the hypothesis.
(defthm fn-peer-refused-transfer-leaves-the-node
  (implies (not (equal (fn-peer-decision-kind
                        (fn-peer-decide-transfer node cfg peer msgid octets clock
                                                 id subject))
                       :want))
           (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock
                                              generation id subject))
                  node))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer)
                                  (fn-peer-decide-transfer
                                   fn-peer-injection-arguments
                                   fn-node-prepare))))
  :rule-classes nil)

; The memberships a transit article is staged with are exactly the scope
; groups: the Newsgroups names that match the peer's accept-groups and are
; live at the configuration's generation.  Nothing else is staged, and an
; article none of whose groups is in scope never reaches fn-node-prepare
; (its decision is :refuse :out-of-scope, above).
(defthm fn-peer-transfer-stages-only-scope-groups
  (implies (and (equal (fn-peer-decision-kind
                        (fn-peer-decide-transfer node cfg peer msgid octets clock
                                                 id subject))
                       :want)
                (not (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets
                                                        clock generation id subject))
                            node)))
           (equal (fn-pending-groups
                   (fn-state-pending
                    (fn-node-acceptance
                     (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock
                                                 generation id subject)))))
                  (nth 3 (fn-peer-injection-arguments node cfg peer msgid octets
                                                      generation id subject))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer)
                                  (fn-peer-decide-transfer
                                   fn-peer-injection-arguments
                                   fn-node-prepare))
           :use ((:instance fn-cnode-node-prepare-stages-the-offered-groups
                            (s node)
                            (generation (nth 0 (fn-peer-injection-arguments
                                                node cfg peer msgid octets
                                                generation id subject)))
                            (msgid (nth 1 (fn-peer-injection-arguments
                                           node cfg peer msgid octets
                                           generation id subject)))
                            (payload (nth 2 (fn-peer-injection-arguments
                                             node cfg peer msgid octets
                                             generation id subject)))
                            (groups (nth 3 (fn-peer-injection-arguments
                                            node cfg peer msgid octets
                                            generation id subject)))
                            (obligation-id (nth 4 (fn-peer-injection-arguments
                                                   node cfg peer msgid octets
                                                   generation id subject)))
                            (subject (nth 5 (fn-peer-injection-arguments
                                             node cfg peer msgid octets
                                             generation id subject)))
                            (evidence (nth 6 (fn-peer-injection-arguments
                                              node cfg peer msgid octets
                                              generation id subject)))
                            (charge (nth 7 (fn-peer-injection-arguments
                                            node cfg peer msgid octets
                                            generation id subject))))))))

; Every group staged through transit is live at the configuration's
; generation: fn-peer-scope-groups admits nothing else.
(defthm fn-peer-scope-groups-are-live
  (implies (member-equal name (fn-peer-scope-groups groups record cfg))
           (fn-cfg-group-livep (fn-cfg-value cfg) (fn-cfg-generation cfg) name))
  :hints (("Goal" :induct (fn-peer-scope-groups groups record cfg)
           :in-theory (e/d (fn-peer-scope-groups)
                           (fn-cfg-group-livep fn-peer-wildmat-matchp)))))

; -----------------------------------------------------------------------------
; K2. Loop freedom (inbound half)

; An article whose Path already names this node is never accepted through
; transit.  The spec's statement carried fn-node-statep, fn-cfgp and the
; parse hypothesis; none is needed (every cond arm before the loop arm is a
; refusal or a :have, and an unparsable article is :refuse :proto-article),
; so the theorem carries none and the teeth separate the reasons instead.
(defthm fn-peer-loop-is-refused
  (implies (fn-path-names-p
            (fn-af-path-field-value
             (fn-article-result-article (fn-article-parse octets)))
            (fn-peer-local-identity cfg))
           (and (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock
                                                   generation id subject))
                       node)
                (member-equal (fn-peer-decision-kind
                               (fn-peer-decide-transfer node cfg peer msgid octets
                                                        clock id subject))
                              '(:refuse :have))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer fn-peer-decide-transfer)
                                  (fn-node-prepare fn-peer-injection-arguments
                                   fn-af-path-field-value fn-path-names-p
                                   fn-peer-local-identity fn-article-parse
                                   fn-article-result-article
                                   fn-article-result-okp fn-article-syntax-p
                                   fn-af-proto-article-check fn-af-relayed-article-check
                                   fn-af-status-kind
                                   fn-af-message-id-equalp fn-af-message-idp
                                   fn-path-date-presentp fn-peer-history-hasp
                                   fn-peer-scope-groups fn-peer-stagedp
                                   fn-retain-admissiblep fn-cfg-peer-find
                                   fn-cfg-peer-inbound
                                   fn-cfg-peer-inbound-max-octets
                                   fn-record-octets-string
                                   fn-charge-for-payload fn-peer-evidence
                                   fn-peer-check-msgid fn-peer-check-groups)))))

; -----------------------------------------------------------------------------
; K3 (this wave). Duplicate suppression: a Message-ID in the history is
; never accepted, at offer and at transfer.

(defthm fn-peer-history-is-refused-at-offer
  (implies (fn-peer-history-hasp (fn-record-octets-string msgid) node)
           (member-equal (fn-peer-decision-kind
                          (fn-peer-decide-offer node cfg peer session msgid clock
                                                inflight))
                         '(:refuse :have)))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-offer)
                                  (fn-peer-history-hasp fn-cfg-peer-find
                                   fn-cfg-peer-inbound fn-af-message-idp
                                   fn-record-octets-string)))))

; With the connection and the offered identifier in order, the offer is
; exactly :have :history (the duplicate answer, 435/438).
(defthm fn-peer-history-is-have-at-offer
  (implies (and (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))
                (fn-cfg-peer-inbound
                 (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
                (fn-af-message-idp msgid)
                (fn-peer-history-hasp (fn-record-octets-string msgid) node))
           (equal (fn-peer-decide-offer node cfg peer session msgid clock inflight)
                  (fn-peer-decision :have :history)))
  :hints (("Goal" :in-theory (e/d (fn-peer-decide-offer)
                                  (fn-peer-history-hasp fn-cfg-peer-find
                                   fn-cfg-peer-inbound fn-af-message-idp
                                   fn-record-octets-string)))))

(defthm fn-peer-history-is-refused-at-transfer
  (implies (fn-peer-history-hasp (fn-record-octets-string msgid) node)
           (and (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock
                                                   generation id subject))
                       node)
                (member-equal (fn-peer-decision-kind
                               (fn-peer-decide-transfer node cfg peer msgid octets
                                                        clock id subject))
                              '(:refuse :have))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer fn-peer-decide-transfer)
                                  (fn-node-prepare fn-peer-injection-arguments
                                   fn-af-path-field-value fn-path-names-p
                                   fn-peer-local-identity fn-article-parse
                                   fn-article-result-article
                                   fn-article-result-okp fn-article-syntax-p
                                   fn-af-proto-article-check fn-af-relayed-article-check
                                   fn-af-status-kind
                                   fn-af-message-id-equalp fn-af-message-idp
                                   fn-path-date-presentp fn-peer-history-hasp
                                   fn-peer-scope-groups fn-peer-stagedp
                                   fn-retain-admissiblep fn-cfg-peer-find
                                   fn-cfg-peer-inbound
                                   fn-cfg-peer-inbound-max-octets
                                   fn-record-octets-string
                                   fn-charge-for-payload fn-peer-evidence
                                   fn-peer-check-msgid fn-peer-check-groups)))))

; The history only grows: a binding is never removed by a transfer
; (fn-node-prepare-preserves-bindings, books/node-invariants.lisp), so a
; Message-ID that is :have stays :have across every later transit accept.
(defthm fn-peer-history-grows-under-transfer
  (implies (and (fn-node-statep node)
                (consp (fn-node-find-binding msgid (fn-node-bindings node))))
           (fn-peer-history-hasp
            msgid
            (mv-nth 0 (fn-peer-transfer node cfg peer m octets clock
                                        generation id subject))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer fn-peer-history-hasp)
                                  (fn-node-prepare fn-peer-decide-transfer
                                   fn-peer-injection-arguments
                                   fn-node-find-binding fn-acceptedp)))))

; -----------------------------------------------------------------------------
; The provenance of a transit acceptance
;
; The typed record and the string the transit path writes today are the same
; provenance: the record's LEGACY rendering is, for every peer name and every
; configuration, exactly what `fn-peer-evidence' answers.  This is the
; subject-equating theorem of AGENTS.md's first assurance rule for the
; provenance row: `fn-peer-transit-provenance' is not a sibling API, it is
; the same value the host line at `books/peer-inbound.lisp:323'
; (`fn-peer-injection-arguments', the seventh element it hands
; `fn-node-prepare') already carries, with the transit command, the Path
; diagnostic and the configuration generation still attached.
;
; What the equation does NOT say: that the STORE holds the record.  It holds
; the rendering, because the transit command is not in scope at
; `fn-peer-decide-transfer' (no `kind' formal) --- the open item recorded in
; planning/lanes/HANDOFF-w10-provenance.md.

(defthm fn-peer-evidence-is-the-legacy-rendering
  (equal (fn-prov-render (fn-peer-transit-provenance peer cfg kind diagnostic))
         (fn-peer-evidence peer cfg))
  :hints (("Goal" :in-theory (enable fn-peer-transit-provenance
                                     fn-peer-evidence))))

(defthm fn-peer-transit-provenance-is-a-provenance
  (fn-provp (fn-peer-transit-provenance peer cfg kind diagnostic))
  :hints (("Goal" :in-theory (enable fn-peer-transit-provenance))))

(defthm fn-peer-transit-provenance-names-the-peer
  (implies (stringp peer)
           (and (equal (fn-prov-kind
                        (fn-peer-transit-provenance peer cfg kind diagnostic))
                       :peer-transit)
                (equal (fn-prov-transit-peer
                        (fn-peer-transit-provenance peer cfg kind diagnostic))
                       peer)))
  :hints (("Goal" :in-theory (enable fn-peer-transit-provenance))))

; The wire form the store may hold, and the record it reads back as.
(defthm fn-peer-transit-evidence-round-trips
  (implies (fn-prov-durablep
            (fn-peer-transit-provenance peer cfg kind diagnostic))
           (equal (fn-prov-of-wire
                   (fn-peer-transit-evidence peer cfg kind diagnostic))
                  (fn-peer-transit-provenance peer cfg kind diagnostic)))
  :hints (("Goal" :in-theory (e/d (fn-peer-transit-evidence)
                                  (fn-peer-transit-provenance)))))

; fn-peer-refused-transfer-leaves-the-node is :rule-classes nil, so it
; designates no rule and (in-theory (disable ...)) on it is a hard error,
; not a no-op.  There is nothing to withdraw; includers cite it by :use.
(in-theory (current-theory :here))
