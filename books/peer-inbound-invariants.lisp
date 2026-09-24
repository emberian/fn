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
(include-book "path-update-tail")

(local (in-theory (enable fn-peer-vocabulary fn-path-vocabulary)))

; -----------------------------------------------------------------------------
; K1. Peering refines acceptance

; An unusable observation makes the peer transfer defer before prepare; the
; same invalid stamp makes the post path's prepare an identity transition.
(local
 (defthm fn-peer-invalid-stamp-prepare-is-no-op
   (implies (not (fn-record-stampp stamp))
            (equal (fn-node-prepare node generation msgid payload groups
                                    obligation-id subject evidence charge stamp)
                   node))
   :hints (("Goal" :in-theory (enable fn-node-prepare fn-accept-prepare)))))

(local
 (defthm fn-peer-unusable-observation-gives-invalid-stamp
   (implies (not (natp (fn-record-stamp-of-observation clock)))
            (not (fn-record-stampp (fn-record-stamp-of-observation clock))))
   :hints (("Goal" :use ((:instance
                            fn-record-stamp-of-observation-is-natural-or-unusable
                            (obs clock)))
            :in-theory (enable fn-record-stampp)))))

(local
 (defthm fn-peer-injection-stamp-is-owner-observation
   (equal (nth 8 (fn-peer-injection-arguments
                  node cfg peer msgid octets generation id subject clock))
          (fn-record-stamp-of-observation clock))
   :hints (("Goal" :in-theory (e/d (fn-peer-injection-arguments)
                                   (fn-article-parse
                                    fn-af-relayed-article-check))))))

; The node a transit transfer produces is the node the post path produces on
; the arguments ACL2 computes from the same octets, including clock refusal.
(defthm fn-peer-transfer-is-the-post-path
  (implies (equal (fn-peer-decision-kind
                   (fn-peer-decide-transfer node cfg peer msgid octets clock
                                            id subject))
                  :want)
           (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock generation id subject))
                  (let ((a (fn-peer-injection-arguments node cfg peer msgid octets generation id subject clock)))
                    (fn-node-prepare node (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                                     (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a) (nth 8 a)))))
  :hints (("Goal" :cases ((natp (fn-record-stamp-of-observation clock)))
           :in-theory (e/d (fn-peer-transfer)
                           (fn-peer-decide-transfer fn-node-prepare
                            fn-peer-injection-arguments
                            fn-record-stamp-of-observation)))))

; A transfer the decision refuses, defers or already has leaves the node
; exactly as it was.  -by-definition: the branch test is the hypothesis.
(defthm fn-peer-refused-transfer-leaves-the-node
  (implies (not (equal (fn-peer-decision-kind
                        (fn-peer-decide-transfer node cfg peer msgid octets clock
                                                 id subject))
                       :want))
           (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock generation id subject))
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
                (not (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock generation id subject))
                            node)))
           (equal (fn-pending-groups
                   (fn-state-pending
                    (fn-node-acceptance
                     (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock generation id subject)))))
                  (nth 3 (fn-peer-injection-arguments node cfg peer msgid octets generation id subject clock))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer)
                                  (fn-peer-decide-transfer
                                   fn-peer-injection-arguments
                                   fn-node-prepare))
           :use ((:instance fn-cnode-node-prepare-stages-the-offered-groups
                            (s node)
                            (generation (nth 0 (fn-peer-injection-arguments
                                                node cfg peer msgid octets generation id subject clock)))
                            (msgid (nth 1 (fn-peer-injection-arguments
                                           node cfg peer msgid octets generation id subject clock)))
                            (payload (nth 2 (fn-peer-injection-arguments
                                             node cfg peer msgid octets generation id subject clock)))
                            (groups (nth 3 (fn-peer-injection-arguments
                                            node cfg peer msgid octets generation id subject clock)))
                            (obligation-id (nth 4 (fn-peer-injection-arguments
                                                   node cfg peer msgid octets generation id subject clock)))
                            (subject (nth 5 (fn-peer-injection-arguments
                                             node cfg peer msgid octets generation id subject clock)))
                            (evidence (nth 6 (fn-peer-injection-arguments
                                              node cfg peer msgid octets generation id subject clock)))
                            (charge (nth 7 (fn-peer-injection-arguments
                                            node cfg peer msgid octets generation id subject clock)))
                            (stamp (nth 8 (fn-peer-injection-arguments
                                           node cfg peer msgid octets generation id subject clock))))))))

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
           (and (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock generation id subject))
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
           (and (equal (mv-nth 0 (fn-peer-transfer node cfg peer msgid octets clock generation id subject))
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
            (mv-nth 0 (fn-peer-transfer node cfg peer m octets clock generation id subject))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transfer fn-peer-history-hasp)
                                  (fn-node-prepare fn-peer-decide-transfer
                                   fn-peer-injection-arguments
                                   fn-node-find-binding fn-acceptedp)))))

; -----------------------------------------------------------------------------
; The offer the wire carries is the offer decision (AGENTS.md, the theorem
; subject is the function the host calls)
;
; The host line is books/owner.lisp `fn-own-read', which the host calls once
; per socket read at host/owner-host.lisp `fn-owner-chunk'; it runs
; `fn-served-step' -> `fn-served-dispatch' -> `fn-auth-step' -> `fn-peer-step'
; -> `fn-peer-command', and the IHAVE and CHECK arms of `fn-peer-command' are
; the only two callers of `fn-peer-decide-offer' on this tree.  K3
; (`fn-peer-history-is-have-at-offer', books/peer-inbound-invariants.lisp) is
; about `fn-peer-decide-offer'; these two theorems are the equation between
; that decision and the octets, so the keystone is about the answer a peer
; reads off the socket and not only about a function beside it.
;
; What each one says beyond the definition: the reply is the decision's code
; AND the connection does not enter article mode, so a duplicate offer costs
; the peer no bytes.  Their hypotheses are the connection facts
; `fn-peer-decide-offer' needs before it can reach its history arm -- the
; peer record exists and has an inbound half, the offered identifier is a
; Message-ID -- and the history itself; the teeth in
; tests/acl2/peer-inbound-tests.lisp remove one at a time.

(defthm fn-peer-ihave-of-a-held-message-id-is-435-and-no-article
  (implies (and (fn-peer-session-peer ps)
                (fn-nntp-keywordp keyword "IHAVE")
                (fn-peer-msgid-argp args)
                (fn-cfg-peer-find (fn-peer-session-peer ps)
                                  (fn-cfg-peers (fn-cfg-value (fn-peer-session-cfg ps))))
                (fn-cfg-peer-inbound
                 (fn-cfg-peer-find (fn-peer-session-peer ps)
                                   (fn-cfg-peers (fn-cfg-value (fn-peer-session-cfg ps)))))
                (fn-peer-history-hasp (fn-record-octets-string (car args))
                                      (fn-peer-session-node ps)))
           (and (equal (fn-post-result-effects (fn-peer-command ps keyword args))
                       (fn-peer-single ps "435 duplicate"))
                (equal (fn-peer-session-transfer
                        (fn-post-result-session (fn-peer-command ps keyword args)))
                       (fn-peer-session-transfer ps))))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-command) (:d fn-peer-msgid-argp)
                                   (:d fn-peer-ihave-offer-line))
                                  ((:d fn-peer-decide-offer) (:d fn-peer-single)
                                   (:d fn-peer-echo-reply)
                                   (:d fn-peer-history-hasp) (:d fn-cfg-peer-find)
                                   (:d fn-cfg-peer-inbound)
                                   (:d fn-record-octets-string)
                                   (:d fn-af-message-idp)
                                   (:d fn-nntp-printable-tokenp)
                                   (:d fn-nntp-multi) (:d fn-peer-capability-lines)
                                   (:d fn-nntp-capability-lines)))
           :use ((:instance fn-peer-history-is-have-at-offer
                            (node (fn-peer-session-node ps))
                            (cfg (fn-peer-session-cfg ps))
                            (peer (fn-peer-session-peer ps))
                            (session ps)
                            (msgid (car args))
                            (clock nil)
                            (inflight (fn-peer-session-inflight ps)))))))

(defthm fn-peer-check-of-a-held-message-id-is-438-and-no-offer-outstanding
  (implies (and (fn-peer-session-peer ps)
                (fn-nntp-keywordp keyword "CHECK")
                (fn-peer-msgid-argp args)
                (fn-cfg-peer-find (fn-peer-session-peer ps)
                                  (fn-cfg-peers (fn-cfg-value (fn-peer-session-cfg ps))))
                (fn-cfg-peer-inbound
                 (fn-cfg-peer-find (fn-peer-session-peer ps)
                                   (fn-cfg-peers (fn-cfg-value (fn-peer-session-cfg ps)))))
                (fn-peer-history-hasp (fn-record-octets-string (car args))
                                      (fn-peer-session-node ps)))
           (and (equal (fn-post-result-effects (fn-peer-command ps keyword args))
                       (fn-peer-echo-reply "438 " (car args)))
                (equal (fn-post-result-session (fn-peer-command ps keyword args)) ps)))
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-command) (:d fn-peer-msgid-argp)
                                   (:d fn-peer-check-code) (:d fn-nntp-keywordp)
                                   (:d fn-nntp-string-octets))
                                  ((:d fn-peer-decide-offer) (:d fn-peer-single)
                                   (:d fn-peer-echo-reply)
                                   (:d fn-peer-history-hasp) (:d fn-cfg-peer-find)
                                   (:d fn-cfg-peer-inbound)
                                   (:d fn-record-octets-string)
                                   (:d fn-af-message-idp)
                                   (:d fn-nntp-printable-tokenp)
                                   (:d fn-nntp-upcase-keyword)
                                   (:d fn-nntp-multi) (:d fn-peer-capability-lines)
                                   (:d fn-nntp-capability-lines)))
           :use ((:instance fn-peer-history-is-have-at-offer
                            (node (fn-peer-session-node ps))
                            (cfg (fn-peer-session-cfg ps))
                            (peer (fn-peer-session-peer ps))
                            (session ps)
                            (msgid (car args))
                            (clock nil)
                            (inflight (fn-peer-session-inflight ps)))))))

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

; -----------------------------------------------------------------------------
; What this node stores for an article a peer transferred (RFC 5537 sections
; 3.6 and 3.7; books/path-update.lisp): the received octets with Path
; updated and Xref removed, nothing else.  The subject is
; fn-peer-relayed-octets, which host/owner-host.lisp fn-owner-take calls to
; fill fn-owner-submit-octets, the octets the native drain digests and stores
; (host/native/owner.lisp fnn-owner-drain-one), and which
; fn-peer-injection-arguments stages as the payload fn-node-prepare is given
; (fn-peer-injection-arguments-payload-unfolds).  Each is the article-level
; keystone of books/path-update.lisp at the node's own identity and the peer
; record's expected identity, which is a <path-identity> or none.

; -unfolds: the payload the transfer stages is the relayed octets.  This is
; the correspondence the native drain checks at run time
; (fn-owner-transit-payload against fn-owner-submit-octets).
(defthm fn-peer-injection-arguments-payload-unfolds
  (equal (nth 2 (fn-peer-injection-arguments node cfg peer msgid octets generation id subject clock))
         (fn-peer-relayed-octets cfg peer octets))
  :hints (("Goal" :in-theory (e/d (fn-peer-injection-arguments)
                                  (fn-peer-relayed-octets)))))

; Removing every Path and Xref field from what arrived and from what is
; stored leaves the same octets: every other header, in order, the blank
; line and the body are byte-identical (RFC 5537 section 3.6, last paragraph).
(defthm fn-peer-relayed-octets-change-only-path-and-xref
  (equal (fn-pu-strip (fn-peer-relayed-octets cfg peer octets) nil)
         (fn-pu-strip octets nil))
  :hints (("Goal" :in-theory (e/d (fn-peer-relayed-octets)
                                  (fn-pu-relay-article fn-pu-strip
                                   fn-peer-expected-identity)))))

; A second pass changes nothing: the stored Path already begins with this
; node's identity and no Xref is left, so relaying a stored article again, or
; replaying the record that carries it, reproduces it.
(defthm fn-peer-relayed-octets-are-idempotent
  (equal (fn-peer-relayed-octets cfg peer
                                 (fn-peer-relayed-octets cfg peer octets))
         (fn-peer-relayed-octets cfg peer octets))
  :hints (("Goal" :in-theory (e/d (fn-peer-relayed-octets)
                                  (fn-pu-relay-article
                                   fn-peer-expected-identity)))))

; No Xref is stored (RFC 5537 section 3.7 step 7; specs/peering.md 2.3).
(defthm fn-peer-relayed-octets-carry-no-xref
  (fn-pu-xref-freep (fn-peer-relayed-octets cfg peer octets))
  :hints (("Goal" :in-theory (e/d (fn-peer-relayed-octets)
                                  (fn-pu-relay-article fn-pu-xref-freep
                                   fn-peer-expected-identity)))))

; Every Path field of the stored article begins with this node's own
; <path-identity> and "!" (RFC 5537 section 3.6 step 7, section 3.7 step 6),
; when the node has one; `policy set path-identity' is what gives it one.
(defthm fn-peer-relayed-octets-name-this-node-in-every-path
  (implies (fn-path-identityp (fn-peer-local-identity cfg))
           (fn-pu-path-markedp (fn-peer-relayed-octets cfg peer octets)
                               (fn-peer-local-identity cfg)))
  :hints (("Goal" :in-theory (e/d (fn-peer-relayed-octets)
                                  (fn-pu-relay-article fn-pu-path-markedp
                                   fn-peer-expected-identity
                                   fn-peer-local-identity fn-path-identityp)))))

; RFC 5537 section 3.2.1: the stored Path is the received Path with this
; node's identity, "!", the diagnostic and "!" in front, field line by field
; line; a line that already begins with this node's identity is kept.  The
; diagnostic is books/path.lisp's over the peer record's expected identity
; and the received Path.  With -name-this-node-in-every-path it says the
; update prepends and keeps what arrived.  Covered scope: the first physical
; line of each Path field (books/path-update-tail.lisp).
(defthm fn-peer-relayed-octets-keep-the-received-path-tail
  (implies (fn-path-identityp (fn-peer-local-identity cfg))
           (equal (fn-pu-path-contents (fn-peer-relayed-octets cfg peer octets))
                  (fn-pu-prepend-paths
                   (fn-pu-path-contents octets)
                   (fn-peer-local-identity cfg)
                   (fn-pu-diagnostic-octets
                    (fn-path-diagnostic
                     (fn-pu-expected
                      (fn-peer-expected-identity
                       (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
                     (fn-pu-received-path octets))))))
  :hints (("Goal" :use ((:instance fn-pu-relay-article-keeps-the-received-path-tail
                                   (identity (fn-peer-local-identity cfg))
                                   (expected (fn-peer-expected-identity
                                              (fn-cfg-peer-find
                                               peer (fn-cfg-peers (fn-cfg-value cfg)))))))
           :in-theory (e/d (fn-peer-relayed-octets)
                           (fn-pu-relay-article-keeps-the-received-path-tail
                            fn-pu-relay-article fn-pu-path-contents
                            fn-pu-prepend-paths fn-pu-received-path
                            fn-pu-diagnostic-octets fn-path-diagnostic
                            fn-pu-expected
                            fn-peer-expected-identity
                            fn-peer-local-identity fn-path-identityp)))))

; fn-peer-refused-transfer-leaves-the-node is :rule-classes nil, so it
; designates no rule and (in-theory (disable ...)) on it is a hard error,
; not a no-op.  There is nothing to withdraw; includers cite it by :use.
(in-theory (current-theory :here))
