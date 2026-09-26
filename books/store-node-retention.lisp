;; P9 over the functions the host calls (plan 2026-09-22 s2.1 P9, T11;
;; audit planning/v0-audit-p7-p9.md s P9).
;;
;; Refusal.  The host prepares an article through `fn-store-sn-prepare'
;; (host/store-node-host.lisp:438; the native bridge `fnn-bridge-prepare',
;; host/native/io.lisp:810, calls it), which calls `fn-spc-prepare' at
;; host/store-node-host.lisp:472 and answers :refused when the returned state
;; is the input (:475).  `fn-spc-prepare' reaches `fn-node-prepare' through
;; `fn-sn-prepare-node'; `fn-node-prepare' refuses on its own
;; `fn-retain-admissiblep' test (books/node.lisp:185) before it would call
;; `fn-retain-admit'.  The theorems below state the refusal over
;; `fn-node-prepare' and `fn-spc-prepare', and equate `fn-node-prepare''s
;; retention refusal with `fn-retain-admit''s no-op, so RET-002's keystone
;; `fn-retain-admit-refuses-unaffordable-obligation' is reached through the
;; called function by a named theorem instead of by prose.
;;
;; Keeping.  The host completes through `fn-sn-finish'
;; (host/store-node-host.lisp:546).  No finish arm removes an accepted article
;; (the article is the value with its payload octets), and an obligation leaves
;; the ledger only on the retention-release arm whose event matches it exactly.
;; Store retention events release only :forward obligations, so an article's
;; :archive obligation is never released by any finish arm.
(in-package "ACL2")
(include-book "store-prepare-correspondence")
(include-book "store-node-invariants")
(include-book "node-retention-transitions")
(include-book "node-invariants")
(include-book "retention-invariants")

; -----------------------------------------------------------------------------
; Refusal of an unaffordable obligation

; Keystone at the node: the capacity comparison alone makes prepare a no-op,
; whatever the node's other fields hold.

(defthm fn-node-prepare-refuses-unaffordable-obligation
  (implies (> (+ (fn-retain-reserved (fn-node-retention s)) charge)
              (fn-retain-capacity (fn-node-retention s)))
           (equal (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge stamp)
                  s))
  :hints (("Goal" :in-theory (enable fn-node-prepare fn-retain-admissiblep))))

; `fn-retain-admit' leaves the ledger unchanged exactly when its admission
; test fails.  With the theorem after it this makes `fn-node-prepare''s
; refusal test and `fn-retain-admit''s no-op one decision.

(defthm fn-retain-admit-is-a-no-op-exactly-when-inadmissible
  (iff (equal (fn-retain-admit r id subject kind evidence charge) r)
       (not (fn-retain-admissiblep r id subject kind evidence charge)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-retain-admit) (fn-retain-admissiblep))
           :cases ((fn-retain-admissiblep r id subject kind evidence charge)))
          ("Subgoal 1" :in-theory (e/d (fn-retain-admit)
                                       (fn-retain-admissiblep))
           :use ((:instance fn-retain-admissiblep (s r))
                 (:instance fn-retain-reserved (x r))
                 (:instance fn-retain-reserved
                            (x (fn-retain-admit r id subject kind evidence charge)))))))

; The equation assurance rule 1 asks for: whenever `fn-retain-admit' would
; refuse the obligation `fn-node-prepare' is given, `fn-node-prepare' refuses.
; So RET-002's keystone (retention-invariants.lisp) concludes, through this
; theorem, that the called function refuses.

(defthm fn-node-prepare-refuses-whatever-retain-admit-refuses
  (implies (equal (fn-retain-admit (fn-node-retention s) obligation-id subject
                                   :archive evidence charge)
                  (fn-node-retention s))
           (equal (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge stamp)
                  s))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                                  (fn-retain-admissiblep fn-retain-admit))
           :use ((:instance fn-retain-admit-is-a-no-op-exactly-when-inadmissible
                            (r (fn-node-retention s)) (id obligation-id)
                            (kind :archive))))))

; The host-called prepare.  The node `fn-sn-prepare-node' builds from an
; unaffordable record carries no stage, so the record does not bind and the
; live store state is returned unchanged; the host answers :refused.

(local
 (defthm fn-snrt-advance-keeps-retention-and-stage
   (and (equal (fn-node-retention (fn-replay-advance-txid node txid))
               (fn-node-retention node))
        (implies (not (consp (fn-node-stage node)))
                 (not (consp (fn-node-stage (fn-replay-advance-txid node txid))))))
   :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))
(local
 (defthm fn-snrt-unaffordable-record-does-not-bind
   (implies (and (null (fn-node-stage node))
                 (> (+ (fn-retain-reserved (fn-node-retention node))
                       (fn-record-charge record))
                    (fn-retain-capacity (fn-node-retention node))))
            (not (fn-sn-record-bindsp (fn-sn-prepare-node node record) record)))
   :hints (("Goal" :in-theory (e/d (fn-sn-prepare-node fn-sn-record-bindsp
                                    fn-node-pending-matchesp)
                                   (fn-node-prepare fn-replay-advance-txid))
            :use ((:instance fn-snrt-advance-keeps-retention-and-stage
                   (txid (fn-record-txid record)))
                  (:instance fn-node-prepare-refuses-unaffordable-obligation
                   (s (fn-replay-advance-txid node (fn-record-txid record)))
                   (generation (fn-record-generation record))
                   (msgid (fn-record-msgid record))
                   (payload (fn-record-payload record))
                   (groups (fn-record-groups record))
                   (obligation-id (fn-record-obligation-id record))
                   (subject (fn-record-content-subject record))
                   (evidence (fn-record-release-evidence record))
                   (charge (fn-record-charge record))
                   (stamp (fn-record-stamp record))))))))
(defthm fn-spc-prepare-refuses-unaffordable-obligation
  (implies (> (+ (fn-retain-reserved (fn-node-retention (fn-sn-node s)))
                 (fn-record-charge record))
              (fn-retain-capacity (fn-node-retention (fn-sn-node s))))
           (equal (fn-spc-prepare s record) s))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare)
                                  (fn-sn-prepare-node fn-sn-record-bindsp
                                   fn-sn-statep fn-spc-stage-record fn-sn-update)))))

; The same over the replaying specification `fn-sn-prepare', which
; `fn-spc-prepare-equals-specification-under-relation' equates to the host's.

(defthm fn-sn-prepare-refuses-unaffordable-obligation
  (implies (> (+ (fn-retain-reserved (fn-node-retention (fn-sn-node s)))
                 (fn-record-charge record))
              (fn-retain-capacity (fn-node-retention (fn-sn-node s))))
           (equal (fn-sn-prepare s record) s))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare)
                                  (fn-sn-prepare-node fn-sn-record-bindsp
                                   fn-sn-statep fn-sf-prepare-record fn-sn-update)))))

; -----------------------------------------------------------------------------
; Keeping until release: node steps

(local
 (defthm fn-snrt-complete-keeps-articles
   (implies (member-equal a (fn-state-articles (fn-node-acceptance s)))
            (member-equal a (fn-state-articles
                             (fn-node-acceptance
                              (fn-node-complete s txid generation status)))))
   :hints (("Goal" :in-theory (enable fn-node-complete fn-accept-complete
                                      fn-install-pending fn-clear-pending)))))
(local
 (defthm fn-snrt-complete-keeps-pins
   (implies (and (fn-node-statep s)
                 (member-equal p (fn-retain-pins (fn-node-retention s))))
            (member-equal p (fn-retain-pins
                             (fn-node-retention
                              (fn-node-complete s txid generation status)))))
   :hints (("Goal" :in-theory (e/d (fn-node-complete fn-node-pending-matchesp)
                                   (fn-accept-complete fn-node-stagep))
            :use ((:instance fn-node-stage-retention-pins
                   (acceptance (fn-node-acceptance s))
                   (committed (fn-node-retention s))
                   (stage (fn-node-stage s)))
                  (:instance fn-node-statep (x s)))))))
(local
 (defthm fn-snrt-remove-id-keeps-other-pins
   (implies (and (member-equal p pins)
                 (not (equal (fn-retain-obligation-id p) id)))
            (member-equal p (fn-retain-remove-id id pins)))
   :hints (("Goal" :in-theory (enable fn-retain-remove-id)))))
(local
 (defthm fn-snrt-member-pin-has-member-id
   (implies (member-equal p pins)
            (member-equal (fn-retain-obligation-id p)
                          (fn-retain-obligation-ids pins)))
   :hints (("Goal" :in-theory (enable fn-retain-obligation-ids)))))
(local
 (defthm fn-snrt-find-id-of-unique-member
   (implies (and (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
                 (member-equal p pins))
            (equal (fn-retain-find-id (fn-retain-obligation-id p) pins) p))
   :hints (("Goal" :in-theory (enable fn-retain-find-id fn-retain-obligation-ids
                                      fn-retain-no-duplicatesp)))))
(local
 (defthm fn-snrt-retention-of-apply-retention-event
   (implies (consp (fn-replay-apply-retention-event node event))
            (equal (fn-node-retention (fn-replay-apply-retention-event node event))
                   (if (equal (fn-store-event-kind event) :undertake)
                       (fn-retain-admit (fn-node-retention node)
                                        (fn-store-event-obligation-id event)
                                        (fn-store-event-subject event) :forward
                                        (fn-store-event-evidence event)
                                        (fn-store-event-charge event))
                     (fn-retain-release (fn-node-retention node)
                                        (fn-store-event-obligation-id event)
                                        (fn-store-event-subject event) :forward
                                        (fn-store-event-evidence event)))))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-retention-event
                                    fn-replay-complete-retention)
                                   (fn-retain-admit fn-retain-release
                                    fn-retain-admissiblep fn-node-statep))))))
(local
 (defthm fn-snrt-retention-event-removes-only-its-matching-release
   (implies (and (fn-node-statep node)
                 (consp (fn-replay-apply-retention-event node event))
                 (member-equal p (fn-retain-pins (fn-node-retention node)))
                 (not (member-equal
                       p (fn-retain-pins
                          (fn-node-retention
                           (fn-replay-apply-retention-event node event))))))
            (and (not (equal (fn-store-event-kind event) :undertake))
                 (fn-retain-matching-releasep
                  p (fn-store-event-obligation-id event)
                  (fn-store-event-subject event) :forward
                  (fn-store-event-evidence event))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-retain-admit fn-retain-release)
                                   (fn-replay-apply-retention-event
                                    fn-retain-admissiblep fn-node-statep
                                    fn-retain-statep fn-retain-find-id
                                    fn-retain-remove-id
                                    fn-retain-matching-releasep))
            :use (fn-nrt-node-statep-retention
                  (:instance fn-nrt-statep-no-duplicate-pins
                             (s (fn-node-retention node)))
                  (:instance fn-snrt-remove-id-keeps-other-pins
                             (pins (fn-retain-pins (fn-node-retention node)))
                             (id (fn-store-event-obligation-id event)))
                  (:instance fn-snrt-find-id-of-unique-member
                             (pins (fn-retain-pins (fn-node-retention node)))))))))
(local
 (defthm fn-snrt-prepare-keeps-retention
   (equal (fn-node-retention
           (fn-node-prepare s generation msgid payload groups
                            obligation-id subject evidence charge stamp))
          (fn-node-retention s))
   :hints (("Goal" :in-theory (enable fn-node-prepare)))))
(local
 (defthm fn-snrt-prepare-keeps-articles
   (implies (fn-node-statep s)
            (equal (fn-state-articles
                    (fn-node-acceptance
                     (fn-node-prepare s generation msgid payload groups
                                      obligation-id subject evidence charge stamp)))
                   (fn-state-articles (fn-node-acceptance s))))
   :hints (("Goal" :in-theory (enable fn-node-prepare fn-accept-prepare)))))
(local
 (defthm fn-snrt-prepare-then-complete-keeps-articles-and-pins
   (implies (fn-node-statep n)
            (and (implies (member-equal a (fn-state-articles (fn-node-acceptance n)))
                          (member-equal a (fn-state-articles
                                           (fn-node-acceptance
                                            (fn-node-complete
                                             (fn-node-prepare n generation msgid payload groups
                                                              obligation-id subject evidence charge stamp)
                                             txid gen status)))))
                 (implies (member-equal p (fn-retain-pins (fn-node-retention n)))
                          (member-equal p (fn-retain-pins
                                           (fn-node-retention
                                            (fn-node-complete
                                             (fn-node-prepare n generation msgid payload groups
                                                              obligation-id subject evidence charge stamp)
                                             txid gen status)))))))
   :hints (("Goal" :in-theory '(fn-snrt-prepare-keeps-retention
                                fn-snrt-prepare-keeps-articles
                                fn-node-prepare-preserves-state)
            :use ((:instance fn-snrt-complete-keeps-articles
                   (s (fn-node-prepare n generation msgid payload groups
                                       obligation-id subject evidence charge stamp))
                   (generation gen))
                  (:instance fn-snrt-complete-keeps-pins
                   (s (fn-node-prepare n generation msgid payload groups
                                       obligation-id subject evidence charge stamp))
                   (generation gen)))))))
(local
 (defthm fn-snrt-matching-stage-keeps-pins
   (implies (and (fn-node-statep n)
                 (fn-node-pending-matchesp n txid gen)
                 (member-equal p (fn-retain-pins (fn-node-retention n))))
            (member-equal p (fn-retain-pins
                             (fn-node-stage-retention (fn-node-stage n)))))
   :hints (("Goal" :in-theory (e/d (fn-node-pending-matchesp) (fn-node-stagep))
            :use ((:instance fn-node-stage-retention-pins
                   (acceptance (fn-node-acceptance n))
                   (committed (fn-node-retention n))
                   (stage (fn-node-stage n)))
                  (:instance fn-node-statep (x n)))))))
(local
 (defthm fn-snrt-apply-record-keeps-articles-and-pins
   (implies (and (fn-node-statep node)
                 (not (fn-store-retention-event-p record))
                 (consp (fn-replay-apply-record node record)))
            (and (implies (member-equal a (fn-state-articles (fn-node-acceptance node)))
                          (member-equal a (fn-state-articles
                                           (fn-node-acceptance
                                            (fn-replay-apply-record node record)))))
                 (implies (member-equal p (fn-retain-pins (fn-node-retention node)))
                          (member-equal p (fn-retain-pins
                                           (fn-node-retention
                                            (fn-replay-apply-record node record)))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-record
                                    fn-replay-apply-identity-neutral)
                                   (fn-node-statep fn-node-prepare fn-node-complete
                                    fn-replay-advance-txid
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p fn-cpe-eventp
                                    fn-th-topic-eventp fn-record-p
                                    fn-replay-composite-record
                                    fn-node-pending-matchesp
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary
                                    fn-snrt-prepare-then-complete-keeps-articles-and-pins))
            :use ((:instance fn-replay-advance-preserves-node-statep (recorded-txid (fn-store-event-txid record)))
                  (:instance fn-snrt-prepare-then-complete-keeps-articles-and-pins
                   (n (fn-replay-advance-txid node (fn-store-event-txid record)))
                   (generation (fn-record-generation (fn-replay-composite-record record)))
                   (msgid (fn-record-msgid (fn-replay-composite-record record)))
                   (payload (fn-record-payload (fn-replay-composite-record record)))
                   (groups (fn-record-groups (fn-replay-composite-record record)))
                   (obligation-id (fn-record-obligation-id (fn-replay-composite-record record)))
                   (subject (fn-record-content-subject (fn-replay-composite-record record)))
                   (evidence (fn-record-release-evidence (fn-replay-composite-record record)))
                   (charge (fn-record-charge (fn-replay-composite-record record)))
                   (stamp (fn-record-stamp (fn-replay-composite-record record)))
                   (txid (fn-record-txid (fn-replay-composite-record record)))
                   (gen (fn-record-generation (fn-replay-composite-record record)))
                   (status :durable))
                  (:instance fn-snrt-prepare-then-complete-keeps-articles-and-pins
                   (n (fn-replay-advance-txid node (fn-store-event-txid record)))
                   (generation (fn-record-generation record))
                   (msgid (fn-record-msgid record))
                   (payload (fn-record-payload record))
                   (groups (fn-record-groups record))
                   (obligation-id (fn-record-obligation-id record))
                   (subject (fn-record-content-subject record))
                   (evidence (fn-record-release-evidence record))
                   (charge (fn-record-charge record))
                   (stamp (fn-record-stamp record))
                   (txid (fn-record-txid record))
                   (gen (fn-record-generation record))
                   (status :durable)))))))
(local
 (defthm fn-snrt-retention-event-keeps-articles
   (equal (fn-state-articles
           (fn-node-acceptance (fn-replay-apply-retention-event node event)))
          (if (consp (fn-replay-apply-retention-event node event))
              (fn-state-articles (fn-node-acceptance node))
            nil))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-retention-event
                                    fn-replay-complete-retention
                                    fn-replay-node-with-retention)
                                   (fn-retain-admit fn-retain-release
                                    fn-retain-admissiblep fn-node-statep))))))

; -----------------------------------------------------------------------------
; Keeping until release: the node `fn-sn-finish' leaves, arm by arm, with the
; record codec and the event recognizers closed.

(local
 (defthm fn-snrt-node-of-make-v6
   (equal (fn-sn-node
           (fn-sn-make-v6 groups capacity files node keyring index
                          keyring-generation verdicts snapshots identity-next
                          config-history consumer topic event-index))
          node)
   :hints (("Goal" :in-theory (enable fn-sn-make-v6 fn-sn-node)))))
(local
 (defthm fn-snrt-node-of-sn-with-consumer
   (equal (fn-sn-node (fn-sn-with-consumer s consumer)) (fn-sn-node s))
   :hints (("Goal" :in-theory '(fn-sn-with-consumer fn-snrt-node-of-make-v6)))))
(local
 (defthm fn-snrt-node-of-sn-with-topic
   (equal (fn-sn-node (fn-sn-with-topic s topic)) (fn-sn-node s))
   :hints (("Goal" :in-theory '(fn-sn-with-topic fn-snrt-node-of-make-v6)))))
(local
 (defthm fn-snrt-node-of-sn-advance-identity-next
   (equal (fn-sn-node (fn-sn-advance-identity-next s)) (fn-sn-node s))
   :hints (("Goal" :in-theory '(fn-sn-advance-identity-next fn-snrt-node-of-make-v6)))))
(local
 (defthm fn-snrt-node-of-sn-update-indexed
   (equal (fn-sn-node (fn-sn-update-indexed s files node index)) node)
   :hints (("Goal" :in-theory '(fn-sn-update-indexed fn-snrt-node-of-make-v6)))))
(local
 (defthm fn-snrt-node-of-sn-update-accepted
   (equal (fn-sn-node (fn-sn-update-accepted s files node index msgid verdict)) node)
   :hints (("Goal" :in-theory '(fn-sn-update-accepted fn-snrt-node-of-make-v6)))))
(local
 (defthm fn-snrt-node-of-sn-finish-identity
   (equal (fn-sn-node (fn-sn-finish-identity s files record node)) node)
   :hints (("Goal" :in-theory '(fn-sn-finish-identity fn-snrt-node-of-make-v6)))))
(local
 (defthmd fn-snrt-node-of-finish
   (implies (fn-sn-completion-enabledp s)
            (equal (fn-sn-node (fn-sn-finish s))
                   (let ((rec (fn-sn-completion-record s)))
                     (cond ((fn-store-retention-event-p rec)
                            (fn-replay-apply-retention-event (fn-sn-node s) rec))
                           ((or (fn-stxe-p rec) (fn-stxk-p rec) (fn-stxa-p rec)
                                (fn-cpe-eventp rec) (fn-th-topic-eventp rec))
                            (fn-replay-apply-record (fn-sn-node s) rec))
                           (t (fn-node-complete (fn-sn-node s) (fn-record-txid rec)
                                                (fn-record-generation rec)
                                                :durable))))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish)
                                   (fn-sn-completion-enabledp fn-sn-statep
                                    fn-sn-completion-record
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-cpe-eventp fn-th-topic-eventp
                                    fn-replay-apply-record
                                    fn-replay-apply-retention-event
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-node-complete fn-sn-accepted-delta
                                    fn-sf-core-completion fn-sf-emit-success
                                    fn-sn-with-consumer fn-sn-with-topic
                                    fn-sn-advance-identity-next
                                    fn-sn-update-indexed fn-sn-update-accepted
                                    fn-sn-finish-identity fn-sn-make-v6
                                    fn-stx-index-add fn-stx-verdict-of-octets
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))
(local
 (defthm fn-snrt-enabled-completion-arm-facts
   (implies (fn-sn-completion-enabledp s)
            (and (fn-node-statep (fn-sn-node s))
                 (implies (fn-store-retention-event-p (fn-sn-completion-record s))
                          (consp (fn-replay-apply-retention-event
                                  (fn-sn-node s) (fn-sn-completion-record s))))
                 (implies (and (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                               (or (fn-stxe-p (fn-sn-completion-record s))
                                   (fn-stxk-p (fn-sn-completion-record s))
                                   (fn-stxa-p (fn-sn-completion-record s))
                                   (fn-cpe-eventp (fn-sn-completion-record s))
                                   (fn-th-topic-eventp (fn-sn-completion-record s))))
                          (consp (fn-replay-apply-record
                                  (fn-sn-node s) (fn-sn-completion-record s))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp
                                    fn-sn-completion-core-enabledp fn-sn-statep)
                                   (fn-sn-completion-record
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-cpe-eventp fn-th-topic-eventp
                                    fn-replay-apply-record
                                    fn-replay-apply-retention-event
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-sn-record-bindsp fn-node-statep fn-sf-statep
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

; Keystone: every article accepted before a completion is accepted after it,
; on every arm and on the disabled no-op.  An article is its Message-ID, its
; payload octets and its number assignments, so its octets are kept too.

(defthm fn-sn-finish-keeps-accepted-articles
  (implies (member-equal article (fn-state-articles
                                  (fn-node-acceptance (fn-sn-node s))))
           (member-equal article (fn-state-articles
                                  (fn-node-acceptance
                                   (fn-sn-node (fn-sn-finish s))))))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :in-theory (e/d (fn-snrt-node-of-finish)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-sn-completion-record fn-node-statep
                            fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-cpe-eventp fn-th-topic-eventp
                            fn-replay-apply-record
                            fn-replay-apply-retention-event fn-node-complete))
           :use (fn-sn-finish-disabled-is-no-op
                 fn-snrt-enabled-completion-arm-facts
                 (:instance fn-snrt-apply-record-keeps-articles-and-pins
                  (node (fn-sn-node s)) (record (fn-sn-completion-record s))
                  (a article) (p nil))))))

; Keystone: an obligation leaves the ledger across `fn-sn-finish' only when
; the completed record is a retention release (not an undertaking) whose
; identity, subject, kind and evidence match that obligation.

(defthm fn-sn-finish-releases-an-obligation-only-by-its-matching-release
  (implies (and (member-equal pin (fn-retain-pins
                                   (fn-node-retention (fn-sn-node s))))
                (not (member-equal pin (fn-retain-pins
                                        (fn-node-retention
                                         (fn-sn-node (fn-sn-finish s)))))))
           (let ((record (fn-sn-completion-record s)))
             (and (fn-store-retention-event-p record)
                  (not (equal (fn-store-event-kind record) :undertake))
                  (fn-retain-matching-releasep
                   pin (fn-store-event-obligation-id record)
                   (fn-store-event-subject record) :forward
                   (fn-store-event-evidence record)))))
  :rule-classes nil
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :in-theory (e/d (fn-snrt-node-of-finish)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-sn-completion-record fn-node-statep
                            fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-cpe-eventp fn-th-topic-eventp
                            fn-retain-matching-releasep
                            fn-replay-apply-record
                            fn-replay-apply-retention-event fn-node-complete))
           :use (fn-sn-finish-disabled-is-no-op
                 fn-snrt-enabled-completion-arm-facts
                 (:instance fn-snrt-apply-record-keeps-articles-and-pins
                  (node (fn-sn-node s)) (record (fn-sn-completion-record s))
                  (a nil) (p pin))
                 (:instance fn-snrt-retention-event-removes-only-its-matching-release
                  (node (fn-sn-node s)) (event (fn-sn-completion-record s))
                  (p pin))
                 (:instance fn-snrt-complete-keeps-pins
                  (s (fn-sn-node s)) (p pin)
                  (txid (fn-record-txid (fn-sn-completion-record s)))
                  (generation (fn-record-generation (fn-sn-completion-record s)))
                  (status :durable))))))

; Corollary for the article's own obligation: a Store retention release names
; kind :forward, so no finish arm releases an :archive obligation.  With
; `fn-node-state-has-committed-archive-pins' (every accepted article is bound
; to an :archive pin) this is "kept until explicit release" for articles; v0
; has no archive-release event, so the archive pin is kept outright.
(defthm fn-sn-finish-keeps-every-archive-obligation
  (implies (and (member-equal pin (fn-retain-pins
                                   (fn-node-retention (fn-sn-node s))))
                (equal (fn-retain-obligation-kind pin) :archive))
           (member-equal pin (fn-retain-pins
                              (fn-node-retention
                               (fn-sn-node (fn-sn-finish s))))))
  :hints (("Goal" :in-theory (e/d (fn-retain-matching-releasep)
                                  (fn-sn-finish))
           :use fn-sn-finish-releases-an-obligation-only-by-its-matching-release)))
