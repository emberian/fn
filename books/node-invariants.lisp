; Preservation for the composite logical acceptance/retention transaction.
; Durability observations and authorization remain external assumptions.
;
; The node, acceptance and retention recognizers and transitions are opened
; locally; nothing here opens a record.  The export theory keeps the three
; node preservation keystones and the install-stage keystone.
(in-package "ACL2")
(include-book "node")
(include-book "acceptance-invariants")

(local (in-theory (enable fn-acceptance-invariants-vocabulary
                          fn-node-stagep fn-node-bindingp fn-node-statep
                          fn-node-initial-state fn-node-pending-matchesp
                          fn-node-prepare fn-node-complete fn-node-recover
                          fn-articlep fn-pendingp fn-statep fn-initial-state
                          fn-install-pending fn-clear-pending
                          fn-accept-prepare fn-accept-complete fn-accept-recover
                          fn-retain-obligationp fn-retain-releasep
                          fn-retain-statep fn-retain-initial-state
                          fn-retain-admissiblep fn-retain-admit
                          fn-retain-release)))

(defthm fn-node-prepare-preserves-state
  (implies (fn-node-statep s)
           (fn-node-statep
            (fn-node-prepare s generation msgid payload groups
                             obligation-id subject evidence charge))))

(defthm fn-member-of-subset
  (implies (and (fn-subsetp xs ys)
                (member-equal x xs))
           (member-equal x ys)))

(defthm fn-retain-find-id-absent
  (implies (not (member-equal id (fn-retain-obligation-ids pins)))
           (equal (fn-retain-find-id id pins) nil)))

(defthm fn-node-old-archive-bindings-preserved
  (implies (and (fn-node-articles-have-archive-bindingsp articles bindings pins)
                (not (fn-acceptedp msgid articles))
                (not (member-equal id (fn-retain-obligation-ids pins))))
           (fn-node-articles-have-archive-bindingsp
            articles
            (cons (fn-node-make-binding msgid subject id) bindings)
            (cons (fn-retain-make-obligation id subject :archive evidence charge)
                  pins)))
  :hints (("Goal" :induct (fn-node-articles-have-archive-bindingsp
                           articles bindings pins))))

(defthm fn-not-member-of-subset
  (implies (and (fn-subsetp xs ys)
                (not (member-equal x ys)))
           (not (member-equal x xs)))
  :hints (("Goal" :use fn-member-of-subset)))

(defthm fn-node-new-msgid-not-bound
  (implies (and (fn-subsetp (fn-node-binding-msgids bindings)
                            (fn-article-msgids articles))
                (not (fn-acceptedp msgid articles)))
           (not (member-equal msgid (fn-node-binding-msgids bindings))))
  :hints (("Goal" :use ((:instance fn-not-member-of-subset
                        (xs (fn-node-binding-msgids bindings))
                        (ys (fn-article-msgids articles)) (x msgid))))))

(defthm fn-node-stage-retention-is-state
  (implies (fn-node-stagep acceptance committed stage)
           (fn-retain-statep (fn-node-stage-retention stage)))
  :hints (("Goal" :in-theory (disable fn-retain-admit fn-retain-statep))))

(defthm fn-node-stage-retention-pins
  (implies (fn-node-stagep acceptance committed stage)
           (equal (fn-retain-pins (fn-node-stage-retention stage))
                  (cons (fn-retain-make-obligation
                         (fn-node-stage-id stage) (fn-node-stage-subject stage)
                         :archive (fn-node-stage-evidence stage)
                         (fn-node-stage-charge stage))
                        (fn-retain-pins committed)))))

(defthm fn-node-pending-message-is-new
  (implies (and (fn-statep acceptance)
                (consp (fn-state-pending acceptance)))
           (not (fn-acceptedp (fn-pending-msgid (fn-state-pending acceptance))
                              (fn-state-articles acceptance)))))

(defthm fn-node-install-stage-preserves-state
  (implies (and (fn-node-statep s)
                (consp (fn-node-stage s)))
           (fn-node-statep
            (fn-node-make-state
             (fn-install-pending (fn-node-acceptance s))
             (fn-node-stage-retention (fn-node-stage s)) nil
             (cons (fn-node-make-binding (fn-node-stage-msgid (fn-node-stage s))
                                         (fn-node-stage-subject (fn-node-stage s))
                                         (fn-node-stage-id (fn-node-stage s)))
                   (fn-node-bindings s)))))
  :hints (("Goal"
           :use ((:instance fn-node-pending-message-is-new
                  (acceptance (fn-node-acceptance s)))
                 (:instance fn-install-preserves-state
                  (s (fn-node-acceptance s)))
                 (:instance fn-node-stage-retention-is-state
                  (acceptance (fn-node-acceptance s))
                  (committed (fn-node-retention s)) (stage (fn-node-stage s)))
                 (:instance fn-node-old-archive-bindings-preserved
                  (articles (fn-state-articles (fn-node-acceptance s)))
                  (bindings (fn-node-bindings s))
                  (pins (fn-retain-pins (fn-node-retention s)))
                  (msgid (fn-node-stage-msgid (fn-node-stage s)))
                  (id (fn-node-stage-id (fn-node-stage s)))
                  (subject (fn-node-stage-subject (fn-node-stage s)))
                  (evidence (fn-node-stage-evidence (fn-node-stage s)))
                  (charge (fn-node-stage-charge (fn-node-stage s))))
                 (:instance fn-node-stage-retention-pins
                  (acceptance (fn-node-acceptance s))
                  (committed (fn-node-retention s)) (stage (fn-node-stage s))))
           :in-theory (disable fn-statep fn-retain-statep))))

(defthm fn-node-complete-preserves-state
  (implies (fn-node-statep s)
           (fn-node-statep (fn-node-complete s txid generation completion-status)))
  :hints (("Goal"
           :use fn-node-install-stage-preserves-state
           :in-theory (disable fn-install-pending))))

(defthm fn-node-recover-preserves-state
  (implies (fn-node-statep s)
           (fn-node-statep (fn-node-recover s txid generation recovery-result)))
  :hints (("Goal"
           :use fn-node-install-stage-preserves-state
           :in-theory (disable fn-install-pending))))

(defthm fn-node-state-has-committed-archive-pins
  (implies (fn-node-statep s)
           (fn-node-articles-have-archive-bindingsp
            (fn-state-articles (fn-node-acceptance s))
            (fn-node-bindings s)
            (fn-retain-pins (fn-node-retention s)))))

; The three facts below are corollaries: the invariant projected through the
; preservation keystones.  They are not registry events and not rewrite rules.
(defthm fn-node-prepare-preserves-committed-archive-pins
  (implies (fn-node-statep s)
           (fn-node-articles-have-archive-bindingsp
            (fn-state-articles
             (fn-node-acceptance
              (fn-node-prepare s generation msgid payload groups
                               obligation-id subject evidence charge)))
            (fn-node-bindings
             (fn-node-prepare s generation msgid payload groups
                              obligation-id subject evidence charge))
            (fn-retain-pins
             (fn-node-retention
              (fn-node-prepare s generation msgid payload groups
                               obligation-id subject evidence charge)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-node-prepare-preserves-state
                               fn-node-state-has-committed-archive-pins))))

(defthm fn-node-complete-preserves-committed-archive-pins
  (implies (fn-node-statep s)
           (fn-node-articles-have-archive-bindingsp
            (fn-state-articles
             (fn-node-acceptance (fn-node-complete s txid generation completion-status)))
            (fn-node-bindings (fn-node-complete s txid generation completion-status))
            (fn-retain-pins
             (fn-node-retention (fn-node-complete s txid generation completion-status)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-node-complete-preserves-state
                               fn-node-state-has-committed-archive-pins))))

(defthm fn-node-recover-preserves-committed-archive-pins
  (implies (fn-node-statep s)
           (fn-node-articles-have-archive-bindingsp
            (fn-state-articles
             (fn-node-acceptance (fn-node-recover s txid generation recovery-result)))
            (fn-node-bindings (fn-node-recover s txid generation recovery-result))
            (fn-retain-pins
             (fn-node-retention (fn-node-recover s txid generation recovery-result)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-node-recover-preserves-state
                               fn-node-state-has-committed-archive-pins))))

(defthm fn-node-find-binding-absent
  (implies (not (member-equal msgid (fn-node-binding-msgids bindings)))
           (equal (fn-node-find-binding msgid bindings) nil)))

(defthm fn-node-prepare-preserves-bindings
  (equal (fn-node-bindings
          (fn-node-prepare s generation msgid payload groups
                           obligation-id subject evidence charge))
         (fn-node-bindings s)))

(defthm fn-node-complete-preserves-existing-binding
  (implies (and (fn-node-statep s)
                (member-equal msgid (fn-node-binding-msgids (fn-node-bindings s))))
           (equal (fn-node-find-binding
                   msgid (fn-node-bindings
                          (fn-node-complete s txid generation completion-status)))
                  (fn-node-find-binding msgid (fn-node-bindings s))))
  :hints (("Goal" :in-theory (disable fn-install-pending))))

(defthm fn-node-recover-preserves-existing-binding
  (implies (and (fn-node-statep s)
                (member-equal msgid (fn-node-binding-msgids (fn-node-bindings s))))
           (equal (fn-node-find-binding
                   msgid (fn-node-bindings
                          (fn-node-recover s txid generation recovery-result)))
                  (fn-node-find-binding msgid (fn-node-bindings s))))
  :hints (("Goal" :in-theory (disable fn-install-pending))))

; -----------------------------------------------------------------------------
; Export.  Keystones stay enabled: the three node preservation theorems,
; `fn-node-install-stage-preserves-state',
; `fn-node-state-has-committed-archive-pins', `fn-node-prepare-preserves-bindings'
; and the two existing-binding theorems.  The subset and stage lemmas are proof
; vocabulary and are withdrawn.
(deftheory fn-node-invariants-vocabulary
  '(fn-member-of-subset
    fn-retain-find-id-absent
    fn-node-old-archive-bindings-preserved
    fn-not-member-of-subset
    fn-node-new-msgid-not-bound
    fn-node-stage-retention-is-state
    fn-node-stage-retention-pins
    fn-node-pending-message-is-new
    fn-node-find-binding-absent))
(in-theory (disable fn-node-invariants-vocabulary))
