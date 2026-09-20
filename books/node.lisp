; fn M1 composite local node transaction machine.
;
; This book composes the acceptance and retention machines; it does not repeat
; their allocation, persistence-result, or resource-accounting decisions.  The
; retention stage is an actual prospective fn-retain state.  It reserves
; capacity before an acceptance proposal exists, but becomes committed only with
; the matching abstract durable acceptance completion.
;
; Records are opaque and `fn-node-statep' is a carried invariant guarding the
; three host transitions and `fn-node-pending-matchesp' (docs/proof-style.md).
; The :logic bodies are the original total ones; preservation is proved in
; node-invariants.lisp.

(in-package "ACL2")
(include-book "acceptance")
(include-book "retention")
(include-book "defrecord")

; -----------------------------------------------------------------------------
; Node state and a staged archive obligation

; Stage: (message-id generation obligation-id immutable-content-subject
;         release-evidence charge prospective-retention-state).  The explicit
; content subject is not a Message-ID and this model makes no claim that it
; is a verified hash.
(fn-defrecord fn-node-stage
  :constructor (fn-node-make-stage msgid generation id subject evidence
                                   charge retention)
  :fields ((fn-node-stage-msgid stringp)
           (fn-node-stage-generation natp)
           (fn-node-stage-id stringp)
           (fn-node-stage-subject stringp)
           (fn-node-stage-evidence stringp)
           (fn-node-stage-charge
            (and (posp (fn-node-stage-charge x))
                 (consp (fn-state-pending acceptance))
                 (equal (fn-node-stage-msgid x)
                        (fn-pending-msgid (fn-state-pending acceptance)))
                 (equal (fn-node-stage-generation x)
                        (fn-pending-generation (fn-state-pending acceptance)))
                 (fn-retain-admissiblep committed
                                        (fn-node-stage-id x)
                                        (fn-node-stage-subject x)
                                        :archive
                                        (fn-node-stage-evidence x)
                                        (fn-node-stage-charge x))))
           (fn-node-stage-retention
            (equal (fn-node-stage-retention x)
                   (fn-retain-admit committed
                                    (fn-node-stage-id x)
                                    (fn-node-stage-subject x)
                                    :archive
                                    (fn-node-stage-evidence x)
                                    (fn-node-stage-charge x)))))
  :recognizer-formals (acceptance committed)
  :recognizer-guard (fn-retain-statep committed)
  :recognizer-verify-guards nil)

; Binding: (message-id immutable-content-subject archive-obligation-id).  This
; persists the article-to-archive relationship after the pending stage clears.
(fn-defrecord fn-node-binding
  :constructor (fn-node-make-binding msgid subject id)
  :fields ((fn-node-binding-msgid stringp)
           (fn-node-binding-subject stringp)
           (fn-node-binding-id stringp))
  :recognizer-verify-guards nil)

(defun fn-node-binding-msgids (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (cons (fn-node-binding-msgid (car xs))
            (fn-node-binding-msgids (cdr xs)))
    nil))

(defun fn-node-binding-ids (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (cons (fn-node-binding-id (car xs))
            (fn-node-binding-ids (cdr xs)))
    nil))

(defun fn-node-binding-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (fn-node-bindingp (car xs))
           (not (member-equal (fn-node-binding-msgid (car xs))
                              (fn-node-binding-msgids (cdr xs))))
           (not (member-equal (fn-node-binding-id (car xs))
                              (fn-node-binding-ids (cdr xs))))
           (fn-node-binding-listp (cdr xs)))
    (null xs)))

(defun fn-node-find-binding (msgid xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (if (equal msgid (fn-node-binding-msgid (car xs)))
          (car xs)
        (fn-node-find-binding msgid (cdr xs)))
    nil))

(defun fn-node-articles-have-archive-bindingsp (articles bindings pins)
  (declare (xargs :guard (fn-retain-obligation-listp pins)
                  :verify-guards nil))
  (if (consp articles)
      (let ((binding (fn-node-find-binding (fn-article-msgid (car articles))
                                           bindings)))
        (and (consp binding)
             (fn-retain-matching-releasep
              (fn-retain-find-id (fn-node-binding-id binding) pins)
              (fn-node-binding-id binding)
              (fn-node-binding-subject binding)
              :archive
              (fn-retain-obligation-evidence
               (fn-retain-find-id (fn-node-binding-id binding) pins)))
             (fn-node-articles-have-archive-bindingsp (cdr articles)
                                                       bindings pins)))
    t))

; State: (committed-acceptance committed-retention pending-retention-stage
;         committed-article-to-archive-bindings).
; The conjuncts of `fn-node-statep' keep the order they were written in:
; each cross-field conjunct rides with the last field it reads, so the
; carried invariant ACL2 admits is the same term as before.

(fn-defrecord fn-node-state
  :constructor (fn-node-make-state acceptance retention stage bindings)
  :fields ((fn-node-acceptance (fn-statep (fn-node-acceptance x)))
           (fn-node-retention (fn-retain-statep (fn-node-retention x)))
           (fn-node-stage t)
           (fn-node-bindings
            (and (fn-node-binding-listp (fn-node-bindings x))
                 ; No orphan binding can preempt a later article or obligation
                 ; identity.
                 (fn-subsetp (fn-node-binding-msgids (fn-node-bindings x))
                             (fn-article-msgids
                              (fn-state-articles (fn-node-acceptance x))))
                 (fn-subsetp (fn-node-binding-ids (fn-node-bindings x))
                             (fn-retain-obligation-ids
                              (fn-retain-pins (fn-node-retention x))))
                 (equal (null (fn-node-stage x))
                        (null (fn-state-pending (fn-node-acceptance x))))
                 (fn-node-articles-have-archive-bindingsp
                  (fn-state-articles (fn-node-acceptance x))
                  (fn-node-bindings x)
                  (fn-retain-pins (fn-node-retention x)))
                 (or (null (fn-node-stage x))
                     (and (fn-node-stagep (fn-node-acceptance x)
                                          (fn-node-retention x)
                                          (fn-node-stage x))
                          (consp (fn-state-pending (fn-node-acceptance x)))))
                 ; An indeterminate storage result retains both proposals
                 ; until recovery.
                 (or (not (equal (fn-state-fenced (fn-node-acceptance x)) t))
                     (consp (fn-node-stage x))))))
  :recognizer-verify-guards nil)

(defun fn-node-initial-state (groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-make-state (fn-initial-state groups)
                      (fn-retain-initial-state capacity)
                      nil nil))

; Matching is decided under the carried invariant: the :logic body keeps the
; whole-state recognizer as its first conjunct, the :exec path relies on the
; guard.
(defun fn-node-pending-matchesp (s txid generation)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (and (mbe :logic (fn-node-statep s) :exec t)
       (equal (fn-state-fenced (fn-node-acceptance s)) nil)
       (consp (fn-node-stage s))
       (fn-pending-matchesp (fn-state-pending (fn-node-acceptance s))
                            txid generation)))

; -----------------------------------------------------------------------------
; Composite transitions

; The caller supplies an externally unique obligation identity, an explicit
; subject, and a positive abstract charge that includes retention's permanent
; history unit.  No cryptographic verification occurs in this machine.
(defun fn-node-prepare (s generation msgid payload groups
                          obligation-id subject evidence charge)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-node-statep s)) :exec nil)
      s
    (if (not (fn-retain-admissiblep (fn-node-retention s)
                                    obligation-id subject :archive evidence
                                    charge))
        s
      (let ((next-acceptance
             (fn-accept-prepare (fn-node-acceptance s)
                                generation msgid payload groups)))
        ; The acceptance machine decides duplicates, groups, transaction
        ; serialization, and fencing.  Do not reserve if it refused to stage.
        (if (equal next-acceptance (fn-node-acceptance s))
            s
          (let ((next-retention
                 (fn-retain-admit (fn-node-retention s)
                                  obligation-id subject :archive evidence
                                  charge)))
            (fn-node-make-state
             next-acceptance
             (fn-node-retention s)
             (fn-node-make-stage msgid generation obligation-id subject
                                 evidence charge next-retention)
             (fn-node-bindings s))))))))

(defun fn-node-complete (s txid generation completion-status)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (not (fn-node-pending-matchesp s txid generation))
      s
    (if (equal completion-status :durable)
        (fn-node-make-state
         (fn-accept-complete (fn-node-acceptance s)
                             txid generation :durable)
         (fn-node-stage-retention (fn-node-stage s))
         nil
         (cons (fn-node-make-binding (fn-node-stage-msgid (fn-node-stage s))
                                     (fn-node-stage-subject (fn-node-stage s))
                                     (fn-node-stage-id (fn-node-stage s)))
               (fn-node-bindings s)))
      (if (equal completion-status :aborted)
          (fn-node-make-state
           (fn-accept-complete (fn-node-acceptance s)
                               txid generation :aborted)
           (fn-node-retention s)
           nil (fn-node-bindings s))
        (if (equal completion-status :indeterminate)
            (fn-node-make-state
             (fn-accept-complete (fn-node-acceptance s)
                                 txid generation :indeterminate)
             (fn-node-retention s)
             (fn-node-stage s) (fn-node-bindings s))
          s)))))

(defun fn-node-recover (s txid generation recovery-result)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (or (mbe :logic (not (fn-node-statep s)) :exec nil)
          (not (equal (fn-state-fenced (fn-node-acceptance s)) t))
          (not (consp (fn-node-stage s)))
          (not (fn-pending-matchesp
                (fn-state-pending (fn-node-acceptance s)) txid generation)))
      s
    (if (equal recovery-result :committed)
        (fn-node-make-state
         (fn-accept-recover (fn-node-acceptance s)
                            txid generation :committed)
         (fn-node-stage-retention (fn-node-stage s))
         nil
         (cons (fn-node-make-binding (fn-node-stage-msgid (fn-node-stage s))
                                     (fn-node-stage-subject (fn-node-stage s))
                                     (fn-node-stage-id (fn-node-stage s)))
               (fn-node-bindings s)))
      (if (equal recovery-result :absent)
          (fn-node-make-state
           (fn-accept-recover (fn-node-acceptance s)
                              txid generation :absent)
           (fn-node-retention s)
           nil (fn-node-bindings s))
        s))))

; Verify every executable node definition.  The three transitions and the
; matching test carry `fn-node-statep'; their callees' guards are discharged
; by opening it.
(verify-guards fn-node-stagep)
(verify-guards fn-node-bindingp)
(verify-guards fn-node-binding-msgids)
(verify-guards fn-node-binding-ids)
(verify-guards fn-node-binding-listp)
(verify-guards fn-node-find-binding)
(verify-guards fn-node-articles-have-archive-bindingsp)
(verify-guards fn-node-statep
  :hints (("Goal" :in-theory (enable fn-retain-statep))))
(verify-guards fn-node-initial-state)
(verify-guards fn-node-pending-matchesp)
(verify-guards fn-node-prepare
  :hints (("Goal" :in-theory (enable fn-node-statep))))
(verify-guards fn-node-complete
  :hints (("Goal" :in-theory (enable fn-node-statep fn-node-pending-matchesp))))
(verify-guards fn-node-recover
  :hints (("Goal" :in-theory (enable fn-node-statep))))

; -----------------------------------------------------------------------------
; Composite proof events.  They establish only correspondence among these
; abstract transitions; actual storage durability remains A-DURABILITY/A-HOST.

(defthm fn-node-initial-state-is-state
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-node-statep (fn-node-initial-state groups capacity)))
  :hints (("Goal" :in-theory (enable fn-node-initial-state fn-node-statep
                                      fn-initial-state fn-statep))))

; The two `-by-definition' facts restate a refusing branch with its test as
; hypothesis.  They are not registry events and not rewrite rules.
(defthm fn-node-capacity-refusal-is-no-op
  (implies (and (fn-node-statep s)
                (not (fn-retain-admissiblep (fn-node-retention s)
                                             obligation-id subject :archive
                                             evidence charge)))
           (equal (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge)
                  s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-node-prepare))))

(defthm fn-node-prepare-does-not-publish-or-commit-retention
  (implies (fn-node-statep s)
           (and (equal (fn-state-articles
                        (fn-node-acceptance
                         (fn-node-prepare s generation msgid payload groups
                                          obligation-id subject evidence charge)))
                       (fn-state-articles (fn-node-acceptance s)))
                (equal (fn-node-retention
                        (fn-node-prepare s generation msgid payload groups
                                         obligation-id subject evidence charge))
                       (fn-node-retention s))))
  :hints (("Goal" :in-theory (enable fn-node-prepare fn-node-statep))))

(defthm fn-node-stale-completion-is-no-op
  (implies (not (fn-node-pending-matchesp s txid generation))
           (equal (fn-node-complete s txid generation completion-status) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-node-complete))))

(defthm fn-node-durable-completion-promotes-matching-stage
  (implies (fn-node-pending-matchesp s txid generation)
           (and (equal (fn-node-retention
                        (fn-node-complete s txid generation :durable))
                       (fn-node-stage-retention (fn-node-stage s)))
                (equal (fn-node-stage
                        (fn-node-complete s txid generation :durable))
                       nil)))
  :hints (("Goal" :in-theory (enable fn-node-complete))))

; -----------------------------------------------------------------------------
; Export.  Records were disabled at their definitions.  Withdrawn here: the
; stage, binding and node recognizers, the initial state, the matching test
; and the three transitions.  The binding folds and the archive-binding
; relation stay enabled as list vocabulary.
(in-theory (disable (:d fn-node-stagep) (:d fn-node-bindingp)
                    (:d fn-node-statep) (:d fn-node-initial-state)
                    (:d fn-node-pending-matchesp) (:d fn-node-prepare)
                    (:d fn-node-complete) (:d fn-node-recover)))
