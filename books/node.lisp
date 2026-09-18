; fn M1 composite local node transaction machine.
;
; This book composes the acceptance and retention machines; it does not repeat
; their allocation, persistence-result, or resource-accounting decisions.  The
; retention stage is an actual prospective fn-retain state.  It reserves
; capacity before an acceptance proposal exists, but becomes committed only with
; the matching abstract durable acceptance completion.

(in-package "ACL2")
(include-book "acceptance")
(include-book "retention")

; -----------------------------------------------------------------------------
; Node state and a staged archive obligation

; Stage: (message-id generation obligation-id immutable-content-subject
;         release-evidence charge prospective-retention-state).  The explicit content subject is not a
; Message-ID and this model makes no claim that it is a verified hash.
(defun fn-node-stage-msgid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-node-stage-generation (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-node-stage-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-node-stage-subject (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-node-stage-evidence (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-node-stage-charge (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                      (fn-ag-cdr (fn-ag-cdr x))))))))
(defun fn-node-stage-retention (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))

(defun fn-node-make-stage (msgid generation id subject evidence charge retention)
  (declare (xargs :guard t :verify-guards nil))
  (list msgid generation id subject evidence charge retention))

(defun fn-node-stagep (acceptance committed x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x)
       (equal (len x) 7)
       (stringp (fn-node-stage-msgid x))
       (natp (fn-node-stage-generation x))
       (stringp (fn-node-stage-id x))
       (stringp (fn-node-stage-subject x))
       (stringp (fn-node-stage-evidence x))
       (posp (fn-node-stage-charge x))
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
                               (fn-node-stage-charge x))
       (equal (fn-node-stage-retention x)
              (fn-retain-admit committed
                               (fn-node-stage-id x)
                               (fn-node-stage-subject x)
                               :archive
                               (fn-node-stage-evidence x)
                               (fn-node-stage-charge x)))))

; Binding: (message-id immutable-content-subject archive-obligation-id).  This
; persists the article-to-archive relationship after the pending stage clears.
(defun fn-node-binding-msgid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-node-binding-subject (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-node-binding-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-node-make-binding (msgid subject id)
  (declare (xargs :guard t :verify-guards nil))
  (list msgid subject id))

(defun fn-node-bindingp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x) (equal (len x) 3)
       (stringp (fn-node-binding-msgid x))
       (stringp (fn-node-binding-subject x))
       (stringp (fn-node-binding-id x))))

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
  (declare
   (xargs :guard (and (fn-node-binding-listp bindings)
                      (fn-retain-obligation-listp pins))
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
(defun fn-node-acceptance (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car s) :exec (fn-ag-car s)))
(defun fn-node-retention (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr s)) :exec (fn-ag-car (fn-ag-cdr s))))
(defun fn-node-stage (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))
(defun fn-node-bindings (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr s))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))

(defun fn-node-make-state (acceptance retention stage bindings)
  (declare (xargs :guard t :verify-guards nil))
  (list acceptance retention stage bindings))

(defun fn-node-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp s)
       (equal (len s) 4)
       (fn-statep (fn-node-acceptance s))
       (fn-retain-statep (fn-node-retention s))
       (fn-node-binding-listp (fn-node-bindings s))
       ; No orphan binding can preempt a later article or obligation identity.
       (fn-subsetp (fn-node-binding-msgids (fn-node-bindings s))
                   (fn-article-msgids (fn-state-articles (fn-node-acceptance s))))
       (fn-subsetp (fn-node-binding-ids (fn-node-bindings s))
                   (fn-retain-obligation-ids (fn-retain-pins (fn-node-retention s))))
       (equal (null (fn-node-stage s))
              (null (fn-state-pending (fn-node-acceptance s))))
       (fn-node-articles-have-archive-bindingsp
        (fn-state-articles (fn-node-acceptance s))
        (fn-node-bindings s)
        (fn-retain-pins (fn-node-retention s)))
       (or (null (fn-node-stage s))
           (and (fn-node-stagep (fn-node-acceptance s)
                                (fn-node-retention s) (fn-node-stage s))
                (consp (fn-state-pending (fn-node-acceptance s)))))
       ; An indeterminate storage result retains both proposals until recovery.
       (or (not (equal (fn-state-fenced (fn-node-acceptance s)) t))
           (consp (fn-node-stage s)))))

(defun fn-node-initial-state (groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-make-state (fn-initial-state groups)
                      (fn-retain-initial-state capacity)
                      nil nil))

(defun fn-node-pending-matchesp (s txid generation)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-node-statep s)
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
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-node-statep s))
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
  (declare (xargs :guard t :verify-guards nil))
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
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-node-statep s))
          (not (equal (fn-state-fenced (fn-node-acceptance s)) t))
          (not (consp (fn-node-stage s))
          )
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

; Typed search results bridge the precise raw guards in the retention helpers.
(local
 (defthm fn-node-guard-find-retention-is-true-list
   (implies (fn-retain-obligation-listp pins)
            (true-listp (fn-retain-find-id id pins)))))

(local
 (defthm fn-node-guard-find-retention-is-obligation
   (implies (and (fn-retain-obligation-listp pins)
                 (consp (fn-retain-find-id id pins)))
            (fn-retain-obligationp (fn-retain-find-id id pins)))))

; Verify every executable node definition, including all three public
; acceptance/retention transaction transitions.
(verify-guards fn-node-stage-msgid)
(verify-guards fn-node-stage-generation)
(verify-guards fn-node-stage-id)
(verify-guards fn-node-stage-subject)
(verify-guards fn-node-stage-evidence)
(verify-guards fn-node-stage-charge)
(verify-guards fn-node-stage-retention)
(verify-guards fn-node-make-stage)
(verify-guards fn-node-stagep)
(verify-guards fn-node-binding-msgid)
(verify-guards fn-node-binding-subject)
(verify-guards fn-node-binding-id)
(verify-guards fn-node-make-binding)
(verify-guards fn-node-bindingp)
(verify-guards fn-node-binding-msgids)
(verify-guards fn-node-binding-ids)
(verify-guards fn-node-binding-listp)
(verify-guards fn-node-find-binding)
(verify-guards fn-node-articles-have-archive-bindingsp
 :hints (("Goal"
          :use ((:instance fn-node-guard-find-retention-is-true-list)
                (:instance fn-node-guard-find-retention-is-obligation)))))
(verify-guards fn-node-acceptance)
(verify-guards fn-node-retention)
(verify-guards fn-node-stage)
(verify-guards fn-node-bindings)
(verify-guards fn-node-make-state)
(verify-guards fn-node-statep)
(verify-guards fn-node-initial-state)
(verify-guards fn-node-pending-matchesp)
(verify-guards fn-node-prepare)
(verify-guards fn-node-complete)
(verify-guards fn-node-recover)

; -----------------------------------------------------------------------------
; Composite proof events.  They establish only correspondence among these
; abstract transitions; actual storage durability remains A-DURABILITY/A-HOST.

(defthm fn-node-initial-state-is-state
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-node-statep (fn-node-initial-state groups capacity)))
  :hints (("Goal" :in-theory (enable fn-node-initial-state fn-node-statep))))

(defthm fn-node-capacity-refusal-is-no-op
  (implies (and (fn-node-statep s)
                (not (fn-retain-admissiblep (fn-node-retention s)
                                             obligation-id subject :archive
                                             evidence charge)))
           (equal (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge)
                  s))
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
  :hints (("Goal" :in-theory (enable fn-node-prepare))))

(defthm fn-node-stale-completion-is-no-op
  (implies (not (fn-node-pending-matchesp s txid generation))
           (equal (fn-node-complete s txid generation completion-status) s))
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
