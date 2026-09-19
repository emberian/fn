; fn M1: a small, executable logical acceptance machine.
;
; This book deliberately models no bytes-on-disk, network, or cryptography.  A
; host supplies a generation and reports an abstract persistence result.  The
; machine makes publication conditional on the matching durable result.
;
; Records are opaque (docs/proof-style.md): each record has a shape
; recognizer, a constructor and accessors; the shape lemma and the
; accessor-of-constructor lemmas are proved once and the record is disabled.
; The state recognizer `fn-statep' is a carried invariant: the three host
; transitions take it as their guard, the :exec path never recomputes it, and
; the :logic body is unchanged so every theorem below keeps its statement.
; Its preservation is proved in acceptance-invariants.lisp.

(in-package "ACL2")
(include-book "acceptance-alloc")

; -----------------------------------------------------------------------------
; Article: (message-id payload requested-groups memberships archive-pin)

(defun fn-article-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5)))

(defun fn-article-msgid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-article-msgid)
(defun fn-article-payload (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-article-payload)
(defun fn-article-groups (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-article-groups)
(defun fn-article-memberships (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-article-memberships)
(defun fn-article-pin (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(verify-guards fn-article-pin)

(defun fn-make-article (msgid payload groups memberships pin)
  (declare (xargs :guard t))
  (list msgid payload groups memberships pin))

(defthm fn-article-shapep-of-fn-make-article
  (fn-article-shapep (fn-make-article msgid payload groups memberships pin)))
(defthm fn-article-msgid-of-fn-make-article
  (equal (fn-article-msgid (fn-make-article msgid payload groups memberships pin))
         msgid))
(defthm fn-article-payload-of-fn-make-article
  (equal (fn-article-payload (fn-make-article msgid payload groups memberships pin))
         payload))
(defthm fn-article-groups-of-fn-make-article
  (equal (fn-article-groups (fn-make-article msgid payload groups memberships pin))
         groups))
(defthm fn-article-memberships-of-fn-make-article
  (equal (fn-article-memberships
          (fn-make-article msgid payload groups memberships pin))
         memberships))
(defthm fn-article-pin-of-fn-make-article
  (equal (fn-article-pin (fn-make-article msgid payload groups memberships pin))
         pin))

(in-theory (disable (:d fn-article-shapep) (:d fn-article-msgid) (:d fn-article-payload) (:d fn-article-groups) (:d fn-article-memberships) (:d fn-article-pin) (:d fn-make-article)))

(defun fn-articlep (configured x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-article-shapep x)
       (stringp (fn-article-msgid x))
       (fn-octet-listp (fn-article-payload x))
       (fn-selection-validp (fn-article-groups x) configured)
       (fn-membership-listp (fn-article-groups x)
                            (fn-article-memberships x))
       (equal (fn-article-pin x) t)))

(verify-guards fn-articlep)

(defun fn-article-msgids (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (cons (fn-article-msgid (car xs))
            (fn-article-msgids (cdr xs)))
    nil))

(verify-guards fn-article-msgids)

(defun fn-article-listp (configured xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (fn-articlep configured (car xs))
           (not (member-equal (fn-article-msgid (car xs))
                              (fn-article-msgids (cdr xs))))
           (fn-article-listp configured (cdr xs)))
    (null xs)))

(verify-guards fn-article-listp)

(defun fn-acceptedp (msgid articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (or (equal msgid (fn-article-msgid (car articles)))
          (fn-acceptedp msgid (cdr articles)))
    nil))

(verify-guards fn-acceptedp)

(defun fn-find-article (msgid xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (if (equal msgid (fn-article-msgid (car xs)))
          (car xs)
        (fn-find-article msgid (cdr xs)))
    nil))

(verify-guards fn-find-article)

(defun fn-pair-equalp (a b)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp a)
       (consp b)
       (equal (car a) (car b))
       (equal (cdr a) (cdr b))))

(verify-guards fn-pair-equalp)

(defun fn-pair-memberp (pair xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (or (fn-pair-equalp pair (car xs))
          (fn-pair-memberp pair (cdr xs)))
    nil))

(verify-guards fn-pair-memberp)

(defun fn-all-article-memberships (articles)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp articles)
           (append (fn-article-memberships (car articles))
                   (fn-all-article-memberships (cdr articles)))
         nil)
       :exec
       (if (consp articles)
           (fn-ag-append (fn-article-memberships (fn-ag-car articles))
                         (fn-all-article-memberships (fn-ag-cdr articles)))
         nil)))

(verify-guards fn-all-article-memberships)

(defun fn-memberships-conflictsp (memberships articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp memberships)
      (or (fn-pair-memberp (car memberships)
                           (fn-all-article-memberships articles))
          (fn-memberships-conflictsp (cdr memberships) articles))
    nil))

(verify-guards fn-memberships-conflictsp)

(defun fn-articles-freshp (articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (and (not (fn-memberships-conflictsp
                 (fn-article-memberships (car articles))
                 (cdr articles)))
           (fn-articles-freshp (cdr articles)))
    t))

(verify-guards fn-articles-freshp)

(defun fn-articles-below-nextsp (articles nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (and (fn-memberships-below-nextsp
            (fn-article-memberships (car articles)) nexts)
           (fn-articles-below-nextsp (cdr articles) nexts))
    t))

(verify-guards fn-articles-below-nextsp)

; -----------------------------------------------------------------------------
; Pending: (txid generation message-id payload groups memberships archive-pin)

(defun fn-pending-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7)))

(defun fn-pending-txid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-pending-txid)
(defun fn-pending-generation (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-pending-generation)
(defun fn-pending-msgid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-pending-msgid)
(defun fn-pending-payload (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-pending-payload)
(defun fn-pending-groups (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(verify-guards fn-pending-groups)
(defun fn-pending-memberships (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))
(verify-guards fn-pending-memberships)
(defun fn-pending-pin (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                     (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))
(verify-guards fn-pending-pin)

(defun fn-make-pending (txid generation msgid payload groups memberships pin)
  (declare (xargs :guard t))
  (list txid generation msgid payload groups memberships pin))

(defthm fn-pending-shapep-of-fn-make-pending
  (fn-pending-shapep
   (fn-make-pending txid generation msgid payload groups memberships pin)))
(defthm fn-pending-txid-of-fn-make-pending
  (equal (fn-pending-txid
          (fn-make-pending txid generation msgid payload groups memberships pin))
         txid))
(defthm fn-pending-generation-of-fn-make-pending
  (equal (fn-pending-generation
          (fn-make-pending txid generation msgid payload groups memberships pin))
         generation))
(defthm fn-pending-msgid-of-fn-make-pending
  (equal (fn-pending-msgid
          (fn-make-pending txid generation msgid payload groups memberships pin))
         msgid))
(defthm fn-pending-payload-of-fn-make-pending
  (equal (fn-pending-payload
          (fn-make-pending txid generation msgid payload groups memberships pin))
         payload))
(defthm fn-pending-groups-of-fn-make-pending
  (equal (fn-pending-groups
          (fn-make-pending txid generation msgid payload groups memberships pin))
         groups))
(defthm fn-pending-memberships-of-fn-make-pending
  (equal (fn-pending-memberships
          (fn-make-pending txid generation msgid payload groups memberships pin))
         memberships))
(defthm fn-pending-pin-of-fn-make-pending
  (equal (fn-pending-pin
          (fn-make-pending txid generation msgid payload groups memberships pin))
         pin))

(in-theory (disable (:d fn-pending-shapep) (:d fn-pending-txid) (:d fn-pending-generation) (:d fn-pending-msgid) (:d fn-pending-payload) (:d fn-pending-groups) (:d fn-pending-memberships) (:d fn-pending-pin) (:d fn-make-pending)))

(defun fn-pendingp (configured nexts next-txid x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-pending-shapep x)
       (natp (fn-pending-txid x))
       (mbe :logic (< (fn-pending-txid x) next-txid)
            :exec (fn-ag-less (fn-pending-txid x) next-txid))
       (natp (fn-pending-generation x))
       (stringp (fn-pending-msgid x))
       (fn-octet-listp (fn-pending-payload x))
       (fn-selection-validp (fn-pending-groups x) configured)
       (fn-membership-listp (fn-pending-groups x)
                            (fn-pending-memberships x))
       (fn-memberships-at-watermarkp
        (fn-pending-memberships x) nexts)
       (equal (fn-pending-pin x) t)))

(verify-guards fn-pendingp)

; -----------------------------------------------------------------------------
; State: (groups nexts articles next-txid pending fenced)

(defun fn-state-shapep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 6)))

(defun fn-make-state (groups nexts articles next-txid pending fenced)
  (declare (xargs :guard t))
  (list groups nexts articles next-txid pending fenced))

(defun fn-state-groups (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car s) :exec (fn-ag-car s)))
(verify-guards fn-state-groups)
(defun fn-state-nexts (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr s)) :exec (fn-ag-car (fn-ag-cdr s))))
(verify-guards fn-state-nexts)
(defun fn-state-articles (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))
(verify-guards fn-state-articles)
(defun fn-state-next-txid (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr s))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))
(verify-guards fn-state-next-txid)
(defun fn-state-pending (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr s)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))
(verify-guards fn-state-pending)
(defun fn-state-fenced (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr s))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))))
(verify-guards fn-state-fenced)

(defthm fn-state-shapep-of-fn-make-state
  (fn-state-shapep
   (fn-make-state groups nexts articles next-txid pending fenced)))
(defthm fn-state-groups-of-fn-make-state
  (equal (fn-state-groups
          (fn-make-state groups nexts articles next-txid pending fenced))
         groups))
(defthm fn-state-nexts-of-fn-make-state
  (equal (fn-state-nexts
          (fn-make-state groups nexts articles next-txid pending fenced))
         nexts))
(defthm fn-state-articles-of-fn-make-state
  (equal (fn-state-articles
          (fn-make-state groups nexts articles next-txid pending fenced))
         articles))
(defthm fn-state-next-txid-of-fn-make-state
  (equal (fn-state-next-txid
          (fn-make-state groups nexts articles next-txid pending fenced))
         next-txid))
(defthm fn-state-pending-of-fn-make-state
  (equal (fn-state-pending
          (fn-make-state groups nexts articles next-txid pending fenced))
         pending))
(defthm fn-state-fenced-of-fn-make-state
  (equal (fn-state-fenced
          (fn-make-state groups nexts articles next-txid pending fenced))
         fenced))

(in-theory (disable (:d fn-state-shapep) (:d fn-state-groups) (:d fn-state-nexts) (:d fn-state-articles) (:d fn-state-next-txid) (:d fn-state-pending) (:d fn-state-fenced) (:d fn-make-state)))

(defun fn-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-state-shapep s)
       (fn-string-listp (fn-state-groups s))
       (fn-no-duplicatesp (fn-state-groups s))
       (fn-nexts-for-p (fn-state-groups s) (fn-state-nexts s))
       (natp (fn-state-next-txid s))
       (fn-article-listp (fn-state-groups s) (fn-state-articles s))
       (fn-articles-freshp (fn-state-articles s))
       (fn-articles-below-nextsp (fn-state-articles s)
                                 (fn-state-nexts s))
       (or (null (fn-state-pending s))
           (and (not (fn-acceptedp
                      (fn-pending-msgid (fn-state-pending s))
                      (fn-state-articles s)))
                (fn-pendingp (fn-state-groups s)
                             (fn-state-nexts s)
                             (fn-state-next-txid s)
                             (fn-state-pending s))))
       (fn-fencedp (fn-state-fenced s))
       (or (null (fn-state-fenced s))
           (consp (fn-state-pending s)))))

(verify-guards fn-statep)

(defun fn-initial-state (groups)
  (declare (xargs :guard t :verify-guards nil))
  (fn-make-state groups (fn-initial-nexts groups) nil 0 nil nil))

(verify-guards fn-initial-state)

; -----------------------------------------------------------------------------
; Transitions.
;
; Each host transition is guarded by `fn-statep'.  The :logic body is the
; original total definition, which returns a non-state unchanged; under the
; guard that branch is dead, so the :exec path omits the recognizer and no
; served operation revalidates the whole state.

(defun fn-pending-matchesp (pending txid generation)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp pending)
       (equal txid (fn-pending-txid pending))
       (equal generation (fn-pending-generation pending))))

(verify-guards fn-pending-matchesp)

(defun fn-article-from-pending (pending)
  (declare (xargs :guard t :verify-guards nil))
  (fn-make-article
   (fn-pending-msgid pending)
   (fn-pending-payload pending)
   (fn-pending-groups pending)
   (fn-pending-memberships pending)
   (fn-pending-pin pending)))

(verify-guards fn-article-from-pending)

(defun fn-install-pending (s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((p (fn-state-pending s)))
    (fn-make-state
     (fn-state-groups s)
     (fn-advance-nexts (fn-pending-groups p) (fn-state-nexts s))
     (cons (fn-article-from-pending p) (fn-state-articles s))
     (fn-state-next-txid s)
     nil
     nil)))

(verify-guards fn-install-pending)

(defun fn-clear-pending (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-make-state (fn-state-groups s)
                 (fn-state-nexts s)
                 (fn-state-articles s)
                 (fn-state-next-txid s)
                 nil
                 nil))

(verify-guards fn-clear-pending)

; Prepare reserves a unique txid and stages every local membership.  It does
; not change committed articles or group watermarks.
(defun fn-accept-prepare (s generation msgid payload groups)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    (if (or (equal (fn-state-fenced s) t)
            (consp (fn-state-pending s))
            (not (natp generation))
            (not (stringp msgid))
            (not (fn-octet-listp payload))
            (not (fn-selection-validp groups (fn-state-groups s)))
            (fn-acceptedp msgid (fn-state-articles s)))
        s
      (fn-make-state
       (fn-state-groups s)
       (fn-state-nexts s)
       (fn-state-articles s)
       (1+ (fn-state-next-txid s))
       (fn-make-pending
        (fn-state-next-txid s)
        generation
        msgid
        payload
        groups
        (fn-allocate-memberships groups (fn-state-nexts s))
        t)
       nil))))

(verify-guards fn-accept-prepare)

; completion-status is one of :durable, :aborted, or :indeterminate.  Only a
; matching :durable completion publishes the proposal.  An indeterminate
; result retains it and fences ordinary submissions and completions until
; recovery resolves the proposal.
(defun fn-accept-complete (s txid generation completion-status)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    (if (or (equal (fn-state-fenced s) t)
            (not (fn-pending-matchesp (fn-state-pending s)
                                      txid generation)))
        s
      (if (equal completion-status :durable)
          (fn-install-pending s)
        (if (equal completion-status :aborted)
            (fn-clear-pending s)
          (if (equal completion-status :indeterminate)
              (fn-make-state (fn-state-groups s)
                             (fn-state-nexts s)
                             (fn-state-articles s)
                             (fn-state-next-txid s)
                             (fn-state-pending s)
                             t)
            s))))))

(verify-guards fn-accept-complete)

; Recovery is an abstract host observation, not a disk algorithm.  It may
; resolve only the still-fenced matching proposal as committed or absent.
(defun fn-accept-recover (s txid generation recovery-result)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    (if (or (not (equal (fn-state-fenced s) t))
            (not (fn-pending-matchesp (fn-state-pending s)
                                      txid generation)))
        s
      (if (equal recovery-result :committed)
          (fn-install-pending s)
        (if (equal recovery-result :absent)
            (fn-clear-pending s)
          s)))))

(verify-guards fn-accept-recover)

; -----------------------------------------------------------------------------
; First proof events.  These are ordinary theorem events with no proof
; shortcuts or trust tags.  The larger allocation/refinement preservation
; chain is in acceptance-invariants.lisp.

(defthm fn-initial-state-is-state
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups))
           (fn-statep (fn-initial-state groups)))
  :hints (("Goal" :in-theory (enable fn-initial-state fn-statep))))

(defthm fn-fenced-prepare-is-no-op
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) t))
           (equal (fn-accept-prepare s generation msgid payload groups)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-duplicate-accepted-prepare-is-no-op
  (implies (and (fn-statep s)
                (fn-acceptedp msgid (fn-state-articles s)))
           (equal (fn-accept-prepare s generation msgid payload groups)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-unknown-or-duplicate-group-prepare-is-no-op
  (implies (and (fn-statep s)
                (not (fn-selection-validp groups (fn-state-groups s))))
           (equal (fn-accept-prepare s generation msgid payload groups)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-prepare-does-not-publish
  (implies (fn-statep s)
           (equal (fn-state-articles
                   (fn-accept-prepare s generation msgid payload groups))
                  (fn-state-articles s)))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-stale-completion-is-no-op
  (implies (and (fn-statep s)
                (not (fn-pending-matchesp (fn-state-pending s)
                                          txid generation)))
           (equal (fn-accept-complete s txid generation completion-status)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-stale-completion-preserves-state
  (implies (and (fn-statep s)
                (not (fn-pending-matchesp (fn-state-pending s)
                                          txid generation)))
           (fn-statep
            (fn-accept-complete s txid generation completion-status)))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-fenced-completion-is-no-op
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) t))
           (equal (fn-accept-complete s txid generation completion-status)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-indeterminate-completion-fences
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) nil)
                (fn-pending-matchesp (fn-state-pending s)
                                     txid generation))
           (equal (fn-state-fenced
                   (fn-accept-complete s txid generation :indeterminate))
                  t))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-indeterminate-completion-retains-pending
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) nil)
                (fn-pending-matchesp (fn-state-pending s)
                                     txid generation))
           (equal (fn-state-pending
                   (fn-accept-complete s txid generation :indeterminate))
                  (fn-state-pending s)))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-durable-completion-clears-pending
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) nil)
                (fn-pending-matchesp (fn-state-pending s)
                                     txid generation))
           (and (equal (fn-state-pending
                        (fn-accept-complete s txid generation :durable))
                       nil)
                (equal (fn-state-fenced
                        (fn-accept-complete s txid generation :durable))
                       nil)))
  :hints (("Goal" :in-theory (enable fn-accept-complete fn-install-pending))))

(defthm fn-durable-completion-publishes-message-id
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) nil)
                (fn-pending-matchesp (fn-state-pending s)
                                     txid generation))
           (equal
            (fn-acceptedp
             (fn-pending-msgid (fn-state-pending s))
             (fn-state-articles
              (fn-accept-complete s txid generation :durable)))
            t))
  :hints (("Goal" :in-theory (enable fn-accept-complete fn-install-pending
                                      fn-acceptedp))))

(defthm fn-durable-completion-installs-exact-pending-article
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) nil)
                (fn-pending-matchesp (fn-state-pending s)
                                     txid generation))
           (equal
            (fn-find-article
             (fn-pending-msgid (fn-state-pending s))
             (fn-state-articles
              (fn-accept-complete s txid generation :durable)))
            (fn-article-from-pending (fn-state-pending s))))
  :hints (("Goal" :in-theory (enable fn-accept-complete fn-install-pending
                                      fn-find-article fn-article-from-pending))))

(defthm fn-prepare-allocates-fresh-monotone-txid
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) nil)
                (null (fn-state-pending s))
                (natp generation)
                (stringp msgid)
                (fn-octet-listp payload)
                (fn-selection-validp groups (fn-state-groups s))
                (not (fn-acceptedp msgid (fn-state-articles s))))
           (and (equal
                 (fn-pending-txid
                  (fn-state-pending
                   (fn-accept-prepare s generation msgid payload groups)))
                 (fn-state-next-txid s))
                (equal
                 (fn-state-next-txid
                  (fn-accept-prepare s generation msgid payload groups))
                 (1+ (fn-state-next-txid s)))))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

; -----------------------------------------------------------------------------
; Export.  Records were disabled at their definitions.  The recognizers of
; records and of the state, the initial state, the transition halves and the
; three host transitions are withdrawn here; a book that must open one
; enables it locally.  Keystones and record lemmas stay enabled.  The list
; vocabulary of acceptance-alloc.lisp is untouched.
(in-theory (disable (:d fn-articlep) (:d fn-pendingp) (:d fn-statep) (:d fn-initial-state) (:d fn-install-pending) (:d fn-clear-pending) (:d fn-accept-prepare) (:d fn-accept-complete) (:d fn-accept-recover)))
