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
(include-book "defrecord")
(include-book "records-shape")

; -----------------------------------------------------------------------------
; Article: (message-id payload requested-groups memberships archive-pin)

(fn-defrecord fn-article
  :constructor (fn-make-article msgid payload groups memberships pin stamp)
  :fields ((fn-article-msgid stringp)
           (fn-article-payload fn-octet-listp)
           (fn-article-groups
            (fn-selection-validp (fn-article-groups x) configured))
           (fn-article-memberships
            (fn-membership-listp (fn-article-groups x)
                                 (fn-article-memberships x)))
           (fn-article-pin (equal (fn-article-pin x) t))
           (fn-article-stamp fn-record-stampp))
  :recognizer-formals (configured))

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

(fn-defrecord fn-pending
  :constructor (fn-make-pending txid generation msgid payload groups
                                memberships pin stamp)
  :fields ((fn-pending-txid
            (and (natp (fn-pending-txid x))
                 (mbe :logic (< (fn-pending-txid x) next-txid)
                      :exec (fn-ag-less (fn-pending-txid x) next-txid))))
           (fn-pending-generation natp)
           (fn-pending-msgid stringp)
           (fn-pending-payload fn-octet-listp)
           (fn-pending-groups
            (fn-selection-validp (fn-pending-groups x) configured))
           (fn-pending-memberships
            (and (fn-membership-listp (fn-pending-groups x)
                                      (fn-pending-memberships x))
                 (fn-memberships-at-watermarkp
                  (fn-pending-memberships x) nexts)))
           (fn-pending-pin (equal (fn-pending-pin x) t))
           (fn-pending-stamp fn-record-stampp))
  :recognizer-formals (configured nexts next-txid))

; -----------------------------------------------------------------------------
; State: (groups nexts articles next-txid pending fenced)

; `fn-statep' is the carried invariant of docs/proof-style.md section 3, and
; its conjuncts are kept in the order they were written in: a conjunct is
; attached to the field whose position it held, so `natp' of the transaction
; counter rides with the watermarks and the three article conjuncts follow.
; The recognizer that ACL2 admits is therefore the same term as before.

(fn-defrecord fn-state
  :constructor (fn-make-state groups nexts articles next-txid pending fenced)
  :fields ((fn-state-groups
            (and (fn-string-listp (fn-state-groups x))
                 (fn-no-duplicatesp (fn-state-groups x))))
           (fn-state-nexts
            (and (fn-nexts-for-p (fn-state-groups x) (fn-state-nexts x))
                 (natp (fn-state-next-txid x))))
           (fn-state-articles
            (and (fn-article-listp (fn-state-groups x) (fn-state-articles x))
                 (fn-articles-freshp (fn-state-articles x))
                 (fn-articles-below-nextsp (fn-state-articles x)
                                           (fn-state-nexts x))))
           (fn-state-next-txid t)
           (fn-state-pending
            (or (null (fn-state-pending x))
                (and (not (fn-acceptedp
                           (fn-pending-msgid (fn-state-pending x))
                           (fn-state-articles x)))
                     (fn-pendingp (fn-state-groups x)
                                  (fn-state-nexts x)
                                  (fn-state-next-txid x)
                                  (fn-state-pending x)))))
           (fn-state-fenced
            (and (fn-fencedp (fn-state-fenced x))
                 (or (null (fn-state-fenced x))
                     (consp (fn-state-pending x)))))))

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
   (fn-pending-pin pending)
   (fn-pending-stamp pending)))

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
(defun fn-accept-prepare (s generation msgid payload groups stamp)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    (if (or (equal (fn-state-fenced s) t)
            (consp (fn-state-pending s))
            (not (natp generation))
            (not (stringp msgid))
            (not (fn-octet-listp payload))
            (not (fn-record-stampp stamp))
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
        t
        stamp)
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
           (equal (fn-accept-prepare s generation msgid payload groups stamp)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-duplicate-accepted-prepare-is-no-op
  (implies (and (fn-statep s)
                (fn-acceptedp msgid (fn-state-articles s)))
           (equal (fn-accept-prepare s generation msgid payload groups stamp)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-unknown-or-duplicate-group-prepare-is-no-op
  (implies (and (fn-statep s)
                (not (fn-selection-validp groups (fn-state-groups s))))
           (equal (fn-accept-prepare s generation msgid payload groups stamp)
                  s))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-prepare-does-not-publish
  (implies (fn-statep s)
           (equal (fn-state-articles
                   (fn-accept-prepare s generation msgid payload groups stamp))
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
                (fn-record-stampp stamp)
                (fn-selection-validp groups (fn-state-groups s))
                (not (fn-acceptedp msgid (fn-state-articles s))))
           (and (equal
                 (fn-pending-txid
                  (fn-state-pending
                   (fn-accept-prepare s generation msgid payload groups stamp)))
                 (fn-state-next-txid s))
                (equal
                 (fn-state-next-txid
                  (fn-accept-prepare s generation msgid payload groups stamp))
                 (1+ (fn-state-next-txid s)))))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

; -----------------------------------------------------------------------------
; Export.  Records were disabled at their definitions.  The recognizers of
; records and of the state, the initial state, the transition halves and the
; three host transitions are withdrawn here; a book that must open one
; enables it locally.  Keystones and record lemmas stay enabled.  The list
; vocabulary of acceptance-alloc.lisp is untouched.
(in-theory (disable (:d fn-articlep) (:d fn-pendingp) (:d fn-statep) (:d fn-initial-state) (:d fn-install-pending) (:d fn-clear-pending) (:d fn-accept-prepare) (:d fn-accept-complete) (:d fn-accept-recover)))
