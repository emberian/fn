; fn M1: a small, executable logical acceptance machine.
;
; This book deliberately models no bytes-on-disk, network, or cryptography.  A
; host supplies a generation and reports an abstract persistence result.  The
; machine makes publication conditional on the matching durable result.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Primitive domains and list helpers

(defun fn-octetp (x)
  (and (integerp x) (<= 0 x) (<= x 255)))

(defun fn-octet-listp (xs)
  (if (consp xs)
      (and (fn-octetp (car xs))
           (fn-octet-listp (cdr xs)))
    (null xs)))

(defun fn-string-listp (xs)
  (if (consp xs)
      (and (stringp (car xs))
           (fn-string-listp (cdr xs)))
    (null xs)))

(defun fn-no-duplicatesp (xs)
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-no-duplicatesp (cdr xs)))
    t))

(defun fn-subsetp (xs ys)
  (if (consp xs)
      (and (member-equal (car xs) ys)
           (fn-subsetp (cdr xs) ys))
    t))

(defun fn-selection-validp (selection configured)
  (and (consp selection)
       (fn-string-listp selection)
       (fn-no-duplicatesp selection)
       (fn-subsetp selection configured)))

(defun fn-fencedp (x)
  (or (null x) (equal x t)))

; -----------------------------------------------------------------------------
; Local group watermarks and membership allocation

; A nexts list is kept in configured-group order.  Its entries are
; (group . next-number); numbers are allocated from the current watermark.
(defun fn-nexts-for-p (groups nexts)
  (if (consp groups)
      (and (consp nexts)
           (consp (car nexts))
           (equal (car (car nexts)) (car groups))
           (posp (cdr (car nexts)))
           (fn-nexts-for-p (cdr groups) (cdr nexts)))
    (null nexts)))

(defun fn-initial-nexts (groups)
  (if (consp groups)
      (cons (cons (car groups) 1)
            (fn-initial-nexts (cdr groups)))
    nil))

(defun fn-next-number (group nexts)
  (if (consp nexts)
      (if (equal group (car (car nexts)))
          (cdr (car nexts))
        (fn-next-number group (cdr nexts)))
    0))

(defun fn-bump-number (group nexts)
  (if (consp nexts)
      (if (equal group (car (car nexts)))
          (cons (cons (car (car nexts))
                      (1+ (cdr (car nexts))))
                (cdr nexts))
        (cons (car nexts)
              (fn-bump-number group (cdr nexts))))
    nil))

(defun fn-allocate-memberships (groups nexts)
  (if (consp groups)
      (cons (cons (car groups)
                  (fn-next-number (car groups) nexts))
            (fn-allocate-memberships
             (cdr groups)
             (fn-bump-number (car groups) nexts)))
    nil))

(defun fn-advance-nexts (groups nexts)
  (if (consp groups)
      (fn-advance-nexts (cdr groups)
                        (fn-bump-number (car groups) nexts))
    nexts))

(defun fn-membership-listp (groups memberships)
  (if (consp groups)
      (and (consp memberships)
           (consp (car memberships))
           (equal (car (car memberships)) (car groups))
           (posp (cdr (car memberships)))
           (fn-membership-listp (cdr groups) (cdr memberships)))
    (null memberships)))

(defun fn-memberships-at-watermarkp (memberships nexts)
  (if (consp memberships)
      (and (equal (cdr (car memberships))
                  (fn-next-number (car (car memberships)) nexts))
           (fn-memberships-at-watermarkp (cdr memberships) nexts))
    t))

(defun fn-memberships-below-nextsp (memberships nexts)
  (if (consp memberships)
      (and (< (cdr (car memberships))
              (fn-next-number (car (car memberships)) nexts))
           (fn-memberships-below-nextsp (cdr memberships) nexts))
    t))

; -----------------------------------------------------------------------------
; Articles, pending proposals, and state

; Article: (message-id payload requested-groups memberships archive-pin)
(defun fn-article-msgid (x) (car x))
(defun fn-article-payload (x) (car (cdr x)))
(defun fn-article-groups (x) (car (cdr (cdr x))))
(defun fn-article-memberships (x) (car (cdr (cdr (cdr x)))))
(defun fn-article-pin (x) (car (cdr (cdr (cdr (cdr x))))))

(defun fn-make-article (msgid payload groups memberships pin)
  (cons msgid
        (cons payload
              (cons groups
                    (cons memberships
                          (cons pin nil))))))

(defun fn-articlep (configured x)
  (and (consp x)
       (true-listp x)
       (equal (len x) 5)
       (stringp (fn-article-msgid x))
       (fn-octet-listp (fn-article-payload x))
       (fn-selection-validp (fn-article-groups x) configured)
       (fn-membership-listp (fn-article-groups x)
                            (fn-article-memberships x))
       (equal (fn-article-pin x) t)))

(defun fn-article-msgids (xs)
  (if (consp xs)
      (cons (fn-article-msgid (car xs))
            (fn-article-msgids (cdr xs)))
    nil))

(defun fn-article-listp (configured xs)
  (if (consp xs)
      (and (fn-articlep configured (car xs))
           (not (member-equal (fn-article-msgid (car xs))
                              (fn-article-msgids (cdr xs))))
           (fn-article-listp configured (cdr xs)))
    (null xs)))

(defun fn-acceptedp (msgid articles)
  (if (consp articles)
      (or (equal msgid (fn-article-msgid (car articles)))
          (fn-acceptedp msgid (cdr articles)))
    nil))

(defun fn-find-article (msgid xs)
  (if (consp xs)
      (if (equal msgid (fn-article-msgid (car xs)))
          (car xs)
        (fn-find-article msgid (cdr xs)))
    nil))

(defun fn-pair-equalp (a b)
  (and (consp a)
       (consp b)
       (equal (car a) (car b))
       (equal (cdr a) (cdr b))))

(defun fn-pair-memberp (pair xs)
  (if (consp xs)
      (or (fn-pair-equalp pair (car xs))
          (fn-pair-memberp pair (cdr xs)))
    nil))

(defun fn-all-article-memberships (articles)
  (if (consp articles)
      (append (fn-article-memberships (car articles))
              (fn-all-article-memberships (cdr articles)))
    nil))

(defun fn-memberships-conflictsp (memberships articles)
  (if (consp memberships)
      (or (fn-pair-memberp (car memberships)
                           (fn-all-article-memberships articles))
          (fn-memberships-conflictsp (cdr memberships) articles))
    nil))

(defun fn-articles-freshp (articles)
  (if (consp articles)
      (and (not (fn-memberships-conflictsp
                 (fn-article-memberships (car articles))
                 (cdr articles)))
           (fn-articles-freshp (cdr articles)))
    t))

(defun fn-articles-below-nextsp (articles nexts)
  (if (consp articles)
      (and (fn-memberships-below-nextsp
            (fn-article-memberships (car articles)) nexts)
           (fn-articles-below-nextsp (cdr articles) nexts))
    t))

; Pending: (txid generation message-id payload groups memberships archive-pin)
(defun fn-pending-txid (x) (car x))
(defun fn-pending-generation (x) (car (cdr x)))
(defun fn-pending-msgid (x) (car (cdr (cdr x))))
(defun fn-pending-payload (x) (car (cdr (cdr (cdr x)))))
(defun fn-pending-groups (x) (car (cdr (cdr (cdr (cdr x))))))
(defun fn-pending-memberships (x)
  (car (cdr (cdr (cdr (cdr (cdr x)))))))
(defun fn-pending-pin (x)
  (car (cdr (cdr (cdr (cdr (cdr (cdr x))))))))

(defun fn-make-pending (txid generation msgid payload groups memberships pin)
  (cons txid
        (cons generation
              (cons msgid
                    (cons payload
                          (cons groups
                                (cons memberships
                                      (cons pin nil))))))))

(defun fn-pendingp (configured nexts next-txid x)
  (and (consp x)
       (true-listp x)
       (equal (len x) 7)
       (natp (fn-pending-txid x))
       (< (fn-pending-txid x) next-txid)
       (natp (fn-pending-generation x))
       (stringp (fn-pending-msgid x))
       (fn-octet-listp (fn-pending-payload x))
       (fn-selection-validp (fn-pending-groups x) configured)
       (fn-membership-listp (fn-pending-groups x)
                            (fn-pending-memberships x))
       (fn-memberships-at-watermarkp
        (fn-pending-memberships x) nexts)
       (equal (fn-pending-pin x) t)))

(defun fn-make-state (groups nexts articles next-txid pending fenced)
  (cons groups
        (cons nexts
              (cons articles
                    (cons next-txid
                          (cons pending
                                (cons fenced nil)))))))

(defun fn-state-groups (s) (car s))
(defun fn-state-nexts (s) (car (cdr s)))
(defun fn-state-articles (s) (car (cdr (cdr s))))
(defun fn-state-next-txid (s) (car (cdr (cdr (cdr s)))))
(defun fn-state-pending (s) (car (cdr (cdr (cdr (cdr s))))))
(defun fn-state-fenced (s) (car (cdr (cdr (cdr (cdr (cdr s)))))))

(defun fn-statep (s)
  (and (consp s)
       (true-listp s)
       (equal (len s) 6)
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

(defun fn-initial-state (groups)
  (fn-make-state groups (fn-initial-nexts groups) nil 0 nil nil))

(defthm fn-initial-nexts-are-valid
  (implies (fn-string-listp groups)
           (fn-nexts-for-p groups (fn-initial-nexts groups)))
  :hints (("Goal" :induct (fn-initial-nexts groups))))

; -----------------------------------------------------------------------------
; Transitions

(defun fn-pending-matchesp (pending txid generation)
  (and (consp pending)
       (equal txid (fn-pending-txid pending))
       (equal generation (fn-pending-generation pending))))

(defun fn-article-from-pending (pending)
  (fn-make-article
   (fn-pending-msgid pending)
   (fn-pending-payload pending)
   (fn-pending-groups pending)
   (fn-pending-memberships pending)
   (fn-pending-pin pending)))

(defun fn-install-pending (s)
  (let ((p (fn-state-pending s)))
    (fn-make-state
     (fn-state-groups s)
     (fn-advance-nexts (fn-pending-groups p) (fn-state-nexts s))
     (cons (fn-article-from-pending p) (fn-state-articles s))
     (fn-state-next-txid s)
     nil
     nil)))

(defun fn-clear-pending (s)
  (fn-make-state (fn-state-groups s)
                 (fn-state-nexts s)
                 (fn-state-articles s)
                 (fn-state-next-txid s)
                 nil
                 nil))

; Prepare reserves a unique txid and stages every local membership.  It does
; not change committed articles or group watermarks.
(defun fn-accept-prepare (s generation msgid payload groups)
  (if (not (fn-statep s))
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

; completion-status is one of :durable, :aborted, or :indeterminate.  Only a
; matching :durable completion publishes the proposal.  An indeterminate
; result retains it and fences ordinary submissions and completions until
; recovery resolves the proposal.
(defun fn-accept-complete (s txid generation completion-status)
  (if (not (fn-statep s))
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

; Recovery is an abstract host observation, not a disk algorithm.  It may
; resolve only the still-fenced matching proposal as committed or absent.
(defun fn-accept-recover (s txid generation recovery-result)
  (if (not (fn-statep s))
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

; -----------------------------------------------------------------------------
; First proof events.  These are ordinary theorem events with no proof
; shortcuts or trust tags.  The current bounded slice intentionally leaves
; the larger allocation/refinement preservation chain for a later book.

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
