; fn M1: a small, executable logical acceptance machine.
;
; This book deliberately models no bytes-on-disk, network, or cryptography.  A
; host supplies a generation and reports an abstract persistence result.  The
; machine makes publication conditional on the matching durable result.

(in-package "ACL2")

(defun fn-ag-less (x y)
  (declare (xargs :guard t))
  (if (and (rationalp x) (rationalp y))
      (< x y)
    (let ((x1 (if (acl2-numberp x) x 0))
          (y1 (if (acl2-numberp y) y 0)))
      (or (< (realpart x1) (realpart y1))
          (and (equal (realpart x1) (realpart y1))
               (< (imagpart x1) (imagpart y1)))))))
(defthm fn-ag-less-is-less
  (equal (fn-ag-less x y) (< x y))
  :hints (("Goal" :use completion-of-<)))
; Raw Common Lisp CAR/CDR and list primitives have narrower domains than
; ACL2's total logic.  These guard-verified executable helpers reproduce the
; existing logical values on atoms and dotted lists.  MBE below keeps the
; original logical bodies and proves the alternate execution equal.
(defun fn-ag-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))
(defun fn-ag-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))
(defthm fn-ag-car-is-car (equal (fn-ag-car x) (car x)))
(defthm fn-ag-cdr-is-cdr (equal (fn-ag-cdr x) (cdr x)))
(defun fn-ag-member (x xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal x (car xs)) xs (fn-ag-member x (cdr xs)))
    nil))
(defthm fn-ag-member-is-member
  (equal (fn-ag-member x xs) (member-equal x xs)))
(defun fn-ag-append (xs ys)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-ag-append (cdr xs) ys)) ys))
(defthm fn-ag-append-is-append
  (equal (fn-ag-append xs ys) (append xs ys)))



; -----------------------------------------------------------------------------
; Primitive domains and list helpers

(defun fn-octetp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (integerp x) (<= 0 x) (<= x 255)))

(verify-guards fn-octetp)

(defun fn-octet-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (fn-octetp (car xs))
           (fn-octet-listp (cdr xs)))
    (null xs)))

(verify-guards fn-octet-listp)

(defun fn-string-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (stringp (car xs))
           (fn-string-listp (cdr xs)))
    (null xs)))

(verify-guards fn-string-listp)

(defun fn-no-duplicatesp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-no-duplicatesp (cdr xs)))
    t)
       :exec
(if (consp xs)
      (and (not (fn-ag-member (fn-ag-car xs) (fn-ag-cdr xs)))
           (fn-no-duplicatesp (fn-ag-cdr xs)))
    t)))

(verify-guards fn-no-duplicatesp)

(defun fn-subsetp (xs ys)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp xs)
      (and (member-equal (car xs) ys)
           (fn-subsetp (cdr xs) ys))
    t)
       :exec
(if (consp xs)
      (and (fn-ag-member (fn-ag-car xs) ys)
           (fn-subsetp (fn-ag-cdr xs) ys))
    t)))

(verify-guards fn-subsetp)

(defun fn-selection-validp (selection configured)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp selection)
       (fn-string-listp selection)
       (fn-no-duplicatesp selection)
       (fn-subsetp selection configured)))

(verify-guards fn-selection-validp)

(defun fn-fencedp (x)
  (declare (xargs :guard t :verify-guards nil))
  (or (null x) (equal x t)))

(verify-guards fn-fencedp)

; -----------------------------------------------------------------------------
; Local group watermarks and membership allocation

; A nexts list is kept in configured-group order.  Its entries are
; (group . next-number); numbers are allocated from the current watermark.
(defun fn-nexts-for-p (groups nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (and (consp nexts)
           (consp (car nexts))
           (equal (car (car nexts)) (car groups))
           (posp (cdr (car nexts)))
           (fn-nexts-for-p (cdr groups) (cdr nexts)))
    (null nexts)))

(verify-guards fn-nexts-for-p)

(defun fn-initial-nexts (groups)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (cons (cons (car groups) 1)
            (fn-initial-nexts (cdr groups)))
    nil))

(verify-guards fn-initial-nexts)

(defun fn-next-number (group nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp nexts)
      (if (equal group (car (car nexts)))
          (cdr (car nexts))
        (fn-next-number group (cdr nexts)))
    0)
       :exec
(if (consp nexts)
      (if (equal group (fn-ag-car (fn-ag-car nexts)))
          (fn-ag-cdr (fn-ag-car nexts))
        (fn-next-number group (fn-ag-cdr nexts)))
    0)))

(verify-guards fn-next-number)

(defun fn-bump-number (group nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp nexts)
      (if (equal group (car (car nexts)))
          (cons (cons (car (car nexts))
                      (1+ (cdr (car nexts))))
                (cdr nexts))
        (cons (car nexts)
              (fn-bump-number group (cdr nexts))))
    nil)
       :exec
(if (consp nexts)
      (if (equal group (fn-ag-car (fn-ag-car nexts)))
          (cons (cons (fn-ag-car (fn-ag-car nexts))
                      (1+ (fix (fn-ag-cdr (fn-ag-car nexts)))))
                (fn-ag-cdr nexts))
        (cons (fn-ag-car nexts)
              (fn-bump-number group (fn-ag-cdr nexts))))
    nil)))

(verify-guards fn-bump-number)

(defun fn-allocate-memberships (groups nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (cons (cons (car groups)
                  (fn-next-number (car groups) nexts))
            (fn-allocate-memberships
             (cdr groups)
             (fn-bump-number (car groups) nexts)))
    nil))

(verify-guards fn-allocate-memberships)

(defun fn-advance-nexts (groups nexts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (fn-advance-nexts (cdr groups)
                        (fn-bump-number (car groups) nexts))
    nexts))

(verify-guards fn-advance-nexts)

(defun fn-membership-listp (groups memberships)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (and (consp memberships)
           (consp (car memberships))
           (equal (car (car memberships)) (car groups))
           (posp (cdr (car memberships)))
           (fn-membership-listp (cdr groups) (cdr memberships)))
    (null memberships)))

(verify-guards fn-membership-listp)

(defun fn-memberships-at-watermarkp (memberships nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp memberships)
      (and (equal (cdr (car memberships))
                  (fn-next-number (car (car memberships)) nexts))
           (fn-memberships-at-watermarkp (cdr memberships) nexts))
    t)
       :exec
(if (consp memberships)
      (and (equal (fn-ag-cdr (fn-ag-car memberships))
                  (fn-next-number (fn-ag-car (fn-ag-car memberships)) nexts))
           (fn-memberships-at-watermarkp (fn-ag-cdr memberships) nexts))
    t)))

(verify-guards fn-memberships-at-watermarkp)

(defun fn-memberships-below-nextsp (memberships nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(if (consp memberships)
      (and (< (cdr (car memberships))
              (fn-next-number (car (car memberships)) nexts))
           (fn-memberships-below-nextsp (cdr memberships) nexts))
    t)
       :exec
(if (consp memberships)
      (and (fn-ag-less (fn-ag-cdr (fn-ag-car memberships))
              (fn-next-number (fn-ag-car (fn-ag-car memberships)) nexts))
           (fn-memberships-below-nextsp (fn-ag-cdr memberships) nexts))
    t)))

(verify-guards fn-memberships-below-nextsp)

; -----------------------------------------------------------------------------
; Articles, pending proposals, and state

; Article: (message-id payload requested-groups memberships archive-pin)
(defun fn-article-msgid (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car x)
       :exec
(fn-ag-car x)))

(verify-guards fn-article-msgid)
(defun fn-article-payload (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr x))
       :exec
(fn-ag-car (fn-ag-cdr x))))

(verify-guards fn-article-payload)
(defun fn-article-groups (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr x)))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(verify-guards fn-article-groups)
(defun fn-article-memberships (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr x))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(verify-guards fn-article-memberships)
(defun fn-article-pin (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr (cdr x)))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))

(verify-guards fn-article-pin)

(defun fn-make-article (msgid payload groups memberships pin)
  (declare (xargs :guard t :verify-guards nil))
  (cons msgid
        (cons payload
              (cons groups
                    (cons memberships
                          (cons pin nil))))))

(verify-guards fn-make-article)

(defun fn-articlep (configured x)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp x)
       (true-listp x)
       (equal (len x) 5)
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

; Pending: (txid generation message-id payload groups memberships archive-pin)
(defun fn-pending-txid (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car x)
       :exec
(fn-ag-car x)))

(verify-guards fn-pending-txid)
(defun fn-pending-generation (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr x))
       :exec
(fn-ag-car (fn-ag-cdr x))))

(verify-guards fn-pending-generation)
(defun fn-pending-msgid (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr x)))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(verify-guards fn-pending-msgid)
(defun fn-pending-payload (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr x))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(verify-guards fn-pending-payload)
(defun fn-pending-groups (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr (cdr x)))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))

(verify-guards fn-pending-groups)
(defun fn-pending-memberships (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))

(verify-guards fn-pending-memberships)
(defun fn-pending-pin (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))

(verify-guards fn-pending-pin)

(defun fn-make-pending (txid generation msgid payload groups memberships pin)
  (declare (xargs :guard t :verify-guards nil))
  (cons txid
        (cons generation
              (cons msgid
                    (cons payload
                          (cons groups
                                (cons memberships
                                      (cons pin nil))))))))

(verify-guards fn-make-pending)

(defun fn-pendingp (configured nexts next-txid x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
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
       (equal (fn-pending-pin x) t))
       :exec
(and (consp x)
       (true-listp x)
       (equal (len x) 7)
       (natp (fn-pending-txid x))
       (fn-ag-less (fn-pending-txid x) next-txid)
       (natp (fn-pending-generation x))
       (stringp (fn-pending-msgid x))
       (fn-octet-listp (fn-pending-payload x))
       (fn-selection-validp (fn-pending-groups x) configured)
       (fn-membership-listp (fn-pending-groups x)
                            (fn-pending-memberships x))
       (fn-memberships-at-watermarkp
        (fn-pending-memberships x) nexts)
       (equal (fn-pending-pin x) t))))

(verify-guards fn-pendingp)

(defun fn-make-state (groups nexts articles next-txid pending fenced)
  (declare (xargs :guard t :verify-guards nil))
  (cons groups
        (cons nexts
              (cons articles
                    (cons next-txid
                          (cons pending
                                (cons fenced nil)))))))

(verify-guards fn-make-state)

(defun fn-state-groups (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car s)
       :exec
(fn-ag-car s)))

(verify-guards fn-state-groups)
(defun fn-state-nexts (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr s))
       :exec
(fn-ag-car (fn-ag-cdr s))))

(verify-guards fn-state-nexts)
(defun fn-state-articles (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr s)))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))

(verify-guards fn-state-articles)
(defun fn-state-next-txid (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr s))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))

(verify-guards fn-state-next-txid)
(defun fn-state-pending (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr (cdr s)))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))

(verify-guards fn-state-pending)
(defun fn-state-fenced (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
(car (cdr (cdr (cdr (cdr (cdr s))))))
       :exec
(fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))))

(verify-guards fn-state-fenced)

(defun fn-statep (s)
  (declare (xargs :guard t :verify-guards nil))
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

(verify-guards fn-statep)

(defun fn-initial-state (groups)
  (declare (xargs :guard t :verify-guards nil))
  (fn-make-state groups (fn-initial-nexts groups) nil 0 nil nil))

(verify-guards fn-initial-state)

(defthm fn-initial-nexts-are-valid
  (implies (fn-string-listp groups)
           (fn-nexts-for-p groups (fn-initial-nexts groups)))
  :hints (("Goal" :induct (fn-initial-nexts groups))))

; -----------------------------------------------------------------------------
; Transitions

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
  (declare (xargs :guard t :verify-guards nil))
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

(verify-guards fn-accept-prepare)

; completion-status is one of :durable, :aborted, or :indeterminate.  Only a
; matching :durable completion publishes the proposal.  An indeterminate
; result retains it and fences ordinary submissions and completions until
; recovery resolves the proposal.
(defun fn-accept-complete (s txid generation completion-status)
  (declare (xargs :guard t :verify-guards nil))
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

(verify-guards fn-accept-complete)

; Recovery is an abstract host observation, not a disk algorithm.  It may
; resolve only the still-fenced matching proposal as committed or absent.
(defun fn-accept-recover (s txid generation recovery-result)
  (declare (xargs :guard t :verify-guards nil))
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

(verify-guards fn-accept-recover)

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
