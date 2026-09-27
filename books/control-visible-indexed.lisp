; fn: the cancel refresh's row lookup through the Store's Message-ID index
; (lane post-alloc-2, 2026-09-27; flip-L8-2's per-POST walk).
;
; The refresh (books/control-visible.lisp fn-ctl-refresh-withdrawals, called
; by books/owner.lisp fn-own-refresh) finds a new article's row with
; `fn-ctl-row-event': a head-first walk of the whole history comparing one
; Message-ID per row.  The new article's row is at the tail, so every
; accepted POST walks all N events, again per cancel for its target
; (`fn-ctl-row-control') and per record naming the new article
; (`fn-ctl-resolve-tlocks').
;
; The Store already carries the index that answers it: `fn-sn-event-index',
; a pair of tries (sequence -> event, Message-ID -> the article records the
; history commits under it, oldest first), maintained as the index of the
; committed history (`fn-cei-correspondencep'; PRF-144/PRF-180,
; books/consumer-event-index-store-invariants.lisp fn-ceis-indexedp).
;
;   fn-ctl-row-event-ix  the Message-ID trie's first record R for M (the
;                        oldest), then the event at R's sequence in the
;                        sequence trie.  It is taken when that event's row
;                        is R and R is not repeated later in M's list;
;                        otherwise (never on a history the Store builds) the
;                        walk.  O(|M| + R's list) per lookup.
;
; No sequence invariant is needed for composites: the check above is what
; makes the event at R's sequence the FIRST event whose row carries M (a
; composite whose interned article's sequence were not its position would
; take the walk, not a wrong answer).  What IS needed of the history is that
; the refresh's row dispatch (`fn-ctl-event-row', by head and shape) and the
; index's (`fn-cei-event-article', by recognizer) agree on every event:
; `fn-ctl-rows-okp', which every Store history satisfies
; (fn-ctl-rows-okp-of-sf-state: fn-sf-statep conjoins fn-sf-record-listp,
; every record a Store event).
;
; KEYSTONES
;   fn-ctl-row-event-ix-is-row-event   the lookup is the walk, under the
;                                      index's correspondence and the rows'
;                                      agreement.
;   fn-ctl-refresh-withdrawals-ix-is-refresh-withdrawals
;                                      the refresh over the index is the
;                                      reference refresh (whose keystones,
;                                      fn-ctl-refresh-withdrawals-is-the-journal
;                                      and fn-ctl-refresh-visible-is-visible,
;                                      it thereby inherits).
; The owner-level twin and its keystone: books/owner-refresh-indexed.lisp.
(in-package "ACL2")
(include-book "control-visible")
(include-book "consumer-event-index")
(include-book "store-files")

; -----------------------------------------------------------------------------
; 1. The two dispatches agree on every Store event.

(defun fn-ctl-row-okp (e)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-ctl-event-row e)))
    (if r
        (and (fn-held-p r) (equal r (fn-cei-event-article e)))
      (not (fn-held-p (fn-cei-event-article e))))))

(defun fn-ctl-rows-okp (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (and (fn-ctl-row-okp (car records))
           (fn-ctl-rows-okp (cdr records)))
    t))

(local
 (defthm fn-ctl-held-p-is-held-shaped
   (implies (fn-held-p x) (fn-held-shapep x))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ctl-held-shape-len
   (implies (fn-held-shapep x) (equal (len x) 15))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-held-shapep)))))

(local
 (defthm fn-ctl-stxe-len
   (implies (fn-stxe-p x) (equal (len x) 8))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-stxe-shapep)
            :use fn-stxe-p-forward-shape))))

(local
 (defthm fn-ctl-stxk-len
   (implies (fn-stxk-p x) (equal (len x) 6))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-stxk-shapep)
            :use fn-stxk-p-forward-shape))))

(local
 (defthm fn-ctl-symbol-headed-events
   (and (implies (fn-store-retention-event-p x) (equal (car x) :retention))
        (implies (fn-cpe-eventp x) (equal (car x) :consumer))
        (implies (fn-th-topic-eventp x)
                 (member-equal (car x)
                               '(:topic-anchor :topic-admit :topic-admin-install))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-store-retention-event-p fn-store-event-nth
                                    fn-cpe-eventp fn-cp-nth
                                    fn-th-topic-eventp fn-th-local-admin-eventp
                                    fn-th-at)
                                   (fn-th-source-id-p fn-th-auth-ref-p
                                    fn-th-exact-octets-p fn-th-parents-p
                                    fn-record-uint32p fn-cpe-operationp fn-cp-uintp
                                    fn-record-metadata-bytes-p))))))

(local
 (defthm fn-ctl-stxe-natural-head
   (implies (fn-stxe-p x) (natp (car x)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-stxe-p fn-stxe-internals fn-ag-car
                                      fn-record-uint32p)))))

(local
 (defthm fn-ctl-stxk-natural-head
   (implies (fn-stxk-p x) (natp (car x)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-stxk-p fn-stxk-internals fn-ag-car
                                      fn-record-uint32p)))))

(local
 (defthm fn-ctl-row-okp-of-held
   (implies (fn-held-p e) (fn-ctl-row-okp e))
   :hints (("Goal" :in-theory (e/d (fn-ctl-row-okp fn-ctl-event-row fn-cei-event-article)
                                   (fn-held-p fn-hstxa-p))
            :use ((:instance fn-hstxa-p-forward-shape (x e)))))))
(local
 (defthm fn-ctl-row-okp-of-hstxa
   (implies (fn-hstxa-p e) (fn-ctl-row-okp e))
   :hints (("Goal" :in-theory (e/d (fn-ctl-row-okp fn-ctl-event-row fn-cei-event-article
                                    fn-replay-composite-held)
                                   (fn-held-p fn-hstxa-p))))))
(local
 (defthm fn-ctl-row-okp-of-symbol-headed
   (implies (or (fn-store-retention-event-p e) (fn-cpe-eventp e) (fn-th-topic-eventp e))
            (fn-ctl-row-okp e))
   :hints (("Goal" :in-theory (e/d (fn-ctl-row-okp fn-ctl-event-row fn-cei-event-article)
                                   (fn-held-p fn-hstxa-p fn-store-retention-event-p
                                    fn-cpe-eventp fn-th-topic-eventp))
            :use ((:instance fn-ctl-symbol-headed-events (x e))
                  (:instance fn-hstxa-p-forward-shape (x e)))))))
(local
 (defthm fn-ctl-row-okp-of-stxe-stxk
   (implies (or (fn-stxe-p e) (fn-stxk-p e))
            (fn-ctl-row-okp e))
   :hints (("Goal" :in-theory (e/d (fn-ctl-row-okp fn-ctl-event-row fn-cei-event-article)
                                   (fn-held-p fn-hstxa-p fn-stxe-p fn-stxk-p))
            :use ((:instance fn-hstxa-p-forward-shape (x e)))))))
(defthm fn-ctl-row-okp-of-store-event
  (implies (fn-store-event-p e)
           (fn-ctl-row-okp e))
  :hints (("Goal" :in-theory (e/d (fn-store-event-p)
                                  (fn-ctl-row-okp fn-held-p fn-hstxa-p fn-stxe-p fn-stxk-p
                                   fn-store-retention-event-p fn-cpe-eventp
                                   fn-th-topic-eventp)))))

(defthm fn-ctl-rows-okp-of-sf-record-listp
  (implies (fn-sf-record-listp records sequence lower frontier)
           (fn-ctl-rows-okp records))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
           :in-theory (e/d (fn-ctl-rows-okp fn-sf-record-listp)
                           (fn-ctl-row-okp fn-store-event-p
                            fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation)))))

; Every Store's history: fn-sn-statep conjoins fn-sf-statep.
(defthm fn-ctl-rows-okp-of-sf-state
  (implies (fn-sf-statep files)
           (fn-ctl-rows-okp (fn-sf-records files)))
  :hints (("Goal" :in-theory (e/d (fn-sf-statep)
                                  (fn-ctl-rows-okp fn-sf-record-listp)))))

; -----------------------------------------------------------------------------
; 2. The lookup.

(defun fn-ctl-row-event-ix (m records index)
  (declare (xargs :guard t))
  (if (stringp m)
      (let ((rs (fn-cei-msgid-records m index)))
        (if (consp rs)
            (let* ((r (car rs))
                   (e (fn-cei-get (fn-record-sequence r) index)))
              (if (and e
                       (equal (fn-ctl-event-row e) r)
                       (not (member-equal r (cdr rs))))
                  e
                (fn-ctl-row-event m records)))
          nil))
    (fn-ctl-row-event m records)))

; The sequence trie only ever answers an event it was given.
(local
 (defthm fn-ctl-cei-get-of-put-non-uint
   (implies (not (fn-cp-uintp sequence))
            (equal (fn-cei-get k (fn-cei-put sequence event index))
                   (fn-cei-get k index)))
   :hints (("Goal" :in-theory (enable fn-cei-get fn-cei-put fn-cei-sequence-trie)))))

(local
 (defthm fn-ctl-cei-get-of-non-uint
   (implies (not (fn-cp-uintp k))
            (equal (fn-cei-get k index) nil))
   :hints (("Goal" :in-theory (enable fn-cei-get)))))

(local
 (defthm fn-ctl-cei-get-of-build-aux-is-member
   (implies (fn-cei-get k (fn-cei-build-aux events sequence index))
            (or (member-equal (fn-cei-get k (fn-cei-build-aux events sequence index))
                              events)
                (equal (fn-cei-get k (fn-cei-build-aux events sequence index))
                       (fn-cei-get k index))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cei-build-aux events sequence index)
            :in-theory (e/d (fn-cei-build-aux) (fn-cei-get fn-cei-put))
            :expand ((fn-cei-build-aux events sequence index)))
           ("Subgoal *1/1" :cases ((fn-cp-uintp k)))
           ("Subgoal *1/1.1" :cases ((fn-cp-uintp sequence))))))

(local
 (defthm fn-ctl-cei-get-of-correspondence-is-member
   (implies (and (fn-cei-correspondencep index events)
                 (fn-cei-get k index))
            (member-equal (fn-cei-get k index) events))
   :hints (("Goal" :use ((:instance fn-ctl-cei-get-of-build-aux-is-member
                                    (sequence 0) (index nil)))
            :in-theory (e/d (fn-cei-correspondencep fn-cei-build)
                            (fn-cei-get fn-cei-build-aux))))))

; The spec's records are held rows carrying M.
(local
 (defthm fn-ctl-member-of-article-records-for
   (implies (member-equal r (fn-cei-article-records-for m events))
            (and (fn-held-p r) (equal (fn-record-msgid r) m)))
   :hints (("Goal" :in-theory (disable fn-held-p fn-cei-event-article)))))

; Under the rows' agreement: a row carrying M is in M's list...
(local
 (defthm fn-ctl-member-row-in-article-records-for
   (implies (and (fn-ctl-rows-okp records)
                 (member-equal e records)
                 (fn-ctl-event-row e)
                 (equal (fn-record-msgid (fn-ctl-event-row e)) m))
            (member-equal (fn-ctl-event-row e)
                          (fn-cei-article-records-for m records)))
   :hints (("Goal" :in-theory (disable fn-held-p fn-ctl-event-row fn-cei-event-article)))))

(local
 (defthm fn-ctl-car-of-article-records-for
   (implies (consp (fn-cei-article-records-for m events))
            (and (fn-held-p (car (fn-cei-article-records-for m events)))
                 (equal (fn-record-msgid (car (fn-cei-article-records-for m events))) m)))
   :hints (("Goal" :use ((:instance fn-ctl-member-of-article-records-for
                                    (r (car (fn-cei-article-records-for m events)))))
            :in-theory (disable fn-ctl-member-of-article-records-for fn-held-p
                                fn-cei-article-records-for)))))

; ... no list for M means no row carries M ...
(local
 (defthm fn-ctl-row-event-of-no-records
   (implies (and (stringp m)
                 (fn-ctl-rows-okp records)
                 (not (consp (fn-cei-article-records-for m records))))
            (equal (fn-ctl-row-event m records) nil))
   :hints (("Goal" :induct (fn-ctl-row-event m records)
            :in-theory (e/d (fn-ctl-row-event fn-ctl-rows-okp fn-ctl-row-okp
                             fn-cei-article-records-for)
                            (fn-held-p fn-ctl-event-row fn-cei-event-article))))))

; ... and an event whose row is the first of M's list, repeated nowhere
; after it, is the first event whose row carries M (a later event carrying
; M puts its row in the rest of the list).
(local
 (defthm fn-ctl-article-records-for-of-cons
   (implies (and (fn-ctl-row-okp x) (stringp m))
            (equal (fn-cei-article-records-for m (cons x rest))
                   (if (and (fn-ctl-event-row x)
                            (equal (fn-record-msgid (fn-ctl-event-row x)) m))
                       (cons (fn-ctl-event-row x) (fn-cei-article-records-for m rest))
                     (fn-cei-article-records-for m rest))))
   :hints (("Goal" :in-theory (e/d (fn-ctl-row-okp fn-cei-article-records-for)
                                   (fn-held-p fn-ctl-event-row fn-cei-event-article))))))

(local
 (defthm fn-ctl-later-row-is-in-the-rest
   (implies (and (stringp m)
                 (fn-ctl-rows-okp records)
                 (member-equal e records)
                 (fn-ctl-event-row e)
                 (equal (fn-record-msgid (fn-ctl-event-row e)) m)
                 (not (equal (fn-ctl-row-event m records) e)))
            (member-equal (fn-ctl-event-row e)
                          (cdr (fn-cei-article-records-for m records))))
   :hints (("Goal" :induct (fn-ctl-row-event m records)
            :in-theory (e/d (fn-ctl-row-event fn-ctl-rows-okp)
                            (fn-held-p fn-ctl-event-row fn-cei-event-article
                             fn-ctl-row-okp fn-cei-article-records-for))))))

(local
 (defthm fn-ctl-row-event-of-unrepeated-first
   (implies (and (stringp m)
                 (fn-ctl-rows-okp records)
                 (member-equal e records)
                 (fn-ctl-event-row e)
                 (equal (fn-ctl-event-row e)
                        (car (fn-cei-article-records-for m records)))
                 (not (member-equal (car (fn-cei-article-records-for m records))
                                    (cdr (fn-cei-article-records-for m records)))))
            (equal (fn-ctl-row-event m records) e))
   :hints (("Goal" :use (fn-ctl-later-row-is-in-the-rest
                         (:instance fn-ctl-car-of-article-records-for (events records)))
            :in-theory (disable fn-ctl-later-row-is-in-the-rest fn-ctl-car-of-article-records-for
                                fn-held-p fn-ctl-event-row fn-cei-event-article
                                fn-ctl-rows-okp fn-cei-article-records-for fn-ctl-row-event)))))

; KEYSTONE: the index lookup is the walk.  Subject: fn-ctl-row-event-ix,
; reached from books/owner-refresh-indexed.lisp fn-own-refresh-ix with
; INDEX = the Store's event index and RECORDS = its history.
(defthm fn-ctl-row-event-ix-is-row-event
  (implies (and (fn-cei-correspondencep index records)
                (fn-ctl-rows-okp records))
           (equal (fn-ctl-row-event-ix m records index)
                  (fn-ctl-row-event m records)))
  :hints (("Goal" :cases ((stringp m))
           :in-theory (e/d (fn-ctl-row-event-ix)
                           (fn-ctl-row-event fn-ctl-rows-okp fn-cei-msgid-records
                            fn-cei-get fn-ctl-event-row fn-held-p
                            fn-cei-correspondencep fn-cei-article-records-for
                            fn-ctl-row-event-of-unrepeated-first
                            fn-ctl-cei-get-of-correspondence-is-member)))
          ("Subgoal 1"
           :use ((:instance fn-cei-msgid-records-of-correspondence
                            (msgid m) (events records))
                 (:instance fn-ctl-car-of-article-records-for (events records))
                 (:instance fn-ctl-cei-get-of-correspondence-is-member
                            (k (fn-record-sequence (car (fn-cei-msgid-records m index))))
                            (events records))
                 (:instance fn-ctl-row-event-of-unrepeated-first
                            (e (fn-cei-get (fn-record-sequence
                                            (car (fn-cei-msgid-records m index)))
                                           index)))))))

; -----------------------------------------------------------------------------
; 3. The refresh over the index: each definition is its reference in
; books/control-visible.lisp with fn-ctl-row-event replaced by
; fn-ctl-row-event-ix.

(defun fn-ctl-row-control-ix (msgid records index)
  (declare (xargs :guard t))
  (let ((e (fn-ctl-row-event-ix msgid records index)))
    (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil)))

(defun fn-ctl-article-plan-ix (a verdicts records index configs)
  (declare (xargs :guard t))
  (if (consp a)
      (let* ((m (fn-article-msgid a))
             (e (fn-ctl-row-event-ix m records index))
             (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
             (target (fn-ctl-control-target control)))
        (if target
            (fn-ctl-w-with-tlocks
             (fn-ctl-withdrawal-plan
              m (fn-ctl-lookup-verdict m verdicts) target
              (fn-ctl-control-keys control)
              (fn-ctl-config-at (fn-store-event-txid e) configs))
             (fn-ctl-control-locks (fn-ctl-row-control-ix target records index)))
          nil))
    nil))

(defun fn-ctl-article-withdrawals-ix (a verdicts records index configs)
  (declare (xargs :guard t))
  (let ((plan (fn-ctl-article-plan-ix a verdicts records index configs)))
    (if (fn-ctl-withdrawalp plan) (list plan) nil)))

(defun fn-ctl-resolve-tlocks-ix (ws m records index)
  (declare (xargs :guard t))
  (if (fn-ctl-targets-p ws m)
      (fn-ctl-set-tlocks ws m (fn-ctl-control-locks
                               (fn-ctl-row-control-ix m records index)))
    ws))

; The discontinuity arm is the reference's (recovery's one-table pass).
(defun fn-ctl-refresh-withdrawals-ix (new old ws verdicts records index configs)
  (declare (xargs :guard t))
  (cond ((equal new old) ws)
        ((and (consp new) (equal (cdr new) old))
         (fn-ctl-prepend (fn-ctl-article-withdrawals-ix (car new) verdicts records
                                                        index configs)
                         (if (consp (car new))
                             (fn-ctl-resolve-tlocks-ix ws (fn-article-msgid (car new))
                                                       records index)
                           ws)))
        (t (fn-ctl-articles-withdrawals new verdicts records configs))))

(defthm fn-ctl-row-control-ix-is-row-control
  (implies (and (fn-cei-correspondencep index records)
                (fn-ctl-rows-okp records))
           (equal (fn-ctl-row-control-ix m records index)
                  (fn-ctl-row-control m records)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-row-control-ix fn-ctl-row-control)
                                  (fn-ctl-row-event-ix fn-ctl-row-event
                                   fn-ctl-rows-okp fn-cei-correspondencep)))))

(defthm fn-ctl-article-withdrawals-ix-is-article-withdrawals
  (implies (and (fn-cei-correspondencep index records)
                (fn-ctl-rows-okp records))
           (equal (fn-ctl-article-withdrawals-ix a verdicts records index configs)
                  (fn-ctl-article-withdrawals a verdicts records configs)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-article-withdrawals-ix fn-ctl-article-withdrawals
                                   fn-ctl-article-plan-ix fn-ctl-article-plan)
                                  (fn-ctl-row-event-ix fn-ctl-row-event
                                   fn-ctl-row-control-ix fn-ctl-row-control
                                   fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks
                                   fn-ctl-lookup-verdict fn-ctl-config-at
                                   fn-ctl-withdrawalp
                                   fn-ctl-rows-okp fn-cei-correspondencep)))))

(defthm fn-ctl-resolve-tlocks-ix-is-resolve-tlocks
  (implies (and (fn-cei-correspondencep index records)
                (fn-ctl-rows-okp records))
           (equal (fn-ctl-resolve-tlocks-ix ws m records index)
                  (fn-ctl-resolve-tlocks ws m records)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-resolve-tlocks-ix fn-ctl-resolve-tlocks)
                                  (fn-ctl-row-control-ix fn-ctl-row-control
                                   fn-ctl-set-tlocks fn-ctl-targets-p
                                   fn-ctl-rows-okp fn-cei-correspondencep)))))

; KEYSTONE: the refresh over the index is the reference refresh.  Subject:
; fn-ctl-refresh-withdrawals-ix, called by books/owner-refresh-indexed.lisp
; fn-own-refresh-ix.  With it, flip-L8-2's keystones over the reference
; (fn-ctl-refresh-withdrawals-is-the-journal, fn-ctl-refresh-visible-is-visible)
; hold of the twin.
(defthm fn-ctl-refresh-withdrawals-ix-is-refresh-withdrawals
  (implies (and (fn-cei-correspondencep index records)
                (fn-ctl-rows-okp records))
           (equal (fn-ctl-refresh-withdrawals-ix new old ws verdicts records index configs)
                  (fn-ctl-refresh-withdrawals new old ws verdicts records configs)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-refresh-withdrawals-ix fn-ctl-refresh-withdrawals)
                                  (fn-ctl-article-withdrawals-ix fn-ctl-article-withdrawals
                                   fn-ctl-resolve-tlocks-ix fn-ctl-resolve-tlocks
                                   fn-ctl-articles-withdrawals fn-ctl-prepend-is-append
                                   fn-ctl-rows-okp fn-cei-correspondencep)))))

(in-theory (disable fn-ctl-row-okp fn-ctl-rows-okp fn-ctl-row-event-ix
                    fn-ctl-row-control-ix fn-ctl-article-plan-ix
                    fn-ctl-article-withdrawals-ix fn-ctl-resolve-tlocks-ix
                    fn-ctl-refresh-withdrawals-ix))
