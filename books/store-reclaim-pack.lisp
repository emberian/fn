; fn: content reclamation's per-article rewrite (STO-017, PRF-119).
;
; `operator CONFIG store reclaim' removes released payload octets from the
; disk.  It never edits a file in place.  On the record log (format 9, the
; one store format) it checkpoints the REWRITTEN history and drops the
; segments the checkpoint covers (books/store-log-reclaim.lisp
; `fn-lgr-decide-stream', over the fold of books/store-reclaim-stream.lisp).
; This book decides the rewrite: the same event list with each reclaimable
; article record re-encoded with its payload replaced by
; `fn-rcl-tombstone-of', and every other event's octets exact.  (Before the
; record log it decided a reclaiming pack generation; the pack layer went
; with the per-file layout, design 2026-09-27 storage-log section 9 row 5.)
;
; Three operations are kept apart (specs/storage.md STO-017): the exact
; event history is kept; history compaction is not done here; content
; reclamation changes only payload octets of released article records and
; keeps every identity, number, obligation and anti-resurrection fact the
; record carries.
;
; What is decided here, over the functions the host calls
; (host/checkpoint-host.lisp `fn-store-log-reclaim-event' = `fn-rclp-event'
; per record and `fn-store-reclaim-context' = `fn-rclp-ctx', called by
; host/native/checkpoint.lisp `fnn-log-reclaim-steps'):
;   - which events change: only a legacy article record whose article is
;     `fn-rcl-reclaimable' in the opened store (KEYSTONE
;     `fn-rclp-events-never-touch-a-held-article');
;   - what a changed event is: the encoding of the same record with the
;     tombstone as its payload, and nothing else of it changes
;     (`fn-rclp-event-decodes-to-the-tombstoned-record');
;   - that the new list is still a well-formed event list
;     (`fn-rclp-events-keep-the-summary-shape');
;   - that a rerun after any cut rewrites nothing more
;     (`fn-rclp-events-idempotent');
;   - the octets freed in the committed history the admission gate counts
;     (`fn-rclp-freed-octets-account').
(in-package "ACL2")
(include-book "store-reclaim-holders")
(include-book "checkpoint-compaction")
(include-book "expiry-verdict")

; The record an article record becomes: the same fields with the tombstone
; of its payload in place of the payload, and the retention charge of its
; archive pin reduced to the one permanent history unit (reclaim-lifecycle-2,
; step 2; D03).  The release is the operator's authorized retention rule
; (the configuration record `retention set' wrote, which
; `fn-rcl-reclaimable' reads); the pin itself stays (every bound article
; keeps a live pin, `fn-node-statep'), and what the ledger keeps for it is
; exactly what `fn-retain-release' keeps for a released obligation: one
; unit.  The content charge (pages) returns to the ledger's headroom when
; the rewritten history is replayed.  Only the rewritten article's own pin
; changes (every other event is the same octets,
; `fn-rclp-events-never-touch-a-held-article',
; `fn-rclp-events-keep-every-other-kind').
(defconst *fn-rclp-history-unit* 1)
(defun fn-rclp-tombstoned (r)
  (declare (xargs :guard (fn-rcl-payload-profilep (fn-record-payload r))
                  :verify-guards nil))
  (fn-record-make (fn-record-sequence r) (fn-record-txid r)
                  (fn-record-generation r) (fn-record-msgid r)
                  (fn-rcl-tombstone-of (fn-record-payload r)
                                       (fn-record-string-octets (fn-record-msgid r)))
                  (fn-record-groups r) (fn-record-obligation-id r)
                  (fn-record-content-subject r) (fn-record-release-evidence r)
                  *fn-rclp-history-unit* (fn-record-stamp r) (fn-record-binding r)))

; The articles indexed by Message-ID (row A8): the first article naming a
; Message-ID is the one bound, as `fn-find-article's walk finds it
; (`fn-rclp-article-index-finds-the-article').  The context carries it as a
; fast alist, so one record's step is one hashed lookup where the walk was
; linear in the Store's articles (485 s at 100k for `store reclaim
; --dry-run', every record walking the list).  The lookup asks `make-fast-alist'
; of the slot: the context's own index is already fast, so that is a table
; probe; a context built another way (a witness's literal list) is made fast
; there rather than breaking on ACL2's slow-alist discipline.
;
; It is built in ONE forward pass in history order, tail-recursively (a
; 25,000-article Store exhausted the control stack through a consing
; recursion): each article is bound unless an earlier one already binds its
; Message-ID (one hashed probe), so the first article naming a Message-ID is
; the binding `hons-get' finds.  No reversed copy of the article list is
; made (the earlier build reversed the whole list first so that the last
; `hons-acons' was the first article).
(defun fn-rclp-index-into (xs acc)
  (declare (xargs :guard t))
  (if (consp xs)
      (let ((m (fn-article-msgid (car xs))))
        (fn-rclp-index-into (cdr xs)
                            (if (hons-get m acc) acc (hons-acons m (car xs) acc))))
    acc))

(defun fn-rclp-article-index (articles)
  (declare (xargs :guard t))
  (fn-rclp-index-into articles nil))

; One step's correspondence: after the fold over XS from ACC, a Message-ID
; bound in ACC keeps its binding, and any other is bound to the first
; article of XS naming it (nil when none does).
(defthm fn-rclp-index-into-finds
  (equal (cdr (hons-assoc-equal msgid (fn-rclp-index-into xs acc)))
         (if (hons-assoc-equal msgid acc)
             (cdr (hons-assoc-equal msgid acc))
           (fn-find-article msgid xs)))
  :hints (("Goal" :induct (fn-rclp-index-into xs acc))))

(defthm fn-rclp-article-index-finds-the-article
  (equal (cdr (hons-assoc-equal msgid (fn-rclp-article-index articles)))
         (fn-find-article msgid articles)))

(in-theory (disable fn-rclp-article-index))

; The index as the host builds it (`fn-rclp-ctx-expiring').
(defun fn-rclp-index-built (articles)
  (declare (xargs :guard t))
  (fn-rclp-index-into articles nil))

(defthm fn-rclp-index-built-is-the-index-by-definition
  (equal (fn-rclp-index-built articles)
         (fn-rclp-article-index articles))
  :hints (("Goal" :in-theory (enable fn-rclp-article-index))))

; CTX is (RULE NOW HOLDERS VERDICTS ARTICLES EXPIRED INDEX) of the opened
; store: EXPIRED the Message-IDs the operator's expiry policy expires at NOW
; (books/expiry `fn-xpy-expired-set'; nil when there is none); INDEX
; `fn-rclp-article-index' of ARTICLES (`fn-rclp-ctx-expiring' builds it).
; An article is released by the rule or by the policy, and kept by every
; holder either way (books/expiry-verdict
; `fn-xpy-releasablep-is-rule-or-expired-and-unheld').
(defun fn-rclp-ctx-reclaimable (ctx msgid)
  (declare (xargs :guard t :verify-guards nil))
  (fn-xpy-releasablep (fn-rcl-nth 0 ctx) (fn-rcl-nth 1 ctx) (fn-rcl-nth 2 ctx)
                      (fn-rcl-nth 3 ctx) (fn-rcl-nth 5 ctx)
                      (cdr (hons-get msgid (make-fast-alist (fn-rcl-nth 6 ctx))))))

; Whether the event OCTETS is rewritten: a legacy article record, not already
; a tombstone, whose article the context finds reclaimable, and whose
; tombstoned record is a record (its payload within the record codec).
(defun fn-rclp-rewrites-p (octets ctx)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-record-decode-exact octets)))
    (and (fn-record-result-okp d)
         (fn-rcl-payload-profilep (fn-record-payload (fn-record-result-record d)))
         (not (fn-rcl-tombstonep (fn-record-payload (fn-record-result-record d))))
         (fn-rclp-ctx-reclaimable ctx (fn-record-msgid (fn-record-result-record d)))
         (fn-record-p (fn-rclp-tombstoned (fn-record-result-record d))))))

(defun fn-rclp-event (octets ctx)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-rclp-rewrites-p octets ctx)
      (fn-record-encode
       (fn-rclp-tombstoned (fn-record-result-record (fn-record-decode-exact octets))))
    octets))

(defun fn-rclp-events (events ctx)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (cons (fn-rclp-event (car events) ctx) (fn-rclp-events (cdr events) ctx))
    events))

; The Message-IDs actually rewritten, in history order (what the verb reports).
(defun fn-rclp-rewritten-msgids (events ctx)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (if (fn-rclp-rewrites-p (car events) ctx)
          (cons (fn-record-msgid (fn-record-result-record
                                  (fn-record-decode-exact (car events))))
                (fn-rclp-rewritten-msgids (cdr events) ctx))
        (fn-rclp-rewritten-msgids (cdr events) ctx))
    nil))

(defun fn-rclp-octets (events)
  (declare (xargs :guard t))
  (if (consp events)
      (+ (len (car events)) (fn-rclp-octets (cdr events)))
    0))

; The octets freed: for each rewritten event, its length less its
; replacement's.  An integer; the tombstone is 145 octets plus the Path agent,
; so a payload shorter than that frees a negative amount, which the verb
; reports and never hides.
(defun fn-rclp-freed (events ctx)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (+ (- (len (car events)) (len (fn-rclp-event (car events) ctx)))
         (fn-rclp-freed (cdr events) ctx))
    0))

; -----------------------------------------------------------------------------
; What a rewritten event is.

(local (in-theory (disable fn-rcl-payload-profilep
                           fn-rcl-tombstone-of fn-rcl-tombstonep fn-rcl-reclaimable
                           fn-record-result-okp fn-record-result-record)))

(defthm fn-rclp-event-of-an-unrewritten-event-by-definition
  (implies (not (fn-rclp-rewrites-p octets ctx))
           (equal (fn-rclp-event octets ctx) octets)))

; A rewritten event decodes to the tombstoned record: every field of the
; record the event held, with the payload replaced by its tombstone and the
; charge released to the history unit.
(defthm fn-rclp-event-decodes-to-the-tombstoned-record
  (implies (fn-rclp-rewrites-p octets ctx)
           (let ((new (fn-record-decode-exact (fn-rclp-event octets ctx)))
                 (old (fn-record-result-record (fn-record-decode-exact octets))))
             (and (fn-record-result-okp new)
                  (equal (fn-record-result-record new) (fn-rclp-tombstoned old))
                  (equal (fn-record-payload (fn-record-result-record new))
                         (fn-rcl-tombstone-of
                          (fn-record-payload old)
                          (fn-record-string-octets (fn-record-msgid old))))
                  (equal (fn-record-msgid (fn-record-result-record new))
                         (fn-record-msgid old))
                  (equal (fn-record-groups (fn-record-result-record new))
                         (fn-record-groups old))
                  (equal (fn-record-sequence (fn-record-result-record new))
                         (fn-record-sequence old))
                  (equal (fn-record-txid (fn-record-result-record new))
                         (fn-record-txid old))
                  (equal (fn-record-generation (fn-record-result-record new))
                         (fn-record-generation old))
                  (equal (fn-record-obligation-id (fn-record-result-record new))
                         (fn-record-obligation-id old))
                  (equal (fn-record-content-subject (fn-record-result-record new))
                         (fn-record-content-subject old))
                  (equal (fn-record-release-evidence (fn-record-result-record new))
                         (fn-record-release-evidence old))
                  (equal (fn-record-charge (fn-record-result-record new))
                         *fn-rclp-history-unit*)
                  (equal (fn-record-stamp (fn-record-result-record new))
                         (fn-record-stamp old)))))
  :hints (("Goal" :in-theory (disable fn-rclp-tombstoned)
                  :use ((:instance fn-record-round-trip-succeeds
                                   (record (fn-rclp-tombstoned
                                            (fn-record-result-record
                                             (fn-record-decode-exact octets)))))))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-rclp-tombstoned)))))

; PRF-1089: the actual host-called per-event rewrite preserves the selected
; relay-v1 commitment, in addition to every record identity field above.
; This says nothing about injectivity of that commitment.
(defthm fn-rclp-event-retains-article-subject
  (implies (fn-rclp-rewrites-p octets ctx)
           (equal
            (fn-rcl-tomb-article-subject
             (fn-record-payload
              (fn-record-result-record (fn-record-decode-exact
                                        (fn-rclp-event octets ctx)))))
            (fn-asj-subject
             (fn-record-payload
              (fn-record-result-record (fn-record-decode-exact octets))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (fn-rclp-event-decodes-to-the-tombstoned-record
                        (:instance fn-rcl-tombstone-of-fields
                         (payload (fn-record-payload
                                   (fn-record-result-record (fn-record-decode-exact octets))))
                         (msgid (fn-record-string-octets
                                 (fn-record-msgid
                                  (fn-record-result-record (fn-record-decode-exact octets))))))))))

; -----------------------------------------------------------------------------
; The new list is an event list on the same terms as the old.

(local
 (defthm store-event-decode-of-a-record-octets
   (implies (fn-record-result-okp (fn-record-decode-exact octets))
            (equal (fn-store-event-decode-exact octets)
                   (fn-record-decode-exact octets)))
   :hints (("Goal" :in-theory (enable fn-store-event-decode-exact)))))

(local
 (defthm record-result-shape
   (implies (fn-record-result-okp result)
            (and (equal (car result) :ok)
                 (equal (fn-cc-nth 1 result) (fn-record-result-record result))))
   :hints (("Goal" :in-theory (enable fn-record-result-okp fn-record-result-record
                                      fn-cbor-ag-car fn-cc-nth)))))

(local
 (defthm store-event-fields-of-a-record
   (implies (fn-record-p r)
            (and (fn-wire-event-p r)
                 (equal (fn-wire-event-sequence r) (fn-record-sequence r))
                 (equal (fn-wire-event-txid r) (fn-record-txid r))
                 (equal (fn-wire-event-generation r) (fn-record-generation r))))
   :hints (("Goal" :in-theory (enable fn-wire-event-p fn-wire-event-sequence
                                      fn-wire-event-txid fn-wire-event-generation)))))

(local
 (defthm rewritten-event-facts
   (implies (fn-rclp-rewrites-p octets ctx)
            (let ((new (fn-rclp-event octets ctx)))
              (and (fn-cbor-octet-listp new)
                   (fn-cbor-octet-listp octets)
                   (equal (car (fn-store-event-decode-exact octets)) :ok)
                   (fn-wire-event-p (fn-cc-nth 1 (fn-store-event-decode-exact octets)))
                   (equal (car (fn-store-event-decode-exact new)) :ok)
                   (fn-wire-event-p (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                   (equal (fn-wire-event-sequence
                           (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                          (fn-wire-event-sequence
                           (fn-cc-nth 1 (fn-store-event-decode-exact octets))))
                   (equal (fn-wire-event-txid
                           (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                          (fn-wire-event-txid
                           (fn-cc-nth 1 (fn-store-event-decode-exact octets))))
                   (equal (fn-wire-event-generation
                           (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                          (fn-wire-event-generation
                           (fn-cc-nth 1 (fn-store-event-decode-exact octets)))))))
   :hints (("Goal" :in-theory (disable fn-rclp-event fn-rclp-tombstoned
                                       fn-rclp-event-decodes-to-the-tombstoned-record)
                   :use (fn-rclp-event-decodes-to-the-tombstoned-record
                         (:instance fn-record-decode-exact-yields-a-record
                                    (octets (fn-rclp-event octets ctx)))
                         (:instance fn-record-decode-exact-yields-a-record
                                    (octets octets))
                         (:instance fn-record-accepted-input-is-an-octet-list
                                    (octets (fn-rclp-event octets ctx)))
                         (:instance fn-record-accepted-input-is-an-octet-list
                                    (octets octets))))
           (and stable-under-simplificationp
                '(:in-theory (enable fn-rclp-rewrites-p))))))

(local
 (defthm cc-listp-of-a-rewritten-head
   (implies (fn-rclp-rewrites-p a ctx)
            (equal (fn-cc-octet-event-listp (cons (fn-rclp-event a ctx) rest) seq lo hi)
                   (fn-cc-octet-event-listp (cons a rest) seq lo hi)))
   :hints (("Goal" :in-theory (e/d () (fn-rclp-event fn-rclp-rewrites-p
                                       fn-store-event-decode-exact
                                       store-event-decode-of-a-record-octets
                                       record-result-shape rewritten-event-facts))
                   :use ((:instance rewritten-event-facts (octets a)))
                   :expand ((fn-cc-octet-event-listp (cons (fn-rclp-event a ctx) rest)
                                                     seq lo hi)
                            (fn-cc-octet-event-listp (cons a rest) seq lo hi))))))

(local
 (defthm cc-listp-of-any-head
   (equal (fn-cc-octet-event-listp (cons (fn-rclp-event a ctx) rest) seq lo hi)
          (fn-cc-octet-event-listp (cons a rest) seq lo hi))
   :hints (("Goal" :cases ((fn-rclp-rewrites-p a ctx))
                   :in-theory (disable fn-rclp-event fn-rclp-rewrites-p
                                       fn-store-event-decode-exact)))))

;  KEYSTONE (the rewrite is a history).  The rewrite is an event list
; from SEQUENCE with txids in [LOWER, UPPER) (`fn-cc-octet-event-listp')
; exactly when the committed history is, so the replay the log reclaim runs
; before its checkpoint reads it through the one Store decoder.
(defthm fn-rclp-events-keep-the-summary-shape
  (equal (fn-cc-octet-event-listp (fn-rclp-events events ctx) sequence lower upper)
         (fn-cc-octet-event-listp events sequence lower upper))
  :hints (("Goal" :induct (fn-cc-octet-event-listp events sequence lower upper)
                  :in-theory (e/d (fn-cc-octet-event-listp)
                                  (fn-rclp-event fn-rclp-rewrites-p
                                   fn-store-event-decode-exact)))))

(defthm fn-rclp-events-keep-the-length
  (equal (len (fn-rclp-events events ctx)) (len events)))

; -----------------------------------------------------------------------------
; Idempotence: a rerun after a cut rewrites nothing more.

(local
 (defthm rewritten-event-payload-is-a-tombstone
   (implies (fn-rclp-rewrites-p octets ctx)
            (fn-rcl-tombstonep
             (fn-record-payload
              (fn-record-result-record
               (fn-record-decode-exact (fn-rclp-event octets ctx))))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
                   :use (fn-rclp-event-decodes-to-the-tombstoned-record
                         (:instance fn-rcl-tombstone-of-fields
                                    (payload (fn-record-payload
                                              (fn-record-result-record
                                               (fn-record-decode-exact octets))))
                                    (msgid (fn-record-string-octets
                                            (fn-record-msgid
                                             (fn-record-result-record
                                              (fn-record-decode-exact octets)))))))))))

(local
 (defthm rewritten-event-is-not-rewritten-again
   (implies (fn-rclp-rewrites-p octets ctx)
            (not (fn-rclp-rewrites-p (fn-rclp-event octets ctx) ctx2)))
   :hints (("Goal" :in-theory (union-theories '(fn-rclp-rewrites-p)
                                              (theory 'minimal-theory))
                   :use rewritten-event-payload-is-a-tombstone))))

;  KEYSTONE (convergence).  An event the reclaim rewrote is never
; rewritten again, under any later context (the store reopened after the
; reclaim, a later rule, other holders): a reclaimed payload stays reclaimed.
(defthm fn-rclp-a-reclaimed-event-stays-reclaimed
  (implies (fn-rclp-rewrites-p octets ctx)
           (equal (fn-rclp-event (fn-rclp-event octets ctx) ctx2)
                  (fn-rclp-event octets ctx)))
  :hints (("Goal" :in-theory (disable fn-rclp-rewrites-p
                                      rewritten-event-is-not-rewritten-again)
                  :use rewritten-event-is-not-rewritten-again)))

(local
 (defthm event-idempotent
   (equal (fn-rclp-event (fn-rclp-event octets ctx) ctx)
          (fn-rclp-event octets ctx))
   :hints (("Goal" :cases ((fn-rclp-rewrites-p octets ctx))
                   :in-theory (disable fn-rclp-rewrites-p fn-rclp-event)))))

; And a rerun with the same context writes the same history.
(defthm fn-rclp-events-idempotent
  (equal (fn-rclp-events (fn-rclp-events events ctx) ctx)
         (fn-rclp-events events ctx))
  :hints (("Goal" :induct (fn-rclp-events events ctx)
                  :in-theory (disable fn-rclp-rewrites-p fn-rclp-event))))

; -----------------------------------------------------------------------------
; A held article is never touched.

(local
 (defthm rewrites-p-means-reclaimable
   (implies (fn-rclp-rewrites-p octets (list rule now h verdicts articles expired
                                             (fn-rclp-article-index articles)))
            (fn-xpy-releasablep rule now h verdicts expired
                                (fn-find-article
                                 (fn-record-msgid (fn-record-result-record
                                                   (fn-record-decode-exact octets)))
                                 articles)))
   :hints (("Goal" :in-theory (enable fn-rclp-rewrites-p fn-rclp-ctx-reclaimable)))))

(local
 (defthm nth-of-rclp-events
   (equal (nth i (fn-rclp-events events ctx))
          (if (< (nfix i) (len events))
              (fn-rclp-event (nth i events) ctx)
            nil))
   :hints (("Goal" :induct (nth i events) :in-theory (disable fn-rclp-event)))))

;  KEYSTONE (PRF-119, a held article is never touched).  The subject is
; the event list the host publishes.  If the I-th committed event is an
; article record whose article any obligation of the lifetimes table names
; (reader pin, consumer cursor, undelivered feed, BP obligation), or whose
; Store verdict needs its payload, or the rule is keep-forever and the
; expiry policy has not expired it, the I-th event of the rewritten history
; is the same octets.  Under every expiry policy (Q14): expiry releases no
; held article.
(defthm fn-rclp-events-never-touch-a-held-article
  (let* ((o (nth i events))
         (m (fn-record-msgid (fn-record-result-record (fn-record-decode-exact o))))
         (article (fn-find-article m articles)))
    (implies (or (fn-rcl-some-names-p (fn-rcl-obligations h)
                                      (fn-article-msgid article)
                                      (fn-article-memberships article))
                 (fn-rcl-verdict-heldp (fn-article-msgid article) verdicts)
                 (and (equal rule '(:keep-forever))
                      (not (fn-xpy-expiredp (fn-article-msgid article) expired))))
             (equal (nth i (fn-rclp-events events
                                           (list rule now h verdicts articles expired
                                                 (fn-rclp-article-index articles))))
                    (nth i events))))
  :hints (("Goal" :in-theory (disable fn-rclp-event fn-rclp-rewrites-p
                                      fn-rcl-some-names-p fn-rcl-obligations
                                      fn-rcl-verdict-heldp
                                      rewrites-p-means-reclaimable)
                  :use ((:instance rewrites-p-means-reclaimable
                                   (octets (nth i events)))
                        (:instance fn-xpy-releasablep-is-rule-or-expired-and-unheld
                                   (article (fn-find-article
                                             (fn-record-msgid
                                              (fn-record-result-record
                                               (fn-record-decode-exact (nth i events))))
                                             articles)))
                        (:instance fn-rcl-reclaimable-is-no-obligation-names-it
                                   (article (fn-find-article
                                             (fn-record-msgid
                                              (fn-record-result-record
                                               (fn-record-decode-exact (nth i events))))
                                             articles)))))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-rclp-event)))))

;  KEYSTONE (PRF-119, PRF-088: a held article is never touched), stated of
; the per-record rewrite the host calls (host/checkpoint-host.lisp
; fn-store-log-reclaim-event, per record from host/native/checkpoint.lisp
; fnn-log-reclaim-steps).  If the record's article is named by an obligation
; of the lifetimes table, or its Store verdict needs its payload, or the rule
; is keep-forever and the expiry policy has not expired it, the rewrite
; returns the same octets.  fn-rclp-events-never-touch-a-held-article is its
; map over the history.
(defthm fn-rclp-event-never-touches-a-held-article
  (let* ((m (fn-record-msgid (fn-record-result-record (fn-record-decode-exact o))))
         (article (fn-find-article m articles)))
    (implies (or (fn-rcl-some-names-p (fn-rcl-obligations h)
                                      (fn-article-msgid article)
                                      (fn-article-memberships article))
                 (fn-rcl-verdict-heldp (fn-article-msgid article) verdicts)
                 (and (equal rule '(:keep-forever))
                      (not (fn-xpy-expiredp (fn-article-msgid article) expired))))
             (equal (fn-rclp-event o (list rule now h verdicts articles expired
                                           (fn-rclp-article-index articles)))
                    o)))
  :hints (("Goal" :in-theory (disable fn-rclp-rewrites-p
                                      fn-rcl-some-names-p fn-rcl-obligations
                                      fn-rcl-verdict-heldp
                                      rewrites-p-means-reclaimable)
                  :use ((:instance rewrites-p-means-reclaimable (octets o))
                        (:instance fn-xpy-releasablep-is-rule-or-expired-and-unheld
                                   (article (fn-find-article
                                             (fn-record-msgid
                                              (fn-record-result-record
                                               (fn-record-decode-exact o)))
                                             articles)))
                        (:instance fn-rcl-reclaimable-is-no-obligation-names-it
                                   (article (fn-find-article
                                             (fn-record-msgid
                                              (fn-record-result-record
                                               (fn-record-decode-exact o)))
                                             articles)))))))

;  KEYSTONE (signed composites and every other kind are protected).  An
; event that is not a legacy article record -- an accepted-statement
; composite, a keyring snapshot, a statement verdict, a retention,
; consumer or topic event -- is the same octets in the rewritten history.
(defthm fn-rclp-events-keep-every-other-kind
  (implies (not (fn-record-result-okp (fn-record-decode-exact (nth i events))))
           (equal (nth i (fn-rclp-events events ctx)) (nth i events)))
  :hints (("Goal" :in-theory (enable fn-rclp-rewrites-p))))

; -----------------------------------------------------------------------------
; The octets freed.

(defthm fn-rclp-freed-octets-account
  (equal (fn-rclp-octets (fn-rclp-events events ctx))
         (- (fn-rclp-octets events) (fn-rclp-freed events ctx)))
  :hints (("Goal" :in-theory (disable fn-rclp-event))))

;  The retention charge (reclaim-lifecycle-2, step 2).  The charge an event
; carries into the ledger when it is replayed: an article record's archive
; pin charge, 0 for any other event (its own pins are the other kinds'
; events, which the rewrite never touches).
(defun fn-rclp-charge-of (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-record-decode-exact octets)))
    (if (fn-record-result-okp d)
        (fn-record-charge (fn-record-result-record d))
      0)))

(defun fn-rclp-charges (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (+ (fn-rclp-charge-of (car events)) (fn-rclp-charges (cdr events)))
    0))

; The charge released: for each rewritten event, its charge less the history
; unit its replacement keeps.
(defun fn-rclp-freed-charge (events ctx)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (+ (- (fn-rclp-charge-of (car events))
            (fn-rclp-charge-of (fn-rclp-event (car events) ctx)))
         (fn-rclp-freed-charge (cdr events) ctx))
    0))

;  KEYSTONE (a released article keeps only the history unit).  A rewritten
; event's replacement carries the one permanent history unit of charge; an
; event that is not rewritten carries its own charge unchanged, so a release
; of one article's pin changes no other obligation's charge.
(defthm fn-rclp-rewritten-charge-is-the-history-unit
  (equal (fn-rclp-charge-of (fn-rclp-event octets ctx))
         (if (fn-rclp-rewrites-p octets ctx)
             *fn-rclp-history-unit*
           (fn-rclp-charge-of octets)))
  :hints (("Goal" :use ((:instance fn-rclp-event-decodes-to-the-tombstoned-record))
           :in-theory (e/d (fn-rclp-charge-of)
                           (fn-rclp-event fn-rclp-rewrites-p
                            fn-rclp-event-decodes-to-the-tombstoned-record
                            fn-rclp-tombstoned))
           :cases ((fn-rclp-rewrites-p octets ctx)))
          ("Subgoal 2" :in-theory (enable fn-rclp-event))))

(defthm fn-rclp-freed-charge-account
  (equal (fn-rclp-charges (fn-rclp-events events ctx))
         (- (fn-rclp-charges events) (fn-rclp-freed-charge events ctx)))
  :hints (("Goal" :in-theory (disable fn-rclp-event fn-rclp-charge-of))))

;  KEYSTONE (the freed charge is what admission counts).  For a rewritten
; event, the committed-record octets the admission gate sums
; (books/store-budget `fn-sbud-record-octets', which re-encodes each
; replayed record with `fn-store-event-encode') fall by exactly the event's
; length less its replacement's: the record codec is canonical.
(local
 (defthm rewrites-p-decodes
   (implies (fn-rclp-rewrites-p octets ctx)
            (fn-record-result-okp (fn-record-decode-exact octets)))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-rclp-rewrites-p)
                                              (theory 'minimal-theory))))))

(defthm fn-rclp-freed-is-the-admission-count
  (implies (fn-rclp-rewrites-p octets ctx)
           (let ((old (fn-record-result-record (fn-record-decode-exact octets)))
                 (new (fn-record-result-record
                       (fn-record-decode-exact (fn-rclp-event octets ctx)))))
             (equal (- (len (fn-store-event-encode old))
                       (len (fn-store-event-encode new)))
                    (- (len octets) (len (fn-rclp-event octets ctx))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rewrites-p-decodes
                        fn-rclp-event-decodes-to-the-tombstoned-record
                        fn-record-accepted-input-is-canonical
                        (:instance fn-record-accepted-input-is-canonical
                                   (octets (fn-rclp-event octets ctx)))
                        (:instance fn-record-decode-exact-yields-a-record
                                   (octets (fn-rclp-event octets ctx)))
                        (:instance fn-record-decode-exact-yields-a-record
                                   (octets octets))
                        (:instance fn-store-event-article-encoding-is-legacy-record-encoding
                                   (record (fn-record-result-record
                                            (fn-record-decode-exact octets))))
                        (:instance fn-store-event-article-encoding-is-legacy-record-encoding
                                   (record (fn-record-result-record
                                            (fn-record-decode-exact
                                             (fn-rclp-event octets ctx)))))))))

; -----------------------------------------------------------------------------
; The per-article context the rewrite reads.
;
; RULE: the configured retention rule (`fn-rcl-config-rule').  NOW: the
; instant the rule is measured at (the clock observation's stamp, nil when
; the clock is unusable, which reclaims nothing under release-after).  S:
; the Store state the open replayed (holders, verdicts, articles).
; EXPIRED: the Message-IDs the expiry policy expires at NOW
; (books/expiry `fn-xpy-ctx' builds it); `fn-rclp-ctx' is the context
; without one.
(defun fn-rclp-ctx-expiring (rule now s expired)
  (declare (xargs :guard t :verify-guards nil))
  (let ((articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (list rule now (fn-rcl-store-holders s) (fn-sn-verdicts s) articles expired
          (fn-rclp-index-built articles))))

(defun fn-rclp-ctx (rule now s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rclp-ctx-expiring rule now s nil))
