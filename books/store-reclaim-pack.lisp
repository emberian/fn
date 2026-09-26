; fn: content reclamation's durable step, the reclaiming pack (STO-017, PRF-119).
;
; `operator CONFIG store reclaim' removes released payload octets from the
; disk.  It never edits a file in place.  The store is first compacted into
; one selected lossless pack (books/store-compact-verb, the ordinary verb),
; so every committed record lives in the pack and no transaction file is
; left.  Then this book decides a second pack generation: the same event
; list with each reclaimable article record re-encoded with its payload
; replaced by `fn-rcl-tombstone-of', and every other event's octets exact.
; The host publishes it, selects it (the marker replacement is the one
; commit point) and retires the older generation, whose unlink is what
; returns the octets to the file system.
;
; Three operations are kept apart (specs/storage.md STO-017): packing keeps
; the exact event history; history compaction is not done here; content
; reclamation changes only payload octets of released article records and
; keeps every identity, number, obligation and anti-resurrection fact the
; record carries.
;
; What is decided here, over the function the host calls
; (host/checkpoint-host.lisp `fn-store-reclaim-decide', called by
; host/native/checkpoint.lisp `fnn-reclaim-steps'):
;   - which events change: only a legacy article record whose article is
;     `fn-rcl-reclaimable' in the opened store (KEYSTONE
;     `fn-rclp-events-never-touch-a-held-article');
;   - what a changed event is: the encoding of the same record with the
;     tombstone as its payload, and nothing else of it changes
;     (`fn-rclp-event-decodes-to-the-tombstoned-record');
;   - that the new list is still a pack summary's event list
;     (`fn-rclp-events-keep-the-summary-shape');
;   - that a rerun after any cut rewrites nothing more
;     (`fn-rclp-events-idempotent');
;   - the octets freed in the committed history the admission gate counts
;     (`fn-rclp-freed-octets-account').
(in-package "ACL2")
(include-book "store-reclaim-holders")
(include-book "store-compact-verb")

; The record an article record becomes: the same eleven fields with the
; tombstone of its payload in place of the payload.
(defun fn-rclp-tombstoned (r)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-make (fn-record-sequence r) (fn-record-txid r)
                  (fn-record-generation r) (fn-record-msgid r)
                  (fn-rcl-tombstone-of (fn-record-payload r)
                                       (fn-record-string-octets (fn-record-msgid r)))
                  (fn-record-groups r) (fn-record-obligation-id r)
                  (fn-record-content-subject r) (fn-record-release-evidence r)
                  (fn-record-charge r) (fn-record-stamp r)))

; CTX is (RULE NOW HOLDERS VERDICTS ARTICLES) of the opened store.
(defun fn-rclp-ctx-reclaimable (ctx msgid)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rcl-reclaimable (fn-rcl-nth 0 ctx) (fn-rcl-nth 1 ctx) (fn-rcl-nth 2 ctx)
                      (fn-rcl-nth 3 ctx)
                      (fn-find-article msgid (fn-rcl-nth 4 ctx))))

; Whether the event OCTETS is rewritten: a legacy article record, not already
; a tombstone, whose article the context finds reclaimable, and whose
; tombstoned record is a record (its payload within the record codec).
(defun fn-rclp-rewrites-p (octets ctx)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-record-decode-exact octets)))
    (and (fn-record-result-okp d)
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
; replacement's.  An integer; the tombstone is 89 octets plus the Path agent,
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

(local (in-theory (disable fn-rcl-tombstone-of fn-rcl-tombstonep fn-rcl-reclaimable
                           fn-record-result-okp fn-record-result-record)))

(defthm fn-rclp-event-of-an-unrewritten-event-by-definition
  (implies (not (fn-rclp-rewrites-p octets ctx))
           (equal (fn-rclp-event octets ctx) octets)))

; A rewritten event decodes to the tombstoned record: every field of the
; record the event held, with the payload replaced by its tombstone.
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
                         (fn-record-charge old))
                  (equal (fn-record-stamp (fn-record-result-record new))
                         (fn-record-stamp old)))))
  :hints (("Goal" :in-theory (disable fn-rclp-tombstoned)
                  :use ((:instance fn-record-round-trip-succeeds
                                   (record (fn-rclp-tombstoned
                                            (fn-record-result-record
                                             (fn-record-decode-exact octets)))))))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-rclp-tombstoned)))))

; -----------------------------------------------------------------------------
; The new list is a pack summary's event list.

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
            (and (fn-store-event-p r)
                 (equal (fn-store-event-sequence r) (fn-record-sequence r))
                 (equal (fn-store-event-txid r) (fn-record-txid r))
                 (equal (fn-store-event-generation r) (fn-record-generation r))))
   :hints (("Goal" :in-theory (enable fn-store-event-p fn-store-event-sequence
                                      fn-store-event-txid fn-store-event-generation)))))

(local
 (defthm rewritten-event-facts
   (implies (fn-rclp-rewrites-p octets ctx)
            (let ((new (fn-rclp-event octets ctx)))
              (and (fn-cbor-octet-listp new)
                   (fn-cbor-octet-listp octets)
                   (equal (car (fn-store-event-decode-exact octets)) :ok)
                   (fn-store-event-p (fn-cc-nth 1 (fn-store-event-decode-exact octets)))
                   (equal (car (fn-store-event-decode-exact new)) :ok)
                   (fn-store-event-p (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                   (equal (fn-store-event-sequence
                           (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                          (fn-store-event-sequence
                           (fn-cc-nth 1 (fn-store-event-decode-exact octets))))
                   (equal (fn-store-event-txid
                           (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                          (fn-store-event-txid
                           (fn-cc-nth 1 (fn-store-event-decode-exact octets))))
                   (equal (fn-store-event-generation
                           (fn-cc-nth 1 (fn-store-event-decode-exact new)))
                          (fn-store-event-generation
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

;  KEYSTONE (the reclaiming pack is a pack).  The rewrite is a summary's
; event list from SEQUENCE with txids in [LOWER, UPPER) exactly when the
; committed history is: the capture the host publishes (`fn-cc-capture'
; through `fn-store-reclaim-decide') accepts it on the same terms as the
; ordinary pack, and the open replays it through the one Store decoder.
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

;  KEYSTONE (convergence).  An event the reclaiming pack rewrote is never
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

; And a rerun with the same context writes the same pack.
(defthm fn-rclp-events-idempotent
  (equal (fn-rclp-events (fn-rclp-events events ctx) ctx)
         (fn-rclp-events events ctx))
  :hints (("Goal" :induct (fn-rclp-events events ctx)
                  :in-theory (disable fn-rclp-rewrites-p fn-rclp-event))))

; -----------------------------------------------------------------------------
; A held article is never touched.

(local
 (defthm rewrites-p-means-reclaimable
   (implies (fn-rclp-rewrites-p octets (list rule now h verdicts articles))
            (fn-rcl-reclaimable rule now h verdicts
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
; Store verdict needs its payload, or the rule is keep-forever, the I-th
; event of the reclaiming pack is the same octets.
(defthm fn-rclp-events-never-touch-a-held-article
  (let* ((o (nth i events))
         (m (fn-record-msgid (fn-record-result-record (fn-record-decode-exact o))))
         (article (fn-find-article m articles)))
    (implies (or (fn-rcl-some-names-p (fn-rcl-obligations h)
                                      (fn-article-msgid article)
                                      (fn-article-memberships article))
                 (fn-rcl-verdict-heldp (fn-article-msgid article) verdicts)
                 (equal rule '(:keep-forever)))
             (equal (nth i (fn-rclp-events events (list rule now h verdicts articles)))
                    (nth i events))))
  :hints (("Goal" :in-theory (disable fn-rclp-event fn-rclp-rewrites-p
                                      fn-rcl-some-names-p fn-rcl-obligations
                                      fn-rcl-verdict-heldp
                                      rewrites-p-means-reclaimable)
                  :use ((:instance rewrites-p-means-reclaimable
                                   (octets (nth i events)))
                        (:instance fn-rcl-reclaimable-is-no-obligation-names-it
                                   (article (fn-find-article
                                             (fn-record-msgid
                                              (fn-record-result-record
                                               (fn-record-decode-exact (nth i events))))
                                             articles)))))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-rclp-event)))))

;  KEYSTONE (signed composites and every other kind are protected).  An
; event that is not a legacy article record -- an accepted-statement
; composite, a keyring snapshot, a statement verdict, a retention,
; consumer or topic event -- is the same octets in the reclaiming pack.
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
; The verb's decision.
;
; RULE: the configured retention rule (`fn-rcl-config-rule').  NOW: the
; instant the rule is measured at (the clock observation's stamp, nil when
; the clock is unusable, which reclaims nothing under release-after).  S:
; the Store state the open replayed (holders, verdicts, articles).  RECORDS:
; the committed history as octets (pack plus suffix).  FRONTIER: the durable
; allocator frontier.  LOWER, NAMES, GENERATIONS, SELECTED: the compact verb's
; observation; DISK-FREE: the free octets the host observed (PKT-169).  DRY: `--dry-run'.
;
;   (:compact-first)                 the history is not one selected pack
;                                    with no transaction file left: the host
;                                    runs the compact verb's decision first
;   (:resume-retire COUNTS)          nothing to rewrite; an older generation
;                                    survives a cut after the selection: retire it
;   (:none COUNTS)                   nothing is reclaimable now (with no
;                                    authorized release this is the answer,
;                                    and it writes nothing)
;   (:dry-run MSGIDS FREED COUNTS)   what a run would reclaim; nothing written
;   (:reclaim STEPS MSGIDS FREED SUMMARY-OCTETS COUNTS)
;   (:refused REASON)                nothing written
;
; STEPS are `*fn-rclp-steps*': drop the derived state checkpoint (it holds
; payload octets and would be opened in place of the history), publish the
; reclaiming pack, select it, retire the older generations.
(defconst *fn-rclp-steps* '(:drop-state-checkpoint :pack :select :retire))

(defun fn-rclp-ctx (rule now s)
  (declare (xargs :guard t :verify-guards nil))
  (list rule now (fn-rcl-store-holders s) (fn-sn-verdicts s)
        (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))

(defun fn-rclp-decide (profile rule now s records frontier lower names
                               generations selected disk-free dry)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((used (len records))
         (reclaim (fn-bs-pack-reclaim-plan
                   names (fn-bs-profile-max-transactions profile) lower))
         (counts (fn-rcl-store-counts rule now s))
         (ctx (fn-rclp-ctx rule now s))
         (msgids (fn-rclp-rewritten-msgids records ctx)))
    (cond ((not (fn-bs-profile-admittedp profile)) (list :refused :profile))
          ((or (not (natp lower)) (< used lower) (equal reclaim :invalid))
           (list :refused :observation))
          ; Nothing left to rewrite, but a generation older than the
          ; selected one survives: a cut between the selection and the
          ; retirement (the older generation still holds the released
          ; payloads).  The rerun finishes the retirement.
          ((and (atom msgids) (not dry)
                (posp (fn-cverb-older-count generations selected)))
           (list :resume-retire counts))
          ((atom msgids) (list :none counts))
          (dry (list :dry-run msgids (fn-rclp-freed records ctx) counts))
          ((or (not (equal lower used)) (consp reclaim) (null selected))
           (list :compact-first))
          (t
           (let ((new (fn-rclp-events records ctx)))
             (if (not (fn-cverb-disk-admitsp disk-free (fn-cverb-pack-octets new)))
                 (list :refused :temporary-space)
               (let ((captured (fn-cc-capture new frontier)))
                 (if (not (equal (car captured) :ok))
                     (list :refused :capture)
                   (list :reclaim *fn-rclp-steps* msgids (fn-rclp-freed records ctx)
                         (fn-cc-encode (cadr captured)) counts)))))))))

;  KEYSTONE (the decision publishes the rewrite and nothing else).  When the
; verb reclaims, the pack it publishes is the encoded summary of exactly
; `fn-rclp-events' of the committed history, so every theorem above about
; that list is a theorem about the bytes the host writes.
(defthm fn-rclp-decide-publishes-the-rewrite
  (let ((d (fn-rclp-decide profile rule now s records frontier lower names
                           generations selected disk-free dry)))
    (implies (equal (car d) :reclaim)
             (and (equal (nth 1 d) *fn-rclp-steps*)
                  (equal (car (fn-cc-capture
                               (fn-rclp-events records (fn-rclp-ctx rule now s))
                               frontier))
                         :ok)
                  (equal (nth 4 d)
                         (fn-cc-encode
                          (cadr (fn-cc-capture
                                 (fn-rclp-events records (fn-rclp-ctx rule now s))
                                 frontier))))
                  (not dry)
                  (equal lower (len records))
                  (consp (fn-rclp-rewritten-msgids records (fn-rclp-ctx rule now s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-rclp-events fn-rclp-rewritten-msgids
                                      fn-rclp-freed fn-cc-capture fn-cc-encode
                                      fn-rcl-store-counts fn-rclp-ctx
                                      fn-bs-pack-reclaim-plan fn-cverb-pack-octets
                                      fn-cverb-disk-admitsp
                                      fn-cverb-older-count
                                      fn-bs-profile-admittedp
                                      fn-bs-profile-max-transactions))))

;  KEYSTONE (temporary space against the disk, PKT-169).  When the verb
; reclaims, the pack file the host seals from the octets it is handed (the
; payload plus the frame trailer) fits the free octets the host reported for
; the store's filesystem.
(defthm fn-rclp-pack-fits-the-disk
  (let ((d (fn-rclp-decide profile rule now s records frontier lower names
                           generations selected disk-free dry)))
    (implies (equal (car d) :reclaim)
             (<= (+ (len (nth 4 d)) *fn-frame-trailer-octets*) disk-free)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cverb-capture-within-pack-octets
                                   (records (fn-rclp-events
                                             records (fn-rclp-ctx rule now s)))))
           :in-theory (e/d (fn-cverb-disk-admitsp fn-cverb-pack-octets fn-cc-nth)
                           (fn-rclp-events fn-rclp-rewritten-msgids
                            fn-cverb-capture-within-pack-octets
                            fn-rclp-freed fn-cc-capture fn-cc-encode
                            fn-cc-event-octets-size
                            fn-rcl-store-counts fn-rclp-ctx
                            fn-bs-pack-reclaim-plan
                            fn-cverb-older-count
                            fn-bs-profile-admittedp
                            fn-bs-profile-max-transactions)))))

(local
 (defthm rewritten-msgids-under-keep-forever
   (equal (fn-rclp-rewritten-msgids records (list '(:keep-forever) now h v a)) nil)
   :hints (("Goal" :in-theory (enable fn-rclp-rewrites-p fn-rclp-ctx-reclaimable
                                      fn-rcl-reclaimable)))))

;  KEYSTONE (bounded refusal without an authorized release).  Under the
; default keep-forever rule the verb writes nothing: its answer is never
; :reclaim.
(defthm fn-rclp-keep-forever-writes-nothing
  (not (equal (car (fn-rclp-decide profile '(:keep-forever) now s records frontier
                                   lower names generations selected disk-free dry))
              :reclaim))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-rclp-events fn-rclp-freed fn-cc-capture
                                      fn-cc-encode fn-rcl-store-counts
                                      fn-bs-pack-reclaim-plan fn-cverb-pack-octets
                                      fn-cverb-disk-admitsp
                                      fn-rclp-rewritten-msgids fn-cverb-older-count
                                      fn-bs-profile-admittedp
                                      fn-bs-profile-max-transactions))))
