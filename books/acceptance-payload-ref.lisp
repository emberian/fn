; The acceptance state's payload field as a reference to the record's bytes
; (lane acceptance-payload-arena, 2026-09-26; PRF-219).
;
; The acceptance state stores an accepted article as (MSGID PAYLOAD GROUPS
; MEMBERSHIPS PIN STAMP) (books/acceptance.lisp).  PAYLOAD is not a second
; copy of the article's bytes: the replay hands the record's own payload to
; `fn-node-prepare' (`fn-replay-apply-record'), the POST builds the record
; from the pending proposal's payload (`fn-sn-pending-record'), and the
; schema-3 checkpoint writes the stored article's payload as a reference to
; the record's P row.  Measured (planning/evidence/acceptance-payload-arena-
; 2026-09-26.md section 3): at N = 1,000 and 10,000 x 2 KiB the acceptance
; state retains no payload cell the Store's records do not.
;
; What this book states is the relation that makes the field a reference and
; not a value of its own: every article's payload is the payload of the
; article record its Message-ID names in the durable history (the last one,
; as the event index lists them).  `fn-apr-refsp' is the relation; it holds
; of every replayed node (`fn-apr-replay-establishes-refs', the fold over
; `fn-replay-apply-record', no hypothesis beyond the replay succeeding),
; hence at every entry the host has: the open's replay, the checkpoint open
; (equal to the full replay, `fn-ock-finalize-of-extended-capture'), and
; every idle phase of the live Store (`fn-snt-relation': the node IS the
; replay of its history).
;
; The readers: `fn-apr-payload-of' resolves a Message-ID to the record's
; payload through the Store's event index (the record's identity resolved
; through the catalog's predecessor, `fn-cei-msgid-records'), and
; `fn-apr-payload-of-is-the-article-payload' is the boundary theorem that
; lets a host reader of the acceptance field read the record instead.  When
; the record's payload becomes an arena handle (records-freeze), the
; resolver is the one place that changes.
(in-package "ACL2")
(include-book "consumer-event-index-store-invariants")
(include-book "store-node-traces-prepare")
(include-book "owner")

; -----------------------------------------------------------------------------
; The reference.

(defun fn-apr-last (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs)) (fn-apr-last (cdr xs)) (car xs))
    nil))

; The bytes a Message-ID's reference resolves to in EVENTS: the payload of
; the last article record the event index lists for it.
(defun fn-apr-history-payload (msgid events)
  (declare (xargs :guard t))
  (fn-record-payload (fn-apr-last (fn-cei-article-records-for msgid events))))

; The relation: every article names an article record of the history, and
; its payload is that record's payload.
(defun fn-apr-refsp (articles events)
  (declare (xargs :guard t))
  (if (consp articles)
      (and (consp (fn-cei-article-records-for (fn-article-msgid (car articles))
                                              events))
           (equal (fn-article-payload (car articles))
                  (fn-apr-history-payload (fn-article-msgid (car articles))
                                          events))
           (fn-apr-refsp (cdr articles) events))
    t))

; -----------------------------------------------------------------------------
; The history grows at its end.

(defthm fn-apr-records-for-of-append
  (equal (fn-cei-article-records-for msgid (append a b))
         (append (fn-cei-article-records-for msgid a)
                 (fn-cei-article-records-for msgid b))))

(defthm fn-apr-last-of-append
  (equal (fn-apr-last (append a b))
         (if (consp b) (fn-apr-last b) (fn-apr-last a))))

(local
 (defthm fn-apr-records-for-of-one
   (equal (fn-cei-article-records-for msgid (list e))
          (if (and (fn-held-p (fn-cei-event-article e))
                   (equal msgid (fn-record-msgid (fn-cei-event-article e))))
              (list (fn-cei-event-article e))
            nil))))

(in-theory (disable fn-cei-article-records-for))

; An event whose article record names no article of ARTICLES leaves the
; relation as it was.
(defthm fn-apr-refsp-of-append-foreign
  (implies (and (fn-apr-refsp articles events)
                (or (not (fn-held-p (fn-cei-event-article e)))
                    (not (fn-acceptedp (fn-record-msgid (fn-cei-event-article e))
                                       articles))))
           (fn-apr-refsp articles (append events (list e)))))

; The converse half, needed for a lookup to agree with the article's
; absence: every article record of the history names an accepted article.
(defun fn-apr-recordedp (events articles)
  (declare (xargs :guard t))
  (if (consp events)
      (and (or (not (fn-held-p (fn-cei-event-article (car events))))
               (fn-acceptedp (fn-record-msgid (fn-cei-event-article (car events)))
                             articles))
           (fn-apr-recordedp (cdr events) articles))
    t))

(defthm fn-apr-recordedp-of-append
  (equal (fn-apr-recordedp (append a b) articles)
         (and (fn-apr-recordedp a articles) (fn-apr-recordedp b articles))))

(defthm fn-apr-recordedp-of-cons-article
  (implies (fn-apr-recordedp events articles)
           (fn-apr-recordedp events (cons x articles))))

(defthm fn-apr-recordedp-of-grown
  (implies (and (consp y) (fn-apr-recordedp events (cdr y)))
           (fn-apr-recordedp events y))
  :hints (("Goal" :use ((:instance fn-apr-recordedp-of-cons-article
                                   (articles (cdr y)) (x (car y))))
           :in-theory (disable fn-apr-recordedp-of-cons-article))))

(defthm fn-apr-records-for-nonempty-is-accepted
  (implies (and (fn-apr-recordedp events articles)
                (consp (fn-cei-article-records-for msgid events)))
           (fn-acceptedp msgid articles))
  :hints (("Goal" :in-theory (enable fn-cei-article-records-for))))

; -----------------------------------------------------------------------------
; One replayed event (`fn-replay-apply-record', books/replay.lisp).

; The arms of `fn-replay-apply-record' that install an article.
(defun fn-apr-article-armp (e)
  (declare (xargs :guard t))
  (not (or (fn-store-retention-event-p e) (fn-stxe-p e) (fn-stxk-p e)
           (fn-cpe-eventp e) (fn-th-topic-eventp e))))

; The other arms carry no article record.
(defthm fn-apr-other-arms-carry-no-article
  (implies (not (fn-apr-article-armp e))
           (not (fn-held-p (fn-cei-event-article e))))
  :hints (("Goal" :in-theory (enable fn-cei-event-article fn-held-p
                                     fn-held-shapep fn-store-retention-event-p
                                     fn-stxe-p fn-stxe-shapep fn-stxk-p
                                     fn-stxk-shapep fn-hstxa-p
                                     fn-cpe-eventp fn-th-topic-eventp))))

(defthm fn-apr-other-arms-keep-articles
  (implies (and (not (fn-apr-article-armp e))
                (consp (fn-replay-apply-record node e)))
           (equal (fn-stx-store (fn-replay-apply-record node e))
                  (fn-stx-store node)))
  :hints (("Goal" :in-theory (enable fn-replay-apply-record
                                     fn-replay-apply-retention-event
                                     fn-replay-complete-retention
                                     fn-replay-node-with-retention
                                     fn-replay-apply-identity-neutral
                                     fn-stx-store))))

; The article arm refuses a staged node.
(defthm fn-apr-article-arm-needs-no-stage
  (implies (and (fn-apr-article-armp e)
                (consp (fn-replay-apply-record node e)))
           (not (fn-node-stage node)))
  :hints (("Goal" :in-theory (enable fn-replay-apply-record))))

; The acceptance steps the arm composes (fn-accept-prepare, then the
; durable fn-accept-complete), each on the fields this relation reads.
(local
 (defthm fn-apr-idle-advance-has-no-stage
   (implies (not (fn-node-stage node))
            (not (fn-node-stage (fn-replay-advance-txid node x))))
   :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local
 (defthm fn-apr-idle-node-has-no-pending
   (implies (and (fn-node-statep node) (not (fn-node-stage node)))
            (not (fn-state-pending (fn-node-acceptance node))))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(local
 (defthm fn-apr-idle-advance-has-no-pending
   (implies (and (fn-node-statep node) (not (fn-node-stage node)))
            (not (fn-state-pending
                  (fn-node-acceptance (fn-replay-advance-txid node x)))))
   :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local
 (defthm fn-apr-prepare-stages-its-arguments
   (implies (and (fn-statep s)
                 (not (consp (fn-state-pending s)))
                 (consp (fn-state-pending (fn-accept-prepare s g m p gr st))))
            (let ((prep (fn-accept-prepare s g m p gr st)))
              (and (equal (fn-pending-msgid (fn-state-pending prep)) m)
                   (equal (fn-pending-payload (fn-state-pending prep)) p)
                   (equal (fn-state-articles prep) (fn-state-articles s))
                   (not (fn-acceptedp m (fn-state-articles s)))
                   (not (fn-state-fenced prep)))))
   :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep))))))

(local
 (defthm fn-apr-durable-complete-conses-the-pending
   (implies (and (fn-statep s) (not (fn-state-fenced s))
                 (fn-pending-matchesp (fn-state-pending s) txid gen))
            (equal (fn-state-articles (fn-accept-complete s txid gen :durable))
                   (cons (fn-article-from-pending (fn-state-pending s))
                         (fn-state-articles s))))
   :hints (("Goal" :in-theory (e/d (fn-accept-complete fn-install-pending)
                                   (fn-statep fn-article-from-pending))))))

(local
 (defthm fn-apr-node-acceptance-is-state
   (implies (fn-node-statep node) (fn-statep (fn-node-acceptance node)))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

; The article arm conses one article, the record's, whose Message-ID the
; node had not accepted.
(defthm fn-apr-article-arm-installs-the-record-payload
  (implies (and (fn-node-statep node)
                (not (fn-node-stage node))
                (fn-apr-article-armp e)
                (consp (fn-replay-apply-record node e)))
           (let ((art (fn-cei-event-article e))
                 (after (fn-stx-store (fn-replay-apply-record node e))))
             (and (fn-held-p art)
                  (not (fn-acceptedp (fn-record-msgid art) (fn-stx-store node)))
                  (consp after)
                  (equal (fn-article-msgid (car after)) (fn-record-msgid art))
                  (equal (fn-article-payload (car after)) (fn-record-payload art))
                  (equal (cdr after) (fn-stx-store node)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-node-prepare-preserves-state
                            (s (fn-replay-advance-txid node (fn-store-event-txid e)))
                            (generation (fn-record-generation (fn-cei-event-article e)))
                            (msgid (fn-record-msgid (fn-cei-event-article e)))
                            (payload (fn-record-payload (fn-cei-event-article e)))
                            (groups (fn-record-groups (fn-cei-event-article e)))
                            (obligation-id (fn-record-obligation-id (fn-cei-event-article e)))
                            (subject (fn-record-content-subject (fn-cei-event-article e)))
                            (evidence (fn-record-release-evidence (fn-cei-event-article e)))
                            (charge (fn-record-charge (fn-cei-event-article e)))
                            (stamp (fn-record-stamp (fn-cei-event-article e)))))
           :in-theory (e/d (fn-replay-apply-record fn-cei-event-article
                            fn-node-complete fn-node-prepare fn-stx-store
                            fn-node-pending-matchesp fn-article-from-pending)
                           (fn-statep fn-node-statep fn-record-shape-vocabulary
                            fn-record-record-vocabulary fn-accept-prepare
                            fn-accept-complete fn-node-prepare-preserves-state
                            fn-replay-composite-record
                            fn-replay-advance-txid)))))

(local
 (defthm fn-apr-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; One event keeps both halves of the relation.
(defthm fn-apr-apply-record-keeps-refs
  (implies (and (fn-node-statep node)
                (fn-apr-refsp (fn-stx-store node) events)
                (fn-apr-recordedp events (fn-stx-store node))
                (consp (fn-replay-apply-record node e)))
           (and (fn-apr-refsp (fn-stx-store (fn-replay-apply-record node e))
                              (append events (list e)))
                (fn-apr-recordedp (append events (list e))
                                  (fn-stx-store (fn-replay-apply-record node e)))))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-apr-article-armp e))
           :use (fn-apr-article-arm-installs-the-record-payload)
           :in-theory (e/d (fn-apr-history-payload)
                           (fn-apr-article-arm-installs-the-record-payload
                            fn-apr-article-armp fn-stx-store
                            fn-replay-apply-record fn-node-statep)))))

; -----------------------------------------------------------------------------
; The replay establishes the relation.

(local
 (defun fn-apr-loop-induct (node records sequence events)
   (declare (xargs :measure (len records)))
   (if (and (fn-node-statep node)
            (consp records)
            (fn-store-event-p (car records))
            (equal (fn-store-event-sequence (car records)) sequence)
            (fn-node-statep (fn-replay-apply-record node (car records))))
       (fn-apr-loop-induct (fn-replay-apply-record node (car records))
                           (cdr records) (1+ sequence)
                           (append events (list (car records))))
     (list node records sequence events))))

(local
 (defthm fn-apr-recordedp-of-atom
   (implies (not (consp events)) (fn-apr-recordedp events articles))))

(local
 (defthm fn-apr-fault-is-not-ok
   (not (fn-replay-okp (fn-replay-fault node sequence reason)))
   :hints (("Goal" :in-theory (enable fn-replay-okp)))))

(local
 (defthm fn-apr-append-nil-of-true-list
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-apr-refsp-of-append-nil
   (equal (fn-apr-refsp articles (append events nil))
          (fn-apr-refsp articles events))
   :hints (("Goal" :in-theory (enable fn-cei-article-records-for)))))

(defthm fn-apr-replay-loop-keeps-refs
  (implies (and (fn-apr-refsp (fn-stx-store node) events)
                (fn-apr-recordedp events (fn-stx-store node))
                (fn-replay-okp (fn-replay-loop node records sequence)))
           (and (fn-apr-refsp
                 (fn-stx-store (fn-replay-result-node
                                (fn-replay-loop node records sequence)))
                 (append events records))
                (fn-apr-recordedp
                 (append events records)
                 (fn-stx-store (fn-replay-result-node
                                (fn-replay-loop node records sequence))))))
  :hints (("Goal" :induct (fn-apr-loop-induct node records sequence events)
           :in-theory (e/d (fn-replay-loop)
                           (fn-apr-refsp fn-apr-recordedp fn-stx-store
                            fn-replay-apply-record fn-node-statep)))
          ("Subgoal *1/1" :use ((:instance fn-apr-apply-record-keeps-refs
                                           (e (car records))))
           :in-theory (e/d (fn-replay-loop)
                           (fn-apr-apply-record-keeps-refs
                            fn-apr-refsp fn-apr-recordedp fn-stx-store
                            fn-replay-apply-record fn-node-statep)))))

(defthm fn-apr-initial-node-has-no-articles
  (equal (fn-stx-store (fn-node-initial-state groups capacity)) nil)
  :hints (("Goal" :in-theory (enable fn-stx-store fn-node-initial-state
                                     fn-initial-state))))

; KEYSTONE (the relation at the replay).  Every node the replay reaches
; relates its articles to the history it replayed: each article's payload
; is its record's, and each article record names an article.
(defthm fn-apr-replay-establishes-refs
  (implies (fn-replay-okp (fn-replay groups capacity records))
           (let ((articles (fn-stx-store (fn-replay-result-node
                                          (fn-replay groups capacity records)))))
             (and (fn-apr-refsp articles records)
                  (fn-apr-recordedp records articles))))
  :hints (("Goal" :use ((:instance fn-apr-replay-loop-keeps-refs
                                   (node (fn-node-initial-state groups capacity))
                                   (events nil) (sequence 0)))
           :in-theory (e/d (fn-replay)
                           (fn-apr-replay-loop-keeps-refs fn-apr-refsp
                            fn-apr-recordedp fn-stx-store fn-node-statep
                            fn-replay-loop)))))

; The replay the Store's idle phases are equal to (`fn-snt-relation').
(defthm fn-apr-replay-node-refs
  (implies (consp (fn-sf-replay-node groups capacity records frontier))
           (let ((articles (fn-stx-store
                            (fn-sf-replay-node groups capacity records frontier))))
             (and (fn-apr-refsp articles records)
                  (fn-apr-recordedp records articles))))
  :hints (("Goal" :use fn-apr-replay-establishes-refs
           :in-theory (e/d (fn-sf-replay-node fn-stx-store)
                           (fn-apr-replay-establishes-refs fn-apr-refsp
                            fn-apr-recordedp fn-replay)))))

; -----------------------------------------------------------------------------
; The reader through the reference.

(defthm fn-apr-refsp-finds-the-record-payload
  (implies (and (fn-apr-refsp articles events)
                (fn-find-article msgid articles))
           (and (consp (fn-cei-article-records-for msgid events))
                (equal (fn-article-payload (fn-find-article msgid articles))
                       (fn-apr-history-payload msgid events))))
  :hints (("Goal" :in-theory (disable fn-apr-history-payload))))

(defthm fn-apr-accepted-string-is-found
  (implies (and (stringp msgid) (fn-acceptedp msgid articles))
           (fn-find-article msgid articles)))

; A Message-ID's payload: the record's, found through the Store's event
; index (the record's identity; the catalog's rows replace the index), or
; NIL when the history holds no article record for it.
(defun fn-apr-payload-of (msgid s)
  (declare (xargs :guard t))
  (let ((records (fn-cei-msgid-records msgid (fn-sn-event-index s))))
    (if (consp records) (fn-record-payload (fn-apr-last records)) nil)))

; The value a reader of the acceptance field returned: the stored article's
; payload, or NIL.  (The subject every host reader below replaced.)
(defun fn-apr-field-payload (msgid s)
  (declare (xargs :guard t))
  (let ((article (fn-find-article msgid (fn-stx-store (fn-sn-node s)))))
    (if (consp article) (fn-article-payload article) nil)))

; The Store's relation at an idle phase, the reference half: the node is the
; replay of the history (`fn-snt-relation'), and the event index is the
; history's (`fn-ceis-indexedp', established at every open and preserved by
; every transition, books/consumer-event-index-store-invariants.lisp).
(defun fn-apr-store-at-restp (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-snt-relation s)
       (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files s)))
       (fn-ceis-indexedp s)))

; At rest the node is the replay of the history, and the index is its fold.
(defthm fn-apr-at-rest-unfolds
  (implies (fn-apr-store-at-restp s)
           (and (equal (fn-sn-node s)
                       (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                          (fn-sf-records (fn-sn-files s))
                                          (fn-sf-frontier (fn-sn-files s))))
                (consp (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                          (fn-sf-records (fn-sn-files s))
                                          (fn-sf-frontier (fn-sn-files s))))
                (fn-cei-correspondencep (fn-sn-event-index s)
                                        (fn-sf-records (fn-sn-files s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-apr-store-at-restp fn-snt-relation
                                fn-sf-history-recoverablep fn-ceis-indexedp)
                              (theory 'minimal-theory)))))

; The two halves of the relation on a Store at rest, for one Message-ID.
(local
 (defthm fn-apr-at-rest-lookup
   (implies (and (fn-apr-store-at-restp s) (stringp msgid))
            (let ((articles (fn-stx-store (fn-sn-node s)))
                  (events (fn-sf-records (fn-sn-files s))))
              (and (equal (fn-cei-msgid-records msgid (fn-sn-event-index s))
                          (fn-cei-article-records-for msgid events))
                   (implies (fn-find-article msgid articles)
                            (and (consp (fn-cei-article-records-for msgid events))
                                 (equal (fn-article-payload
                                         (fn-find-article msgid articles))
                                        (fn-apr-history-payload msgid events))))
                   (implies (not (fn-find-article msgid articles))
                            (not (consp (fn-cei-article-records-for msgid events)))))))
   :hints (("Goal" :do-not-induct t
            :use (fn-apr-at-rest-unfolds
                  (:instance fn-apr-replay-node-refs
                             (groups (fn-sn-groups s))
                             (capacity (fn-sn-capacity s))
                             (records (fn-sf-records (fn-sn-files s)))
                             (frontier (fn-sf-frontier (fn-sn-files s))))
                  (:instance fn-apr-refsp-finds-the-record-payload
                             (articles (fn-stx-store (fn-sn-node s)))
                             (events (fn-sf-records (fn-sn-files s))))
                  (:instance fn-apr-records-for-nonempty-is-accepted
                             (events (fn-sf-records (fn-sn-files s)))
                             (articles (fn-stx-store (fn-sn-node s))))
                  (:instance fn-cei-msgid-records-of-correspondence
                             (index (fn-sn-event-index s))
                             (events (fn-sf-records (fn-sn-files s)))))
            :in-theory (union-theories
                        '(fn-apr-accepted-string-is-found)
                        (theory 'minimal-theory))))))

; KEYSTONE (the boundary).  At rest, the record's payload found through the
; index IS what the acceptance field held, for every Message-ID string.
(defthm fn-apr-payload-of-is-the-article-payload
  (implies (and (fn-apr-store-at-restp s) (stringp msgid))
           (equal (fn-apr-payload-of msgid s)
                  (fn-apr-field-payload msgid s)))
  :hints (("Goal" :do-not-induct t
           :use fn-apr-at-rest-lookup
           :in-theory (e/d (fn-apr-payload-of fn-apr-field-payload
                            fn-apr-history-payload)
                           (fn-apr-at-rest-lookup fn-apr-store-at-restp
                            fn-cei-msgid-records fn-find-article
                            fn-stx-store fn-apr-last)))))

; -----------------------------------------------------------------------------
; The host readers.

; The feed's byte source (host/owner-host.lisp, the feed service's article
; fetch), through the reference: the record's payload by Message-ID.
(defun fn-apr-feed-article (o msgid)
  (declare (xargs :guard t))
  (fn-apr-payload-of (fn-record-octets-string msgid) (fn-own-store o)))

; The boundary for the feed: at rest it is what `fn-own-feed-article' read
; off the acceptance state's article.
(defthm fn-apr-feed-article-is-own-feed-article
  (implies (fn-apr-store-at-restp (fn-own-store o))
           (equal (fn-apr-feed-article o msgid)
                  (fn-own-feed-article o msgid)))
  :hints (("Goal" :use ((:instance fn-apr-payload-of-is-the-article-payload
                                   (s (fn-own-store o))
                                   (msgid (fn-record-octets-string msgid))))
           :in-theory (e/d (fn-own-feed-article fn-apr-field-payload fn-stx-store)
                           (fn-apr-payload-of-is-the-article-payload
                            fn-apr-payload-of fn-apr-store-at-restp)))))

; Whether the history holds an article record for MSGID (the bridge's
; lookup-found, host/store-node-host.lisp `fn-store-sn-lookup-foundp').
(defun fn-apr-foundp (msgid s)
  (declare (xargs :guard t))
  (consp (fn-cei-msgid-records msgid (fn-sn-event-index s))))

(defthm fn-apr-foundp-is-article-found
  (implies (and (fn-apr-store-at-restp s) (stringp msgid))
           (equal (fn-apr-foundp msgid s)
                  (if (fn-find-article msgid (fn-stx-store (fn-sn-node s))) t nil)))
  :hints (("Goal" :do-not-induct t
           :use fn-apr-at-rest-lookup
           :in-theory (e/d (fn-apr-foundp)
                           (fn-apr-at-rest-lookup fn-apr-store-at-restp
                            fn-cei-msgid-records fn-find-article
                            fn-stx-store)))))
