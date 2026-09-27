;; PRF-132: the BP receiver binds a signed article the Store committed, and
;; never submits it a second time (PKT-247, lane mission-signed-2).
;;
;; The subject is fn-bpaj-dispatch-fast (books/bp-native-app-fast.lisp), the
;; receiver's dispatcher: host/bp-receipt-journal-host.lisp
;; fn-bprj-request-action calls it over the owner's bound Store, and
;; host/native/bp-app.lisp fnn-bpapp-action asks it before every step of
;; fnn-bpapp-accept-locked (persist the intent, submit to the Store, bind
;; the committed record, prepare the receipt).
;;
;; A signed article is committed as a kind-4 acceptance composite
;; (fn-stxa-p), not as a plain article record: the composite carries the
;; article record and the receiving Store's own kind-2 verdict, built by
;; fn-hsig-authorized-article-event from the receiving node's enrolled
;; keyring snapshot and its own two primitive observations (D23: carriage is
;; not the author's verification; PRF-026 for the verdict the completion
;; records).  The dispatcher read only plain records, so after the commit its
;; lookup answered (:absent), it answered :submit again, and the owner's
;; transfer decision refused the second submission as (:have :history)
;; (planning/evidence/mission-signed-2026-09-26.md, layer 2).  The Store
;; binding now reads a history's article records (fn-bpr-article-records,
;; books/bp-receipt.lisp): a plain record, or the one a composite carries.
;;
;; Keystones (stated over the live owner's Store in
;; books/owner-store-indexed.lisp; the -under-index lemmas here):
;;   fn-bpaj-dispatch-never-resubmits-a-stored-article: once the Store's
;;     history holds an article record (plain or signed) with the Message-ID
;;     the dispatcher reads, the dispatcher never answers (:submit): the first
;;     durable commit is the only submission.
;;   fn-bpaj-dispatch-binds-the-stores-own-record: whatever the dispatcher
;;     binds is an article record of an event of the Store's own history, for
;;     the request's Message-ID, accepted by the receiver's Store check; when
;;     that event is a signed composite, the composite binds its verdict to
;;     exactly this record (fn-stxa-bindsp: Message-ID, transaction,
;;     generation, profile and keyring generation).  The request carries no
;;     verdict: the one the delivery is bound to is the receiving Store's.
;; Both read the Store's Message-ID index since 2026-09-26 (PRF-144 part 1,
;; lane signed-history-index): the lookups no longer walk the history or
;; decode every composite.  This book states them over any Store whose index
;; is the index of its history (fn-ceis-indexedp): the two -under-index
;; lemmas below are the refinement layer.  The keystones themselves, with
;; those names, are stated over the Store the host dispatches over, the
;; Store of every owner the host reaches from its open, where the premise is
;; a theorem (books/owner-store-indexed.lisp,
;; fn-osi-live-owner-store-is-indexed; lane signed-history-index-2).
;; Teeth: tests/acl2/bp-signed-binding-tests.lisp.  The channel the request
;; arrived on is admitted before any of this (PRF-128); relaying keeps the
;; authored source (PRF-127); the D23 source decision is PRF-117.
(in-package "ACL2")
(include-book "bp-native-app-fast")

;; The Message-ID the dispatcher's lookup reads: the relaying agent's check
;; for a transit intent, the injecting agent's for a direct one.
(defun fn-bpaj-dispatch-msgid (joined request-octets)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((request (fn-bpaj-request request-octets))
         (intent (fn-bpaj-request-intent joined request-octets))
         (fields (if (equal (fn-bpaj-nth 0 intent) :request-transit-intent)
                     (fn-bpaj-transit-article-fields request)
                   (fn-bpaj-article-fields request))))
    (and (equal (car fields) :ok)
         (fn-record-octets-string (cadr fields)))))

(local (defthm fn-bpsb-record-for-msgid-finds-a-member
  (implies (and (member-equal record (fn-bpr-article-records events))
                (fn-held-p record)
                (equal (fn-record-msgid record) msgid))
           (consp (fn-bpaj-record-for-msgid msgid events)))
  :hints (("Goal" :induct (fn-bpr-article-records events)
           :in-theory (e/d (fn-bpr-article-records fn-bpaj-record-for-msgid)
                           (fn-bpr-event-article fn-held-p))))))

;; After the records flip the history's article records are retained held
;; rows (a plain article's, or the one a composite row retains): RECORD is
;; such a row.
(defthm fn-bpaj-dispatch-never-resubmits-under-index
  (implies (and (fn-ceis-indexedp store)
                (member-equal record
                              (fn-bpr-article-records
                               (fn-sf-records (fn-sn-files store))))
                (fn-held-p record)
                (equal (fn-record-msgid record)
                       (fn-bpaj-dispatch-msgid joined request-octets)))
           (not (equal (fn-bpaj-dispatch-fast joined store request-octets
                                              generation fn-arena)
                       (list :submit))))
  :hints (("Goal" :use ((:instance fn-bpsb-record-for-msgid-finds-a-member
                                   (events (fn-sf-records (fn-sn-files store)))
                                   (msgid (fn-record-msgid record))))
           :in-theory (e/d (fn-bpaj-dispatch-fast fn-bpaj-dispatch-msgid
                            fn-bpaj-transit-record-lookup-fast
                            fn-bpaj-record-lookup-fast)
                           (fn-bpsb-record-for-msgid-finds-a-member
                            fn-bpaj-record-for-msgid fn-held-p fn-row-wire-of
                            fn-record-octets-string fn-sn-event-index
                            fn-cei-msgid-records
                            fn-bpr-article-records
                            fn-bpaj-transit-article-fields fn-bpaj-article-fields
                            fn-bpaj-transit-intentp fn-bpaj-request-intent
                            fn-bpaj-request fn-bpaj-request-status-fast
                            fn-bpaj-store-record-accepted-fast
                            fn-bpaj-record-matches-request-fast)))))

;; The first event of EVENTS whose article record is the retained row that
;; stands for RECORD (a held row whose wire form through the arena is RECORD).
(defun fn-bpaj-article-event (record events fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp events)
      (if (fn-bpr-row-stands-for (fn-bpr-event-article (car events)) record fn-arena)
          (car events)
        (fn-bpaj-article-event record (cdr events) fn-arena))
    nil))

(local (defthm fn-bpsb-record-for-msgid-members
  (implies (member-equal row (fn-bpaj-record-for-msgid msgid events))
           (and (member-equal row (fn-bpr-article-records events))
                (fn-held-p row)
                (equal (fn-record-msgid row) msgid)))
  :hints (("Goal" :induct (fn-bpr-article-records events)
           :in-theory (e/d (fn-bpr-article-records fn-bpaj-record-for-msgid)
                           (fn-bpr-event-article fn-held-p))))))

(local (defthm fn-bpsb-article-event-of-member
  (implies (and (member-equal row (fn-bpr-article-records events))
                (fn-bpr-row-stands-for row record fn-arena))
           (and (member-equal (fn-bpaj-article-event record events fn-arena) events)
                (fn-bpr-row-stands-for
                 (fn-bpr-event-article (fn-bpaj-article-event record events fn-arena))
                 record fn-arena)))
  :hints (("Goal" :induct (fn-bpr-article-records events)
           :in-theory (e/d (fn-bpr-article-records fn-bpaj-article-event)
                           (fn-bpr-event-article fn-bpr-row-stands-for))))))

(local (defthm fn-bpsb-composite-article-binds
  (implies (and (fn-stxa-p event)
                (fn-record-p (fn-bpr-event-article event)))
           (fn-stxa-bindsp event))
  :hints (("Goal" :in-theory (enable fn-bpr-event-article
                                     fn-replay-composite-record)))))

;; A composite row's composite, whose article record decodes (what the
;; intern established: fn-row-composite-okp, books/history-fold-refinement.lisp),
;; binds its verdict to that article.
(local (defthm fn-bpsb-composite-row-binds
  (implies (and (fn-hstxa-p event)
                (fn-record-p (fn-bpr-event-article (fn-hstxa-stxa event))))
           (fn-stxa-bindsp (fn-hstxa-stxa event)))
  :hints (("Goal" :use ((:instance fn-bpsb-composite-article-binds
                                   (event (fn-hstxa-stxa event))))
           :in-theory (e/d (fn-hstxa-p fn-hstxa-stxa)
                           (fn-bpsb-composite-article-binds fn-stxa-p fn-stxa-bindsp
                            fn-bpr-event-article fn-held-p))))))

(local (defthm fn-bpsb-car-member
  (implies (consp x) (member-equal (car x) x))))

(local (defthm fn-bpsb-transit-lookup-found
  (implies (and (fn-ceis-indexedp store)
                (equal (car (fn-bpaj-transit-record-lookup-fast
                             store request intent fn-arena))
                       :found))
           (let ((fields (fn-bpaj-transit-article-fields request))
                 (record (cadr (fn-bpaj-transit-record-lookup-fast
                                store request intent fn-arena))))
             (and (equal (car fields) :ok)
                  (member-equal (car (fn-bpaj-record-for-msgid
                                      (fn-record-octets-string (cadr fields))
                                      (fn-sf-records (fn-sn-files store))))
                                (fn-bpaj-record-for-msgid
                                 (fn-record-octets-string (cadr fields))
                                 (fn-sf-records (fn-sn-files store))))
                  (equal record (fn-row-wire-of
                                 (car (fn-bpaj-record-for-msgid
                                       (fn-record-octets-string (cadr fields))
                                       (fn-sf-records (fn-sn-files store))))
                                 fn-arena))
                  (fn-bpaj-store-record-accepted-fast store record fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-bpaj-transit-record-lookup-fast)
                                  (fn-bpaj-record-for-msgid fn-record-p
                                   fn-sn-event-index fn-cei-msgid-records
                                   fn-bpa-requestp fn-record-octets-string
                                   fn-bpaj-transit-article-fields
                                   fn-bpaj-transit-intentp
                                   fn-bpaj-store-record-accepted-fast))))))

(local (defthm fn-bpsb-direct-lookup-found
  (implies (and (fn-ceis-indexedp store)
                (equal (car (fn-bpaj-record-lookup-fast store request fn-arena)) :found))
           (let ((fields (fn-bpaj-article-fields request))
                 (record (cadr (fn-bpaj-record-lookup-fast store request fn-arena))))
             (and (equal (car fields) :ok)
                  (member-equal (car (fn-bpaj-record-for-msgid
                                      (fn-record-octets-string (cadr fields))
                                      (fn-sf-records (fn-sn-files store))))
                                (fn-bpaj-record-for-msgid
                                 (fn-record-octets-string (cadr fields))
                                 (fn-sf-records (fn-sn-files store))))
                  (equal record (fn-row-wire-of
                                 (car (fn-bpaj-record-for-msgid
                                       (fn-record-octets-string (cadr fields))
                                       (fn-sf-records (fn-sn-files store))))
                                 fn-arena))
                  (fn-bpaj-store-record-accepted-fast store record fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-bpaj-record-lookup-fast
                                   fn-bpaj-record-matches-request-fast)
                                  (fn-bpaj-record-for-msgid fn-record-p
                                   fn-sn-event-index fn-cei-msgid-records
                                   fn-bpa-requestp fn-record-octets-string
                                   fn-bpaj-article-fields
                                   fn-bpaj-store-record-accepted-fast))))))

(local (defthm fn-bpsb-dispatch-bind-is-a-found-lookup
  (implies (equal (car (fn-bpaj-dispatch-fast joined store request-octets
                                              generation fn-arena))
                  :bind)
           (let ((request (fn-bpaj-request request-octets))
                 (intent (fn-bpaj-request-intent joined request-octets))
                 (record (cadr (fn-bpaj-dispatch-fast joined store request-octets
                                                      generation fn-arena))))
             (if (equal (fn-bpaj-nth 0 intent) :request-transit-intent)
                 (and (equal (car (fn-bpaj-transit-record-lookup-fast
                                   store request intent fn-arena)) :found)
                      (equal (cadr (fn-bpaj-transit-record-lookup-fast
                                    store request intent fn-arena)) record))
               (and (equal (car (fn-bpaj-record-lookup-fast store request fn-arena)) :found)
                    (equal (cadr (fn-bpaj-record-lookup-fast store request fn-arena))
                           record)))))
  :hints (("Goal" :in-theory (e/d (fn-bpaj-dispatch-fast)
                                  (fn-bpaj-transit-record-lookup-fast
                                   fn-bpaj-record-lookup-fast
                                   fn-bpaj-request fn-bpaj-request-intent
                                   fn-bpaj-request-status-fast
                                   fn-bpaj-request-generation
                                   fn-bpaj-request-planned-result
                                   fn-bpaj-request-planned-txid))))))

;; A held row stands for its own wire form, which carries its Message-ID.
(local (defthm fn-bpsb-held-row-stands-for-its-wire
  (implies (fn-held-p row)
           (and (fn-bpr-row-stands-for row (fn-row-wire-of row fn-arena) fn-arena)
                (equal (fn-record-msgid (fn-row-wire-of row fn-arena))
                       (fn-record-msgid row))))
  :hints (("Goal" :in-theory (e/d (fn-bpr-row-stands-for fn-row-wire-of)
                                  (fn-held-p fn-held-wire fn-row-bytes))))))

(local (defthm fn-bpsb-accepted-fast-is-a-record
  (implies (fn-bpaj-store-record-accepted-fast store record fn-arena)
           (fn-record-p record))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpaj-store-record-accepted-fast)))))

(defthm fn-bpaj-dispatch-binds-the-stores-own-record-under-index
  (implies (and (fn-ceis-indexedp store)
                (equal (car (fn-bpaj-dispatch-fast joined store request-octets
                                                   generation fn-arena))
                       :bind))
           (let* ((record (cadr (fn-bpaj-dispatch-fast
                                 joined store request-octets generation fn-arena)))
                  (events (fn-sf-records (fn-sn-files store)))
                  (event (fn-bpaj-article-event record events fn-arena)))
             (and (fn-record-p record)
                  (equal (fn-record-msgid record)
                         (fn-bpaj-dispatch-msgid joined request-octets))
                  (fn-bpaj-store-record-accepted-fast store record fn-arena)
                  (member-equal event events)
                  (fn-bpr-row-stands-for (fn-bpr-event-article event) record fn-arena)
                  (implies (and (fn-hstxa-p event)
                                (fn-record-p (fn-bpr-event-article (fn-hstxa-stxa event))))
                           (fn-stxa-bindsp (fn-hstxa-stxa event))))))
  :hints (("Goal"
           :use (fn-bpsb-dispatch-bind-is-a-found-lookup
                 (:instance fn-bpsb-transit-lookup-found
                            (request (fn-bpaj-request request-octets))
                            (intent (fn-bpaj-request-intent joined request-octets)))
                 (:instance fn-bpsb-direct-lookup-found
                            (request (fn-bpaj-request request-octets)))
                 (:instance fn-bpsb-record-for-msgid-members
                            (row (car (fn-bpaj-record-for-msgid
                                       (fn-record-octets-string
                                        (cadr (fn-bpaj-transit-article-fields
                                               (fn-bpaj-request request-octets))))
                                       (fn-sf-records (fn-sn-files store)))))
                            (events (fn-sf-records (fn-sn-files store)))
                            (msgid (fn-record-octets-string
                                    (cadr (fn-bpaj-transit-article-fields
                                           (fn-bpaj-request request-octets))))))
                 (:instance fn-bpsb-record-for-msgid-members
                            (row (car (fn-bpaj-record-for-msgid
                                       (fn-record-octets-string
                                        (cadr (fn-bpaj-article-fields
                                               (fn-bpaj-request request-octets))))
                                       (fn-sf-records (fn-sn-files store)))))
                            (events (fn-sf-records (fn-sn-files store)))
                            (msgid (fn-record-octets-string
                                    (cadr (fn-bpaj-article-fields
                                           (fn-bpaj-request request-octets))))))
                 (:instance fn-bpsb-article-event-of-member
                            (row (car (fn-bpaj-record-for-msgid
                                       (fn-record-octets-string
                                        (cadr (fn-bpaj-transit-article-fields
                                               (fn-bpaj-request request-octets))))
                                       (fn-sf-records (fn-sn-files store)))))
                            (record (cadr (fn-bpaj-dispatch-fast
                                           joined store request-octets generation fn-arena)))
                            (events (fn-sf-records (fn-sn-files store))))
                 (:instance fn-bpsb-article-event-of-member
                            (row (car (fn-bpaj-record-for-msgid
                                       (fn-record-octets-string
                                        (cadr (fn-bpaj-article-fields
                                               (fn-bpaj-request request-octets))))
                                       (fn-sf-records (fn-sn-files store)))))
                            (record (cadr (fn-bpaj-dispatch-fast
                                           joined store request-octets generation fn-arena)))
                            (events (fn-sf-records (fn-sn-files store))))
                 (:instance fn-bpsb-composite-row-binds
                            (event (fn-bpaj-article-event
                                    (cadr (fn-bpaj-dispatch-fast
                                           joined store request-octets generation fn-arena))
                                    (fn-sf-records (fn-sn-files store)) fn-arena))))
           :in-theory (e/d (fn-bpaj-dispatch-msgid)
                           (fn-bpr-row-stands-for fn-row-wire-of
                            fn-bpr-row-stands-for-held-accessors
                            fn-bpsb-record-for-msgid-members
                            fn-bpsb-article-event-of-member
                            fn-bpsb-composite-row-binds
                            fn-stxa-p fn-stxa-bindsp fn-held-p fn-held-wire fn-hstxa-p
                            fn-bpsb-dispatch-bind-is-a-found-lookup
                            fn-bpsb-transit-lookup-found fn-bpsb-direct-lookup-found
                            fn-bpaj-dispatch-fast
                            fn-bpaj-transit-record-lookup-fast
                            fn-bpaj-record-lookup-fast
                            fn-bpaj-record-for-msgid fn-record-p
                            fn-bpr-article-records fn-bpr-event-article
                            fn-bpaj-article-event fn-record-octets-string
                            fn-bpaj-transit-article-fields fn-bpaj-article-fields
                            fn-bpaj-request-intent fn-bpaj-request
                            fn-bpaj-store-record-accepted-fast)))))
