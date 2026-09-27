; Witnesses and teeth for books/bp-signed-binding.lisp (PRF-132).
;
; The refinement lemmas (-under-index) over Stores built by the Store's own
; transitions; the keystones themselves are stated over the live owner's
; Store and toothed in tests/acl2/owner-store-indexed-tests.lisp.
; The subject is fn-bpaj-dispatch-fast, which host/bp-receipt-journal-host.lisp
; fn-bprj-request-action calls for host/native/bp-app.lisp fnn-bpapp-action.
; The Store below is built by the Store's own transitions: a hybrid author is
; enrolled (a kind-3 keyring event), then a signed article is committed as the
; kind-4 composite fn-hsig-authorized-article-event builds from the Store's
; enrolled snapshot and the two primitive observations (:verified :verified;
; the observations exercise the Store codec and the replay route, not the
; native primitives).  The article is the transit shape of the signed mission:
; injected (it carries Injection-Info, as every Store-rendered hybrid-signed
; carrier does) and stored as the relaying node's Path projection.
(in-package "ACL2")
(include-book "../../books/bp-signed-binding")
(include-book "../../books/codec-attach")
; Intents pin digests (PKT-646): fn-frame-digest runs through its attachment.
(include-book "../../books/crypto-attach")
(include-book "must-fail-checked")
(include-book "arena-lift")
(bpr-lift fn-bpaj-article-event 2)
(bpr-lift fn-bpaj-dispatch-fast 4)
(bpr-lift fn-bpaj-replay 2)
(bpr-lift fn-bpr-store-record-acceptedp 2)
(bpr-lift fn-row-wire-of 1)


(defun bsb-o (s) (fn-record-string-octets s))
(defun bsb-lines (strings)
  (if (consp strings) (cons (bsb-o (car strings)) (bsb-lines (cdr strings))) nil))

(defconst *bsb-msgid* "<a1@example.invalid>")
(defconst *bsb-article*
  (fn-post-body-octets
   (bsb-lines '("Path: a.mission.invalid!not-for-mail"
                "From: poster@example.invalid"
                "Newsgroups: fn.letters" "Subject: mission report"
                "Date: Sat, 26 Sep 2026 12:00:00 +0000"
                "Injection-Info: a.mission.invalid"
                "Message-ID: <a1@example.invalid>" "" "The signed report."))))
(make-event
 `(defconst *bsb-request*
    ',(fn-bpa-make-request
       "work-a-report"
       (fn-record-octets-string
        (fn-id-text (fn-id-subject-of-payload *bsb-article*)))
       "dtn://fn-a/" "dtn://fn.lab/inbox" "receiver-policy"
       "incarnation" "auth" "terms" *bsb-article*)))
(defconst *bsb-request-octets* (fn-bpa-encode *bsb-request*))
(make-event
 `(defconst *bsb-stored*
    ',(fn-pu-relay-article *bsb-article* (bsb-o "b.mission.invalid")
                           (bsb-o "y.mission.invalid"))))
(defconst *bsb-payloads* (list *bsb-stored*))
; The durable transit intent the host persists before any Store attempt:
; planned transaction 1 (the Store's next after the enrollment), :accepted;
; the request by reference and the stored projection by length and digest
; (PKT-646).
(make-event
 `(defconst *bsb-intent*
    ',(let ((ref (fn-bpaj-request-ref *bsb-request*)))
        (list :request-transit-intent "bundle-a-report" (car ref) 1 1
              :accepted "y-boundary" "b.mission.invalid" "y.mission.invalid"
              (cadr ref) (caddr ref)
              (len *bsb-stored*) (fn-frame-digest *bsb-stored*)))))
(assert-event (fn-bpaj-transit-intentp *bsb-intent*))
(assert-event
 (equal (car (fn-bpaj-transit-article-fields *bsb-request*)) :ok))
(defconst *bsb-config*
  '(:config "dtn://fn.lab/inbox" "receiver-policy" "dtn://fn.lab/issuer"))
(make-event
 `(defconst *bsb-joined*
    ',(fn-bpaj-nth 1 (in-arena-fn-bpaj-replay *bsb-payloads* (fn-sn-initial '("fn.letters" "fn.test") 10) (list *bsb-config* *bsb-intent*)))))
(assert-event
 (equal (fn-bpaj-request-status-fast *bsb-joined* *bsb-request-octets*) :intent))
(assert-event
 (equal (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*) *bsb-msgid*))

; The Store: the hybrid author's enrollment, then the signed article.
(defconst *bsb-principal* (make-list 32 :initial-element 7))
(defconst *bsb-keys*
  (list (cons :ed25519 (make-list 32 :initial-element 11))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(defconst *bsb-signatures*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(make-event
 `(defconst *bsb-snapshot*
    ',(fn-hsig-keyring-snapshot *bsb-principal* *bsb-keys*)))
(make-event
 `(defconst *bsb-enrollment*
    ',(fn-hsig-keyring-event 0 0 0 1 *bsb-principal* *bsb-keys*)))
(defun bsb-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun bsb-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defun bsb-commit (s event)
  (fn-sn-finish (bsb-publish (fn-sn-prepare-identity (bsb-reserve s) event))))

(defconst *bsb-store0* (fn-sn-initial '("fn.letters" "fn.test") 10))
(make-event
 `(defconst *bsb-enrolled* ',(bsb-commit *bsb-store0* *bsb-enrollment*)))
(make-event
 `(defconst *bsb-record*
    ',(fn-record-make 1 1 1 *bsb-msgid* *bsb-stored* '("fn.letters")
                      "pin-a-report" "subject-a-report" "release" 2 843700000)))
(make-event
 `(defconst *bsb-composite*
    ',(fn-hsig-authorized-article-event
       1 1 1 1 *bsb-snapshot* *bsb-msgid*
       (fn-record-string-octets "subject-a-report")
       (fn-record-encode-impl *bsb-record*)
       *bsb-principal* *bsb-keys* *bsb-stored*
       *bsb-signatures* (cdr (cadr *bsb-keys*))
       :verified :verified)))
(assert-event (fn-stxa-p *bsb-composite*))
(assert-event (fn-stxa-bindsp *bsb-composite*))
;; The Store retains the composite as a composite ROW (records-flip): its
;; article is the held row the intern makes of the composite's article record
;; at handle 0 (the arena of this test holds the stored projection there).
(make-event
 `(defconst *bsb-row*
    ',(fn-intern-row-at *bsb-record* (fn-sn-keyring *bsb-enrolled*)
                        (fn-sn-keyring-generation *bsb-enrolled*) 0)))
(defconst *bsb-row-composite* (fn-hstxa-make *bsb-composite* *bsb-row*))

(assert-event (fn-hstxa-p *bsb-row-composite*))
(make-event
 `(defconst *bsb-store* ',(bsb-commit *bsb-enrolled* *bsb-row-composite*)))
(assert-event (fn-sn-statep *bsb-store*))
(assert-event (equal (fn-sf-phase (fn-sn-files *bsb-store*)) :ready))
(assert-event
 (member-equal *bsb-row-composite* (fn-sf-records (fn-sn-files *bsb-store*))))
(assert-event (equal (fn-bpr-event-article *bsb-composite*) *bsb-record*))
(assert-event (equal (fn-bpr-event-article *bsb-row-composite*) *bsb-row*))
(assert-event (fn-record-p *bsb-record*))
(assert-event (fn-held-p *bsb-row*))
(assert-event (equal (in-arena-fn-row-wire-of *bsb-payloads* *bsb-row*) *bsb-record*))
(assert-event
 (member-equal *bsb-row*
               (fn-bpr-article-records (fn-sf-records (fn-sn-files *bsb-store*)))))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *bsb-payloads* *bsb-store* *bsb-record*))

; -----------------------------------------------------------------------------
; Reachable positive witness.  Before the commit the dispatcher asks for the
; one Store submission; after it, over the Store holding the signed
; composite, it binds the composite's article record.  Both keystones'
; antecedents and conclusions are asserted literally.
(assert-event
 (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-enrolled* *bsb-request-octets* 1)
        '(:submit)))
(assert-event
 (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-store* *bsb-request-octets* 1)
        (list :bind *bsb-record*)))

; The index premise (PRF-144) holds of both Stores: built by the Store's own
; transitions from the initial state, whose index is the empty build.
(assert-event (fn-ceis-indexedp *bsb-enrolled*))
(assert-event (fn-ceis-indexedp *bsb-store*))
(assert-event (equal (fn-cei-msgid-records *bsb-msgid*
                                           (fn-sn-event-index *bsb-store*))
                     (list *bsb-row*)))

; fn-bpaj-dispatch-never-resubmits-under-index
(assert-event
 (and (fn-ceis-indexedp *bsb-store*)
      (member-equal *bsb-row*
                    (fn-bpr-article-records (fn-sf-records (fn-sn-files *bsb-store*))))
      (fn-held-p *bsb-row*)
      (equal (fn-record-msgid *bsb-row*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (not (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-store* *bsb-request-octets* 1)
                  (list :submit)))))

; fn-bpaj-dispatch-binds-the-stores-own-record-under-index
(defun bsb-binds-own-record-conclusion (joined store octets generation fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((record (cadr (fn-bpaj-dispatch-fast joined store octets generation fn-arena)))
         (events (fn-sf-records (fn-sn-files store)))
         (event (fn-bpaj-article-event record events fn-arena)))
    (and (fn-record-p record)
         (equal (fn-record-msgid record) (fn-bpaj-dispatch-msgid joined octets))
         (fn-bpaj-store-record-accepted-fast store record fn-arena)
         (member-equal event events)
         (fn-bpr-row-stands-for (fn-bpr-event-article event) record fn-arena)
         (implies (and (fn-hstxa-p event)
                       (fn-record-p (fn-bpr-event-article (fn-hstxa-stxa event))))
                  (fn-stxa-bindsp (fn-hstxa-stxa event))))))
(bpr-lift bsb-binds-own-record-conclusion 4)
(assert-event
 (equal (car (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-store* *bsb-request-octets* 1))
        :bind))
(assert-event
 (in-arena-bsb-binds-own-record-conclusion *bsb-payloads* *bsb-joined* *bsb-store* *bsb-request-octets* 1))
; The event it names is the signed composite itself, whose verdict event is
; the Store's own kind-2 :verified verdict for this Message-ID.
(assert-event
 (equal (in-arena-fn-bpaj-article-event *bsb-payloads* *bsb-record* (fn-sf-records (fn-sn-files *bsb-store*)))
        *bsb-row-composite*))
(assert-event
 (let ((verdict (fn-stmt-value (fn-stxe-decode-exact
                                (fn-stxa-verdict-event *bsb-composite*)))))
   (and (equal (fn-stxe-msgid verdict) *bsb-msgid*)
        (equal (fn-stxe-token verdict) :verified))))

; The bound record carries on through the receiver: the transit context the
; host publishes for it replays against the Store and the request is bound.
(make-event
 `(defconst *bsb-context*
    ',(fn-bpaj-transit-context-record "bundle-a-report" *bsb-request-octets*
                                      (fn-record-encode-impl *bsb-record*)
                                      1 1 1 :accepted)))
(assert-event *bsb-context*)
(make-event
 `(defconst *bsb-context-replay*
    ',(in-arena-fn-bpaj-replay *bsb-payloads* *bsb-store* (list *bsb-config* *bsb-intent* *bsb-context*))))
(assert-event (car *bsb-context-replay*))
(assert-event
 (equal (fn-bpaj-request-status-fast (fn-bpaj-nth 1 *bsb-context-replay*)
                                     *bsb-request-octets*)
        :context))
(assert-event
 (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* (fn-bpaj-nth 1 *bsb-context-replay*) *bsb-store* *bsb-request-octets* 1)
        '(:prepare-receipt)))

; -----------------------------------------------------------------------------
; Labelled mutation witness: the Store binding before PRF-132 read plain
; article records only.  Over the signed Store it finds nothing, so the
; lookup was (:absent) and the dispatcher asked for a second submission,
; which the owner refused as (:have :history) (the layer-2 refusal).
(defun bsb-plain-record-for-msgid (msgid records)
  (if (consp records)
      (let ((rest (bsb-plain-record-for-msgid msgid (cdr records))))
        (if (and (fn-record-p (car records))
                 (equal msgid (fn-record-msgid (car records))))
            (cons (car records) rest)
          rest))
    nil))
(assert-event
 (equal (bsb-plain-record-for-msgid *bsb-msgid*
                                    (fn-sf-records (fn-sn-files *bsb-store*)))
        nil))
(assert-event
 (equal (fn-bpaj-record-for-msgid *bsb-msgid*
                                  (fn-sf-records (fn-sn-files *bsb-store*)))
        (list *bsb-row*)))

; -----------------------------------------------------------------------------
; Hypothesis removal, fn-bpaj-dispatch-never-resubmits-under-index.
;
; (1) Without the Store holding the record: the enrolled Store before the
; commit.  The record is an article record with the dispatcher's
; Message-ID, it is not in that Store's article records, and the dispatcher
; submits.
(assert-event
 (and (fn-held-p *bsb-row*)
      (equal (fn-record-msgid *bsb-row*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (not (member-equal *bsb-row*
                         (fn-bpr-article-records
                          (fn-sf-records (fn-sn-files *bsb-enrolled*)))))))
(must-fail-checked
 (assert-event
  (not (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-enrolled* *bsb-request-octets* 1)
              (list :submit)))))

; (2) Without fn-held-p (fn-record-p before the records flip): a constructed (unreachable) Store whose history
; holds a non-record carrying the Message-ID at the record's position.  It
; is a member of the article records with the dispatcher's Message-ID, it
; is not an article record, and the dispatcher submits.
(defconst *bsb-non-record* (list 0 0 0 *bsb-msgid*))
(defconst *bsb-forged-store*
  (let ((forged (fn-sn-update *bsb-store0*
                              (update-nth 4 (fn-sl-of (list *bsb-non-record*))
                                          (fn-sn-files *bsb-store0*))
                              (fn-sn-node *bsb-store0*))))
    (fn-sn-with-event-index forged
                            (fn-cei-build (fn-sf-records (fn-sn-files forged))))))
(assert-event
 (and (fn-ceis-indexedp *bsb-forged-store*)
      (member-equal *bsb-non-record*
                    (fn-bpr-article-records
                     (fn-sf-records (fn-sn-files *bsb-forged-store*))))
      (equal (fn-record-msgid *bsb-non-record*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (not (fn-held-p *bsb-non-record*))))
(must-fail-checked
 (assert-event
  (not (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-forged-store* *bsb-request-octets* 1)
              (list :submit)))))

; (2b) Without the index premise (PRF-144): a CORRUPTED Store, the committed
; Store with the index it carried before the commit.  The record is in the
; history, is an article record, carries the dispatcher's Message-ID; the
; index no longer corresponds to the history, and the dispatcher submits
; again.  So the premise is doing the work.
(defconst *bsb-stale-index-store*
  (fn-sn-with-event-index *bsb-store* (fn-sn-event-index *bsb-enrolled*)))
(assert-event
 (and (not (fn-ceis-indexedp *bsb-stale-index-store*))
      (member-equal *bsb-row*
                    (fn-bpr-article-records
                     (fn-sf-records (fn-sn-files *bsb-stale-index-store*))))
      (fn-held-p *bsb-row*)
      (equal (fn-record-msgid *bsb-row*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-stale-index-store* *bsb-request-octets* 1)
             '(:submit))))

; (3) Without the Message-ID agreement: a second signed request (another
; Message-ID) over the same Store.  The signed record is in the Store's
; article records and is an article record, its Message-ID is not the one
; the dispatcher reads, and the dispatcher submits the other request.
(defconst *bsb-other-article*
  (fn-post-body-octets
   (bsb-lines '("Path: a.mission.invalid!not-for-mail"
                "From: poster@example.invalid"
                "Newsgroups: fn.letters" "Subject: second report"
                "Date: Sat, 26 Sep 2026 12:05:00 +0000"
                "Injection-Info: a.mission.invalid"
                "Message-ID: <a2@example.invalid>" "" "Another report."))))
(make-event
 `(defconst *bsb-other-request-octets*
    ',(fn-bpa-encode
       (fn-bpa-make-request
        "work-a-second"
        (fn-record-octets-string
         (fn-id-text (fn-id-subject-of-payload *bsb-other-article*)))
        "dtn://fn-a/" "dtn://fn.lab/inbox" "receiver-policy"
        "incarnation" "auth" "terms" *bsb-other-article*))))
(make-event
 `(defconst *bsb-other-intent*
    ',(let ((ref (fn-bpaj-request-ref
                  (fn-bpaj-request *bsb-other-request-octets*)))
            (stored (fn-pu-relay-article *bsb-other-article*
                                         (bsb-o "b.mission.invalid")
                                         (bsb-o "y.mission.invalid"))))
        (list :request-transit-intent "bundle-a-second" (car ref)
              1 2 :accepted "y-boundary" "b.mission.invalid" "y.mission.invalid"
              (cadr ref) (caddr ref) (len stored) (fn-frame-digest stored)))))
(assert-event (fn-bpaj-transit-intentp *bsb-other-intent*))
(make-event
 `(defconst *bsb-other-joined*
    ',(fn-bpaj-nth 1 (in-arena-fn-bpaj-replay *bsb-payloads* *bsb-store0* (list *bsb-config* *bsb-other-intent*)))))
(assert-event
 (and (member-equal *bsb-row*
                    (fn-bpr-article-records (fn-sf-records (fn-sn-files *bsb-store*))))
      (fn-held-p *bsb-row*)
      (not (equal (fn-record-msgid *bsb-row*)
                  (fn-bpaj-dispatch-msgid *bsb-other-joined*
                                          *bsb-other-request-octets*)))))
(must-fail-checked
 (assert-event
  (not (equal (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-other-joined* *bsb-store* *bsb-other-request-octets* 1)
              (list :submit)))))

; Hypothesis removal, fn-bpaj-dispatch-binds-the-stores-own-record-under-index: without
; a :bind answer (the Store before the commit, where the dispatcher submits)
; the conclusion fails: nothing bound is an article record.
(assert-event
 (not (equal (car (in-arena-fn-bpaj-dispatch-fast *bsb-payloads* *bsb-joined* *bsb-enrolled* *bsb-request-octets* 1))
             :bind)))
(must-fail-checked
 (assert-event
  (in-arena-bsb-binds-own-record-conclusion *bsb-payloads* *bsb-joined* *bsb-enrolled*
                                   *bsb-request-octets* 1)))
