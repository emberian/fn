; Witnesses and teeth for books/owner-store-indexed.lisp (PRF-144's carried
; index relation; PRF-132's keystones over the live Store).
;
; The live owner is built the way the host builds it: fn-osi-open over the
; history of tests/acl2/bp-signed-binding-tests.lisp's Store (a hybrid
; author's enrolment, then the signed article committed as a kind-4
; composite) under the default configuration record, then the host's own
; transitions (fn-osi-host-step): the five recovery barriers, and on the
; second owner the reservation, the carried identity prepare of the signed
; composite, its publication and the completion.
(in-package "ACL2")
(include-book "bp-signed-binding-tests")
(include-book "../../books/owner-store-indexed")
(include-book "std/testing/must-fail" :dir :system)

(defconst *osi-configs* (list *fn-cfg-default-record*))
(defconst *osi-events* (fn-sf-records (fn-sn-files *bsb-store*)))
(defconst *osi-frontier* (fn-sf-frontier (fn-sn-files *bsb-store*)))
(defconst *osi-enrolment* (list (car *osi-events*)))
(defconst *osi-barriers*
  (make-list 5 :initial-element '(:io :recovery-barrier :ok)))
(assert-event (equal *osi-events* (list *bsb-enrollment* *bsb-composite*)))

; -----------------------------------------------------------------------------
; Establishment: the open installs an indexed Store, on the full path and on
; the checkpoint path (the enrolment checkpointed, the composite after it).
(make-event
 `(defconst *osi-open*
    ',(fn-osi-open *osi-configs* nil *osi-events* *osi-frontier* 4)))
(assert-event (not (equal *osi-open* :fault)))
(assert-event (fn-ocl-relation *osi-open*))
(assert-event
 (equal (fn-osi-open *osi-configs* *osi-enrolment* (list *bsb-composite*)
                     *osi-frontier* 4)
        *osi-open*))
(assert-event
 (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner *osi-open*))))
(assert-event
 (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *osi-open*))))
        *osi-events*))
; The index answers the signed composite's article record for its Message-ID.
(assert-event
 (equal (fn-cei-msgid-records *bsb-msgid*
                              (fn-sn-event-index
                               (fn-own-store (fn-ocfg-owner *osi-open*))))
        (list *bsb-record*)))
; A refused open (no natural connection bound) is :fault with the empty,
; indexed Store.
(assert-event
 (equal (fn-osi-open *osi-configs* nil *osi-events* *osi-frontier* nil) :fault))
(assert-event (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner :fault))))

; -----------------------------------------------------------------------------
; The live Store after the recovery barriers: :ready, indexed, and the
; dispatcher binds the signed record (both PRF-132 keystones, antecedent and
; conclusion asserted literally).
(make-event
 `(defconst *osi-store*
    ',(fn-osi-live-store *osi-configs* nil *osi-events* *osi-frontier* 4
                     *osi-barriers*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *osi-store*)) :ready))
(assert-event (fn-sn-statep *osi-store*))
(assert-event (fn-ceis-indexedp *osi-store*))

; fn-bpaj-dispatch-never-resubmits-a-stored-article
(assert-event
 (and (member-equal *bsb-record*
                    (fn-bpr-article-records (fn-sf-records (fn-sn-files *osi-store*))))
      (fn-record-p *bsb-record*)
      (equal (fn-record-msgid *bsb-record*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (not (equal (fn-bpaj-dispatch-fast *bsb-joined* *osi-store*
                                         *bsb-request-octets* 1)
                  (list :submit)))))
; fn-bpaj-dispatch-binds-the-stores-own-record
(assert-event
 (equal (fn-bpaj-dispatch-fast *bsb-joined* *osi-store* *bsb-request-octets* 1)
        (list :bind *bsb-record*)))
(assert-event
 (bsb-binds-own-record-conclusion *bsb-joined* *osi-store*
                                  *bsb-request-octets* 1))
(assert-event
 (equal (fn-bpaj-article-event *bsb-record* (fn-sf-records (fn-sn-files *osi-store*)))
        *bsb-composite*))
; The live fast/checked equalities, at the live Store.
(assert-event
 (equal (fn-bpaj-dispatch-fast *bsb-joined* *osi-store* *bsb-request-octets* 1)
        (fn-bpaj-dispatch *bsb-joined* *osi-store* *bsb-request-octets* 1)))
(assert-event
 (equal (fn-bpaj-store-record-accepted-fast *osi-store* *bsb-record*)
        (fn-bpr-store-record-acceptedp *osi-store* *bsb-record*)))
(assert-event (fn-bpr-store-record-acceptedp *osi-store* *bsb-record*))
(assert-event
 (equal (fn-bpaj-transit-record-lookup-fast
         *osi-store* *bsb-request* (fn-bpaj-request-intent *bsb-joined*
                                                           *bsb-request-octets*))
        (fn-bpaj-transit-record-lookup
         *osi-store* *bsb-request* (fn-bpaj-request-intent *bsb-joined*
                                                           *bsb-request-octets*))))

; -----------------------------------------------------------------------------
; Preservation along the host's own transitions: the owner opened over the
; enrolment alone commits the signed composite through the carried identity
; prepare (fn-owner-prepare-identity's function), the record-file,
; record-link and record-directory observations (fn-owner-io's) and the
; completion (fn-owner-finish's).  The record-directory append extends the
; index by the composite; the dispatcher, which submitted before the
; commit, binds after it.
(defconst *osi-commit*
  (append *osi-barriers*
          '((:io :start-frontier nil) (:io :frontier-file :ok)
            (:io :frontier-replace :ok) (:io :frontier-directory :ok))
          (list (list :prepare-identity *bsb-composite*))
          '((:io :record-file :ok) (:io :record-link :ok)
            (:io :record-directory :ok) (:complete))))
(make-event
 `(defconst *osi-before*
    ',(fn-osi-live-store *osi-configs* nil *osi-enrolment* 1 4 *osi-barriers*)))
(make-event
 `(defconst *osi-after*
    ',(fn-osi-live-store *osi-configs* nil *osi-enrolment* 1 4 *osi-commit*)))
(assert-event (fn-ceis-indexedp *osi-before*))
(assert-event (equal (fn-bpaj-dispatch-fast *bsb-joined* *osi-before*
                                            *bsb-request-octets* 1)
                     '(:submit)))
(assert-event (equal (fn-sf-phase (fn-sn-files *osi-after*)) :ready))
(assert-event (equal (fn-sf-records (fn-sn-files *osi-after*)) *osi-events*))
(assert-event (fn-ceis-indexedp *osi-after*))
(assert-event (equal (fn-sn-event-index *osi-after*) (fn-cei-build *osi-events*)))
(assert-event (equal (fn-bpaj-dispatch-fast *bsb-joined* *osi-after*
                                            *bsb-request-octets* 1)
                     (list :bind *bsb-record*)))

; The kernel crash is the one Store transition the host family excludes:
; the crash image carries the empty index while its history is kept, so
; the relation fails until recovery, which rebuilds it.  (A crash is the
; death of the process; its next owner is the open above.)
(make-event
 `(defconst *osi-crashed*
    ',(fn-sn-crash *osi-after* :old :absent)))
(assert-event (equal (fn-sf-phase (fn-sn-files *osi-crashed*)) :replaying))
(assert-event (not (fn-ceis-indexedp *osi-crashed*)))
(assert-event (fn-ceis-relatedp *osi-crashed*))
(assert-event (fn-ceis-indexedp (fn-sn-recover *osi-crashed*)))
(assert-event (not (fn-osi-host-own-eventp
                    '(:store (:crash :old :absent)))))

; -----------------------------------------------------------------------------
; Hypothesis removal for the restated keystones, over live Stores.
;
; fn-bpaj-dispatch-never-resubmits-a-stored-article, (1) without the Store
; holding the record: the live Store opened over the enrolment alone.  The
; record is an article record with the dispatcher's Message-ID, not in that
; Store's article records, and the dispatcher submits.
(assert-event
 (and (fn-record-p *bsb-record*)
      (equal (fn-record-msgid *bsb-record*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (not (member-equal *bsb-record*
                         (fn-bpr-article-records
                          (fn-sf-records (fn-sn-files *osi-before*)))))))
(must-fail
 (assert-event
  (not (equal (fn-bpaj-dispatch-fast *bsb-joined* *osi-before*
                                     *bsb-request-octets* 1)
              (list :submit)))))
; (2) Without the Message-ID agreement: the second signed request over the
; live Store that holds the first.  The record is in the Store's article
; records and is an article record; its Message-ID is not the one the
; dispatcher reads, and the dispatcher submits.
(assert-event
 (and (member-equal *bsb-record*
                    (fn-bpr-article-records (fn-sf-records (fn-sn-files *osi-store*))))
      (fn-record-p *bsb-record*)
      (not (equal (fn-record-msgid *bsb-record*)
                  (fn-bpaj-dispatch-msgid *bsb-other-joined*
                                          *bsb-other-request-octets*)))))
(must-fail
 (assert-event
  (not (equal (fn-bpaj-dispatch-fast *bsb-other-joined* *osi-store*
                                     *bsb-other-request-octets* 1)
              (list :submit)))))
; (3) fn-record-p has no live counter-witness: an open admits only Store
; events, so a live history holds no non-record under a Message-ID; its
; must-fail is the refinement lemma's (bp-signed-binding-tests (2), a
; constructed Store).  The hypothesis is kept; no weakened theorem was
; proved.

; fn-bpaj-dispatch-binds-the-stores-own-record, without a :bind answer: the
; live Store before the commit, where the dispatcher submits; nothing bound
; is an article record.
(assert-event
 (not (equal (car (fn-bpaj-dispatch-fast *bsb-joined* *osi-before*
                                         *bsb-request-octets* 1))
             :bind)))
(must-fail
 (assert-event
  (bsb-binds-own-record-conclusion *bsb-joined* *osi-before*
                                   *bsb-request-octets* 1)))

; -----------------------------------------------------------------------------
; PKT-330 (4): does fn-own-relation (the premise of the article and identity
; prepare keystones, through fn-snt-relation) hold of every live owner?
;
; A group removal keeps it: fn-ocl-publish installs fn-cpo-configure-durable
; of the Store (fn-ocl-complete-success-install-exact-store), and removing
; fn.letters from the live Store above keeps the allocation domain (retired
; names stay in it), so the store-only replay still holds.
(make-event
 `(defconst *osi-drop*
    ',(fn-cpo-configure-durable
       *osi-store*
       (fn-cfg-record-make 1 (fn-sf-frontier (fn-sn-files *osi-store*)) 2
                           (list (fn-cfg-remove-group "fn.letters"))
                           *fn-cfg-default-stamp*))))
(assert-event (not (equal (fn-sn-config-history *osi-drop*)
                          (fn-sn-config-history *osi-store*))))
(assert-event (member-equal "fn.letters" (fn-sn-groups *osi-drop*)))
(assert-event (fn-cst-relation *osi-drop*))
(assert-event (fn-snt-relation *osi-drop*))
(assert-event (fn-ceis-indexedp *osi-drop*))

; COUNTEREXAMPLE (labelled, reachable at the host's open): a history whose
; configuration later reduced the capacity below an undertaking it had
; accepted (config-observed-tests' image).  The owner the host installs
; satisfies the configured relation fn-ocl-relation and the index relation,
; and NOT fn-own-relation: the store-only replay under the final capacity
; refuses the undertaking.  So the -under-relation prepare keystones
; (fn-opc-prepare-equals-owner-event-under-relation,
; fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation) do not cover
; this live owner; the index relation of this book does.
(defconst *osi-cap-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-osi" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-osi" "subject" "evidence" 0)))
(defconst *osi-cap-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(make-event
 `(defconst *osi-cap-owner*
    ',(fn-osi-open *osi-cap-configs* nil *osi-cap-events* 8 4)))
(assert-event (not (equal *osi-cap-owner* :fault)))
(assert-event (fn-ocl-relation *osi-cap-owner*))
(assert-event (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner *osi-cap-owner*))))
(assert-event (not (fn-snt-relation (fn-own-store (fn-ocfg-owner *osi-cap-owner*)))))
(assert-event (not (fn-own-relation (fn-ocfg-owner *osi-cap-owner*))))
; The signed-history owner above is inside both.
(assert-event (fn-own-relation (fn-ocfg-owner *osi-open*)))
