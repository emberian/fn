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
(include-book "must-fail-checked")

(defconst *osi-configs* (list *fn-cfg-default-record*))
(defconst *osi-events* (fn-sf-records (fn-sn-files *bsb-store*)))
(defconst *osi-frontier* (fn-sf-frontier (fn-sn-files *bsb-store*)))
(defconst *osi-enrolment* (list (car *osi-events*)))
(defconst *osi-barriers*
  (make-list *fn-sf-recovery-barrier-count* :initial-element '(:io :recovery-barrier :ok)))
;; by specification: the flip -- the Store retains the signed composite as
;; its composite ROW (books/held-record.lisp fn-hstxa-p; bp-signed-binding-tests
;; *bsb-row-composite*: the wire composite beside its article interned at
;; handle 0, whose bytes are *bsb-payloads*'s one payload).
(assert-event (equal *osi-events* (list *bsb-enrollment* *bsb-row-composite*)))

; -----------------------------------------------------------------------------
; Establishment: the open installs an indexed Store, on the full path and on
; the checkpoint path (the enrolment checkpointed, the composite after it).
(make-event
 `(defconst *osi-open*
    ',(fn-osi-open *osi-configs* nil *osi-events* *osi-frontier* 4)))
(assert-event (not (equal *osi-open* :fault)))
(assert-event (fn-ocl-relation *osi-open*))
(assert-event
 (equal (fn-osi-open *osi-configs* *osi-enrolment* (list *bsb-row-composite*)
                     *osi-frontier* 4)
        *osi-open*))
(assert-event
 (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner *osi-open*))))
(assert-event
 (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *osi-open*))))
        *osi-events*))
; The index answers the signed composite's article record for its Message-ID.
; by specification: the flip -- the index holds retained rows: the answer is
; the held row, which stands for the wire record over the test's arena.
(assert-event
 (equal (fn-cei-msgid-records *bsb-msgid*
                              (fn-sn-event-index
                               (fn-own-store (fn-ocfg-owner *osi-open*))))
        (list *bsb-row*)))
(assert-event (equal (in-arena-fn-row-wire-of *bsb-payloads* *bsb-row*) *bsb-record*))
; A refused open (no natural connection bound) is :fault with the empty,
; indexed Store.
(assert-event
 (equal (fn-osi-open *osi-configs* nil *osi-events* *osi-frontier* nil) :fault))
(assert-event (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner :fault))))

; -----------------------------------------------------------------------------
; The live Store after the recovery barriers: :ready, indexed, and the
; dispatcher binds the signed record (both PRF-132 keystones, antecedent and
; conclusion asserted literally).
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: the signed article's
;; stored projection at handle 0, the handle of *bsb-row* (records-flip).
(defconst *sr-arena* *bsb-payloads*)
(bpr-lift fn-bpaj-dispatch 4)
(bpr-lift fn-bpaj-store-record-accepted-fast 2)
(bpr-lift fn-bpaj-transit-record-lookup-fast 3)
(bpr-lift fn-bpaj-transit-record-lookup 3)
(bpr-lift fn-bpaj-node-record-committed-carriedp 2)
(bpr-lift fn-bpi-node-wire-committedp 2)
(bpr-lift fn-osi-live-owner 6)
(bpr-lift fn-osi-live-store 6)
(make-event
 `(defconst *osi-store*
    ',(in-arena-fn-osi-live-store *sr-arena* *osi-configs* nil *osi-events* *osi-frontier* 4 *osi-barriers*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *osi-store*)) :ready))
(assert-event (fn-sn-statep *osi-store*))
(assert-event (fn-ceis-indexedp *osi-store*))

; fn-bpaj-dispatch-never-resubmits-a-stored-article
; by specification: the flip -- the keystone is stated over the Store's
; retained row (fn-held-p, books/owner-store-indexed.lisp), the held row
; *bsb-row* the Store keeps for the signed record.
(assert-event
 (and (member-equal *bsb-row*
                    (fn-bpr-article-records (fn-sf-records (fn-sn-files *osi-store*))))
      (fn-held-p *bsb-row*)
      (equal (fn-record-msgid *bsb-row*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (not (equal (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-joined* *osi-store*
                                         *bsb-request-octets* 1)
                  (list :submit)))))
; fn-bpaj-dispatch-binds-the-stores-own-record
(assert-event
 (equal (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-joined* *osi-store* *bsb-request-octets* 1)
        (list :bind *bsb-record*)))
(assert-event
 (in-arena-bsb-binds-own-record-conclusion *sr-arena* *bsb-joined* *osi-store*
                                  *bsb-request-octets* 1))
(assert-event
 (equal (in-arena-fn-bpaj-article-event *sr-arena* *bsb-record* (fn-sf-records (fn-sn-files *osi-store*)))
        *bsb-row-composite*))
(bpr-lift fn-bpr-row-stands-for 2)
;; The restated conclusion's arms, literally at the bound record (audit-fixes
;; item 1): the event's article (the held row) stands for the bound wire
;; record through the arena, and the composite arm (fn-hstxa-p) binds its
;; verdict.
(assert-event
 (let ((event (in-arena-fn-bpaj-article-event *sr-arena* *bsb-record*
                                              (fn-sf-records (fn-sn-files *osi-store*)))))
   (and (fn-hstxa-p event)
        (equal (fn-bpr-event-article event) *bsb-row*)
        (in-arena-fn-bpr-row-stands-for *sr-arena* (fn-bpr-event-article event) *bsb-record*)
        (fn-record-p (fn-bpr-event-article (fn-hstxa-stxa event)))
        (fn-stxa-bindsp (fn-hstxa-stxa event)))))
; The live fast/checked equalities, at the live Store.
(assert-event
 (equal (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-joined* *osi-store* *bsb-request-octets* 1)
        (in-arena-fn-bpaj-dispatch *sr-arena* *bsb-joined* *osi-store* *bsb-request-octets* 1)))
(assert-event
 (equal (in-arena-fn-bpaj-store-record-accepted-fast *sr-arena* *osi-store* *bsb-record*)
        (in-arena-fn-bpr-store-record-acceptedp *sr-arena* *osi-store* *bsb-record*)))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *sr-arena* *osi-store* *bsb-record*))
(assert-event
 (equal (in-arena-fn-bpaj-transit-record-lookup-fast *sr-arena*
         *osi-store* *bsb-request* (fn-bpaj-request-intent *bsb-joined*
                                                           *bsb-request-octets*))
        (in-arena-fn-bpaj-transit-record-lookup *sr-arena*
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
          (list (list :prepare-identity *bsb-row-composite*))
          '((:io :record-file :ok) (:io :record-link :ok)
            (:io :record-directory :ok) (:complete))))
(make-event
 `(defconst *osi-before*
    ',(in-arena-fn-osi-live-store *sr-arena* *osi-configs* nil *osi-enrolment* 1 4 *osi-barriers*)))
(make-event
 `(defconst *osi-after*
    ',(in-arena-fn-osi-live-store *sr-arena* *osi-configs* nil *osi-enrolment* 1 4 *osi-commit*)))
(assert-event (fn-ceis-indexedp *osi-before*))
(assert-event (equal (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-joined* *osi-before*
                                            *bsb-request-octets* 1)
                     '(:submit)))
(assert-event (equal (fn-sf-phase (fn-sn-files *osi-after*)) :ready))
(assert-event (equal (fn-sf-records (fn-sn-files *osi-after*)) *osi-events*))
(assert-event (fn-ceis-indexedp *osi-after*))
(assert-event (equal (fn-sn-event-index *osi-after*) (fn-cei-build *osi-events*)))
(assert-event (equal (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-joined* *osi-after*
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
 (and (fn-held-p *bsb-row*)
      (equal (fn-record-msgid *bsb-row*)
             (fn-bpaj-dispatch-msgid *bsb-joined* *bsb-request-octets*))
      (not (member-equal *bsb-row*
                         (fn-bpr-article-records
                          (fn-sf-records (fn-sn-files *osi-before*)))))))
(must-fail-checked
 (assert-event
  (not (equal (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-joined* *osi-before*
                                     *bsb-request-octets* 1)
              (list :submit)))))
; (2) Without the Message-ID agreement: the second signed request over the
; live Store that holds the first.  The record is in the Store's article
; records and is an article record; its Message-ID is not the one the
; dispatcher reads, and the dispatcher submits.
(assert-event
 (and (member-equal *bsb-row*
                    (fn-bpr-article-records (fn-sf-records (fn-sn-files *osi-store*))))
      (fn-held-p *bsb-row*)
      (not (equal (fn-record-msgid *bsb-row*)
                  (fn-bpaj-dispatch-msgid *bsb-other-joined*
                                          *bsb-other-request-octets*)))))
(must-fail-checked
 (assert-event
  (not (equal (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-other-joined* *osi-store*
                                     *bsb-other-request-octets* 1)
              (list :submit)))))
; (3) fn-held-p (fn-record-p before the records flip) has no live
; counter-witness: an open admits only Store
; events, so a live history holds no non-record under a Message-ID; its
; must-fail is the refinement lemma's (bp-signed-binding-tests (2), a
; constructed Store).  The hypothesis is kept; no weakened theorem was
; proved.

; fn-bpaj-dispatch-binds-the-stores-own-record, without a :bind answer: the
; live Store before the commit, where the dispatcher submits; nothing bound
; is an article record.
(assert-event
 (not (equal (car (in-arena-fn-bpaj-dispatch-fast *sr-arena* *bsb-joined* *osi-before*
                                         *bsb-request-octets* 1))
             :bind)))
(must-fail-checked
 (assert-event
  (in-arena-bsb-binds-own-record-conclusion *sr-arena* *bsb-joined* *osi-before*
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

; -----------------------------------------------------------------------------
; PRF-191: the host's open also installs the premise of the POST's view-trie
; lookups (books/post-identity-index.lisp): fn-ocl-relation and
; fn-scar-view-indexedp give fn-pidx-view-okp (fn-pidx-view-okp-of-live-owner),
; and the lookup answers the signed composite's article as the scan does.
(defconst *osi-open-owner* (fn-ocfg-owner *osi-open*))
(defconst *osi-open-arts*
  (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store *osi-open-owner*)))))
(assert-event
 (and (fn-ocl-relation *osi-open*)
      (fn-scar-view-indexedp *osi-open-owner*)
      (fn-pidx-view-okp (fn-own-view *osi-open-owner*))
      (consp (fn-find-article *bsb-msgid* *osi-open-arts*))
      (equal (fn-own-view-raw (fn-own-view *osi-open-owner*)) *osi-open-arts*)
      (equal (fn-pidx-find-article *bsb-msgid* *osi-open-arts*
                                   (fn-own-view *osi-open-owner*))
             (fn-find-article *bsb-msgid* *osi-open-arts*))))

; -----------------------------------------------------------------------------
; PRF-220: the Store check the BP application and receipt-journal hosts run
; carries the node recognizer instead of evaluating it per request.
;
; fn-bpaj-node-record-committed-carriedp-is-committedp (books/bp-native-app-fast.lisp).
; Positive witness: the live Store's node after the recovery barriers, the
; signed record it committed.  Antecedent and conclusion, literally.
(defconst *osi-live-node* (fn-sn-node *osi-store*))
(assert-event (fn-node-statep *osi-live-node*))
(assert-event (in-arena-fn-bpaj-node-record-committed-carriedp *sr-arena* *osi-live-node* *bsb-record*))
(assert-event (in-arena-fn-bpi-node-wire-committedp *sr-arena* *osi-live-node* *bsb-record*))
(assert-event
 (equal (in-arena-fn-bpaj-node-record-committed-carriedp *sr-arena* *osi-live-node* *bsb-record*)
        (in-arena-fn-bpi-node-wire-committedp *sr-arena* *osi-live-node* *bsb-record*)))
; Hypothesis removal (a CORRUPTED node, no host transition builds it): the
; live node with a junk binding after its real ones.  The lookups still find
; the real article and binding, so the carried check answers t; the node
; recognizer fails (the binding list is not a binding list), so the checked
; one answers nil.  Without (fn-node-statep node) the equality is false.
(defconst *osi-bad-node*
  (fn-node-make-state (fn-node-acceptance *osi-live-node*)
                      (fn-node-retention *osi-live-node*)
                      (fn-node-stage *osi-live-node*)
                      (append (fn-node-bindings *osi-live-node*) (list 'junk))))
(assert-event (not (fn-node-statep *osi-bad-node*)))
(assert-event (in-arena-fn-bpaj-node-record-committed-carriedp *sr-arena* *osi-bad-node* *bsb-record*))
(assert-event (not (in-arena-fn-bpi-node-wire-committedp *sr-arena* *osi-bad-node* *bsb-record*)))
(must-fail-checked
 (thm (equal (in-arena-fn-bpaj-node-record-committed-carriedp *sr-arena* *osi-bad-node* *bsb-record*)
             (in-arena-fn-bpi-node-wire-committedp *sr-arena* *osi-bad-node* *bsb-record*))))

; fn-osi-ocl-store-record-accepted-fast-is-checked (books/owner-store-indexed.lisp).
; Positive witness: the configured owner the host holds after the recovery
; barriers; its relation and index hold and the signed record is accepted by
; both checks.
(make-event
 `(defconst *osi-live-oc*
    ',(in-arena-fn-osi-live-owner *sr-arena* *osi-configs* nil *osi-events* *osi-frontier* 4 *osi-barriers*)))
(defconst *osi-live-oc-store* (fn-own-store (fn-ocfg-owner *osi-live-oc*)))
(assert-event (equal *osi-live-oc-store* *osi-store*))
(assert-event (fn-ocl-relation *osi-live-oc*))
(assert-event (fn-ceis-indexedp *osi-live-oc-store*))
(assert-event (in-arena-fn-bpaj-store-record-accepted-fast *sr-arena* *osi-live-oc-store* *bsb-record*))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *sr-arena* *osi-live-oc-store* *bsb-record*))
; Without fn-ocl-relation (CORRUPTED state): the owner whose Store's node is
; the corrupted node above.  The index is untouched (it is derived from the
; history alone), so fn-ceis-indexedp still holds; the relation fails; the
; carried check accepts and the checked one refuses.
(defconst *osi-bad-oc*
  (fn-ocfg-with-owner
   *osi-live-oc*
   (update-nth 0 (update-nth 3 *osi-bad-node* *osi-live-oc-store*)
               (fn-ocfg-owner *osi-live-oc*))))
(defconst *osi-bad-oc-store* (fn-own-store (fn-ocfg-owner *osi-bad-oc*)))
(assert-event (fn-ceis-indexedp *osi-bad-oc-store*))
(assert-event (not (fn-ocl-relation *osi-bad-oc*)))
(assert-event (in-arena-fn-bpaj-store-record-accepted-fast *sr-arena* *osi-bad-oc-store* *bsb-record*))
(assert-event (not (in-arena-fn-bpr-store-record-acceptedp *sr-arena* *osi-bad-oc-store* *bsb-record*)))
(must-fail-checked
 (thm (let ((store (fn-own-store (fn-ocfg-owner *osi-bad-oc*))))
        (implies (fn-ceis-indexedp store)
                 (equal (in-arena-fn-bpaj-store-record-accepted-fast *sr-arena* store *bsb-record*)
                        (in-arena-fn-bpr-store-record-acceptedp *sr-arena* store *bsb-record*))))))
; Without fn-ceis-indexedp (a STALE index, a state no host transition
; reaches): the live owner with the empty index.  The relation does not read
; the derived index, so it still holds; the fast check finds no candidate and
; refuses, the checked one accepts.
(defconst *osi-stale-oc*
  (fn-ocfg-with-owner
   *osi-live-oc*
   (update-nth 0 (update-nth 13 nil *osi-live-oc-store*)
               (fn-ocfg-owner *osi-live-oc*))))
(defconst *osi-stale-oc-store* (fn-own-store (fn-ocfg-owner *osi-stale-oc*)))
(assert-event (fn-ocl-relation *osi-stale-oc*))
(assert-event (not (fn-ceis-indexedp *osi-stale-oc-store*)))
(assert-event (not (in-arena-fn-bpaj-store-record-accepted-fast *sr-arena* *osi-stale-oc-store* *bsb-record*)))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *sr-arena* *osi-stale-oc-store* *bsb-record*))
(must-fail-checked
 (thm (let ((store (fn-own-store (fn-ocfg-owner *osi-stale-oc*))))
        (implies (fn-ocl-relation *osi-stale-oc*)
                 (equal (in-arena-fn-bpaj-store-record-accepted-fast *sr-arena* store *bsb-record*)
                        (in-arena-fn-bpr-store-record-acceptedp *sr-arena* store *bsb-record*))))))
