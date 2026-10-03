; Teeth for books/history-knowledge.lisp (W8, lane reclaim-equivalence,
; 2026-09-29; PRF-997 to PRF-1000).  Every witness asserts the complete
; antecedent and conclusion of the theorem it bites, on a reachable
; fixture: the store-reclaim-pack fixture's history (three articles under a
; releasing rule, tests/acl2/store-reclaim-pack-tests.lisp), the file
; kernel's staged record (tests/acl2/store-node-tests.lisp) and the node
; machine's committed article (tests/acl2/node-tests.lisp).
(in-package "ACL2")
(include-book "store-reclaim-pack-tests")
(include-book "store-node-tests")
(include-book "node-tests")
(include-book "must-fail-checked")
(include-book "../../books/history-knowledge")

; -----------------------------------------------------------------------------
; 1. Knowledge (fn-hkn-reclamation-never-forgets-an-acceptance).

(defconst *hk-absent* "<absent@example.invalid>")
; The fixture's events are encoded by a :program helper (the record codec is
; not executable under defconst's safe mode): the knowledge is computed
; inside each assert-event.
(defmacro hk-before () '(fn-hkn-knowledge t (rpt-events) nil *rpt-msgid*))
(defmacro hk-after () '(fn-hkn-knowledge t (rpt-new) nil *rpt-msgid*))

; REACHABLE, positive: the fixture's article is retained in the history and
; reclaimed in the rewritten one; the keystone's five conjuncts hold of it.
(assert-event (equal (hk-before) :accepted-retained))
(assert-event (equal (hk-after) :accepted-reclaimed))
(assert-event (and (equal (equal (hk-after) :not-accepted) (equal (hk-before) :not-accepted))
                   (equal (equal (hk-after) :outcome-unresolved)
                          (equal (hk-before) :outcome-unresolved))
                   (equal (equal (hk-after) :history-unavailable)
                          (equal (hk-before) :history-unavailable))
                   (implies (equal (hk-before) :accepted-reclaimed)
                            (equal (hk-after) :accepted-reclaimed))
                   (implies (equal (hk-before) :accepted-retained)
                            (member-eq (hk-after) '(:accepted-retained :accepted-reclaimed)))))
; A second reclaim under the same context leaves the reclaimed answer.
(assert-event (equal (fn-hkn-knowledge t (fn-rclp-events (rpt-new) *rpt-ctx*) nil *rpt-msgid*)
                     :accepted-reclaimed))
; The other three states, before and after: an identity the history never
; held is :not-accepted in both, :outcome-unresolved in both when it is the
; staged proposal, :history-unavailable when the history cannot be read.
(assert-event (and (equal (fn-hkn-knowledge t (rpt-events) nil *hk-absent*) :not-accepted)
                   (equal (fn-hkn-knowledge t (rpt-new) nil *hk-absent*) :not-accepted)
                   (equal (fn-hkn-knowledge t (rpt-events) *hk-absent* *hk-absent*)
                          :outcome-unresolved)
                   (equal (fn-hkn-knowledge t (rpt-new) *hk-absent* *hk-absent*)
                          :outcome-unresolved)
                   (equal (fn-hkn-knowledge nil (rpt-events) nil *rpt-msgid*)
                          :history-unavailable)
                   (equal (fn-hkn-knowledge nil (rpt-new) nil *rpt-msgid*)
                          :history-unavailable)))
; A staged proposal that IS in the readable history is resolved by it.
(assert-event (equal (fn-hkn-knowledge t (rpt-events) *rpt-msgid* *rpt-msgid*)
                     :accepted-retained))
; The five states are all the knowledge answers.
(assert-event (equal (len *fn-hkn-states*) 5))

; -----------------------------------------------------------------------------
; 2. Acknowledgement identifies commitment
; (fn-hkn-acceptance-records-subject-principal-and-undertaking,
;  fn-hkn-replay-binds-the-recorded-evidence-not-the-policy).

; REACHABLE, positive: the file kernel's staged row (the record the live
; Store stages, tests/acl2/store-node-tests.lisp *sn-row*) replayed into
; the initial node accepts and records exactly the record's subject,
; evidence and charge.
(defconst *hk-node0* (fn-sn-node *sn-initial*))
(defconst *hk-n* (fn-replay-apply-record *hk-node0* *sn-row*))
(assert-event (fn-hkn-plain-article-record-p *sn-row*))
(assert-event (consp *hk-n*))
(assert-event (equal (fn-node-find-binding (fn-record-msgid *sn-row*) (fn-node-bindings *hk-n*))
                     (fn-node-make-binding (fn-record-msgid *sn-row*)
                                           (fn-record-content-subject *sn-row*)
                                           (fn-record-obligation-id *sn-row*))))
(assert-event (equal (fn-retain-find-id (fn-record-obligation-id *sn-row*)
                                        (fn-retain-pins (fn-node-retention *hk-n*)))
                     (fn-retain-make-obligation (fn-record-obligation-id *sn-row*)
                                                (fn-record-content-subject *sn-row*)
                                                :archive
                                                (fn-record-release-evidence *sn-row*)
                                                (fn-record-charge *sn-row*))))
(assert-event (null (fn-node-stage *hk-n*)))
(assert-event (equal (fn-retain-obligation-evidence
                      (fn-retain-find-id (fn-record-obligation-id *sn-row*)
                                         (fn-retain-pins (fn-node-retention *hk-n*))))
                     (fn-record-release-evidence *sn-row*)))
; The subject is the content subject, not the Message-ID nor the payload.
(assert-event (and (equal (fn-record-content-subject *sn-row*) "sn-content")
                   (not (equal (fn-record-content-subject *sn-row*) (fn-record-msgid *sn-row*)))))
; Provenance: the same record replayed under a different policy (other
; groups, other capacity) is bound with the same evidence.  The constant is
; ground and this policy binds it (sweep 2026-10-03 S137: the disjunct that
; also accepted a refusal could not fail).
(defconst *hk-n-other* (fn-replay-apply-record (fn-sn-node (fn-sn-initial *sn-groups* 3)) *sn-row*))
(assert-event (and *hk-n-other*
                  (equal (fn-retain-obligation-evidence
                          (fn-retain-find-id (fn-record-obligation-id *sn-row*)
                                             (fn-retain-pins (fn-node-retention *hk-n-other*))))
                         (fn-record-release-evidence *sn-row*))))
; Hypothesis removal: a retention :undertake event replayed into the initial
; node is ACCEPTED (n non-nil: the retained hypothesis holds), is not a
; plain article record (the omitted hypothesis fails), and binds no
; Message-ID (the conclusion fails): the hypothesis is not redundant.
(defconst *hk-ev* (fn-store-retention-event-make :undertake 0 0 9 "fwd-1" "subject-1" "release-1" 1))
(defconst *hk-en* (fn-replay-apply-record *hk-node0* *hk-ev*))
(assert-event (fn-store-retention-event-p *hk-ev*))
(assert-event (consp *hk-en*))
(assert-event (not (fn-hkn-plain-article-record-p *hk-ev*)))
(assert-event (equal (fn-retain-pins (fn-node-retention *hk-en*))
                     (list (fn-retain-make-obligation "fwd-1" "subject-1" :forward "release-1" 1))))
(assert-event (with-guard-checking
               :none
               (not (equal (fn-node-find-binding (fn-record-msgid *hk-ev*) (fn-node-bindings *hk-en*))
                           (fn-node-make-binding (fn-record-msgid *hk-ev*)
                                                 (fn-record-content-subject *hk-ev*)
                                                 (fn-record-obligation-id *hk-ev*))))))
(must-fail-checked
 (defthm hk-acceptance-without-the-plain-record-hypothesis-fails
   (let ((n (fn-replay-apply-record node record)))
     (implies n
              (equal (fn-node-find-binding (fn-record-msgid record) (fn-node-bindings n))
                     (fn-node-make-binding (fn-record-msgid record)
                                           (fn-record-content-subject record)
                                           (fn-record-obligation-id record)))))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; 3. The logical release and the continuation language.

(defconst *hk-msgid* "<a@example.invalid>")
(defconst *hk-rel* (fn-hkn-release *node-committed* *hk-msgid* 1))
(assert-event (fn-node-statep *node-committed*))
(assert-event (equal (fn-retain-reserved (fn-node-retention *node-committed*)) 5))
(assert-event (equal (fn-retain-capacity (fn-node-retention *node-committed*)) 8))
; The release: the stage and the bindings untouched, the payload at the
; tombstone handle, the reserved sum at the history unit
; (fn-hkn-release-frees-exactly-the-content-charge).
(assert-event (equal (fn-node-bindings *hk-rel*) (fn-node-bindings *node-committed*)))
(assert-event (equal (fn-node-stage *hk-rel*) (fn-node-stage *node-committed*)))
(assert-event (equal (fn-article-payload
                      (fn-find-article *hk-msgid* (fn-state-articles (fn-node-acceptance *hk-rel*))))
                     1))
(assert-event (equal (fn-retain-reserved (fn-node-retention *hk-rel*)) 1))
(assert-event (equal (fn-retain-capacity (fn-node-retention *hk-rel*)) 8))
(assert-event (equal (fn-retain-obligation-charge
                      (fn-retain-find-id "archive-a" (fn-retain-pins (fn-node-retention *hk-rel*))))
                     1))

; Continuation: a CONFLICTING retry of the released identity (another
; payload, other groups, other ids) is refused after as before
; (fn-hkn-retry-refused-after-release-as-before); the antecedent holds.
(assert-event (fn-acceptedp *hk-msgid* (fn-state-articles (fn-node-acceptance *node-committed*))))
(assert-event (equal (fn-node-prepare *hk-rel* 9 *hk-msgid* 7 '("fn.test")
                                      "archive-c" "content-c" "release-c" 1 841000000)
                     *hk-rel*))
(assert-event (equal (fn-node-prepare *node-committed* 9 *hk-msgid* 7 '("fn.test")
                                      "archive-c" "content-c" "release-c" 1 841000000)
                     *node-committed*))

; Continuation: a receipt / release naming the obligation discharges the same
; obligation after as before, and a receipt with other evidence discharges
; none in both (fn-hkn-release-discharges-the-same-obligation).
(defconst *hk-r0* (fn-node-retention *node-committed*))
(defconst *hk-r1* (fn-node-retention *hk-rel*))
(assert-event (fn-retain-obligation-listp (fn-retain-pins *hk-r0*)))
(assert-event (and (fn-retain-matching-releasep (fn-retain-find-id "archive-a" (fn-retain-pins *hk-r1*))
                                                "archive-a" "content-a" :archive "release-a")
                   (fn-retain-matching-releasep (fn-retain-find-id "archive-a" (fn-retain-pins *hk-r0*))
                                                "archive-a" "content-a" :archive "release-a")
                   (not (fn-retain-matching-releasep
                         (fn-retain-find-id "archive-a" (fn-retain-pins *hk-r1*))
                         "archive-a" "content-a" :archive "release-x"))
                   (not (fn-retain-matching-releasep
                         (fn-retain-find-id "archive-a" (fn-retain-pins *hk-r0*))
                         "archive-a" "content-a" :archive "release-x"))))
(assert-event (equal (fn-retain-pins (fn-retain-release *hk-r1* "archive-a" "content-a" :archive "release-a"))
                     nil))
(assert-event (equal (fn-retain-release *hk-r1* "archive-a" "content-a" :archive "release-x") *hk-r1*))
; Continuation: every obligation id known after as before.
(assert-event (and (fn-retain-known-idp "archive-a" (fn-retain-pins *hk-r1*) (fn-retain-releases *hk-r1*))
                   (fn-retain-known-idp "archive-a" (fn-retain-pins *hk-r0*) (fn-retain-releases *hk-r0*))
                   (not (fn-retain-known-idp "archive-z" (fn-retain-pins *hk-r1*) (fn-retain-releases *hk-r1*)))
                   (not (fn-retain-known-idp "archive-z" (fn-retain-pins *hk-r0*) (fn-retain-releases *hk-r0*)))))

; fn-hkn-release-discharges-the-same-obligation carries no hypothesis: over
; a list that is not an obligation list the release acts only on a found
; cons pin, whose reduction keeps every identifying field.
(defconst *hk-bad* (fn-retain-make-state 8 0 '(5) nil))
(assert-event (with-guard-checking
               :none
               (equal (fn-retain-matching-releasep
                       (fn-retain-find-id nil (fn-retain-pins (fn-hkn-release-retention *hk-bad* nil)))
                       nil nil nil nil)
                      (fn-retain-matching-releasep
                       (fn-retain-find-id nil (fn-retain-pins *hk-bad*))
                       nil nil nil nil))))

; THE ONE OBSERVABLE CHANGE (fn-hkn-release-enables-only-what-the-freed-
; charge-affords), and the FINDING the review asked for: the naive
; equivalence "every continuation observes the same after the release" is
; FALSE.  A POST of charge 4 is refused by the committed node (5 + 4 > 8)
; and admitted by the released one (1 + 4 <= 8); it was refused for
; capacity alone, and it fits the freed charge.
(defconst *hk-post-before*
  (fn-node-prepare *node-committed* 9 "<b@example.invalid>" 0 '("fn.letters")
                   "archive-b" "content-b" "release-b" 4 841000000))
(defconst *hk-post-after*
  (fn-node-prepare *hk-rel* 9 "<b@example.invalid>" 0 '("fn.letters")
                   "archive-b" "content-b" "release-b" 4 841000000))
(assert-event (equal *hk-post-before* *node-committed*))
(assert-event (and (not (equal *hk-post-after* *hk-rel*))
                   (consp (fn-node-stage *hk-post-after*))))
(assert-event (and (fn-retain-statep *hk-r0*)
                   (not (fn-retain-admissiblep *hk-r0* "archive-b" "content-b" :archive "release-b" 4))
                   (fn-retain-admissiblep (fn-hkn-release-retention *hk-r0* "archive-a")
                                          "archive-b" "content-b" :archive "release-b" 4)
                   ; the conclusion: refused for capacity alone, fits the freed charge
                   (stringp "archive-b") (stringp "content-b") (fn-retain-kindp :archive)
                   (fn-provp "release-b") (posp 4)
                   (not (fn-retain-known-idp "archive-b" (fn-retain-pins *hk-r0*)
                                             (fn-retain-releases *hk-r0*)))
                   (< (fn-retain-capacity *hk-r0*) (+ (fn-retain-reserved *hk-r0*) 4))
                   (<= (+ (fn-retain-reserved (fn-hkn-release-retention *hk-r0* "archive-a")) 4)
                       (fn-retain-capacity *hk-r0*))))
; MUST-FAIL (the finding): the naive continuation equivalence for a POST.
(must-fail-checked
 (defthm hk-naive-continuation-equivalence-is-false
   (equal (equal (fn-node-prepare (fn-hkn-release node m tomb)
                                  generation msgid payload groups id subject evidence charge stamp)
                 (fn-hkn-release node m tomb))
          (equal (fn-node-prepare node generation msgid payload groups id subject evidence charge stamp)
                 node))
   :rule-classes nil))
; A POST of charge 1 is admitted in both: it never depended on the release.
(assert-event (and (consp (fn-node-stage
                           (fn-node-prepare *node-committed* 9 "<c@example.invalid>" 0 '("fn.letters")
                                            "archive-c" "content-c" "release-c" 1 841000000)))
                   (consp (fn-node-stage
                           (fn-node-prepare *hk-rel* 9 "<c@example.invalid>" 0 '("fn.letters")
                                            "archive-c" "content-c" "release-c" 1 841000000)))))

; -----------------------------------------------------------------------------
; 4. Refusal footprints.

; The capacity refusal above is the identity and the admitted POST has a
; stage: asserted exactly above (*hk-post-before*, *hk-post-after*); the two
; disjunctions that restated them could not fail while those hold (sweep
; 2026-10-03 S137) and are gone.
; An unmatched completion is the identity.
(assert-event (not (fn-node-pending-matchesp *node-committed* 5 9)))
(assert-event (equal (fn-node-complete *node-committed* 5 9 :durable) *node-committed*))
; An unmatched release is the identity (the "release-x" receipt above).
(assert-event (equal (fn-retain-release *hk-r0* "archive-a" "content-a" :archive "release-x") *hk-r0*))
; The refused path keeps the recovery barriers: the reserved kernel refused
; at its own reservation (tests/acl2/store-node-tests.lisp *sn-reserved*).
(defconst *hk-files* (fn-sn-files *sn-reserved*))
(assert-event (equal (fn-sf-barriers (fn-sf-refuse-reservation *hk-files* (1- (fn-sf-frontier *hk-files*))))
                     (fn-sf-barriers *hk-files*)))
(assert-event (equal (fn-sf-phase (fn-sf-refuse-reservation *hk-files* (1- (fn-sf-frontier *hk-files*))))
                     :ready))
(assert-event (equal (fn-sf-barriers (fn-sf-start-frontier (fn-sn-files *sn-initial*)))
                     (fn-sf-barriers (fn-sn-files *sn-initial*))))
