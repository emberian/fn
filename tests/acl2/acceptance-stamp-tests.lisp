; The schema migration and owner-observation stamp, with executable teeth.
(in-package "ACL2")
(include-book "store-node-tests")
(include-book "store-identity-traces-tests")
(include-book "../../books/acceptance-stamp-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *ast-observation* (fn-clock-observation 1 841000000000 0 t))
(defconst *ast-no-wall* (fn-clock-observation 1 0 0 nil))
(defconst *ast-built*
  (fn-sn-article-record *sn-reserved* *ast-observation* "<sn@example>"
                        '(65 66) *sn-groups* "sn-pin" "sn-content"
                        "sn-release" 2))

; The owner alone supplies the stamp; a payload, Message-ID or peer date does
; not enter its expression.  This candidate is the one the live Store stages.
(assert-event (fn-record-p *ast-built*))
(assert-event (equal (fn-record-stamp *ast-built*) 841000000))
(assert-event (equal *ast-built* *sn-record*))
(assert-event (equal (fn-sf-phase
                      (fn-sn-files (fn-sn-prepare *sn-reserved* *ast-built*)))
                     :record-staged))
(assert-event (equal (fn-sn-article-record *sn-reserved* *ast-no-wall*
                                           "<sn@example>" '(65 66) *sn-groups*
                                           "sn-pin" "sn-content" "sn-release" 2)
                     :clock-unusable))

; Each constructor theorem fails when its clock hypothesis is dropped.
(must-fail
 (defthm ast-stamp-without-usable-clock-fails
   (equal (fn-record-stamp
           (fn-sn-article-record *sn-reserved* *ast-no-wall*
                                 "<sn@example>" '(65 66) *sn-groups*
                                 "sn-pin" "sn-content" "sn-release" 2))
          (floor (fn-clock-wall *ast-no-wall*) 1000))
   :rule-classes nil))
(must-fail
 (defthm ast-refusal-with-usable-clock-fails
   (equal *ast-built* :clock-unusable)
   :rule-classes nil))

; A legacy record remains a read-side value.  The same reserved transaction
; stages a natural stamp and refuses the old marker before any record write.
(defconst *ast-legacy* (fn-record-with-stamp *ast-built* :legacy))
(assert-event (fn-record-p *ast-legacy*))
(assert-event (equal (fn-sn-prepare *sn-reserved* *ast-legacy*)
                     *sn-reserved*))
; Direct replay of a staged node must not complete a different pending
; article that happens to share the record's transaction coordinates.
(assert-event (null (fn-replay-apply-record (fn-sn-node *sn-prepared*)
                                            *sn-record*)))
(must-fail
 (defthm ast-prepare-refusal-without-legacy-hypothesis-fails
   (equal (fn-sn-prepare *sn-reserved* *ast-built*) *sn-reserved*)
   :rule-classes nil))

; The positive finish witness uses the exact pre-completion record staged by
; the file kernel, and checks the four article-arm exclusions independently.
(assert-event (fn-sn-completion-enabledp *sn-completing*))
(assert-event (not (fn-store-retention-event-p
                    (fn-sn-completion-record *sn-completing*))))
(assert-event (not (fn-stxe-p (fn-sn-completion-record *sn-completing*))))
(assert-event (not (fn-stxk-p (fn-sn-completion-record *sn-completing*))))
(assert-event (not (fn-stxa-p (fn-sn-completion-record *sn-completing*))))
(assert-event (equal (fn-article-stamp
                      (fn-find-article "<sn@example>"
                                       (fn-state-articles
                                        (fn-node-acceptance
                                         (fn-sn-node (fn-sn-finish *sn-completing*))))))
                     (fn-record-stamp (fn-sn-completion-record *sn-completing*))))

; The two exact grammars differ only in the schema octet and final stamp item.
(defconst *ast-schema0* *fn-record-schema0-golden-octets*)
(defconst *ast-schema1* *fn-record-schema1-golden-octets*)
(assert-event (equal (fn-record-decode-exact *ast-schema0*)
                     (list :ok (fn-record-make 1 2 3 "<a>" '(9 8) '("g")
                                                    "o" "s" "e" 4 :legacy))))
(assert-event (equal (fn-record-decode-exact *ast-schema1*)
                     (list :ok (fn-record-make 1 2 3 "<a>" '(9 8) '("g")
                                                    "o" "s" "e" 4 5))))
(assert-event (equal (fn-record-encode
                      (fn-record-result-record
                       (fn-record-decode-exact *ast-schema0*)))
                     *ast-schema0*))
(assert-event (equal (fn-record-encode
                      (fn-record-result-record
                       (fn-record-decode-exact *ast-schema1*)))
                     *ast-schema1*))
(assert-event (equal (nth 5 *ast-schema0*) 0))
(assert-event (equal (nth 5 *ast-schema1*) 1))
(assert-event (equal (fn-record-decode-exact
                      (append (butlast *ast-schema1* 1) '(26 0 0 0 5)))
                     '(:error :noncanonical)))
(must-fail
 (defthm ast-canonicality-without-parser-success-fails
   (equal (fn-record-encode
           (fn-record-result-record
            (fn-record-decode-exact
             (append (butlast *ast-schema1* 1) '(26 0 0 0 5)))))
          (append (butlast *ast-schema1* 1) '(26 0 0 0 5)))
   :rule-classes nil))

; Four durable events in one namespace: old grammar, new grammar, retention,
; and a composite whose fn-r child carries its own schema-1 stamp.
(defconst *ast-journal-groups* '("stamp.test"))
(defconst *ast-journal-r0*
  (fn-record-make 0 0 0 "<legacy@stamp.test>" '(65) *ast-journal-groups*
                  "a0" "s0" "e0" 2 :legacy))
(defconst *ast-journal-r1*
  (fn-record-make 1 1 1 "<new@stamp.test>" '(66) *ast-journal-groups*
                  "a1" "s1" "e1" 2 841000001))
(defconst *ast-journal-retention*
  (fn-store-retention-event-make :undertake 2 2 2 "forward" "fwd-subject"
                                 "fwd-evidence" 2))
(defconst *ast-journal-r3*
  (fn-record-make 3 3 3 "<composite@stamp.test>" '(67) *ast-journal-groups*
                  "a3" "s3" "e3" 2 841000003))
(defconst *ast-journal-verdict*
  (fn-stxe-make 3 3 3 "<composite@stamp.test>" :unverified
                *fn-stx-token-signature* 0 '(112)))
(defconst *ast-journal-composite*
  (fn-stxa-make 3 3 3 0 '(112) (fn-record-string-octets "s3")
                (fn-record-encode-impl *ast-journal-r3*)
                (fn-stxe-encode *ast-journal-verdict*)))
(defconst *ast-mixed-journal*
  (list *ast-journal-r0* *ast-journal-r1*
        *ast-journal-retention* *ast-journal-composite*))
(assert-event (equal (fn-record-decode-exact (fn-record-encode *ast-journal-r0*))
                     (list :ok *ast-journal-r0*)))
(assert-event (fn-stxa-bindsp *ast-journal-composite*))
(assert-event (fn-replay-okp
               (fn-replay *ast-journal-groups* 20 *ast-mixed-journal*)))
(assert-event
 (equal (fn-articles-msgid-stamps
         (fn-state-articles
          (fn-node-acceptance
           (fn-replay-result-node
            (fn-replay *ast-journal-groups* 20 *ast-mixed-journal*)))))
        '(("<legacy@stamp.test>" . :legacy)
          ("<new@stamp.test>" . 841000001)
          ("<composite@stamp.test>" . 841000003))))
(assert-event
 (equal (fn-replay-journal-article-stamps *ast-mixed-journal*)
        '(("<legacy@stamp.test>" . :legacy)
          ("<new@stamp.test>" . 841000001)
          ("<composite@stamp.test>" . 841000003))))

; The one-record subject is nonvacuous for both an old article record and a
; kind-4 composite.  Its minimal hypotheses are the article arm and a real
; step result: successful application itself entails a valid node and event.
(defconst *ast-replay-initial* (fn-node-initial-state *ast-journal-groups* 20))
(assert-event (fn-replay-article-eventp *ast-journal-r0*))
(assert-event (consp (fn-replay-apply-record *ast-replay-initial* *ast-journal-r0*)))
(assert-event
 (consp (fn-find-article
         "<legacy@stamp.test>"
         (fn-state-articles
          (fn-node-acceptance
           (fn-replay-apply-record *ast-replay-initial* *ast-journal-r0*))))))
(defconst *ast-before-composite*
  (list *ast-journal-r0* *ast-journal-r1* *ast-journal-retention*))
(assert-event
 (fn-replay-okp (fn-replay *ast-journal-groups* 20 *ast-before-composite*)))
(assert-event (fn-replay-article-eventp *ast-journal-composite*))
(assert-event
 (consp
  (fn-replay-apply-record
   (fn-replay-result-node
    (fn-replay *ast-journal-groups* 20 *ast-before-composite*))
   *ast-journal-composite*)))
(assert-event
 (equal
  (fn-article-stamp
   (fn-find-article
    "<composite@stamp.test>"
    (fn-state-articles
     (fn-node-acceptance
      (fn-replay-apply-record
       (fn-replay-result-node
        (fn-replay *ast-journal-groups* 20 *ast-before-composite*))
       *ast-journal-composite*)))))
  841000003))

(defconst *ast-refused-article*
  (fn-record-make 0 0 0 "<wrong-group@stamp.test>" '(68) '("not-local")
                  "bad" "bad-subject" "bad-evidence" 2 841000009))
(assert-event (fn-replay-article-eventp *ast-refused-article*))
(assert-event (null (fn-replay-apply-record *ast-replay-initial*
                                           *ast-refused-article*)))
(must-fail
 (defthm ast-one-record-without-successful-step-fails
   (consp (fn-find-article
           "<wrong-group@stamp.test>"
           (fn-state-articles
            (fn-node-acceptance
             (fn-replay-apply-record *ast-replay-initial*
                                     *ast-refused-article*)))))
   :rule-classes nil))
(assert-event
 (consp (fn-replay-apply-record
         (fn-replay-result-node
          (fn-replay *ast-journal-groups* 20
                     (list *ast-journal-r0* *ast-journal-r1*)))
         *ast-journal-retention*)))
(must-fail
 (defthm ast-one-record-without-article-arm-fails
   (consp
    (fn-find-article
     (fn-record-msgid *ast-journal-retention*)
     (fn-state-articles
      (fn-node-acceptance
       (fn-replay-apply-record
        (fn-replay-result-node
         (fn-replay *ast-journal-groups* 20
                    (list *ast-journal-r0* *ast-journal-r1*)))
        *ast-journal-retention*)))))
   :rule-classes nil))

; The success hypothesis matters: a bad sequence at event 2 faults at the
; good prefix, while the independent journal projection still includes event 3.
(defconst *ast-bad-sequence-journal*
  (list *ast-journal-r0* *ast-journal-r1*
        (fn-store-retention-event-make :undertake 9 2 2 "forward"
                                        "fwd-subject" "fwd-evidence" 2)
        *ast-journal-composite*))
(assert-event
 (not (fn-replay-okp (fn-replay *ast-journal-groups* 20
                                *ast-bad-sequence-journal*))))
(must-fail
 (defthm ast-journal-without-success-hypothesis-fails
   (equal (fn-articles-msgid-stamps
           (fn-state-articles
            (fn-node-acceptance
             (fn-replay-result-node
              (fn-replay *ast-journal-groups* 20 *ast-bad-sequence-journal*)))))
          (fn-replay-journal-article-stamps *ast-bad-sequence-journal*))
   :rule-classes nil))

; The composite finish witness reuses a complete, signed Store trace: a
; durable keyring snapshot precedes this article, so the actual identity gate
; admits its kind-4 event.  Stop that trace before completion for the negative.
(make-event
 `(defconst *ast-composite-prepared*
    ',(fn-sn-prepare-identity (fn-sit-reserve *sit-after-enrollment*)
                              *sit-composite*)))
(make-event
 `(defconst *ast-composite-completing*
    ',(fn-sit-publish *ast-composite-prepared*)))
(assert-event (fn-sn-completion-enabledp *ast-composite-completing*))
(assert-event (fn-stxa-p (fn-sn-completion-record *ast-composite-completing*)))
(assert-event
 (consp
  (fn-find-article
   "<signed@example.invalid>"
   (fn-state-articles
    (fn-node-acceptance
     (fn-sn-node (fn-sn-finish *ast-composite-completing*)))))))
(assert-event
 (equal
  (fn-article-stamp
   (fn-find-article
    "<signed@example.invalid>"
    (fn-state-articles
     (fn-node-acceptance
      (fn-sn-node (fn-sn-finish *ast-composite-completing*))))))
  841000000))
(assert-event (not (fn-sn-completion-enabledp *ast-composite-prepared*)))
(must-fail
 (defthm ast-composite-without-enabled-completion-fails
   (consp
    (fn-find-article
     "<signed@example.invalid>"
     (fn-state-articles
      (fn-node-acceptance
       (fn-sn-node (fn-sn-finish *ast-composite-prepared*))))))
   :rule-classes nil))
(assert-event (fn-sn-completion-enabledp *sn-completing*))
(assert-event (not (fn-stxa-p (fn-sn-completion-record *sn-completing*))))
(must-fail
 (defthm ast-composite-without-composite-kind-fails
   (consp
    (fn-find-article
     (fn-record-msgid
      (fn-replay-composite-record (fn-sn-completion-record *sn-completing*)))
     (fn-state-articles
      (fn-node-acceptance (fn-sn-node (fn-sn-finish *sn-completing*))))))
   :rule-classes nil))
