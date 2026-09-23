; The schema migration and owner-observation stamp, with executable teeth.
(in-package "ACL2")
(include-book "store-node-tests")
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
