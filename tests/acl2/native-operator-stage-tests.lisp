; Teeth for books/native-operator-stage.lisp (PKT-781 (1), PRF-971).
(in-package "ACL2")
(include-book "../../books/native-operator-stage")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun fn-nsst-test-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words))
            (fn-nsst-test-argv (cdr words)))
    nil))

(defun fn-nsst-test-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10)
              (fn-nsst-test-lines (cdr lines)))
    nil))

(defconst *fn-nsst-config*
  (fn-nsst-test-lines '("[store]" "path = \"/srv/fn\"")))
(defconst *fn-nsst-recover*
  (fn-native-operator-run *fn-nsst-config* (fn-nsst-test-argv '("recover"))))
(defconst *fn-nsst-run*
  (fn-native-operator-run *fn-nsst-config* (fn-nsst-test-argv '("run" "--once"))))
(defconst *fn-nsst-help*
  (fn-native-operator-run *fn-nsst-config* (fn-nsst-test-argv '("help"))))
(defconst *fn-nsst-init-stage* "/srv/fn.init-77b60431a1de")
(defconst *fn-nsst-import-stage* "/srv/fn.import-0a1b2c3d4e5f")
(defconst *fn-nsst-config-json* (list (fn-record-string-octets "config.json")))

; Reachable positive witness (keystone fn-nsst-absent-store-beside-an-init-
; stage-names-it): the host-shaped `recover' and `run' plans, no store entry
; beside /srv/fn (observed nil), the stage init leaves.  Antecedent, then
; every conjunct of the conclusion.
(assert-event (fn-native-operator-result-needs-storep *fn-nsst-recover*))
(assert-event (fn-native-operator-result-needs-storep *fn-nsst-run*))
(assert-event (stringp *fn-nsst-init-stage*))
(defconst *fn-nsst-recover-staged*
  (fn-nsst-store-outcome *fn-nsst-recover* nil *fn-nsst-init-stage* nil))
(assert-event (equal (fn-native-operator-result-status *fn-nsst-recover-staged*) :refused))
(assert-event (equal (fn-native-operator-result-reason *fn-nsst-recover-staged*)
                     :interrupted-init))
(assert-event (equal (fn-native-operator-result-arguments *fn-nsst-recover-staged*)
                     (list *fn-nsst-init-stage*)))
(assert-event (equal (fn-native-operator-exit-code *fn-nsst-recover-staged*) 1))
(assert-event (equal (fn-native-operator-result-native-action *fn-nsst-recover-staged*)
                     :none))
(assert-event (equal (fn-nsst-result-hint *fn-nsst-recover-staged*)
                     "no store at the configured [store] path: an init was interrupted before it published the store; its stage /srv/fn.init-77b60431a1de remains. Remove it and run: fn operator CONFIG init GROUP..."))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-nsst-store-outcome *fn-nsst-run* nil *fn-nsst-init-stage* nil))
                     :interrupted-init))
; An init stage wins over an import stage (init's is the operator's).
(assert-event (equal (fn-native-operator-result-reason
                      (fn-nsst-store-outcome *fn-nsst-run* nil *fn-nsst-init-stage*
                                             *fn-nsst-import-stage*))
                     :interrupted-init))

; Hypothesis 1 removed (a plan that needs no store: help).  Retained: nothing
; observed, a stage.  The plan passes, accepted, exit 0.
(assert-event (not (fn-native-operator-result-needs-storep *fn-nsst-help*)))
(assert-event (equal (fn-nsst-store-outcome *fn-nsst-help* nil *fn-nsst-init-stage* nil)
                     *fn-nsst-help*))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-nsst-store-outcome *fn-nsst-help* nil *fn-nsst-init-stage* nil))
                     0))
(must-fail-checked
 (thm (implies (and (not (consp observed)) (stringp init-stage))
               (equal (fn-native-operator-result-reason
                       (fn-nsst-store-outcome result observed init-stage import-stage))
                      :interrupted-init))))

; Hypothesis 2 removed (a store entry is there: config.json, a partial or
; whole store).  Retained: a store plan, a stage.  The plan proceeds to the
; open unchanged, exit 0.
(assert-event (consp *fn-nsst-config-json*))
(assert-event (equal (fn-nsst-store-outcome *fn-nsst-recover* *fn-nsst-config-json*
                                            *fn-nsst-init-stage* nil)
                     *fn-nsst-recover*))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-nsst-store-outcome *fn-nsst-recover* *fn-nsst-config-json*
                                             *fn-nsst-init-stage* nil))
                     0))
(must-fail-checked
 (thm (implies (and (fn-native-operator-result-needs-storep result)
                    (stringp init-stage))
               (equal (fn-native-operator-result-reason
                       (fn-nsst-store-outcome result observed init-stage import-stage))
                      :interrupted-init))))

; Hypothesis 3 removed (no stage).  Retained: a store plan, nothing observed.
; The answer is PRF-130's NO-STORE, a refusal (exit 1) whose reason is not
; :interrupted-init and whose hint is NO-STORE's "run init".
(defconst *fn-nsst-recover-bare*
  (fn-nsst-store-outcome *fn-nsst-recover* nil nil nil))
(assert-event (equal (fn-native-operator-result-reason *fn-nsst-recover-bare*) :no-store))
(assert-event (equal (fn-native-operator-exit-code *fn-nsst-recover-bare*) 1))
(assert-event (equal *fn-nsst-recover-bare*
                     (fn-native-operator-store-outcome *fn-nsst-recover* nil)))
(assert-event (equal (fn-nsst-result-hint *fn-nsst-recover-bare*)
                     (fn-native-operator-result-hint *fn-nsst-recover-bare*)))
(must-fail-checked
 (thm (implies (and (fn-native-operator-result-needs-storep result)
                    (not (consp observed)))
               (equal (fn-native-operator-result-reason
                       (fn-nsst-store-outcome result observed init-stage import-stage))
                      :interrupted-init))))

; The import stage alone (keystone fn-nsst-absent-store-beside-an-import-
; stage-names-it): refused :interrupted-import, the stage its argument.
(defconst *fn-nsst-recover-imported*
  (fn-nsst-store-outcome *fn-nsst-recover* nil nil *fn-nsst-import-stage*))
(assert-event (equal (fn-native-operator-result-status *fn-nsst-recover-imported*) :refused))
(assert-event (equal (fn-native-operator-result-reason *fn-nsst-recover-imported*)
                     :interrupted-import))
(assert-event (equal (fn-native-operator-result-arguments *fn-nsst-recover-imported*)
                     (list *fn-nsst-import-stage*)))
(assert-event (equal (fn-native-operator-exit-code *fn-nsst-recover-imported*) 1))
(assert-event (equal (fn-native-operator-result-native-action *fn-nsst-recover-imported*)
                     :none))
(assert-event (equal (fn-nsst-result-hint *fn-nsst-recover-imported*)
                     "no store at the configured [store] path: an import was interrupted before it published the store; its stage /srv/fn.import-0a1b2c3d4e5f remains. Remove it and run the import again"))
