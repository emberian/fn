(in-package "ACL2")
(include-book "../../books/journal-publish")
(include-book "../../books/app-journal")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

(defconst *fn-t-jpub-link-window*
  (fn-jpub-step
   (fn-jpub-step
    (fn-jpub-step (fn-jpub-initial t) '(:stage-result :ok))
    '(:file-barrier-result :ok))
   '(:link-begin)))

(assert-event (equal (fn-jpub-phase *fn-t-jpub-link-window*) :link-attempted))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-link-window* '(:link-result :error)))
        :uncertain))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-link-window* '(:link-result :exists)))
        :refused))

(defconst *fn-t-jpub-dir-window*
  (fn-jpub-step *fn-t-jpub-link-window* '(:link-result :ok)))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-dir-window*
                       '(:directory-barrier-result :error)))
        :uncertain))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step *fn-t-jpub-dir-window*
                       '(:directory-barrier-result :ok)))
        :durable))

; Teeth: without established authority an apparent EEXIST is never a known
; refusal, and without the directory barrier the conclusion is not durable.
(must-fail
 (assert-event
  (equal (fn-jpub-outcome
          (fn-jpub-step (fn-jpub-state :link-attempted nil nil)
                        '(:link-result :exists)))
         :refused)))
(must-fail
 (assert-event (equal (fn-jpub-crash-outcome *fn-t-jpub-dir-window*) :durable)))

; The application frontier owns the filename and the admission/capacity
; decision.  Recovery accepts only ACL2's exact next name, and a resolution
; reservation accounts for both the intent and its maximum-sized outcome.
(defconst *fn-t-aj-empty* (fn-aj-initial :workflow))
(defconst *fn-t-aj-config-op*
  (fn-aj-authorize *fn-t-aj-empty* :config 100 nil t t))
(assert-event (fn-aj-operationp *fn-t-aj-config-op*))
(assert-event
 (equal (fn-aj-operation-name *fn-t-aj-config-op*)
        "00000000000000000000.wf"))
(assert-event
 (equal (fn-aj-operation-label *fn-t-aj-config-op*) :config))
(assert-event
 (equal (fn-aj-next (fn-aj-operation-successor *fn-t-aj-config-op*)) 1))
(assert-event
 (equal (fn-aj-recover-record *fn-t-aj-empty*
                              "00000000000000000000.wf" 100 :config)
        (fn-aj-operation-successor *fn-t-aj-config-op*)))
(must-fail
 (assert-event
  (not (equal (fn-aj-recover-record *fn-t-aj-empty*
                                    "00000000000000000001.wf" 100 :config)
              :fault))))
(must-fail
 (assert-event
  (equal (car (fn-aj-authorize *fn-t-aj-empty* :config 100 nil nil t))
         :ok)))
(must-fail
 (assert-event
  (equal (car (fn-aj-authorize
               (fn-aj-state :workflow 4095 0 t)
               :outcome 100 t t t))
         :ok)))

(value-triple :journal-publish-tests-passed)
