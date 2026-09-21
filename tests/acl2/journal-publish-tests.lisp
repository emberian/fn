(in-package "ACL2")
(include-book "../../books/journal-publish")
(include-book "std/testing/must-fail" :dir :system)

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

(value-triple :journal-publish-tests-passed)
