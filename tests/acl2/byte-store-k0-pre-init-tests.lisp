; Witnesses and teeth for books/byte-store-k0-pre-init.lisp (lane
; k0-recovery): the pre-init relation, its crash meaning, and its
; preservation by the initializer's steps, :mkdir and :link-eexist included.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-pre-init")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bski-record* '(1 2 3 4))
(defun bski-step-bs (bs step outcome)
  (mv-let (r b k) (fn-bs-step bs (fn-sf-initial-state) step outcome nil nil)
    (declare (ignore r k))
    b))
(defun bski-prefix-run (outcomes)
  (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
             (fn-bs-k0i-current-init-prefix *fn-bs-sample-config* *bski-record* ".c" ".h")
             outcomes nil nil))
(defun bski-last () (car (car (last (bski-prefix-run nil)))))
; Witness: the fresh prefix runs to its end (every step answered :ok), every
; pair is pre-init, the last state has config.json durable in :root and
; still-pending staging entries, and its crash images scan as no store.
(assert-event (equal (len (bski-prefix-run nil))
                     (len (fn-bs-k0i-current-init-prefix *fn-bs-sample-config* *bski-record* ".c" ".h"))))
(assert-event (fn-bs-k0i-run-pre-init-p (bski-prefix-run nil)))
(assert-event (natp (fn-bs-durable-entry (bski-last) :root *fn-bs-config-name*)))
(assert-event (consp (fn-bs-pending (bski-last))))
(assert-event (not (fn-bs-lookup (fn-bs-crash (bski-last) nil) :root *fn-bs-frontier-name*)))
; An error outcome ends the run early; the pairs are still pre-init.
(assert-event (fn-bs-k0i-run-pre-init-p (bski-prefix-run '(:ok :ok :ok :ok (:eio . 0)))))
; :mkdir with an error, and :link-eexist, as single steps.
(assert-event (fn-bs-k0i-pre-init-relation
               (bski-step-bs (bski-last) '(:mkdir :root "x" :x) :eio)
               (fn-sf-initial-state)))
(defun bski-existing-run ()
  (fn-bs-run (bski-last) (fn-sf-initial-state)
             (fn-bsi-publish-existing-steps "r-" ".c2" :root *fn-bs-config-name* *fn-bs-sample-config*)
             nil nil nil))
(assert-event (equal (len (bski-existing-run)) 10))
(assert-event (fn-bs-k0i-run-pre-init-p (bski-existing-run)))
; Tooth: the step precondition.  Linking a fenced stage onto the frontier
; name leaves a pending frontier entry; the state is no longer pre-init.
(defun bski-stage ()
  (let* ((s1 (bski-step-bs (bski-last) '(:create :staging ".f") :ok))
         (s2 (bski-step-bs s1 (list :write-all :staging ".f" *fn-bs-sample-frontier*) :ok)))
    (bski-step-bs s2 '(:fsync-file :staging ".f") :ok)))
(assert-event (fn-bs-k0i-pre-init-relation (bski-stage) (fn-sf-initial-state)))
(assert-event (not (fn-bs-k0i-step-inputp (list :link :staging ".f" :root *fn-bs-frontier-name*))))
(must-fail
 (assert-event (fn-bs-k0i-pre-init-relation
                (bski-step-bs (bski-stage) (list :link :staging ".f" :root *fn-bs-frontier-name*) :ok)
                (fn-sf-initial-state))))
; Tooth: the relation.  An initialised store is not pre-init, and a step
; the precondition admits does not make it so.
(must-fail
 (assert-event (fn-bs-k0i-pre-init-relation
                (bski-step-bs *fn-bs-initialized-store* '(:cut "x") :ok)
                (fn-sf-initial-state))))
