; Teeth for books/committer-actor.lisp (PRF-1255), TEETH CONTRACT v1, over the
; reached schedule the book asserts: init -> observe (snapshot issued) ->
; snapshot 1 captured (passing).  Not here (no counterexample to a
; hypothesis, so a removal waits on a proof of the weakened theorem):
;  fn-cmt-stop-observation-never-enters-a-pipeline -- its :observe hypothesis
;    (only an :observe enters a pipeline: fn-cmt-pipeline-requires-its-captured-passes);
;  fn-cmt-wrong-snapshot-ticket-faults -- its :snapshot-state and
;    :snapshot-event hypotheses (every unexpected event faults in every state).
(in-package "ACL2")
(include-book "../../books/committer-actor")
(include-book "../../books/defkeystone")

(defconst *cmtt-issued* (car (fn-cmt-step (fn-cmt-init) '(:observe nil 1 nil))))
(defconst *cmtt-captured* (car (fn-cmt-step *cmtt-issued* '(:snapshot 1 ((0 2))))))
(assert-event (and (equal *cmtt-issued* '(:snapshot 1 nil nil))
                   (equal *cmtt-captured* '(:passing 1 ((0 2)) nil))))

(defteeth fn-cmt-step-state-is-valid
  :claim (() (fn-cmt-invp (car (fn-cmt-step s event))))
  :subject fn-cmt-step
  :witness ((s *cmtt-issued*) (event '(:snapshot 1 ((0 2)))))
  :mutations ((step-keeps-state
               (:conclusion (equal (car (fn-cmt-step s event)) s))
               ((s *cmtt-issued*) (event '(:snapshot 1 ((0 2)))))
               :fault "a captured snapshot that leaves the actor where it was")))

(defteeth fn-cmt-pipeline-requires-its-captured-passes
  :claim (((pipeline (equal (car (cadr (fn-cmt-step s event))) :pipeline)))
          (and (equal (fn-cmt-field 0 s) :passing)
               (equal (fn-cmt-field 0 event) :observe)
               (not (fn-cmt-field 1 event)) (fn-cmt-field 3 event)
               (equal (fn-cmt-field 1 (cadr (fn-cmt-step s event)))
                      (nfix (fn-cmt-field 1 s)))
               (equal (fn-cmt-field 2 (cadr (fn-cmt-step s event)))
                      (fn-cmt-field 2 s))))
  :subject fn-cmt-step
  :witness ((s *cmtt-captured*) (event '(:observe nil 1 t)))
  :breaks ((pipeline ((s *cmtt-captured*) (event '(:observe nil 1 nil)))))
  :mutations ((next-ticket
               (:conclusion (and (equal (fn-cmt-field 0 s) :passing)
                                 (equal (fn-cmt-field 0 event) :observe)
                                 (not (fn-cmt-field 1 event)) (fn-cmt-field 3 event)
                                 (equal (fn-cmt-field 1 (cadr (fn-cmt-step s event)))
                                        (+ 1 (nfix (fn-cmt-field 1 s))))
                                 (equal (fn-cmt-field 2 (cadr (fn-cmt-step s event)))
                                        (fn-cmt-field 2 s))))
               ((s *cmtt-captured*) (event '(:observe nil 1 t)))
               :fault "the pipeline names the next ticket rather than the captured one")))
