; New continuation entries keep old HELD source APIs strict. The actor's
; actual consumed ADOPTED terminal authorizes only these final cleanup calls.
(in-package "ACL2")
(include-book "checkpoint-live-adoption")
(include-book "checkpoint-master-rearm")
(include-book "event-rearm")
(fn2-book-layer :c)
(defconst *fn2-live-adoption-post-children*
 (append *fn2-live-adoption-children*
  '(fn2-journal-members fn2-checkpoint-lifecycle fn2-mk fn2-checkpoint-writer fn2-machines)))
(defun fn2-live-adoption-post-tables ()
 (declare (xargs :verify-guards nil))
 (subst 'fn2-checkpoint-writer-table 'fn2-core-checkpoint-writer
        (fn2-checkpoint-root1-child-tables *fn2-live-adoption-post-children*)))
(defmacro fn2-live-adoption-post-operation (name args outputs &rest body)
 (let* ((children *fn2-live-adoption-post-children*)
        (proof (and (consp outputs) (fn2-columns-sym (car outputs) "-PRESERVES"))))
  `(progn
    (defun ,name (,@args ,@children)
     (declare (xargs :stobjs ,children :guard (and ,@(fn2-run-load-frame-hyps children))))
     ,@body)
    ,@(and proof
      `((,proof ,name (,@args ,@children)
         :hyps ,(fn2-run-load-frame-hyps children)
         :specs ,(fn2-checkpoint-root1-child-specs outputs 1)))))))
; The writer machine type/requester relation materialize before this family.
(defmacro fn2-checkpoint-live-adoption-rearm-events ()
 '(progn
  (fn2-live-adoption-post-operation fn2-checkpoint-live-adoption-release-complete (token kind owner generation) ()
   (if (not (fn2-live-adoption-consumed)) :source
    (fn2-checkpoint-master-release-complete-children-at-phase *fn2-csnapshot-phase-adopted*
     token kind owner generation fn2-checkpoint-root1 fn2-checkpoint-plan fn2-checkpoint-build fn2-csnapshot
     fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-publication fn2-extents)))
  (fn2-live-adoption-post-operation fn2-checkpoint-live-adoption-events-rearm ()
   (fn2-event-build fn2-event-read fn2-journal-members)
   (if (not (fn2-live-adoption-consumed)) (mv :source fn2-event-build fn2-event-read fn2-journal-members)
    (fn2-event-producer-rearm-at-phase *fn2-csnapshot-phase-adopted* fn2-event-build fn2-event-read fn2-journal-members
     fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-publication fn2-checkpoint-lifecycle fn2-extents
     fn2-mk fn2-fc fn2-digests fn2-checkpoint-writer fn2-machines)))
  (fn2-live-adoption-post-operation fn2-checkpoint-live-adoption-rearm (token kind owner generation)
   (fn2-checkpoint-build fn2-checkpoint-plan fn2-checkpoint-map-build)
   (if (not (fn2-live-adoption-consumed)) (mv :source fn2-checkpoint-build fn2-checkpoint-plan fn2-checkpoint-map-build)
    (fn2-checkpoint-master-rearm-children-at-phase *fn2-csnapshot-phase-adopted* token kind owner generation
     fn2-checkpoint-build fn2-checkpoint-plan fn2-checkpoint-map-build fn2-csnapshot fn2-checkpoints
     fn2-checkpoint-publication fn2-checkpoint-root1 fn2-extents fn2-checkpoint-page)))))

(defmacro fn2-live-adoption-post-cost (name child)
 `(defcost ,name :child ,child :answers t :steps *fn2-work-stage* :bytes 512 :descriptors 0
   :tables ,(fn2-live-adoption-post-tables)
   :doc "Only the actual consumed ADOPTED handoff may use this phase-specific cleanup continuation."))
(fn2-live-adoption-post-cost fn2-checkpoint-live-adoption-release-complete-op fn2-checkpoint-live-adoption-release-complete)
(fn2-live-adoption-post-cost fn2-checkpoint-live-adoption-events-rearm-op fn2-checkpoint-live-adoption-events-rearm)
(fn2-live-adoption-post-cost fn2-checkpoint-live-adoption-rearm-op fn2-checkpoint-live-adoption-rearm)
