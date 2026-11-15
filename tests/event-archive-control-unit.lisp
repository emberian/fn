; Active/pending metadata isolation only, not a persistence/coverage witness.
(in-package "ACL2")
(include-book "../books/event-archive-control")
(defun fn2-eacu-isolation ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-event-archive
  (mv-let (answer fn2-event-archive)
   (with-local-stobj fn2-digests
    (mv-let (answer fn2-event-archive fn2-digests)
     (b* ((fn2-event-archive (fn2-event-archive-init 2 fn2-event-archive))
          (fn2-digests (fn2-digests-init 1 fn2-digests))
          (fn2-digests (fn2-digest-set-word 0 0 123 fn2-digests))
          (fn2-event-archive (fn2-event-archive-copy-digest 1 :cut-seal 0 0 fn2-digests fn2-event-archive)))
      (mv (and (= (fn2-event-archive-word 1 :cut-seal 0 fn2-event-archive) 123)
               (= (fn2-event-archive-word 0 :cut-seal 0 fn2-event-archive) 0)
               (= (fn2-event-archive-word 1 :member 0 fn2-event-archive) 0)
               (= (fn2-event-archive-word 1 :manifest 0 fn2-event-archive) 0)) fn2-event-archive fn2-digests))
     (mv answer fn2-event-archive))) answer)))
(assert-event (fn2-eacu-isolation))
