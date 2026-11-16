; PREPARED UNEXECUTED actual registry gate. No alternate CORE is declared.
(in-package "ACL2")
(include-book "../books/assembly-index")
(assert-event
 (let ((names (fn2-machine-names (w state)))
       (types (fn2-core-child-types (fn2-core-child-registry (w state)))))
  (and (member-eq 'fn2-checkpoint-master names)
       (member-eq 'fn2-checkpoint-page-worker names)
       (member-eq 'fn2-checkpoint-writer names)
       (subsetp-eq '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                     fn2-checkpoint-page fn2-checkpoint-page-verified
                     fn2-checkpoint-master fn2-checkpoint-page-worker fn2-checkpoint-writer
                     fn2-checkpoint-restore-reader fn2-checkpoint-restore-map
                     fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach
                     fn2-checkpoint-restore-reach-control fn2-checkpoint-restore-semantic
                     fn2-checkpoint-restore-semantic-work) types)
       (posp *fn2-c-read-step-bytes*) (posp *fn2-c-read-callback-bytes*))))
