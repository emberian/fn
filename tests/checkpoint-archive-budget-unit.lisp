; Actual assembled scheduler controls; unrun under the source-only grant.
(in-package "ACL2")
(include-book "../books/executor")
(include-book "../books/checkpoint-restore-semantic-work")
(assert-event (<= *fn2-checkpoint-restore-semantic-entry-bytes* *fn2-checkpoint-semantic-visit-bytes*))
(make-event
 (value `(assert-event
          (and (= ,(fn2-arm-get :bytes (fn2-machine-property 'fn2-boot :budget (w state)))
                  *fn2-checkpoint-semantic-visit-bytes*)
               (<= (+ *fn2-work-empty* *fn2-checkpoint-semantic-visit-bytes* 32)
                   *fn2-turn-transition-max*)))))
(assert-event (and (fn2-execution-profilep *fn2-profile-tiny*)
                  (fn2-turn-work-room-p (fn2-profile-h *fn2-profile-tiny*) (fn2-profile-k *fn2-profile-tiny*) 0 0 0)
                  (fn2-turn-descriptor-room-p 0 (fn2-profile-aturn *fn2-profile-tiny*))
                  (fn2-execution-profilep *fn2-profile-concrete*)
                  (fn2-turn-work-room-p (fn2-profile-h *fn2-profile-concrete*) (fn2-profile-k *fn2-profile-concrete*) 0 0 0)))
; Hypothesis-removal control: a turn without a work grant has no room.
(assert-event (not (fn2-turn-work-room-p 0 0 0 0 0)))
