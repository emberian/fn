; Topic prefix algebra for the actual Store history/recovery relation.
; These are proof-side scans; the served Store carries fn-sn-topic instead.
(in-package "ACL2")
(include-book "topic-history-prefix")

(defthm fn-sti-prefix-loop-append-one
  (implies (true-listp records)
           (equal (fn-th-prefix-loop projection
                                     (append records (list event)))
                  (fn-th-prefix-step
                   (fn-th-prefix-loop projection records) event)))
  :hints (("Goal" :induct (fn-th-prefix-loop projection records)
           :in-theory (enable fn-th-prefix-loop))))

(defthm fn-sti-prefix-project-append-one
  (implies (true-listp records)
           (equal (fn-th-prefix-project (append records (list event)))
                  (fn-th-prefix-step (fn-th-prefix-project records) event)))
  :hints (("Goal" :use ((:instance fn-sti-prefix-loop-append-one
                                    (projection
                                     (fn-th-prefix-state :ok 0 nil nil nil nil nil))))
           :in-theory (enable fn-th-prefix-project))))

(defthm fn-sti-prefix-step-success-needs-successful-input
  (implies (eq (fn-th-at 0 (fn-th-prefix-step projection event)) :ok)
           (eq (fn-th-at 0 projection) :ok))
  :hints (("Goal" :use fn-th-prefix-step-failure-sticks
           :in-theory (disable fn-th-prefix-step))))

(defthm fn-sti-prefix-step-success-advances-next
  (implies (eq (fn-th-at 0 (fn-th-prefix-step projection event)) :ok)
           (equal (fn-th-at 1 (fn-th-prefix-step projection event))
                  (1+ (nfix (fn-th-at 1 projection)))))
  :hints (("Goal" :in-theory
           (e/d (fn-th-prefix-step fn-th-prefix-state)
                (fn-store-event-p fn-stxk-p fn-stxa-p
                 fn-th-local-admin-eventp fn-th-topic-eventp
                 fn-th-commit-anchor fn-th-commit-report)))))

; The topic interpreter deliberately treats ordinary Store events as neutral.
; Only the local-admin, anchor, and report class can require topic authority.
; Their preparation has its own checked gate in fn-sn-prepare-topic.
(defthm fn-sti-local-admin-is-topic-event
  (implies (fn-th-local-admin-eventp event)
           (fn-th-topic-eventp event))
  :hints (("Goal" :in-theory (enable fn-th-topic-eventp))))

(defthm fn-sti-nontopic-step-succeeds-at-next-sequence
  (implies (and (eq (fn-th-at 0 projection) :ok)
                (fn-store-event-p event)
                (equal (fn-store-event-sequence event)
                       (fn-th-at 1 projection))
                (not (fn-th-topic-eventp event)))
           (eq (fn-th-at 0 (fn-th-prefix-step projection event)) :ok))
  :hints (("Goal" :in-theory
           (e/d (fn-th-prefix-step fn-th-prefix-state)
                (fn-store-event-p fn-th-topic-eventp fn-stxk-p fn-stxa-p
                 fn-th-local-admin-eventp)))))

(defthm fn-sti-prefix-append-success-needs-prefix
  (implies (and (true-listp records)
                (eq (fn-th-at 0
                           (fn-th-prefix-project
                            (append records (list event)))) :ok))
           (eq (fn-th-at 0 (fn-th-prefix-project records)) :ok))
  :hints (("Goal" :use ((:instance fn-sti-prefix-loop-append-one
                                    (projection
                                     (fn-th-prefix-state :ok 0 nil nil nil nil nil)))
                         (:instance fn-sti-prefix-step-success-needs-successful-input
                                    (projection (fn-th-prefix-project records))))
           :in-theory (e/d (fn-th-prefix-project)
                           (fn-th-prefix-loop fn-th-prefix-step)))))
