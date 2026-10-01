; Readonly post-completion custody projection, including the published phase.
; Registration is not a disk or allocator proof. No supplied completion/row.
(in-package "ACL2")
(include-book "history-event-backing")
(include-book "admission-preparation-source-capture")
(defun fn-stps-completed-source (fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :guard t))
 (let* ((builder (fn-hep-builder fn-history-backing))
        (token (fn-hed-at 6 builder))
        (completion (fn-hep-completion fn-history-backing))
        (intent (and (boundp-global 'fn-owner-canonical-admission-executor state)
                     (f-get-global 'fn-owner-canonical-admission-executor state)))
        (lease (and (boundp-global 'fn-owner-history-semantic-source state)
                    (f-get-global 'fn-owner-history-semantic-source state)))
        (fault (and (boundp-global 'fn-owner-history-completion-fault state)
                    (f-get-global 'fn-owner-history-completion-fault state))))
  (cond
   (fault (mv :recovery-required nil nil nil nil))
   ((not (and (member-eq (fn-hep-producer-phase fn-history-backing)
                        '(:completed :published))
              (fn-hed-fixedp builder 10)
              (eq (fn-hed-at 0 builder) :history-builder)
              (fn-hep-completion-matchesp completion token fn-history-backing)
              (fn-hed-fixedp intent 8)
              (eq (fn-hed-at 0 intent) :admission-prepare-intent)
              (equal (fn-hed-at 1 intent) token)
              (fn-hed-fixedp lease 4)
              (eq (fn-hed-at 0 lease) :history-semantic-source)
              (equal (fn-hed-at 1 lease) token)))
    (mv :completed-source-unavailable nil nil nil nil))
   (t (mv :retained-completed-source (fn-hed-at 2 builder)
          (fn-hed-at 3 lease) (fn-hed-at 5 intent) token)))))
; Output/effect correspondence to actual retained fields: no old-row lookup,
; post-install configuration substitution or STATE/pool publication.
(defthm fn-stps-source-keeps-actual-retained-aliases-by-definition
 (implies (equal (mv-nth 0 (fn-stps-completed-source backing state))
                 :retained-completed-source)
  (and (equal (mv-nth 1 (fn-stps-completed-source backing state))
              (fn-hed-at 2 (fn-hep-builder backing)))
       (equal (mv-nth 2 (fn-stps-completed-source backing state))
              (fn-hed-at 3 (f-get-global 'fn-owner-history-semantic-source state)))
       (equal (mv-nth 3 (fn-stps-completed-source backing state))
              (fn-hed-at 5 (f-get-global 'fn-owner-canonical-admission-executor state)))
       (equal (mv-nth 4 (fn-stps-completed-source backing state))
              (fn-hed-at 6 (fn-hep-builder backing)))))
 :hints (("Goal" :in-theory
  (e/d (fn-stps-completed-source)
       (fn-hed-at fn-hed-fixedp fn-hep-completion-matchesp
        boundp-global f-get-global member-equal)))))

(defthm fn-stps-completion-projects-original-prepare-source
 (implies
  (and (member-eq (fn-hep-producer-phase backing) '(:completed :published))
       (fn-hed-fixedp (fn-hep-builder backing) 10)
       (eq (fn-hed-at 0 (fn-hep-builder backing)) :history-builder)
       (equal token (fn-hed-at 6 (fn-hep-builder backing)))
       (fn-hep-completion-matchesp (fn-hep-completion backing) token backing)
       (not (and (boundp-global 'fn-owner-history-completion-fault state)
                 (f-get-global 'fn-owner-history-completion-fault state))))
  (equal
   (fn-stps-completed-source backing
    (fn-owner-admission-retain-prepare-source token epoch count frontier
      base-store canonical current parent config obligations readers posting state))
   (mv :retained-completed-source (fn-hed-at 2 (fn-hep-builder backing))
       config base-store token)))
 :hints (("Goal" :in-theory
  (e/d (fn-stps-completed-source fn-owner-admission-retain-prepare-source
        fn-hed-fixedp fn-hed-at)
       (fn-hep-completion-matchesp fn-hep-builder fn-hep-producer-phase
        fn-hep-completion)))))
