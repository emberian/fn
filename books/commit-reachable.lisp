; Reachable durability state: ghost row coverage is derived from the profile.
; This book does not discharge the final ACK claim by adding premises to it.
(in-package "ACL2")
(include-book "commit-durable-all")

(defun-nx fn2-env-reach-structure (profile c)
  (and (fn2-core-profilep profile) (fn2-corep c) (fn2-core-wfp c)
       (fn2-env-commit-slots-p profile c)
       (fn2-env-commit-dir-canonical-p profile c)
       (fn2-env-f c) (fn2-env-x c) (fn2-env-q c)))

(defun-nx fn2-env-reach-history (profile acked log c)
  (let ((ids (fn2-env-commit-ids profile)))
    (and (true-listp acked) (true-listp log)
         (fn2-env-dur-inv ids acked log c)
         (fn2-env-j5-rows ids log c)
         (fn2-env-j5e-rows ids c)
         (fn2-env-j6p-rows ids c)
         (fn2-env-j6l-rows ids c)
         (fn2-env-j6s-rows ids c)
         (fn2-env-fl log c))))

(defun-nx fn2-env-reach-active-inv (profile acked log c)
  (and (fn2-env-reach-structure profile c)
       ; J6's byte/lease links require these semantic representation facts.
       (fn2-core-pool-semanticp c)
       (fn2-ops-semanticp (fn2-core-ops c))
       (fn2-env-reach-history profile acked log c)))

(defthm fn2-env-reach-active-observation-by-definition
  (implies (fn2-env-reach-active-inv profile acked log c)
           (fn2-env-inv (fn2-env-commit-ids profile) acked log c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-history fn2-env-dur-inv))))

(defthm fn2-env-reach-turn-projection
  (implies (fn2-env-reach-active-inv profile acked log c)
           (fn2-env-dur-turn-inv (list (fn2-env-commit-ids profile) acked log) c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-history)
           :use ((:instance fn2-env-dur-inv-entry
                            (ids (fn2-env-commit-ids profile)) (fn2-core c))))))

(defthm fn2-env-reach-covers-visited-commit
  (implies (and (fn2-env-reach-active-inv profile acked log c) (fn2-commit-idp id c))
           (let ((j (fn2-machine-global-id *fn2-commit-kind* (fn2-machine-slot id c) profile)))
             (and (member-equal j (fn2-env-commit-ids profile))
                  (fn2-commit-idp j c)
                  (equal (fn2-machine-slot j c) (fn2-machine-slot id c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-structure)
           :use ((:instance fn2-env-commit-ids-cover (fn2-core c))))))

 ; The recovery-stop branch retains the actual durability observation.
; It does not pretend F/X/Q survive a refused post-swap operation.
(defun-nx fn2-env-reach-inv (profile acked log c)
  (and (fn2-core-profilep profile) (fn2-corep c) (fn2-core-wfp c)
       (true-listp acked) (true-listp log)
       (fn2-env-inv (fn2-env-commit-ids profile) acked log c)
       (or (fn2-core-stopped-p c)
           (fn2-env-reach-active-inv profile acked log c))))
(defthm fn2-env-reach-observation-by-definition
  (implies (fn2-env-reach-inv profile acked log c)
           (fn2-env-inv (fn2-env-commit-ids profile) acked log c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-reach-inv))))
(defthm fn2-env-reach-active-implies-reachable
  (implies (fn2-env-reach-active-inv profile acked log c)
           (fn2-env-reach-inv profile acked log c))
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-structure
                              fn2-env-reach-history fn2-env-reach-inv)
           :use fn2-env-reach-active-observation-by-definition)))

; Initializing the existing structural invariants is one component of the
; full initialization proof, not a replacement for the history/semantic facts.
(defthm fn2-env-reach-structure-init
  (implies (and (fn2-corep c) (fn2-core-profilep profile))
           (fn2-env-reach-structure profile (fn2-init-executor profile :echo nil c)))
  :hints (("Goal" :in-theory '(fn2-env-reach-structure)
           :use ((:instance fn2-env-init-executor-shape (fn2-core c) (mode :echo) (scribe-p nil))
                 (:instance fn2-env-commit-slots-p-init (mode :echo) (scribe-p nil))
                 (:instance fn2-env-commit-dir-canonical-p-init (mode :echo) (scribe-p nil))
                 (:instance fn2-env-f-init (mode :echo) (scribe-p nil))
                 (:instance fn2-env-x-init (mode :echo) (scribe-p nil))
                 (:instance fn2-env-q-init (mode :echo) (scribe-p nil))))))

; These phase facts are the reusable base for the initialization proof.
(defthm fn2-env-reach-free-history-row
  (implies (equal (fn2-machine-phase id c) *fn2-commit-state-free*)
           (and (fn2-env-j3-row id log c) (fn2-env-j3e-row id c)
                (fn2-env-j6-row id c) (fn2-env-j6p-row id c)
                (fn2-env-j6l-row id c) (fn2-env-j6s-row id c)))
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row fn2-env-j6-row
                              fn2-env-j6p-row fn2-env-j6l-row fn2-env-j6s-row
                              member-equal (:e equal) (:e member-equal)))))

(defthm fn2-env-reach-free-durable-row
  (implies (and (equal (fn2-machine-phase id c) *fn2-commit-state-free*)
                (equal (fn2-machine-cb-acks id c) 0)
                (equal (fn2-machine-cb-deps-ok id c) 0)
                (equal (fn2-machine-cb-log-ok id c) 0))
           (fn2-env-j-row id log c))
  :hints (("Goal" :in-theory '(fn2-env-j-row fn2-env-j1-row fn2-env-j2-row
                              member-equal posp natp (:e equal) (:e member-equal)
                              (:e <) (:e integerp)))))

(defthm fn2-env-reach-zero-frontier
  (implies (and (equal (nth 1 (fn2-env-root c)) 0)
                (equal (nth 2 (fn2-env-root c)) 0))
           (fn2-env-j-frontier nil c))
  :hints (("Goal" :in-theory '(fn2-env-j-frontier fn2-env-prefix-durable-p
                              (:e zp) (:e binary-+) (:e <)))))
(defthm fn2-env-reach-core-init-no-lent
  (not (equal (nth 3 (fn2-env-io u (fn2-core-init profile c))) 1))
  :hints (("Goal" :in-theory '(fn2-env-io fn2-env-core-init-commit-children
      fn2-env-commit-io-init-6-facts nth car-cons cdr-cons (:e nth) (:e equal) (:e zp) (:e binary-+) (:e unary--)))))
(defthm fn2-env-reach-executor-io-frame
  (equal (fn2-core-commit-io (fn2-init-executor profile mode scribe-p c))
         (fn2-core-commit-io (fn2-core-init profile c)))
  :hints (("Goal" :in-theory '(fn2-core-commit-io)
           :use fn2-env-init-executor-commit-children)))
(defthm fn2-env-reach-init-no-lent
  (not (equal (nth 3 (fn2-env-io u (fn2-init-executor profile mode scribe-p c))) 1))
  :hints (("Goal" :in-theory '(fn2-env-io fn2-env-reach-executor-io-frame)
           :use fn2-env-reach-core-init-no-lent)))
(defthm fn2-env-reach-lent-ok-init
  (fn2-env-lent-ok (fn2-init-executor profile mode scribe-p c))
  :hints (("Goal" :in-theory '(fn2-env-lent-ok)
           :use ((:instance fn2-env-reach-init-no-lent
                    (u (fn2-env-lent-ok-witness (fn2-init-executor profile mode scribe-p c))))))))

; Actual admission preserves the coupled history and row coverage.
; A stopped result still carries the global durability observation.
(defthm fn2-env-reach-admit-ops-frame
  (equal (fn2-core-ops (fn2-env-admit members mode c)) (fn2-core-ops c))
  :hints (("Goal" :in-theory '(fn2-env-ok fn2-core-ops)
           :use ((:instance fn2-env-admit-ok (fn2-core c) (c0 c))))))

(defthm fn2-env-reach-history-admit
  (implies (and (fn2-env-reach-active-inv profile acked log c)
                (equal (fn2-env-tag action) :admit))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (fn2-env-reach-history profile
               (fn2-env-observe (fn2-env-commit-ids profile) acked after)
               (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-structure
                               fn2-env-reach-history fn2-env-fl
                               fn2-env-observe-true-listp true-listp-append)
           :use ((:instance fn2-env-dur-inv-admit-step (fn2-core c) (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-j5-rows-admit-step (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-j5e-rows-admit-step (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-fresh-lent-admit-step)))))

(defthm fn2-env-reach-admit-step
  (implies (and (fn2-env-reach-active-inv profile acked log c)
                (equal (fn2-env-tag action) :admit))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (fn2-env-reach-inv profile
               (fn2-env-observe (fn2-env-commit-ids profile) acked after)
               (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-structure
                               fn2-env-reach-history fn2-env-reach-inv fn2-env-dur-inv
                               fn2-env-reach-admit-ops-frame
                               fn2-env-observe-true-listp true-listp-append
                               fn2-env-step-preserves-type fn2-env-step-preserves-wfp
                               fn2-env-admit-preserves-type fn2-env-admit-preserves-wfp
                               (:e zp) (:e binary-+) (:e unary--)
                               car-cons cdr-cons mv-nth (:e mv-nth) (:e equal) (:e car) (:e cdr))
           :use ((:instance fn2-env-reach-history-admit)
                 (:instance fn2-env-step-admit-unfolds (fn2-core c))
                 (:instance fn2-env-admit-semanticp (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)))
                 (:instance fn2-env-commit-slots-p-step-but-turn (p profile) (fn2-core c))
                 (:instance fn2-env-commit-dir-canonical-p-step-but-turn (p profile))
                 (:instance fn2-env-f-step-but-turn)
                 (:instance fn2-env-x-step-but-turn)
                 (:instance fn2-env-q-step-but-turn)))))

; Executable data side of initialization. Structural and universal loan facts
; are supplied by the actual initializer theorems, never skipped by the check.
(defun fn2-env-reach-initial-data-p (profile fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((ids (fn2-env-commit-ids profile)))
    (and (fn2-core-profilep profile) (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
         (not (fn2-core-stopped-p fn2-core))
         (fn2-core-pool-semanticp fn2-core)
         (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (ok) (fn2-ops-semanticp fn2-ops) ok)
         (fn2-env-dur-inv ids nil nil fn2-core)
         (fn2-env-j5-rows ids nil fn2-core) (fn2-env-j5e-rows ids fn2-core)
         (fn2-env-j6p-rows ids fn2-core) (fn2-env-j6l-rows ids fn2-core)
         (fn2-env-j6s-rows ids fn2-core) (fn2-env-freshness nil fn2-core))))

(defthm fn2-env-reach-initial-data-covers-whole
  (implies (and (fn2-corep c) (fn2-core-profilep profile)
                (fn2-env-reach-initial-data-p profile (fn2-init-executor profile :echo nil c)))
           (and (fn2-env-reach-active-inv profile nil nil (fn2-init-executor profile :echo nil c))
                (not (fn2-core-stopped-p (fn2-init-executor profile :echo nil c)))))
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-history
                               fn2-env-reach-initial-data-p fn2-env-fl (:e true-listp))
           :use (fn2-env-reach-structure-init
                 (:instance fn2-env-reach-lent-ok-init (mode :echo) (scribe-p nil))))))

(defthm fn2-env-reach-epoch-pool-ops
  (and (equal (fn2-core-pool (fn2-env-begin-epoch epoch c)) (fn2-core-pool c))
       (equal (fn2-core-ops (fn2-env-begin-epoch epoch c)) (fn2-core-ops c)))
  :hints (("Goal" :in-theory (e/d (fn2-env-begin-epoch fn2-core-pool fn2-core-ops update-fn2-core-extents nth-update-nth) (fn2-alloc-begin-epoch nth update-nth)))))
(defthm fn2-env-reach-epoch-unfolds
  (implies (equal (fn2-env-tag action) :epoch)
           (equal (fn2-env-step action nil image rlog c)
                  (mv nil (fn2-env-begin-epoch (fn2-env-arg 1 action) c))))
  :hints (("Goal" :in-theory '(fn2-env-step))))
(defthm fn2-env-reach-active-epoch-step
  (implies (and (fn2-env-reach-active-inv profile acked log c)
                (equal (fn2-env-tag action) :epoch))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (fn2-env-reach-active-inv profile
               (fn2-env-observe (fn2-env-commit-ids profile) acked after)
               (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-structure
                               fn2-env-reach-history fn2-env-fl fn2-core-pool-semanticp
                               fn2-env-reach-epoch-pool-ops
                               fn2-env-observe-true-listp true-listp-append
                               fn2-env-begin-epoch-preserves-type fn2-env-begin-epoch-preserves-wfp
                               car-cons cdr-cons mv-nth (:e mv-nth) (:e equal) (:e car) (:e cdr)
                               (:e zp) (:e binary-+) (:e unary--)
                               member-equal member-eq (:e member-equal) (:e member-eq))
           :use ((:instance fn2-env-reach-epoch-unfolds)
                 (:instance fn2-env-dur-inv-host-step (fn2-core c) (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-j5-rows-frame-step (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-j6p-j6l-rows-host-step (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-j6s-rows-host-step (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-j5e-rows-host-step (ids (fn2-env-commit-ids profile)))
                 (:instance fn2-env-fresh-lent-host-step)
                 (:instance fn2-env-commit-slots-p-step-but-turn (p profile) (fn2-core c))
                 (:instance fn2-env-commit-dir-canonical-p-step-but-turn (p profile))
                 (:instance fn2-env-f-host-step)
                 (:instance fn2-env-x-step-but-turn)
                 (:instance fn2-env-q-step-but-turn)))))

(defthm fn2-env-reach-active-admit-step
  (implies (and (fn2-env-reach-active-inv profile acked log c)
                (equal (fn2-env-tag action) :admit)
                (not (fn2-core-stopped-p (mv-nth 1 (fn2-env-step action nil image rlog c)))))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (fn2-env-reach-active-inv profile
               (fn2-env-observe (fn2-env-commit-ids profile) acked after)
               (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory '(fn2-env-reach-inv) :use fn2-env-reach-admit-step)))

(defthm fn2-env-reach-collect-structure
  (implies (and (fn2-env-reach-active-inv profile acked log c)
                (equal (fn2-commit-row-phase id c) *fn2-commit-state-collect*)
                (not (fn2-core-stopped-p (mv-nth 4 (fn2-commit-run id budget c)))))
           (let ((after (mv-nth 4 (fn2-commit-run id budget c))))
             (and (fn2-env-reach-structure profile after) (fn2-env-fl log after))))
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-structure
                               fn2-env-reach-history
                               fn2-commit-run-preserves-type fn2-commit-run-preserves-wfp
                               member-equal (:e member-equal) (:e equal))
           :use ((:instance fn2-env-commit-slots-p-commit-run (p profile) (fn2-core c))
                 (:instance fn2-env-commit-dir-canonical-p-commit-run (p profile))
                 (:instance fn2-env-f-commit-run (fn2-core c))
                 (:instance fn2-env-x-commit-run (fn2-core c))
                 (:instance fn2-env-q-commit-run)
                 (:instance fn2-env-j5-row-of-commit-ids)
                 (:instance fn2-commit-run-fn2-env-fl (fn2-core c))))))
(defthm fn2-env-reach-structure-and-data
  (implies (and (fn2-env-reach-structure profile c)
                (fn2-env-lent-ok c)
                (fn2-env-reach-initial-data-p profile c))
           (and (fn2-env-reach-active-inv profile nil nil c)
                (not (fn2-core-stopped-p c))))
  :hints (("Goal" :in-theory '(fn2-env-reach-active-inv fn2-env-reach-history
                               fn2-env-reach-initial-data-p fn2-env-fl (:e true-listp)))))

(defthm fn2-env-reach-initial-data-nonstopped
  (implies (fn2-env-reach-initial-data-p profile c) (not (fn2-core-stopped-p c)))
  :hints (("Goal" :in-theory '(fn2-env-reach-initial-data-p))))
