; Whole reachable-invariant witnesses, connected to the actual initializer.
(in-package "ACL2")
(include-book "../books/commit-reachable")

(defun fn2-reach-test-profile ()
  (declare (xargs :guard t))
  (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (8 . 4096)) *fn2-profile-tiny*))
(defun fn2-reach-initial-witness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (let ((fn2-core (fn2-init-executor (fn2-reach-test-profile) :echo nil fn2-core)))
        (mv (fn2-env-reach-initial-data-p (fn2-reach-test-profile) fn2-core) fn2-core))
      ok)))
(assert-event (and (fn2-core-profilep (fn2-reach-test-profile)) (fn2-reach-initial-witness)))
(defthm fn2-reach-initial-witness-unfolds
  (equal (fn2-reach-initial-witness)
         (fn2-env-reach-initial-data-p (fn2-reach-test-profile)
           (fn2-init-executor (fn2-reach-test-profile) :echo nil (create-fn2-core))))
  :hints (("Goal" :in-theory '(fn2-reach-initial-witness))))
(defthm fn2-reach-initial-witness-whole
  (and (fn2-env-reach-active-inv (fn2-reach-test-profile) nil nil
         (fn2-init-executor (fn2-reach-test-profile) :echo nil (create-fn2-core)))
       (not (fn2-core-stopped-p
         (fn2-init-executor (fn2-reach-test-profile) :echo nil (create-fn2-core)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-corep-of-fresh-core
                               (:e fn2-reach-initial-witness) (:e fn2-reach-test-profile)
                               (:e fn2-core-profilep))
           :use ((:instance fn2-env-reach-initial-data-covers-whole
                            (profile (fn2-reach-test-profile)) (c (create-fn2-core)))
                 fn2-reach-initial-witness-unfolds))))

(defun fn2-reach-epoch-core (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((fn2-core (fn2-init-executor (fn2-reach-test-profile) :echo nil fn2-core)))
    (fn2-env-begin-epoch 1 fn2-core)))
(defun fn2-reach-admission-details (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((before-acks (fn2-env-observe (fn2-env-commit-ids (fn2-reach-test-profile)) nil fn2-core)))
    (mv-let (code id batch event fn2-core) (fn2-commit-admit-keyed 2 0 0 0 0 fn2-core)
      (declare (ignore event))
      (let ((fn2-core (if (eq code :ok) (fn2-exec-wake id fn2-core) fn2-core)))
        (mv (list code before-acks
                  (fn2-env-observe (fn2-env-commit-ids (fn2-reach-test-profile)) before-acks fn2-core)
                  (not (fn2-core-stopped-p fn2-core))
                  (fn2-machine-phase id fn2-core) (fn2-machine-member-count id fn2-core) batch)
            fn2-core)))))
(defthm fn2-reach-admission-details-state
  (equal (mv-nth 1 (fn2-reach-admission-details c)) (fn2-env-admit 2 0 c))
  :hints (("Goal" :in-theory '(fn2-reach-admission-details fn2-env-admit
                               mv-nth (:e zp) (:e binary-+) (:e unary--) car-cons cdr-cons))))
(defthm fn2-reach-admission-details-observations
  (let ((result (mv-nth 0 (fn2-reach-admission-details c))))
    (and (equal (nth 1 result) (fn2-env-observe (fn2-env-commit-ids (fn2-reach-test-profile)) nil c))
         (equal (nth 2 result)
                (fn2-env-observe (fn2-env-commit-ids (fn2-reach-test-profile))
                  (fn2-env-observe (fn2-env-commit-ids (fn2-reach-test-profile)) nil c)
                  (fn2-env-admit 2 0 c)))
         (equal (nth 3 result) (not (fn2-core-stopped-p (fn2-env-admit 2 0 c))))))
  :hints (("Goal" :in-theory '(fn2-reach-admission-details fn2-env-admit
                               mv-nth nth (:e zp) (:e binary-+) (:e unary--) car-cons cdr-cons))))
(defun fn2-reach-admission-witness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (let ((fn2-core (fn2-reach-epoch-core fn2-core)))
        (fn2-reach-admission-details fn2-core))
      result)))
(assert-event (equal (fn2-reach-admission-witness)
                     (list :ok nil nil t *fn2-commit-state-collect* 2 1)))
(defthm fn2-reach-admission-witness-unfolds
  (equal (fn2-reach-admission-witness)
         (mv-nth 0 (fn2-reach-admission-details (fn2-reach-epoch-core (create-fn2-core)))))
  :hints (("Goal" :in-theory '(fn2-reach-admission-witness))))
(defthm fn2-reach-epoch-witness-whole
  (fn2-env-reach-active-inv (fn2-reach-test-profile)
    (fn2-env-observe (fn2-env-commit-ids (fn2-reach-test-profile)) nil
      (fn2-reach-epoch-core (create-fn2-core))) nil
    (fn2-reach-epoch-core (create-fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-reach-epoch-core fn2-env-reach-epoch-unfolds
                               fn2-env-tag fn2-env-arg nth (:e zp) (:e binary-+) (:e unary--)
                               (:e consp) (:e car) (:e cdr) (:e equal) car-cons cdr-cons (:e append))
           :use (fn2-reach-initial-witness-whole
                 (:instance fn2-env-reach-active-epoch-step
                   (profile (fn2-reach-test-profile)) (acked nil) (log nil) (action '(:epoch 1))
                   (c (fn2-init-executor (fn2-reach-test-profile) :echo nil (create-fn2-core))))))))
(defthm fn2-reach-admission-witness-whole
  (and (fn2-env-reach-active-inv (fn2-reach-test-profile) nil nil
         (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core))))
       (not (fn2-core-stopped-p (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-tag fn2-env-arg nth (:e zp) (:e binary-+) (:e unary--)
                               (:e consp) (:e car) (:e cdr) (:e equal) car-cons cdr-cons (:e append)
                               (:e fn2-reach-admission-witness))
           :use (fn2-reach-epoch-witness-whole fn2-reach-admission-witness-unfolds
                 (:instance fn2-reach-admission-details-observations
                   (c (fn2-reach-epoch-core (create-fn2-core))))
                 (:instance fn2-env-step-admit-unfolds
                   (action '(:admit 2 0)) (fn2-core (fn2-reach-epoch-core (create-fn2-core))))
                 (:instance fn2-env-reach-active-admit-step
                   (profile (fn2-reach-test-profile)) (acked nil) (log nil) (action '(:admit 2 0))
                   (c (fn2-reach-epoch-core (create-fn2-core))))))))

(defun fn2-reach-collect-details (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((id (car (fn2-env-commit-ids (fn2-reach-test-profile))))
         (before (fn2-commit-row-phase id fn2-core)))
    (mv-let (bytes steps desc runnable fn2-core) (fn2-commit-run id 4 fn2-core)
      (declare (ignore bytes steps desc runnable))
      (mv (list before (fn2-machine-phase id fn2-core)
                (fn2-machine-member-count id fn2-core) (fn2-machine-batch-no id fn2-core)
                (fn2-env-reach-initial-data-p (fn2-reach-test-profile) fn2-core)) fn2-core))))
(defthm fn2-reach-collect-details-observations
  (let* ((id (car (fn2-env-commit-ids (fn2-reach-test-profile))))
         (result (mv-nth 0 (fn2-reach-collect-details c))))
    (and (equal (nth 0 result) (fn2-commit-row-phase id c))
         (equal (nth 4 result)
                (fn2-env-reach-initial-data-p (fn2-reach-test-profile)
                  (mv-nth 4 (fn2-commit-run id 4 c))))))
  :hints (("Goal" :in-theory '(fn2-reach-collect-details mv-nth nth (:e zp)
                               (:e binary-+) (:e unary--) car-cons cdr-cons))))
(defun fn2-reach-collect-witness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (let* ((fn2-core (fn2-reach-epoch-core fn2-core))
             (fn2-core (fn2-env-admit 2 0 fn2-core)))
        (fn2-reach-collect-details fn2-core))
      result)))
(assert-event (equal (fn2-reach-collect-witness)
                     (list *fn2-commit-state-collect* *fn2-commit-state-seal* 2 1 t)))
(defthm fn2-reach-collect-witness-unfolds
  (equal (fn2-reach-collect-witness)
         (mv-nth 0 (fn2-reach-collect-details
           (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core))))))
  :hints (("Goal" :in-theory '(fn2-reach-collect-witness))))
(defthm fn2-reach-collect-witness-whole
  (let* ((id (car (fn2-env-commit-ids (fn2-reach-test-profile))))
         (before (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core))))
         (after (mv-nth 4 (fn2-commit-run id 4 before))))
    (and (fn2-env-reach-active-inv (fn2-reach-test-profile) nil nil before)
         (fn2-env-reach-active-inv (fn2-reach-test-profile) nil nil after)
         (not (fn2-core-stopped-p after))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-fl (:e fn2-reach-collect-witness)
                               nth (:e zp) (:e binary-+) (:e unary--) (:e equal) car-cons cdr-cons)
           :use (fn2-reach-admission-witness-whole fn2-reach-collect-witness-unfolds
                 (:instance fn2-reach-collect-details-observations
                   (c (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core)))))
                 (:instance fn2-env-reach-collect-structure
                   (profile (fn2-reach-test-profile)) (acked nil) (log nil)
                   (id (car (fn2-env-commit-ids (fn2-reach-test-profile)))) (budget 4)
                   (c (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core)))))
                 (:instance fn2-env-reach-initial-data-nonstopped
                   (profile (fn2-reach-test-profile))
                   (c (mv-nth 4 (fn2-commit-run (car (fn2-env-commit-ids (fn2-reach-test-profile))) 4
                        (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core)))))))
                 (:instance fn2-env-reach-structure-and-data
                   (profile (fn2-reach-test-profile))
                   (c (mv-nth 4 (fn2-commit-run (car (fn2-env-commit-ids (fn2-reach-test-profile))) 4
                        (fn2-env-admit 2 0 (fn2-reach-epoch-core (create-fn2-core)))))))))))
(defun fn2-reach-pool-free-count (class fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (n)
  (fn2-pool-class-countsi class fn2-pool) n))
(defun fn2-reach-pool-genesis-witness ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((profile (put-assoc-equal :groups '(("comp.lang.lisp" . 7) ("alt.test" . 9))
                    (put-assoc-equal :identity-arena-bytes 4096
                     (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096)) *fn2-profile-tiny*))))
          (hyps (and (fn2-corep fn2-core) (fn2-core-profilep profile)))
          (fn2-core (fn2-init-executor profile :echo nil fn2-core)))
    (mv (and hyps (fn2-core-pool-semanticp fn2-core) (not (fn2-core-stopped-p fn2-core))
             (< (fn2-reach-pool-free-count 2 fn2-core) 16)) fn2-core))
   answer)))
(assert-event (fn2-reach-pool-genesis-witness))
(defun fn2-reach-pool-break-link (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (fn2-pool)
  (fn2-pool-set-next-free 0 *fn2-none* fn2-pool) fn2-core))
; Removing the incoming semantic premise does not repair a lost free link.
(defun fn2-reach-pool-genesis-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
          (fn2-core (fn2-reach-pool-break-link fn2-core))
          (before (not (fn2-core-pool-semanticp fn2-core)))
          (fn2-core (fn2-init-engine *fn2-profile-tiny* fn2-core)))
    (mv (and before (not (fn2-core-pool-semanticp fn2-core))) fn2-core))
   answer)))
(assert-event (fn2-reach-pool-genesis-control))
