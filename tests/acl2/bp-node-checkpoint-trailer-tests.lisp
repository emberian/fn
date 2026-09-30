(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-trailer")
(include-book "bp-node-checkpoint-digest-tests")

(defun-nx fn-bpckt-emitted ()
  (let* ((token '(:maintenance 0 7 0))
         (initial (fn-bpck-begin token 7 1 8 nil nil 0 0 10000))
         (counted (fn-bpck-census-step initial 128))
         (emitting (fn-bpck-stage-granted counted (list :grown token))))
    (fn-bpck-test-emitted emitting 128 nil)))
(defun-nx fn-bpckt-job ()
  (fn-bpck-stage-observation (car (fn-bpckt-emitted)) :created))
(defun fn-bpckt-run-source (job bytes fuel pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix fuel) :verify-guards nil))
  (if (or (zp (nfix fuel)) (equal (pgs-dc-mode pgs-digest-state) :done))
      pgs-digest-state
    (let ((action (fn-bpck-digest-action job pgs-digest-state)))
      (mv-let (status pgs-digest-state)
        (fn-bpck-digest-step job
          (if (equal (car action) :read)
              (fn-bpnrc-prefix (fn-bpn-nth 2 action)
                               (fn-bpnrc-suffix (fn-bpn-nth 1 action) bytes)) nil)
          pgs-digest-state)
        (declare (ignore status))
        (fn-bpckt-run-source job bytes (1- (nfix fuel)) pgs-digest-state)))))
(defun-nx fn-bpckt-source-done ()
  (fn-bpckt-run-source (fn-bpckt-job) (cadr (fn-bpckt-emitted)) 128
    (mv-nth 1 (fn-bpck-digest-start (fn-bpckt-job) (create-pgs-digest-state)))))

(defthm fn-bpckt-terminal-positive
  (let ((job (fn-bpckt-job)) (cursor (fn-bpckt-source-done)))
    (and (fn-bpck-frame-digest-invariantp job cursor)
         (equal (pgs-dc-mode cursor) :done)
         (equal (fn-bpck-frame-result job cursor)
                (fn-frame-trailer (fn-bpck-frame-prefix job)))))
  :hints (("Goal" :use ((:instance fn-bpck-frame-result-is-exact-frame-trailer
                                 (job (fn-bpckt-job))
                                 (pgs-digest-state (fn-bpckt-source-done))))
    :in-theory (e/d (fn-bpck-test-digest-run fn-bpck-digest-action fn-bpck-digest-step fn-bpckt-job fn-bpckt-emitted fn-bpckt-source-done
                       fn-bpck-frame-digest-invariantp pgs-dcs-invariantp
                       pgs-dbd-domainp pgs-dcd-domainp pgs-dcs-counterp
                       pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                       pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                       ((:executable-counterpart fn-bpck-test-digest-run)))
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm fn-bpckt-implementation-terminal-positive
  (let ((job (fn-bpckt-job)) (cursor (fn-bpckt-source-done)))
    (and (fn-bpck-frame-digest-invariantp job cursor)
         (equal (pgs-dc-mode cursor) :done)
         (equal (fn-bpck-frame-result-impl job cursor)
                (fn-blake3-stobj (fn-bpck-frame-prefix job)))))
  :hints (("Goal" :use (fn-bpckt-terminal-positive
                        (:instance fn-bpck-frame-result-impl-is-exact-blake3
                                   (job (fn-bpckt-job))
                                   (pgs-digest-state (fn-bpckt-source-done))))))
  :rule-classes nil)

(defthm fn-bpckt-missing-done-counterexample
  (let* ((job (fn-bpckt-job))
         (cursor (mv-nth 1 (fn-bpck-digest-start job (create-pgs-digest-state)))))
    (and (fn-bpck-frame-digest-invariantp job cursor)
         (not (equal (pgs-dc-mode cursor) :done))
         (not (equal (fn-bpck-frame-result-impl job cursor)
                     (fn-blake3-stobj (fn-bpck-frame-prefix job))))))
  :hints (("Goal" :in-theory
    (enable fn-bpckt-job fn-bpckt-emitted fn-bpck-digest-start
            fn-bpck-frame-result-impl fn-bpck-frame-prefix fn-bpcke-prefix
            fn-blake3-stobj-is-blake3 fn-bpck-frame-digest-invariantp
            pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
            pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp
            pgs-dcd-framesp pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

; Corrupted capture, kept terminal digest state: retained DONE holds, while
; the exact-source invariant and terminal implementation equality fail.
(defthm fn-bpckt-corrupted-source-invariant-counterexample
  (let ((job (update-nth 5 '(:bad) (fn-bpckt-job)))
        (cursor (fn-bpckt-source-done)))
    (and (equal (pgs-dc-mode cursor) :done)
         (not (fn-bpck-frame-digest-invariantp job cursor))
         (not (equal (fn-bpck-frame-result-impl job cursor)
                     (fn-blake3-stobj (fn-bpck-frame-prefix job))))))
  :hints (("Goal" :in-theory
    (enable fn-bpckt-job fn-bpckt-emitted fn-bpckt-source-done
            fn-bpck-frame-result-impl fn-bpck-frame-prefix fn-bpcke-prefix
            fn-blake3-stobj-is-blake3 fn-bpck-frame-digest-invariantp
            pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
            pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp
            pgs-dcd-framesp pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm fn-bpckt-host-action-terminal-positive
  (let ((job (fn-bpckt-job)) (cursor (fn-bpckt-source-done)))
    (and (fn-bpck-frame-digest-invariantp job cursor)
         (equal (pgs-dc-mode cursor) :done)
         (equal (fn-bpck-digest-action job cursor)
                (list :trailer (fn-frame-trailer (fn-bpck-frame-prefix job))))))
  :hints (("Goal" :use (fn-bpckt-terminal-positive
                        (:instance fn-bpck-digest-action-terminal-is-exact-frame-trailer
                                   (job (fn-bpckt-job))
                                   (pgs-digest-state (fn-bpckt-source-done))))))
  :rule-classes nil)
