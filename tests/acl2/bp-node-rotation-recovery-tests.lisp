; Successful served-path restart from a rotation that owes a queued job.
(in-package "ACL2")
(include-book "bp-node-rotation-due-tests")
(include-book "../../books/bp-node-rotation-recovery")

(defteeth fn-bpnj-rotation-restart-succeeds-with-owed-work
  :claim (let* ((plan (fn-bpnr-published-plan st generation ck))
         (fresh (fn-bpnr-open-fresh st))
         (seeded (fn-bpnr-seed-state fresh plan))
         (event (fn-bpnr-recover-auto-event seeded nil :ready nil plan))
         (served (append (fn-bprpf-admit-recovery event profile) (list domain)))
         (answer (fn-bpnj-step seeded served)))
    (((proposes (equal (car (car (fn-bpnf-answer-effects
                          (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint))
      (invariant (fn-bpn-machine-invariantp (fn-bpnf-base st)))
      (ready (fn-bpnr-replay-readyp st))
      (profile (or (not (equal (fn-bpn-nth 0 (fn-bpn-nth 4 event)) :ready))
            (and (fn-bpnpf-profilep profile)
             (fn-bprpf-held-adus-fitp (fn-bpn-nth 1 (fn-bpn-nth 4 event))
                                    (fn-bpnpf-adu-octets profile)))))
      (domain (fn-bpnp-clock-domain-admitsp served)))
     (and (equal (car (car (fn-bpnf-answer-effects answer))) :restart-ready)
        (equal (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
        (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
        (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                (fn-bpn-lifecycle-recovery-from nil nil (fn-bpnr-plan-start-token plan))
                (fn-bpnf-base (fn-bpnf-answer-state answer))) t))))
  :subject fn-bpnj-step
  :witness ((st (bprd-traced-q)) (generation 1) (ck (bprd-traced-ck))
            (profile '(8 1048576 65538 1048576)) (domain '(:same (7 7 7 7))))
  :breaks ((proposes ((ck (update-nth 7 nil (bprd-owed-ck))) (st (bprd-owed-q))))
           (invariant ((st (bprd-token-q 5000))
                       (ck (update-nth 8 5000 (bprd-owed-ck)))))
           (ready ((st (update-nth 10 0 (bprd-owed-q)))
                        (ck (update-nth 5 0 (bprd-owed-ck)))))
           (profile ((profile nil) (st (bprd-owed-q)) (ck (bprd-owed-ck))))
           (domain ((domain '(:fence :different-boot)) (st (bprd-owed-q)) (ck (bprd-owed-ck)))))
  :mutations ((reopens-unseeded
               (:conclusion (let* ((unseeded-event (fn-bpnr-recover-auto-event fresh nil :ready nil plan))
        (answer (fn-bpnj-step fresh (append (fn-bprpf-admit-recovery unseeded-event profile) (list domain)))))
(and (equal (car (car (fn-bpnf-answer-effects answer))) :restart-ready)
        (equal (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
        (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (fn-bpnf-answer-state answer)))
               (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
        (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                (fn-bpn-lifecycle-recovery-from nil nil (fn-bpnr-plan-start-token plan))
                (fn-bpnf-base (fn-bpnf-answer-state answer))) t))))
               ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
                (profile '(8 1048576 65538 1048576)) (domain '(:same (7 7 7 7))))
               :fault "omitting fn-bpnr-seed-state loses the owed job in fn-bpnj-step's answer")))

;; Implementation mutation, not a changed conclusion.  These are the host
;; open's ACL2 calls: construct a fresh foundation, seed from the selected
;; checkpoint, build/profile-admit the recovery event, append the clock-domain
;; evidence, and drive fn-bpnj-step.  The mutant omits precisely the seed call.
(defun bprr-open (st plan profile domain)
  (let* ((fresh (fn-bpnr-open-fresh st))
         (seeded (fn-bpnr-seed-state fresh plan))
         (event (fn-bpnr-recover-auto-event seeded nil :ready nil plan)))
    (fn-bpnj-step seeded
     (append (fn-bprpf-admit-recovery event profile) (list domain)))))
(defun bprr-mutant-open-without-seed (st plan profile domain)
  (let* ((fresh (fn-bpnr-open-fresh st))
         (seeded fresh)
         (event (fn-bpnr-recover-auto-event seeded nil :ready nil plan)))
    (fn-bpnj-step seeded
     (append (fn-bprpf-admit-recovery event profile) (list domain)))))
(defun bprr-open-keeps-owed-work-p (answer st plan)
  (and (equal (car (car (fn-bpnf-answer-effects answer))) :restart-ready)
       (equal (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnf-answer-state answer)))
              (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
       (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (fn-bpnf-answer-state answer)))
              (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
       (equal (fn-bpn-host-lifecycle-recovery-agrees-p
               (fn-bpn-lifecycle-recovery-from nil nil (fn-bpnr-plan-start-token plan))
               (fn-bpnf-base (fn-bpnf-answer-state answer))) t)))
(defun bprr-traced-plan ()
  (fn-bpnr-published-plan (bprd-traced-q) 1 (bprd-traced-ck)))
(assert-event
 (let* ((st (bprd-traced-q)) (plan (bprr-traced-plan))
        (good (bprr-open st plan '(8 1048576 65538 1048576) '(:same (7 7 7 7))))
        (bad (bprr-mutant-open-without-seed
              st plan '(8 1048576 65538 1048576) '(:same (7 7 7 7)))))
   (and (equal (car plan) :selected)
        (equal (len (fn-bpn-machine-state-jobs (fn-bpnf-base st))) 1)
        (bprr-open-keeps-owed-work-p good st plan)
        (equal (car (car (fn-bpnf-answer-effects bad))) :restart-ready)
        (null (fn-bpn-machine-state-jobs (fn-bpnf-base (fn-bpnf-answer-state bad))))
        (equal (fn-bpn-machine-state-next-token
                (fn-bpnf-base (fn-bpnf-answer-state bad))) 0))))
(must-fail-checked
 (assert-event
  (bprr-open-keeps-owed-work-p
   (bprr-mutant-open-without-seed (bprd-traced-q) (bprr-traced-plan)
                                '(8 1048576 65538 1048576) '(:same (7 7 7 7)))
   (bprd-traced-q) (bprr-traced-plan))))

;; PREMISE-EXCESS-D: the clock-domain premise's host establishment.
(defconst *bprr-boot*
  '(48 49 50 51 52 53 54 55 45 56 57 97 98 45 99 100 101 102 45
    48 49 50 51 45 52 53 54 55 56 57 97 98 99 100 101 102))
(defteeth fn-bpnp-hosted-recovery-admits-the-same-or-a-fresh-domain
  :claim (let ((plan (fn-bpnf-clock-domain-plan saved present observed legacy lock final-absent))
               (event (fn-bprpf-admit-recovery
                       (fn-bpnr-recover-auto-event st records sequence rows gplan) profile)))
           (((admitted (or (equal (fn-bpnf-clock-domain-plan-status plan) :same)
                           (and (equal (fn-bpnf-clock-domain-plan-status plan) :initialize)
                                (null records)
                                (equal (len rows) 0)))))
            (fn-bpnp-clock-domain-admitsp (append event (list plan)))))
  :subject fn-bpnf-clock-domain-plan
  :witness ((saved (fn-bpcd-frame *bprr-boot*)) (present t)
            (observed (append *bprr-boot* '(10))) (legacy nil) (lock t)
            (final-absent nil) (st nil) (records nil) (sequence nil)
            (rows nil) (gplan nil) (profile nil))
  :breaks ((admitted ((saved nil) (present nil)
                      (observed (append *bprr-boot* '(10))) (legacy nil) (lock nil)
                      (final-absent t) (st nil) (records nil) (sequence nil)
                      (rows nil) (gplan nil) (profile nil))))
  :mutations ((initializes-over-records
               (:hypothesis admitted
                (or (equal (fn-bpnf-clock-domain-plan-status plan) :same)
                    (equal (fn-bpnf-clock-domain-plan-status plan) :initialize)))
               ((saved nil) (present nil) (observed (append *bprr-boot* '(10)))
                (legacy nil) (lock t) (final-absent t) (st nil)
                (records '(:lifecycle-record)) (sequence nil) (rows nil)
                (gplan nil) (profile nil))
               :fault "a fresh domain initialized over recovered lifecycle records")))

;; PREMISE-EXCESS-D: the replay premise as an invariant of the host's state.
;; The open establishes it; every fn-bpnj-step answer preserves it.
(defteeth fn-bpnr-open-is-replay-ready
  :claim (let ((st (fn-bpnr-seed-state (fn-bpnf-initial-state config max-held max-octets) plan)))
           (((opened st))
            (fn-bpnr-replay-readyp st)))
  :subject fn-bpnr-seed-state
  :witness ((config *bpcx-config*) (max-held 8) (max-octets 1048576)
            (plan (bprr-traced-plan)))
  :breaks ((opened ((config nil) (max-held 8) (max-octets 1048576)
                    (plan (bprr-traced-plan)))))
  :mutations (:not-applicable "the one hypothesis is that the open produced a state; nothing weaker is a claim about one"))

(defun bprr-pending-store-st ()
  (update-nth 6 (fn-bpnf-operation 0 0 :store nil :pending) (bprd-trace-fresh)))
(defteeth fn-bpnj-step-preserves-replay-readiness
  :claim (((ready (fn-bpnr-replay-readyp st)))
          (fn-bpnr-replay-readyp (fn-bpnf-answer-state (fn-bpnj-step st event))))
  :subject fn-bpnj-step
  :witness ((st (bprd-traced-q)) (event (list :rotate 1 (bprd-traced-ck))))
  :breaks ((ready ((st (update-nth 10 0 (bprd-owed-q)))
                   (event '(:base (:forward-result nil :accepted))))))
  :mutations ((issued-unfenced
               (:hypothesis ready
                (and (natp (fn-bpnf-next-op st))
                     (implies (equal (fn-bpnf-next-op st) 0)
                              (implies (fn-frame-natp (+ 1 (fn-bpnf-epoch st)))
                                       (fn-bpnr-own-replayp st)))))
               ((st (bprr-pending-store-st)) (event '(:persist-result 0 0 :durable)))
               :fault "an operation pending at counter zero settles held rows no recovery validated")))
