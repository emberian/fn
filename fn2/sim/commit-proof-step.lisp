; The real B3 stepper over the assembled core, the simulated adapter and OWN:
; one command (run, start, harvest, take, timeout, complete, or an :auto
; choice) per call. The scenario driver and the owed keystone teeth both
; drive it, so a scenario case and a tooth exercise the same transitions.
; Test evidence only; the served machine never calls these functions.
(in-package "ACL2")
(include-book "../books/executor")
(include-book "sim")
(include-book "check-recovery")
(fn2-book-layer :b)

(fn2-cm-defreaders fn2-commit-proof-tag fn2-commit-proof-arg
 fn2-commit-proof-fault fn2-commit-proof-word)

(fn2-cm-defreaders fn2-commit-proof-start-tag fn2-commit-proof-start-slot
 fn2-commit-proof-start-members fn2-commit-proof-start-key fn2-commit-proof-start-mode)

(defun fn2-commit-proof-flight (left fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)))
 (if (zp left) nil
  (if (equal (fn2-sim-active (- left 1) fn2-sim) 1) (- left 1)
   (fn2-commit-proof-flight (- left 1) fn2-sim))))

; A-PERSISTENCE-FENCE is linked to the environment, not an unused flag:
; lying flush (10) is an admitted adapter behavior ONLY without that premise.
; These epochs exclude later at-rest corruption and forged delivery events.
(defun fn2-commit-proof-faultp (fault profile)
 (declare (xargs :verify-guards nil))
 (or (member-equal fault '(11 12 14 23 24 26))
     (and (equal fault 10) (not (fn2-cm-persistence-fence profile)))))
(defun fn2-commit-proof-auto (command turn ids fn2-core fn2-sim)
 (declare (xargs :stobjs (fn2-core fn2-sim) :verify-guards nil))
 (let ((flight (fn2-commit-proof-flight (fn2-sim-rows fn2-sim) fn2-sim)))
  (cond ((and (eq (fn2-commit-proof-tag command) :auto-slot)
              (not (member-equal (fn2-commit-proof-arg command) '(0 1)))) '(:invalid))
        ((fn2-b-next-result fn2-core) '(:harvest))
        ((consp (fn2-b-outbox fn2-core)) '(:take))
        (flight
         (if (and (eq (fn2-commit-proof-tag command) :auto-timeout)
                  (= (fn2-sim-kind flight fn2-sim) *fn2-action-fence*)
                  (not (= (fn2-machine-phase (fn2-sim-owner-slot flight fn2-sim) fn2-core)
                          *fn2-commit-state-uncertain*)))
             (list :timeout (fn2-sim-owner-slot flight fn2-sim))
           (list :complete flight (if (eq (fn2-commit-proof-tag command) :auto-timeout)
                                     26 (if (eq (fn2-commit-proof-tag command) :auto-slot)
                                          (fn2-commit-proof-fault command) (fn2-commit-proof-arg command))) 1)))
        ((eq (fn2-commit-proof-tag command) :auto-slot)
         (list :run (fn2-commit-proof-arg command)))
        ((eq (fn2-commit-proof-tag command) :auto-follower-first)
         (let ((leader (fn2-machine-phase (car ids) fn2-core))
               (follower (fn2-machine-phase (cadr ids) fn2-core)))
          (list :run
           (cond ((and (member-equal leader (list *fn2-commit-state-collect* *fn2-commit-state-seal*))
                       (< (fn2-machine-cb-stage (car ids) fn2-core) 18)) 0)
                 ((and (= leader *fn2-commit-state-seal*)
                       (= (fn2-machine-cb-stage (car ids) fn2-core) 18)
                       (or (member-equal follower (list *fn2-commit-state-collect* *fn2-commit-state-seal*))
                           (and (= follower *fn2-commit-state-dependencies*)
                                (= (fn2-machine-cb-issued (cadr ids) fn2-core) 0)))) 1)
                 (t (mod (nfix turn) 2))))))
        (t (list :run (mod (nfix turn) 2))))))

(defun fn2-commit-proof-step (command turn ids profile fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* ((command (if (member-eq (fn2-commit-proof-tag command) '(:auto :auto-timeout :auto-follower-first :auto-slot))
                   (fn2-commit-proof-auto command turn ids fn2-core fn2-sim) command))
      (tag (fn2-commit-proof-tag command)) (arg (fn2-commit-proof-arg command))
      (id (nth (nfix arg) ids)))
  (cond
   ((and (member-eq tag '(:run :bypass-notify)) (member-equal arg '(0 1)))
    (b* (((mv & & & & fn2-core)
          (if (eq tag :run) (fn2-commit-run id 4 fn2-core)
           ; Deliberately bypass phase dispatch, but pass the actual row fields
           ; the callback reads (its row bindings) through the same scalar
           ; boundary as generated dispatch.
           (fn2-commit-notify id 4
             (fn2-commit-row-batch-no id fn2-core) (fn2-commit-row-member-count id fn2-core)
             (fn2-commit-row-partner id fn2-core) (fn2-commit-row-cb-stage id fn2-core)
             (fn2-commit-row-cb-acks id fn2-core) fn2-core))))
     (mv (eq tag :run) nil fn2-core fn2-sim fn2-own)))
   ((and (eq tag :start) (equal (len command) 5) (member-equal arg '(0 1)))
    (b* (((mv & events & fn2-core)
          (fn2-b-start id (fn2-commit-proof-start-members command)
           (fn2-commit-proof-start-key command) (fn2-commit-proof-start-mode command)
           (nth (- 1 arg) ids) fn2-core)))
     ; Successful admission and actual refusals are legal; evidence records
     ; requested operation identities independently of the resulting row.
     (mv t events fn2-core fn2-sim fn2-own)))
   ((eq tag :harvest)
    (let ((event (fn2-b-next-result fn2-core)))
     (b* (((mv & & & & & fn2-core) (fn2-exec-harvest fn2-core)))
      (mv t (if event (list event) nil) fn2-core fn2-sim fn2-own))))
   ((eq tag :take)
    (b* (((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own)))
     (mv t nil fn2-core fn2-sim fn2-own)))
   ((and (eq tag :timeout) (member-equal arg ids))
    (b* ((batch (fn2-machine-batch-no arg fn2-core))
         (live (= (fn2-machine-cb-fence-live arg fn2-core) 1))
         (tick (+ 1 (fn2-machine-deadline arg fn2-core)))
         (fn2-core (fn2-sim-post-clock tick tick fn2-core))
         ((mv & & & & & fn2-core) (fn2-exec-mailbox fn2-core))
         ((mv & & & & fn2-core) (fn2-commit-run arg 4 fn2-core))
         (expired (and live (= (fn2-machine-cb-fence-live arg fn2-core) 1)
                       (= (fn2-machine-phase arg fn2-core) *fn2-commit-state-uncertain*))))
     (mv expired (if expired (list (list :timeout batch)) nil) fn2-core fn2-sim fn2-own)))
   ((and (eq tag :complete) (natp arg) (< arg (fn2-sim-rows fn2-sim))
         (= (fn2-sim-active arg fn2-sim) 1)
         (fn2-commit-proof-faultp (fn2-commit-proof-fault command) profile)
         (unsigned-byte-p 32 (fn2-commit-proof-word command)))
    (let* ((fault (fn2-commit-proof-fault command)) (word (fn2-commit-proof-word command))
           (fn2-sim (fn2-sim-clock (fn2-sim-due arg fn2-sim) 26 fn2-sim))
           (fn2-sim (fn2-sim-environment arg fault word fn2-sim)))
     (b* (((mv & fn2-core fn2-sim fn2-own) (fn2-sim-complete arg fault word fn2-core fn2-sim fn2-own)))
      (mv t nil fn2-core fn2-sim fn2-own))))
   (t (mv nil nil fn2-core fn2-sim fn2-own)))))
