; Executed-trace obligations for B3's keyed-mutation fixture with row reuse. Every
; epoch initializes/adopts the real core and runs the real dispatch/harvester
; and simulated adapter. This is not a theorem for arbitrary host adapters.
; Recovery is the B3 image stand-in; the epoch excludes recovery transitions
; until its final death. Evidence comes from outbox/FIFO/visibility boundaries,
; never cb-deps-ok/cb-log-ok/cb-fence-ok. Owed statements are NOT proofs.
(in-package "ACL2")
(include-book "executor")
(include-book "../sim/sim")
(include-book "../sim/commit-history")
(include-book "owed")

(fn2-cm-defreaders fn2-commit-proof-admitted fn2-commit-proof-events
 fn2-commit-proof-recovered fn2-commit-proof-classification
 fn2-commit-proof-stable fn2-commit-proof-saw-uncertain fn2-commit-proof-acks
 fn2-commit-proof-replies fn2-commit-proof-fresh)
(fn2-cm-defreaders fn2-commit-proof-tag fn2-commit-proof-arg
 fn2-commit-proof-fault fn2-commit-proof-word)

(fn2-cm-defreaders fn2-commit-proof-start-tag fn2-commit-proof-start-slot
 fn2-commit-proof-start-members fn2-commit-proof-start-key fn2-commit-proof-start-mode)

; Preserve actual replies by immutable batch, independently of HISTORY's event
; projection. A reused row resetting its counters cannot erase accepted work.
(defun fn2-commit-proof-observe-replies (views replies)
 (declare (xargs :verify-guards nil))
 (if (atom views) replies
  (let* ((view (car views)) (batch (fn2-b-visible-batch view))
         (count (fn2-b-visible-acks view))
         (replies (if (and (posp batch) (posp count))
                      (put-assoc-equal batch (max count (nfix (cdr (assoc-equal batch replies)))) replies)
                    replies)))
   (fn2-commit-proof-observe-replies (cdr views) replies))))

(defun fn2-commit-proof-preservedp (before after)
 (declare (xargs :verify-guards nil))
 (if (atom before) t
  (and (or (not (equal (fn2-b-visible-phase (car before)) *fn2-commit-state-uncertain*))
           (equal (fn2-b-visible-phase (car after)) *fn2-commit-state-uncertain*))
       (fn2-commit-proof-preservedp (cdr before) (cdr after)))))
(defun fn2-commit-proof-uncertainp (views)
 (declare (xargs :verify-guards nil))
 (if (atom views) nil
  (or (equal (fn2-b-visible-phase (car views)) *fn2-commit-state-uncertain*)
      (fn2-commit-proof-uncertainp (cdr views)))))
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
           ; Deliberately bypass phase dispatch, but pass the actual row snapshot
           ; through the same scalar callback boundary as generated dispatch.
           (mv-let (row-phase row-generation row-principal-slot row-account-ref
                    row-ready-prev row-ready-next row-wait-reason row-deadline
                    row-pending row-stopped row-pool-slot row-pool-gen row-batch-no
                    row-member-count row-first-key row-partner row-cb-mode
                    row-cb-stage row-cb-cursor row-cb-issued row-cb-done row-cb-bytes
                    row-cb-failed row-outcome row-cb-reason row-cb-fence-live
                    row-cb-fence-ok row-cb-deps-ok row-cb-log-ok row-cb-published
                    row-cb-acks row-cb-seal-len)
            (fn2-commit-snapshot id fn2-core)
            (fn2-commit-notify id 4
             row-phase row-generation row-principal-slot row-account-ref
             row-ready-prev row-ready-next row-wait-reason row-deadline
             row-pending row-stopped row-pool-slot row-pool-gen row-batch-no
             row-member-count row-first-key row-partner row-cb-mode
             row-cb-stage row-cb-cursor row-cb-issued row-cb-done row-cb-bytes
             row-cb-failed row-outcome row-cb-reason row-cb-fence-live
             row-cb-fence-ok row-cb-deps-ok row-cb-log-ok row-cb-published
             row-cb-acks row-cb-seal-len fn2-core)))))
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

 ; A client may retry an accepted identity: START's real frontier rejects it
; without mutation. Reusing an identity after a terminal refusal is outside
; the full-HISTORY client input contract. A persistent refusal/idempotency
; ledger is a proposed layer-C integration need; B3 does not implement one.
(defun fn2-commit-ready-operation-freshp (command refused)
 (declare (xargs :verify-guards nil))
 (let ((members (fn2-commit-proof-start-members command))
       (key (fn2-commit-proof-start-key command)))
  (if (and (eq (fn2-commit-proof-tag command) :start)
           (posp members) (<= members 16) (unsigned-byte-p 60 key)
           (unsigned-byte-p 60 (+ key members)))
      (fn2-history-disjointp (fn2-b-member-identities members key) refused) t)))
(defun fn2-commit-terminal-refusals (events refused)
 (declare (xargs :verify-guards nil))
 (if (atom events) refused
  (fn2-commit-terminal-refusals (cdr events)
   (if (eq (fn2-lm-event-tag (car events)) :refuse)
       (cons (fn2-lm-event-argument (car events)) refused) refused))))

; Projection failure is evidence failure, never an admission exception.
(defun fn2-commit-proof-replay (commands turn ids profile admitted fresh refused stable saw replies seen manifests events
                                       fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (if (atom commands)
     (mv (and admitted (null commands)) fresh stable saw replies manifests (reverse events) fn2-core fn2-sim fn2-own)
  (b* ((fresh (and fresh (fn2-commit-ready-operation-freshp (car commands) refused)))
       (before (fn2-b-visibility ids fn2-core))
       ((mv legal extra fn2-core fn2-sim fn2-own)
        (fn2-commit-proof-step (car commands) turn ids profile fn2-core fn2-sim fn2-own))
       (refused (fn2-commit-terminal-refusals extra refused))
       (after (fn2-b-visibility ids fn2-core))
       (events (fn2-b-project-visible before after (append (reverse extra) events)))
       ((mv code seen manifests events &)
        (fn2-b-project-issues (fn2-b-outbox fn2-core) seen manifests events 0 fn2-core)))
   (fn2-commit-proof-replay (cdr commands) (+ 1 (nfix turn)) ids profile
    (and admitted legal) fresh refused (and stable (fn2-commit-proof-preservedp before after))
    (or saw (fn2-commit-proof-uncertainp after)) (fn2-commit-proof-observe-replies after replies) seen manifests (if (eq code :ok) events (cons (list :projection-error code) events))
    fn2-core fn2-sim fn2-own))))

(defun fn2-commit-proof-execute (commands model-profile mode members seed fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((unless (and (fn2-cm-profilep model-profile) (member-equal mode '(0 1))
                    (posp members) (<= members 16) (unsigned-byte-p 32 seed)))
       (mv (list nil nil nil :unknown t nil '(0 0) nil t) fn2-core fn2-sim fn2-own))
      (profile (fn2-b-test-profile *fn2-profile-tiny* mode))
      (fn2-core (fn2-core-init profile fn2-core))
      ((mv ec fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
      (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
      ((mv ca ea & fn2-core) (fn2-b-start a members 1 mode b fn2-core))
      ((mv cb eb & fn2-core) (fn2-b-start b members (+ 1 (nfix members)) mode a fn2-core))
      ; The adapter enables lying-flush semantics only in :broad. Keep this
      ; choice tied to the named environment premise as well as FAULTP.
      (fn2-sim (fn2-sim-init seed (if (fn2-cm-persistence-fence model-profile) :none :broad)
                            "B3-keystone" profile fn2-sim))
      (fn2-own (fn2-own-init profile fn2-own))
      (admitted (and (fn2-cm-profilep model-profile) (eq ec :ok) (eq ca :ok) (eq cb :ok)))
      ((mv admitted fresh stable saw replies manifests events fn2-core fn2-sim fn2-own)
       (fn2-commit-proof-replay commands 0 (list a b) model-profile admitted t nil t nil nil nil nil (reverse (append ea eb))
                                fn2-core fn2-sim fn2-own))
      (acks (list (fn2-machine-cb-acks a fn2-core) (fn2-machine-cb-acks b fn2-core)))
      ((mv fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own))
      ((mv classification recovered evidence fn2-core) (fn2-b-recover manifests fn2-core fn2-sim)))
  (mv (list admitted (append events (list '(:crash)) evidence) recovered classification stable saw acks replies fresh)
      fn2-core fn2-sim fn2-own)))

(defun fn2-commit-proof-run (commands profile mode members seed)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core)
   (with-local-stobj fn2-sim
    (mv-let (result fn2-core fn2-sim)
     (with-local-stobj fn2-own
      (mv-let (result fn2-core fn2-sim fn2-own)
       (fn2-commit-proof-execute commands profile mode members seed fn2-core fn2-sim fn2-own)
       (mv result fn2-core fn2-sim)))
     (mv result fn2-core))) result)))

 ; The physical durability obligation does not claim client refusal consistency.
; Remove ONLY terminal refusal events; preserve every request, issued identity,
; completion/count, uncertainty, fence, publication, reply and recovery fact.
; Full HISTORY consumes the original unfiltered events.
(defun fn2-commit-physical-events (events)
 (declare (xargs :verify-guards nil))
 (if (atom events) events
  (if (eq (fn2-lm-event-tag (car events)) :refuse)
      (fn2-commit-physical-events (cdr events))
   (cons (car events) (fn2-commit-physical-events (cdr events))))))

(defun fn2-commit-reply-countsp (replies submitted)
 (declare (xargs :verify-guards nil))
 (if (atom replies) t
  (and (posp (cdar replies))
       (<= (cdar replies)
           (len (fn2-lm-batch-records (assoc-equal (caar replies) submitted))))
       (fn2-commit-reply-countsp (cdr replies) submitted))))

; Actual per-batch reply observations determine the obligation; neither row
; reuse nor a failed evidence projection can erase an accepted batch.
(defun fn2-commit-ack-evidencep (result)
 (declare (xargs :verify-guards nil))
 (let ((accepted (strip-cars (fn2-commit-proof-replies result))))
  (if (not accepted) t
   (mv-let (code trace) (fn2-history-translate (fn2-commit-physical-events (fn2-commit-proof-events result)))
    (let ((s (fn2-lm-trace-state trace)))
     (and (eq code :ok)
          (fn2-commit-reply-countsp (fn2-commit-proof-replies result) (fn2-lm-state-submitted s))
          (fn2-lm-prefixp (fn2-commit-proof-recovered result) (fn2-lm-state-submitted s))
          (subsetp-equal accepted (fn2-lm-state-acknowledged s))
          (subsetp-equal accepted (fn2-lm-state-completed s))
          (subsetp-equal accepted (fn2-lm-state-fenced s))
          (fn2-lm-acknowledged-in-historyp accepted (fn2-commit-proof-recovered result))))))))
(defun fn2-commit-ack-hyps (profile result)
 (declare (xargs :verify-guards nil))
 (and (fn2-cm-profilep profile) (fn2-cm-persistence-fence profile)
      (fn2-commit-proof-admitted result)))

(defthm-owed fn2-commit-ack-implies-durable (commands profile mode members seed)
 (let ((result (fn2-commit-proof-run commands profile mode members seed)))
  (implies (fn2-commit-ack-hyps profile result) (fn2-commit-ack-evidencep result)))
 :teeth (fn2-commit-proof-ack-baseline fn2-commit-proof-ack-fua
         fn2-commit-proof-fence-removal fn2-commit-proof-follower-first
         fn2-commit-proof-reuse-baseline fn2-commit-proof-reuse-fua
         fn2-commit-proof-duplicate-start fn2-commit-proof-refused-retry-contract)
 :doc "Actual B3 replay on the B-owned tiny profile, including explicit starts and reused rows under supported adapter faults and fixed test transactions; exact write identities/completions, baseline or preflush/FUA boundary, and required durable-image prefix. Only terminal :refuse events are removed for this physical claim; full HISTORY retains them. No flag premises; a persistent client refusal/idempotency ledger is a proposed layer-C integration need, and B5 discovery and arbitrary host adapters remain outside scope.")
(defthm-owed fn2-commit-uncertain-persists (commands profile mode members seed)
 (let ((result (fn2-commit-proof-run commands profile mode members seed)))
  (implies (fn2-commit-proof-admitted result) (fn2-commit-proof-stable result)))
 :teeth (fn2-commit-proof-timeout-baseline fn2-commit-proof-timeout-fua
         fn2-commit-proof-dispatch-removal fn2-commit-proof-uncertain-rearm)
 :doc "Every supported replay transition preserves uncertain once entered; final process death/recovery is explicitly outside the epoch. No recovery transition is implemented by this claim.")
