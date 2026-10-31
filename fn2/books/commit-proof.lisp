; Executed-trace obligations for B3's keyed-mutation fixture with row reuse. Every
; epoch initializes/adopts the real core and runs the real dispatch/harvester
; and simulated adapter. This is not a theorem for arbitrary host adapters.
; Recovery is B5's machine on the post-death core; the epoch excludes recovery
; transitions until its final death. Evidence comes from outbox/FIFO/visibility boundaries,
; never cb-deps-ok/cb-log-ok/cb-fence-ok. Owed statements are NOT proofs.
(in-package "ACL2")
(include-book "../sim/commit-proof-step")
(include-book "owed")
(fn2-book-layer :b)

(fn2-cm-defreaders fn2-commit-proof-admitted fn2-commit-proof-events
 fn2-commit-proof-recovered fn2-commit-proof-classification
 fn2-commit-proof-stable fn2-commit-proof-saw-uncertain fn2-commit-proof-acks
 fn2-commit-proof-replies fn2-commit-proof-fresh fn2-commit-proof-outcome)

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

; FAULTS act on the durable image after the final death (B5's scenarios 15/16).
(defun fn2-commit-proof-execute (commands model-profile mode members seed faults fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((unless (and (fn2-cm-profilep model-profile) (member-equal mode '(0 1))
                    (posp members) (<= members 16) (unsigned-byte-p 32 seed)))
       (mv (list nil nil nil :unknown t nil '(0 0) nil t :none) fn2-core fn2-sim fn2-own))
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
      ; A recovery that does not finish recovers nothing: never an admission exception.
      ((mv rstatus classification outcome recovered events fn2-core fn2-sim fn2-own)
       (fn2-b-crash-recover profile model-profile faults manifests events *fn2-fault-none* 0 fn2-core fn2-sim fn2-own)))
  (mv (list admitted events (if (eq rstatus :done) recovered nil) classification stable saw acks replies fresh outcome)
      fn2-core fn2-sim fn2-own)))

(defun fn2-commit-proof-run-faults (commands profile mode members seed faults)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core)
   (with-local-stobj fn2-sim
    (mv-let (result fn2-core fn2-sim)
     (with-local-stobj fn2-own
      (mv-let (result fn2-core fn2-sim fn2-own)
       (fn2-commit-proof-execute commands profile mode members seed faults fn2-core fn2-sim fn2-own)
       (mv result fn2-core fn2-sim)))
     (mv result fn2-core))) result)))
(defun fn2-commit-proof-run (commands profile mode members seed)
 (declare (xargs :verify-guards nil))
 (fn2-commit-proof-run-faults commands profile mode members seed nil))

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
 :schema :crash :doc "Actual B3 replay on the B-owned tiny profile, including explicit starts and reused rows under supported adapter faults and fixed test transactions; exact write identities/completions, baseline or preflush/FUA boundary, and required durable-image prefix. Only terminal :refuse events are removed for this physical claim; full HISTORY retains them. No flag premises; a persistent client refusal/idempotency ledger is a proposed layer-C integration need, and B5 discovery and arbitrary host adapters remain outside scope.")
(defthm-owed fn2-commit-uncertain-persists (commands profile mode members seed)
 (let ((result (fn2-commit-proof-run commands profile mode members seed)))
  (implies (fn2-commit-proof-admitted result) (fn2-commit-proof-stable result)))
 :teeth (fn2-commit-proof-timeout-baseline fn2-commit-proof-timeout-fua
         fn2-commit-proof-dispatch-removal fn2-commit-proof-uncertain-rearm)
 :schema :invariant :doc "Every supported replay transition preserves uncertain once entered; final process death/recovery is explicitly outside the epoch. No recovery transition is implemented by this claim.")

; ---------------------------------------------------------------------------
; B-S2's keystones (b-durability.md section 11b): the transaction member.
; WORKSPACES holds one record list per member, each record (kind . body
; octets); member I is owned by (9, 3+I, 5). COMMANDS are the stepper's
; commands plus (:admit I), which fills member I's workspace and admits it.
; PLANT is a tooth's mutation and nil in every statement:
;  :refuse-written  member 0's settled outcome is set :refused once its
;                   batch has issued a journal write;
;  :flip            one body octet of member 0's workspace changes after
;                   its admission (D's read-only promise broken);
;  :leak            a refused admission reserves a settled row.
; Evidence is read at the outbox and visibility boundaries and from the
; sealed pool image, never from the row's flags.
(defun fn2-ctp-encode (records)
 (declare (xargs :verify-guards nil))
 (if (atom records) nil
  (append (fn2-layout-octets *fn2-format-txn-record* (list (caar records) (len (cdar records))))
          (cdar records) (fn2-ctp-encode (cdr records)))))
(defun fn2-ctp-fill (bytes slot gen at oslot fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (len bytes)))
 (if (atom bytes) (mv :ok fn2-core)
  (mv-let (code fn2-core) (fn2-core-write slot gen at (car bytes) 9 oslot 5 fn2-core)
   (if (not (eq code :ok)) (mv code fn2-core)
    (fn2-ctp-fill (cdr bytes) slot gen (+ 1 at) oslot fn2-core)))))
(defun fn2-ctp-member-row (r fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-commit-member (fn2-core-commit-members fn2-core))) (row)
  (if (< (nfix r) (fn2-commit-member-rows fn2-commit-member))
      (list (fn2-commit-member-kind r fn2-commit-member) (fn2-commit-member-slot r fn2-commit-member)
            (fn2-commit-member-gen r fn2-commit-member) (fn2-commit-member-len r fn2-commit-member)
            (fn2-commit-member-okind r fn2-commit-member) (fn2-commit-member-oslot r fn2-commit-member)
            (fn2-commit-member-ogen r fn2-commit-member) (fn2-commit-member-event r fn2-commit-member)
            (fn2-commit-member-settled r fn2-commit-member))
    nil)
  row))
(defun fn2-ctp-settled-row (r fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-commit-settled (fn2-core-commit-settled fn2-core))) (row)
  (if (< (nfix r) (fn2-commit-settled-rows fn2-commit-settled))
      (list (fn2-commit-settled-state r fn2-commit-settled) (fn2-commit-settled-okind r fn2-commit-settled)
            (fn2-commit-settled-oslot r fn2-commit-settled) (fn2-commit-settled-ogen r fn2-commit-settled))
    nil)
  row))
(defun fn2-ctp-rows (r n settled fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
 (if (zp n) nil
  (cons (if settled (fn2-ctp-settled-row r fn2-core) (fn2-ctp-member-row r fn2-core))
        (fn2-ctp-rows (+ 1 (nfix r)) (- n 1) settled fn2-core))))
(defun fn2-ctp-machine (id fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (list (fn2-machine-phase id fn2-core) (fn2-machine-batch-no id fn2-core)
       (fn2-machine-member-count id fn2-core) (fn2-machine-first-key id fn2-core)
       (fn2-machine-rec-bytes id fn2-core) (fn2-machine-cb-open id fn2-core)))
; Everything an admission may change: the member and settled tables, the two
; rows' admission columns, the frontier and the stop reason.
(defun fn2-ctp-view (ids fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & key & &) (fn2-commit-frontier fn2-core)))
  (list (fn2-ctp-rows 0 (* 2 *fn2-commit-members-per-batch*) nil fn2-core)
        (fn2-ctp-rows 0 (stobj-let ((fn2-commit-settled (fn2-core-commit-settled fn2-core))) (n)
                          (fn2-commit-settled-rows fn2-commit-settled) n) t fn2-core)
        (fn2-ctp-machine (car ids) fn2-core) (fn2-ctp-machine (cadr ids) fn2-core)
        key (fn2-core-stop-reason fn2-core))))
(defun fn2-ctp-diffs (a b)
 (declare (xargs :verify-guards nil))
 (cond ((or (atom a) (atom b)) nil)
       ((equal (car a) (car b)) (fn2-ctp-diffs (cdr a) (cdr b)))
       (t (cons (car b) (fn2-ctp-diffs (cdr a) (cdr b))))))
; Admission is total: :ok changes exactly one member row, and that row holds
; the admitted workspace and its owner; any other answer changes nothing.
(defun fn2-ctp-totalp (code slot gen len oslot before after)
 (declare (xargs :verify-guards nil))
 (if (eq code :ok)
     (let ((d (fn2-ctp-diffs (car before) (car after))))
      (and (equal (len d) 1)
           (equal (take 7 (car d))
                  (list *fn2-commit-member-kind-txn* slot gen len 9 oslot 5))))
   (and (member-eq code '(:exhausted :admission)) (equal before after))))
(defun fn2-ctp-admit (i workspaces plant ids fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((records (nth i workspaces)) (bytes (fn2-ctp-encode records)) (oslot (+ 3 (nfix i)))
      ((mv rc slot gen fn2-core) (fn2-core-reserve (fn2-scribe-window-class fn2-core) 9 oslot 5 fn2-core))
      ; No workspace could be written (the fixture's own pool ran out): no
      ; admission happened, so there is nothing to judge.
      ((unless (eq rc :ok)) (mv (list i :no-workspace 0 0 t nil) fn2-core))
      ((mv fc fn2-core) (fn2-ctp-fill bytes slot gen 0 oslot fn2-core))
      ((unless (eq fc :ok)) (mv (list i :no-workspace 0 0 t nil) fn2-core))
      (before (fn2-ctp-view ids fn2-core))
      ((mv code batch event fn2-core) (fn2-commit-admit-txn slot gen (len bytes) 9 oslot 5 fn2-core))
      ((mv & fn2-core)
       (cond ((and (eq plant :leak) (not (eq code :ok)))
              (stobj-let ((fn2-commit-settled (fn2-core-commit-settled fn2-core))) (c s fn2-commit-settled)
               (fn2-cs-reserve 9 oslot 5 fn2-commit-settled) (mv c fn2-core)))
             ((and (eq plant :flip) (eq code :ok) (equal i 0) (consp bytes))
              (fn2-core-write slot gen (- (len bytes) 1) (logxor 1 (car (last bytes))) 9 oslot 5 fn2-core))
             (t (mv :ok fn2-core))))
      (after (fn2-ctp-view ids fn2-core)))
  (mv (list i code batch event (fn2-ctp-totalp code slot gen (len bytes) oslot before after) records)
      fn2-core)))
; Journal writes per batch: each new write descriptor of a commit row counts
; for the row's batch. The batch's first journal write (its dependency unit,
; then records and seal) is the point after which it can no longer be
; refused (cb-wrote; b-durability.md 11b S1).
(defun fn2-ctp-count (batch counts)
 (declare (xargs :verify-guards nil))
 (let ((c (assoc-equal batch counts))) (put-assoc-equal batch (+ 1 (nfix (cdr c))) counts)))
(defun fn2-ctp-issues (descriptors seen counts fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom descriptors) (mv seen counts)
  (let ((d (car descriptors)))
   (if (or (member-equal (fn2-b-descriptor-token d) seen)
           (not (equal (fn2-b-descriptor-owner-kind d) *fn2-commit-kind*))
           (not (equal (fn2-b-descriptor-kind d) *fn2-action-write*)))
       (fn2-ctp-issues (cdr descriptors) seen counts fn2-core)
    (fn2-ctp-issues (cdr descriptors) (cons (fn2-b-descriptor-token d) seen)
     (fn2-ctp-count (fn2-machine-batch-no (fn2-b-descriptor-owner d) fn2-core) counts) fn2-core)))))
(defun fn2-ctp-published (rows published)
 (declare (xargs :verify-guards nil))
 (if (atom rows) published
  (fn2-ctp-published (cdr rows)
   (if (and (equal (fn2-b-visible-published (car rows)) 1)
            (not (member-equal (fn2-b-visible-batch (car rows)) published)))
       (cons (fn2-b-visible-batch (car rows)) published) published))))
; The sealed records frame of each batch, read once its seal is done and
; before its pools are released.
(defun fn2-ctp-capture (ids images fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom ids) images
  (let* ((id (car ids)) (batch (fn2-machine-batch-no id fn2-core)) (phase (fn2-machine-phase id fn2-core)))
   (fn2-ctp-capture (cdr ids)
    (if (and (posp batch) (not (assoc-equal batch images))
             (member-equal phase (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*
                                       *fn2-commit-state-fence* *fn2-commit-state-durable*)))
        (mv-let (ic image) (fn2-b-pool-image id 1 fn2-core)
         (mv-let (pc payload) (fn2-b-frame-payload image *frame-kind-records*)
          (acons batch (if (and (eq ic :ok) (eq pc :ok)) payload :unreadable) images)))
      images)
    fn2-core))))
(defun fn2-ctp-plant-refusal (counts admissions fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let ((a0 (assoc-equal 0 admissions)))
  (if (not (and a0 (eq (nth 1 a0) :ok) (<= 1 (nfix (cdr (assoc-equal (nth 2 a0) counts))))))
      fn2-core
   (stobj-let ((fn2-commit-settled (fn2-core-commit-settled fn2-core))) (fn2-commit-settled)
    (mv-let (code r) (fn2-cs-find-owner 0 9 3 5 nil fn2-commit-settled)
     (if (and (eq code :ok) (< r (fn2-commit-settled-rows fn2-commit-settled)))
         (fn2-commit-settled-set-outcome r *fn2-commit-outcome-refused* fn2-commit-settled)
       fn2-commit-settled))
    fn2-core))))
(defun fn2-ctp-replay (commands turn ids workspaces plant admissions seen counts published images
                       fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (if (atom commands) (mv admissions counts published images fn2-core fn2-sim fn2-own)
  (b* ((command (car commands))
       ((mv admissions fn2-core fn2-sim fn2-own)
        (if (and (eq (car command) :admit) (natp (cadr command)) (< (cadr command) (len workspaces))
                 (not (assoc-equal (cadr command) admissions)))
            (mv-let (a fn2-core) (fn2-ctp-admit (cadr command) workspaces plant ids fn2-core)
             (mv (append admissions (list a)) fn2-core fn2-sim fn2-own))
         (b* (((mv & & fn2-core fn2-sim fn2-own)
               (fn2-commit-proof-step command turn ids (fn2-cm-profile :crash-only t t nil 0 0) fn2-core fn2-sim fn2-own)))
          (mv admissions fn2-core fn2-sim fn2-own))))
       ((mv seen counts) (fn2-ctp-issues (fn2-b-outbox fn2-core) seen counts fn2-core))
       (published (fn2-ctp-published (fn2-b-visibility ids fn2-core) published))
       (images (fn2-ctp-capture ids images fn2-core))
       (fn2-core (if (eq plant :refuse-written) (fn2-ctp-plant-refusal counts admissions fn2-core) fn2-core)))
   (fn2-ctp-replay (cdr commands) (+ 1 (nfix turn)) ids workspaces plant admissions seen counts published images
                   fn2-core fn2-sim fn2-own))))
(defun fn2-ctp-outcomes (admissions fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom admissions) (mv nil fn2-core)
  (b* ((a (car admissions)) (oslot (+ 3 (nfix (car a))))
       ((mv code batch event outcome fn2-core) (fn2-commit-take 9 oslot 5 fn2-core))
       ((mv rest fn2-core) (fn2-ctp-outcomes (cdr admissions) fn2-core)))
   (mv (cons (list (car a) code batch event outcome) rest) fn2-core))))
(defun fn2-commit-txn-proof-execute (workspaces commands mode plant fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((unless (member-equal mode '(0 1))) (mv (list nil nil nil nil nil nil) fn2-core fn2-sim fn2-own))
      ; Room for the members' workspaces beside the two rows' four windows each.
      (profile (fn2-b-test-profile
                (put-assoc-equal :pool-classes
                 (append (fn2-profile-pool-classes *fn2-profile-tiny*) '((24 . 4096))) *fn2-profile-tiny*) mode))
      (fn2-core (fn2-core-init profile fn2-core))
      (fn2-core (fn2-init-executor profile :null nil fn2-core))
      ((mv ec fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (ids (list (fn2-machine-global-id *fn2-commit-kind* 0 profile)
                 (fn2-machine-global-id *fn2-commit-kind* 1 profile)))
      (fn2-sim (fn2-sim-init 1 :none "B-S2-keystone" profile fn2-sim))
      (fn2-own (fn2-own-init profile fn2-own))
      ((mv admissions counts published images fn2-core fn2-sim fn2-own)
       (fn2-ctp-replay commands 0 ids workspaces plant nil nil nil nil nil fn2-core fn2-sim fn2-own))
      ((mv outcomes fn2-core) (fn2-ctp-outcomes admissions fn2-core)))
  (mv (list (eq ec :ok) admissions counts published images outcomes) fn2-core fn2-sim fn2-own)))
(defun fn2-commit-txn-proof-run (workspaces commands mode plant)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core)
   (with-local-stobj fn2-sim
    (mv-let (result fn2-core fn2-sim)
     (with-local-stobj fn2-own
      (mv-let (result fn2-core fn2-sim fn2-own)
       (fn2-commit-txn-proof-execute workspaces commands mode plant fn2-core fn2-sim fn2-own)
       (mv result fn2-core fn2-sim)))
     (mv result fn2-core))) result)))
(fn2-cm-defreaders fn2-ctp-initialized fn2-ctp-admissions fn2-ctp-counts
 fn2-ctp-published-batches fn2-ctp-images fn2-ctp-outcome-list)

; Statement 1: every settled outcome matches its batch's evidence.
(defun fn2-ctp-outcome-okp (o result)
 (declare (xargs :verify-guards nil))
 (let ((writes (nfix (cdr (assoc-equal (nth 2 o) (fn2-ctp-counts result))))))
  (or (not (eq (nth 1 o) :ok))
      (case (nth 4 o)
       (1 (and (member-equal (nth 2 o) (fn2-ctp-published-batches result)) t))
       (2 (<= 1 writes))
       (3 (equal writes 0))
       (otherwise nil)))))
(defun fn2-ctp-outcomes-okp (outcomes result)
 (declare (xargs :verify-guards nil))
 (or (atom outcomes)
     (and (fn2-ctp-outcome-okp (car outcomes) result) (fn2-ctp-outcomes-okp (cdr outcomes) result))))
(defun fn2-commit-txn-outcome-evidencep (result)
 (declare (xargs :verify-guards nil))
 (fn2-ctp-outcomes-okp (fn2-ctp-outcome-list result) result))
; Statement 2: a batch's sealed records frame is its members' admitted
; records in event order, each a record header at the member's event (its
; occurrence the same event) and the body verbatim, and only the frame's
; zero padding after (a record header's schema version is never 0).
(defun fn2-ctp-match-record (record event payload)
 (declare (xargs :verify-guards nil))
 (mv-let (code header rest) (fn2-layout-parse *fn2-format-record-header* payload)
  (let ((body (cdr record)))
   (if (and (eq code :ok)
            (equal (nth *fn2-format-record-header-field-record-kind* header) (car record))
            (equal (nth *fn2-format-record-header-field-event* header) event)
            (equal (nth *fn2-format-record-header-field-occurrence* header) event)
            (<= (len body) (len rest)) (equal (take (len body) rest) body))
       (mv t (nthcdr (len body) rest))
    (mv nil payload)))))
(defun fn2-ctp-match-records (records event payload)
 (declare (xargs :verify-guards nil))
 (if (atom records) (mv t payload)
  (mv-let (ok rest) (fn2-ctp-match-record (car records) event payload)
   (if ok (fn2-ctp-match-records (cdr records) event rest) (mv nil payload)))))
(defun fn2-ctp-batch-members (batch admissions)
 (declare (xargs :verify-guards nil))
 (cond ((atom admissions) nil)
       ((and (eq (nth 1 (car admissions)) :ok) (equal (nth 2 (car admissions)) batch))
        (cons (car admissions) (fn2-ctp-batch-members batch (cdr admissions))))
       (t (fn2-ctp-batch-members batch (cdr admissions)))))
(defun fn2-ctp-zerosp (bytes)
 (declare (xargs :verify-guards nil))
 (or (atom bytes) (and (equal (car bytes) 0) (fn2-ctp-zerosp (cdr bytes)))))
(defun fn2-ctp-match-members (members payload)
 (declare (xargs :verify-guards nil))
 (if (atom members) (fn2-ctp-zerosp payload)
  (mv-let (ok rest) (fn2-ctp-match-records (nth 5 (car members)) (nth 3 (car members)) payload)
   (and ok (fn2-ctp-match-members (cdr members) rest)))))
(defun fn2-ctp-images-okp (images admissions)
 (declare (xargs :verify-guards nil))
 (or (atom images)
     (and (consp (car images)) (listp (cdar images))
          (fn2-ctp-match-members (fn2-ctp-batch-members (caar images) admissions) (cdar images))
          (fn2-ctp-images-okp (cdr images) admissions))))
(defun fn2-commit-txn-records-verbatimp (result)
 (declare (xargs :verify-guards nil))
 (fn2-ctp-images-okp (fn2-ctp-images result) (fn2-ctp-admissions result)))
; Statement 3: every admission is total (fn2-ctp-totalp).
(defun fn2-ctp-admissions-totalp (admissions)
 (declare (xargs :verify-guards nil))
 (or (atom admissions) (and (nth 4 (car admissions)) (fn2-ctp-admissions-totalp (cdr admissions)))))
(defun fn2-commit-txn-admission-totalp (result)
 (declare (xargs :verify-guards nil))
 (fn2-ctp-admissions-totalp (fn2-ctp-admissions result)))

(defthm-owed fn2-commit-txn-outcome-evidence (workspaces commands mode)
 (let ((result (fn2-commit-txn-proof-run workspaces commands mode nil)))
  (implies (fn2-ctp-initialized result) (fn2-commit-txn-outcome-evidencep result)))
 :teeth (fn2-commit-txn-accepted fn2-commit-txn-uncertain fn2-commit-txn-refused
         fn2-commit-txn-refused-after-write)
 :schema :invariant :doc "B-S2's per-member result on the B-owned tiny profile with the simulated adapter: a settled :accepted member's batch was published, an :uncertain one's issued its first journal write, a :refused one's issued none (known-durable-but-unpublished is never refused). Journal writes are counted at the outbox; publication at the visibility boundary.")
(defthm-owed fn2-commit-txn-records-verbatim (workspaces commands mode)
 (let ((result (fn2-commit-txn-proof-run workspaces commands mode nil)))
  (implies (fn2-ctp-initialized result) (fn2-commit-txn-records-verbatimp result)))
 :teeth (fn2-commit-txn-two-members fn2-commit-txn-flipped)
 :schema :invariant :doc "B-S2 S4: a sealed records frame is its members' admitted workspace records in event order, each after a record header at the member's event with occurrence = event, and nothing after; read from the sealed pool image.")
(defthm-owed fn2-commit-txn-admission-total (workspaces commands mode)
 (let ((result (fn2-commit-txn-proof-run workspaces commands mode nil)))
  (implies (fn2-ctp-initialized result) (fn2-commit-txn-admission-totalp result)))
 :teeth (fn2-commit-txn-refusals-change-nothing fn2-commit-txn-leaked-refusal)
 :schema :invariant :doc "B-S2 S1: an admission answers :ok and changes exactly one member row, which holds the admitted workspace and its owner, or answers :exhausted / :admission and changes nothing in the member and settled tables, the rows' admission columns, the frontier or the stop reason.")
