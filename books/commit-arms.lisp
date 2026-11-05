; Layer B: the commit kind's arms in the arm language (MACHINE-FORM 6.2).
; The declaration is fn2-commit in machines-b.lisp; this book follows the
; commit's first callbacks sections (its operations exist), and the arms are
; generated, with their contracts derived, in the last one
; (fn2-commit-events-2b, assembly-callbacks-r2). Every refusal an arm meets
; is routed by name: a partner row that is not a commit row stops the core
; (:machine-phase); a follower whose leader failed is refused (no journal
; write yet) or made uncertain; every other refusal of an operation is a
; named stop (:commit-edge :commit-resource :commit-io :commit-publish
; :commit-drop :commit-pool :commit-follower) or a move to :uncertain with
; its reason. The shared step sequences below are expanded into the arms at
; declaration time (they differ per site only in their charges and reasons).
(in-package "ACL2")
(include-book "assembly-callbacks-r")
(fn2-book-layer :b)

; The arms' reads of the partner row: total over ids (a non-commit id reads as
; a free row with no batch and no fence; every arm reaches them only once the
; partner is known to be a commit row).
(defun fn2-commit-peer-phase (peer fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (if (fn2-commit-idp peer fn2-core) (nfix (fn2-machine-phase peer fn2-core)) *fn2-commit-state-free*))
(defun fn2-commit-peer-batch-no (peer fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (if (fn2-commit-idp peer fn2-core) (nfix (fn2-machine-batch-no peer fn2-core)) 0))
(defun fn2-commit-peer-fence-live (peer fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (if (fn2-commit-idp peer fn2-core) (nfix (fn2-machine-cb-fence-live peer fn2-core)) 0))
(defthm fn2-commit-peer-reads-natp
 (and (natp (fn2-commit-peer-phase peer fn2-core))
      (natp (fn2-commit-peer-batch-no peer fn2-core))
      (natp (fn2-commit-peer-fence-live peer fn2-core)))
 :rule-classes ((:type-prescription :corollary (natp (fn2-commit-peer-phase peer fn2-core)))
                (:type-prescription :corollary (natp (fn2-commit-peer-batch-no peer fn2-core)))
                (:type-prescription :corollary (natp (fn2-commit-peer-fence-live peer fn2-core)))))
(in-theory (disable fn2-commit-peer-phase fn2-commit-peer-batch-no fn2-commit-peer-fence-live))

;; The declared operations the arms call beyond machines-b's.
(defcost fn2-commit-partner-state :answers (:invalid :failed :ok)
 :doc "The partner row's state: not a commit row, failed (an older partner uncertain, or an abort at or below this batch), or ok.")
(defcost fn2-commit-idp :doc "Whether a row id is a live commit row.")
(defcost fn2-commit-peer-phase :doc "The partner row's phase (free when it is not a commit row).")
(defcost fn2-commit-peer-batch-no :doc "The partner row's batch number (0 when it is not a commit row).")
(defcost fn2-commit-peer-fence-live :doc "Whether the partner row's fence is in flight (0 when it is not a commit row).")
(defcost fn2-commit-follower-waits :doc "b54 M3: a follower's first journal write waits for its leader's.")
(defcost fn2-commit-now :doc "The scheduler's clock.")
(defcost fn2-commit-resource :doc "A row's journal resource for a role: extent, epoch, counter, pool slot and generation.")
(defcost fn2-commit-mark-abort :tables (fn2-core-commit-root)
 :doc "Open (or lower) the suffix abort at this batch.")
(defcost fn2-commit-root-edge :answers t :tables (fn2-core-extents fn2-core-alloc-edges fn2-core-control)
 :doc "Add the batch's prepared-successor edge, or swap it for the installed-root edge.")
(defcost fn2-commit-seal-step :answers t :bytes 4096 :own-writes (cb-cursor cb-issued cb-seal-len)
 :tables (fn2-core-pool fn2-core-control (:layers :b))
 :doc "One seal stage: at most one 4 KiB fill or hash, or one record encoding.")
(defcost fn2-commit-io-edge :answers t :tables (fn2-core-commit-io fn2-core-extents fn2-core-alloc-edges fn2-core-control)
 :doc "Record (or drop) the issuing operation as the holder of a journal role's IO edge.")
(defcost fn2-commit-drop-io :tables (fn2-core-commit-io fn2-core-extents fn2-core-alloc-edges fn2-core-control)
 :doc "Drop the three IO edges once every write result is harvested.")
(defcost fn2-commit-allocate :answers t :tables (fn2-core-extents fn2-core-commit-io)
 :doc "Commit the batch's dependency extent to the batch in the allocator.")
(defcost fn2-commit-root-swap :tables (fn2-core-commit-root fn2-core-control)
 :doc "Install (or publish) the batch's root in the commit directory once it is next; (mv ok core).")
(defcost fn2-commit-stream-wake :answers t :tables ((:layers :b :c :d :e) fn2-core-machines fn2-core-sched)
 :doc "Wake the stream members of a published batch (E's hook).")
(defcost fn2-commit-settle-member :tables (fn2-core-commit-settled fn2-core-commit-members fn2-core-machines fn2-core-sched fn2-core-control)
 :doc "Settle one member's outcome and wake its owner.")
(defcost fn2-commit-unprepare :answers t :tables (fn2-core-extents fn2-core-alloc-edges fn2-core-commit-root fn2-core-control)
 :doc "Drop a refused batch's prepared state (its successor edge when it has one).")
(defcost fn2-commit-end-abort :tables (fn2-core-commit-root fn2-core-control)
 :doc "Close the suffix abort once its last batch has dropped.")
(defcost fn2-commit-release-pool :answers t :own-writes (pool-slot pool-gen) :tables (fn2-core-pool fn2-core-commit-io fn2-core-control)
 :effects :per-use :doc "Release one of the row's pool ranges (role 0..3).")

;; The shared step sequences.
(defconst *fn2-commit-arm-mailbox* '(:charge :steps *fn2-work-mailbox*))
(defconst *fn2-commit-arm-mailbox-run* '(:charge :steps *fn2-work-mailbox* :runnable t))
(defconst *fn2-commit-arm-advance-run* '(:charge :steps *fn2-work-advance* :runnable t))
(defun fn2-commit-arm-reason (reason)
 (declare (xargs :verify-guards nil))
 (intern-in-package-of-symbol (concatenate 'string "*FN2-COMMIT-REASON-" (symbol-name reason) "*") 'fn2-commit))
;; the move to :uncertain (fn2-commit-uncertain): the settlement cursor starts
;; after the members already acknowledged; the first reason is kept
(defun fn2-commit-arm-uncertain-sets (reason)
 (declare (xargs :verify-guards nil))
 `((cb-cursor (if (equal row-phase *fn2-commit-state-uncertain*) row-cb-cursor row-cb-acks))
   (cb-failed 1)
   (cb-reason (if (equal row-cb-failed 0) ,reason row-cb-reason))))
(defun fn2-commit-arm-uncertain (reason extra charge)
 (declare (xargs :verify-guards nil))
 `((:set ,@(fn2-commit-arm-uncertain-sets reason) ,@extra) (:next :uncertain) ,charge))
;; the refusal of a batch with no journal write (fn2-commit-refuse): open the
;; abort; the prepared-successor edge exists once :collect has run
(defun fn2-commit-arm-refuse (charge)
 (declare (xargs :verify-guards nil))
 `((:do () (fn2-commit-mark-abort row-batch-no row-first-key))
   (:set (outcome (if (equal row-phase *fn2-commit-state-collect*) 0 1)) (cb-cursor 0) (cb-stage 0) (cb-open 0))
   (:next :dropping) ,charge))
;; a failure: refused with no journal write, else uncertain (fn2-commit-fail)
(defun fn2-commit-arm-fail (reason refuse-charge uncertain-charge)
 (declare (xargs :verify-guards nil))
 `((:if (equal row-cb-wrote 0)
        ,(fn2-commit-arm-refuse refuse-charge)
        ,(fn2-commit-arm-uncertain (fn2-commit-arm-reason reason) nil uncertain-charge))))
;; a follower whose leader failed: refused, or uncertain (stopped once quiet);
;; WRITTEN: past its first journal write an unwritten row is an invariant
(defun fn2-commit-arm-follower (written)
 (declare (xargs :verify-guards nil))
 `((:if (equal row-cb-wrote 0)
        ,(if written '((:stop :commit-follower :steps *fn2-work-mailbox*))
           (fn2-commit-arm-refuse *fn2-commit-arm-mailbox-run*))
        ,(fn2-commit-arm-uncertain '*fn2-commit-reason-predecessor*
          '((stopped (if (and (equal row-pending 0) (equal row-cb-fence-live 0)) 1 row-stopped)))
          *fn2-commit-arm-mailbox*))))
;; every arm but :dropping's first reads its partner row
(defun fn2-commit-arm-partner (written body)
 (declare (xargs :verify-guards nil))
 `((:do (partner) (fn2-commit-partner-state row-batch-no row-partner)
    :accept ()
    :case (((:invalid) (:stop :machine-phase))
           ((:failed) ,@(fn2-commit-arm-follower written))
           ((:ok) ,@body)))))

;; :dependencies and :log-write: issue the next journal write of the phase,
;; or, once all are harvested, move on by the barrier mode
(defun fn2-commit-arm-writes ()
 (declare (xargs :verify-guards nil))
 (fn2-commit-arm-partner nil
  `((:let dep (equal row-phase *fn2-commit-state-dependencies*))
    (:let target (if dep 1 2))
    (:cond
     ((equal (fn2-commit-peer-phase row-partner) *fn2-commit-state-uncertain*)
      ,@(fn2-commit-arm-fail :predecessor *fn2-commit-arm-mailbox-run* *fn2-commit-arm-mailbox-run*))
     ((equal row-cb-issued target)
      (:cond ((< row-cb-done row-cb-issued) ,*fn2-commit-arm-mailbox*)
             (dep (:set (cb-deps-ok 1) (cb-log-ok 0) (cb-issued 0) (cb-done 0) (cb-bytes 0))
                  (:next (:if (equal row-cb-mode 1) :fence :log-write)) ,*fn2-commit-arm-advance-run*)
             (t (:set (cb-log-ok 1) (cb-issued 0) (cb-done 0) (cb-bytes 0))
                (:next (:if (equal row-cb-mode 1) :durable :fence)) ,*fn2-commit-arm-advance-run*)))
     ((not (and (natp budget) (< 0 budget) (< row-cb-issued target))) (:yield))
     ;; b54 M3: a follower's first journal write waits for its leader's
     ((fn2-commit-follower-waits id row-partner) ,*fn2-commit-arm-mailbox-run*)
     (t (:let role (if dep 0 (+ 1 row-cb-issued)))
        (:do (e epoch counter rslot rgen) (fn2-commit-resource id role))
        (:if (not (unsigned-byte-p 32 e))
             ((:stop :commit-resource))
             ((:do (code opslot opgen)
                   (fn2-issue-write (+ (* e *fn2-commit-extent-bytes*) (* role *fn2-commit-unit-bytes*))
                                    rslot rgen 0 *fn2-commit-unit-bytes* (if dep 0 row-cb-mode) :principal 0)
               :accept ()
               :case (((:ok)
                       (:do (ecode) (fn2-commit-io-edge id role t opslot opgen)
                        :accept ()
                        :case (((:ok) (:set (cb-issued (+ 1 row-cb-issued)) (pending (+ 1 row-pending)) (cb-wrote 1))
                                      (:charge :bytes 4096 :steps *fn2-work-stage* :descriptors 1 :runnable t))
                               (:otherwise (:stop :commit-io)))))
                      ((:exhausted) (:yield))
                      (:otherwise ,@(fn2-commit-arm-fail :issue *fn2-commit-arm-mailbox-run* *fn2-commit-arm-mailbox*)))))))))))

;; :draining and :uncertain: settle an uncertain batch's members, wait for
;; its completions, then release the four pool ranges and free the row
(defun fn2-commit-arm-drain-body ()
 (declare (xargs :verify-guards nil))
 `((:cond
    ((and (equal row-phase *fn2-commit-state-uncertain*) (< row-cb-cursor row-member-count))
     (:do () (fn2-commit-settle-member id row-cb-cursor *fn2-commit-outcome-uncertain* 0))
     (:set (cb-cursor (+ 1 row-cb-cursor))) ,*fn2-commit-arm-advance-run*)
    ((not (and (equal row-pending 0) (equal row-cb-fence-live 0))) ,*fn2-commit-arm-mailbox*)
    ((equal row-phase *fn2-commit-state-uncertain*) (:set (stopped 1)) ,*fn2-commit-arm-mailbox*)
    ((>= row-cb-stage 4) (:set (stopped 1)) (:next :free) ,*fn2-commit-arm-mailbox*)
    (t (:do (code) (fn2-commit-release-pool id row-cb-stage row-generation)
        :effects ((:release (:storage-window)))
        :accept ()
        :case (((:ok :retired) (:set (cb-stage (+ 1 row-cb-stage))) ,*fn2-commit-arm-advance-run*)
               (:otherwise (:stop :commit-pool))))))))
(defun fn2-commit-arm-drain ()
 (declare (xargs :verify-guards nil))
 `((:do (partner) (fn2-commit-partner-state row-batch-no row-partner)
    :accept ()
    :case (((:invalid) (:stop :machine-phase))
           ;; a dropped batch (no journal write) drains whatever its partner does
           ((:failed) (:if (equal row-cb-wrote 1) ,(fn2-commit-arm-follower t) ,(fn2-commit-arm-drain-body)))
           ((:ok) ,@(fn2-commit-arm-drain-body))))))

;; the write and fence results (one handler for both events)
(defun fn2-commit-arm-observe ()
 (declare (xargs :verify-guards nil))
 `((:let fence (equal row-cb-fence-live 1))
   (:let write (equal event *fn2-event-write-result*))
   (:let write-phase (or (equal row-phase *fn2-commit-state-dependencies*)
                         (equal row-phase *fn2-commit-state-log-write*)
                         (and (equal row-phase *fn2-commit-state-uncertain*) (< 0 row-pending))))
   (:let match (if write (and write-phase (not fence) (< row-cb-done row-cb-issued))
                 (and fence (or (equal row-phase *fn2-commit-state-fence*) (equal row-phase *fn2-commit-state-uncertain*))
                      (equal event *fn2-event-fence-result*))))
   (:let success (and match (equal outcome *fn2-outcome-done*) (equal count (if write *fn2-commit-unit-bytes* 0))))
   (:do () (fn2-commit-drop-io id) :when (and match write (equal (+ row-cb-done 1) row-cb-issued)) :else ())
   (:if success
        ((:set (cb-fence-live (if fence 0 row-cb-fence-live))
               (cb-done (if write (+ row-cb-done 1) row-cb-done))
               (cb-bytes (if write (+ row-cb-bytes (nfix count)) row-cb-bytes))
               (cb-fence-ok (if fence 1 row-cb-fence-ok)))
         (:wake))
        ((:set (cb-fence-live (if (and match fence) 0 row-cb-fence-live))
               (cb-done (if (and match write) (+ row-cb-done 1) row-cb-done))
               (cb-bytes (if (and match write) (+ row-cb-bytes (nfix count)) row-cb-bytes))
               (outcome (if (equal row-cb-failed 0) outcome row-outcome))
               ,@(fn2-commit-arm-uncertain-sets '(if match reason *fn2-commit-reason-stray*)))
         (:next :uncertain) (:wake)))))

(defun fn2-commit-arms ()
 (declare (xargs :verify-guards nil))
 `((:free (:idle))
   (:collect
    ,@(fn2-commit-arm-partner nil
       '((:do (code) (fn2-commit-root-edge id nil)
          :accept ()
          :case (((:ok) (:set (cb-open 0)) (:next :seal) (:charge :steps *fn2-work-stage* :runnable t))
                 (:otherwise (:stop :commit-edge)))))))
   ;; a refused seal stays runnable for its :dropping arm (b54 M3)
   (:seal
    ,@(fn2-commit-arm-partner nil
       `((:do (code) (fn2-commit-seal-step id)
          :accept ()
          :case (((:more) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                 ((:ok)
                  (:if (equal row-cb-stage *fn2-commit-seal-stage-hash-seal-frame*)
                       ((:set (cb-stage (+ 1 row-cb-stage)) (cb-issued 0)) (:next :dependencies)
                        (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                       ((:set (cb-stage (+ 1 row-cb-stage)))
                        (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))))
                 (:otherwise
                  ,@(fn2-commit-arm-fail :seal '(:charge :bytes 4096 :steps *fn2-work-stage* :runnable t)
                                         '(:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))))))))
   (:dependencies (:goto writes))
   (:log-write (:goto writes))
   (:fence
    ,@(fn2-commit-arm-partner t
       `((:let now (fn2-commit-now))
         (:cond
          ((and (equal row-cb-fence-live 1) (<= row-deadline now))
           ,@(fn2-commit-arm-uncertain '*fn2-commit-reason-timeout* nil *fn2-commit-arm-mailbox*))
          ((equal row-cb-fence-ok 1)
           (:next (:if (equal row-cb-mode 1) :log-write :durable)) ,*fn2-commit-arm-mailbox-run*)
          ((equal (fn2-commit-peer-phase row-partner) *fn2-commit-state-uncertain*)
           ,@(fn2-commit-arm-uncertain '*fn2-commit-reason-predecessor* nil *fn2-commit-arm-mailbox*))
          ((or (equal row-cb-fence-live 1) (equal (fn2-commit-peer-fence-live row-partner) 1)) ,*fn2-commit-arm-mailbox-run*)
          ((not (and (natp budget) (< 0 budget))) (:yield))
          ((not (and (natp now) (unsigned-byte-p 60 (+ now 1024))))
           ,@(fn2-commit-arm-uncertain '*fn2-commit-reason-timeout* nil *fn2-commit-arm-mailbox*))
          (t (:do (code opslot opgen) (fn2-issue-fence :principal 0)
              :accept ()
              :case (((:ok) (:set (cb-fence-live 1) (deadline (+ now 1024)) (pending (+ 1 row-pending)))
                            (:charge :steps *fn2-work-transition* :descriptors 1 :runnable t))
                     ((:exhausted) (:yield))
                     (:otherwise ,@(fn2-commit-arm-uncertain '*fn2-commit-reason-issue* nil *fn2-commit-arm-mailbox*)))))))))
   (:durable
    ,@(fn2-commit-arm-partner t
       `((:if (not (and (unsigned-byte-p 60 row-batch-no) (equal row-cb-deps-ok 1)
                        (equal row-cb-log-ok 1) (equal row-cb-fence-ok 1) (equal row-cb-failed 0)))
              ,(fn2-commit-arm-uncertain '*fn2-commit-reason-durable* nil *fn2-commit-arm-mailbox*)
              ((:do (code) (fn2-commit-allocate id)
                :accept ()
                :case (((:ok) (:next :install) (:charge :steps *fn2-work-transition* :runnable t))
                       (:otherwise ,@(fn2-commit-arm-uncertain '*fn2-commit-reason-durable* nil
                                      '(:charge :steps *fn2-work-transition* :runnable t))))))))))
   (:install
    ,@(fn2-commit-arm-partner t
       '((:do (ok) (fn2-commit-root-swap id nil))
         (:if (not ok)
              ((:charge :steps *fn2-work-mailbox* :runnable t))
              ((:do (code) (fn2-commit-root-edge id t)
                :accept ()
                :case (((:ok) (:next :publish) (:charge :steps *fn2-work-stage* :runnable t))
                       (:otherwise (:stop :commit-edge)))))))))
   ;; b54 M6: C publishes the batch's private successor before any outcome
   (:publish
    ,@(fn2-commit-arm-partner t
       `((:do (ok) (fn2-commit-root-swap id t))
         (:if (not ok)
              ,(fn2-commit-arm-uncertain '*fn2-commit-reason-durable* nil *fn2-commit-arm-advance-run*)
              ((:do (code) (fn2-successor-publish row-batch-no)
                :accept ()
                :case (((:ok)
                        (:do (wcode) (fn2-commit-stream-wake row-batch-no)
                         :accept ()
                         :case (((:ok :unregistered) (:set (cb-published 1)) (:next :notify) ,*fn2-commit-arm-advance-run*)
                                (:otherwise (:stop :commit-publish)))))
                       (:otherwise (:stop :commit-publish :steps *fn2-work-mailbox*)))))))))
   (:notify
    ,@(fn2-commit-arm-partner t
       `((:if (< row-cb-acks row-member-count)
              ((:do () (fn2-commit-settle-member id row-cb-acks *fn2-commit-outcome-accepted* row-batch-no))
               (:set (cb-acks (+ 1 row-cb-acks))) ,*fn2-commit-arm-advance-run*)
              ((:set (cb-stage 0)) (:next :draining) ,*fn2-commit-arm-advance-run*)))))
   (:draining (:goto drain))
   (:uncertain (:goto drain))
   ;; b54 M3: drop in batch order behind an older dropping partner
   (:dropping
    (:cond
     ((not (fn2-commit-idp row-partner)) (:stop :machine-phase))
     ((and (equal (fn2-commit-peer-phase row-partner) *fn2-commit-state-dropping*)
           (< (fn2-commit-peer-batch-no row-partner) row-batch-no))
      ,*fn2-commit-arm-mailbox-run*)
     ((equal row-cb-stage 0)
      (:do (code) (fn2-successor-drop row-batch-no)
       :accept ()
       :case (((:ok)
               (:do (ucode) (fn2-commit-unprepare id (equal row-outcome 1))
                :accept ()
                :case (((:ok) (:set (cb-stage 1)) ,*fn2-commit-arm-advance-run*)
                       (:otherwise (:stop :commit-drop :steps *fn2-work-advance*)))))
              (:otherwise (:stop :commit-drop :steps *fn2-work-mailbox*)))))
     ((< row-cb-cursor row-member-count)
      (:do () (fn2-commit-settle-member id row-cb-cursor *fn2-commit-outcome-refused* 0))
      (:set (cb-cursor (+ 1 row-cb-cursor))) ,*fn2-commit-arm-advance-run*)
     (t (:do () (fn2-commit-end-abort id))
        (:set (cb-stage 0)) (:next :draining) ,*fn2-commit-arm-advance-run*)))))

(make-event
 `(defmachine-arms fn2-commit :declare
   :subarms ((writes ,@(fn2-commit-arm-writes))
             (drain ,@(fn2-commit-arm-drain)))
   :arms ,(fn2-commit-arms)
   :observes ((:write-result ,@(fn2-commit-arm-observe))
              (:fence-result ,@(fn2-commit-arm-observe)))))
