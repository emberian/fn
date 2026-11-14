; A real generated physical-page owner, distinct from the frozen C producer.
; Producer callbacks pack and bind while they own the workspace, then call
; TAKE and :wake-row its returned actual id. No destination tuple is supplied.
; The producer resumes only after RETURN has restored ownership and wakes it.
; Registration/assembly materializes EVENTS after assigning the kind tag.
(in-package "ACL2")
(include-book "checkpoint-page-io")
(include-book "machine-arms")
(fn2-book-layer :c)

(defmachine fn2-checkpoint-page-worker
 :states (:free :context :format :issue :wait :return :done :uncertain)
 :fields ((pending :u32) (stopped :bool))
 :holds ((:context :storage-window) (:format :storage-window) (:issue :storage-window)
         (:wait :storage-window) (:return :storage-window) (:uncertain :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 1)
 :stops (:checkpoint)
 :capacity 1
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free) (:context) (:format) (:issue) (:wait) (:return) (:done) (:uncertain))
 :observes ((:write-result)))

(defun fn2-checkpoint-page-phase-children (fn2-checkpoint-page)
 (declare (xargs :stobjs fn2-checkpoint-page :guard (fn2-checkpoint-page-wfp fn2-checkpoint-page)))
 (if (< 0 (fn2-checkpoint-page-rows fn2-checkpoint-page))
  (mv :ok (fn2-checkpoint-page-phase 0 fn2-checkpoint-page)) (mv :bounds 0)))

(defun fn2-checkpoint-page-fail-children (fn2-checkpoint-page)
 (declare (xargs :stobjs fn2-checkpoint-page :guard (fn2-checkpoint-page-wfp fn2-checkpoint-page)))
 (if (< 0 (fn2-checkpoint-page-rows fn2-checkpoint-page))
  (let ((fn2-checkpoint-page (fn2-checkpoint-page-set-phase 0 *fn2-checkpoint-page-phase-uncertain* fn2-checkpoint-page)))
   (mv :ok fn2-checkpoint-page)) (mv :bounds fn2-checkpoint-page)))
(fn2-checkpoint-page-preserves fn2-checkpoint-page-fail-children (fn2-checkpoint-page) :position 1)

; TAKE/RETURN children below are generated at callback materialization, when
; the assembly has assigned *FN2-CHECKPOINT-PAGE-WORKER-KIND*. Their operations
; are declared here so their generated faces belong to this machine's book.
(defcost fn2-checkpoint-page-take :child fn2-checkpoint-page-take-children :answers t
 :tables (fn2-checkpoint-page-worker-table fn2-core-checkpoint-page fn2-core-pool)
 :doc "Transfer the source workspace to the actual admitted page worker; return its id for :wake-row.")
(defcost fn2-checkpoint-page-return :child fn2-checkpoint-page-return-children :answers t
 :tables (fn2-checkpoint-page-worker-table fn2-core-checkpoint-page fn2-core-pool)
 :doc "After exact final physical harvest, hand the workspace back and return the retained producer id.")
(defcost fn2-checkpoint-page-context-op :child fn2-checkpoint-page-context :answers t :bytes 32
 :tables (fn2-core-checkpoint-page fn2-core-fc-context fn2-core-digests)
 :doc "Initialize the worker's private checker from actual reservation and boot geometry.")
(defcost fn2-checkpoint-page-format-op :child fn2-checkpoint-page-format-step :answers t :bytes 4096
 :tables (fn2-core-checkpoint-page fn2-core-checkpoint-page-verified fn2-core-fc fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests)
 :doc "Bounded page seal then verification; no producer mutation is callable in these arms.")
(defcost fn2-checkpoint-page-issue-op :child fn2-checkpoint-page-issue :answers t :bytes 4096 :descriptors 1
 :tables (fn2-core-checkpoint-page fn2-core-pool fn2-core-ops fn2-core-control fn2-core-extents fn2-core-alloc-edges)
 :effects :per-use
 :doc "Issue one real sector write under the admitted IO owner tuple.")
(defcost fn2-checkpoint-page-phase-op :child fn2-checkpoint-page-phase-children :answers (:ok :bounds)
 :doc "Read the physically harvested page phase.")
(defcost fn2-checkpoint-page-fail-op :child fn2-checkpoint-page-fail-children :answers (:ok :bounds)
 :tables (fn2-core-checkpoint-page)
 :doc "Retain uncertain ownership without returning or releasing any workspace.")

(defmachine-arms fn2-checkpoint-page-worker :declare
 :arms
 ((:free (:idle))
  (:context :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-page-context-op))
   (:next :format) (:charge :bytes 32 :steps *fn2-work-small* :runnable t))
  (:format :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-page-format-op 4096)
    :accept () :case (((:more :sealed) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                     ((:verified) (:next :issue) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:issue :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:if (and (natp budget) (< 0 budget))
    ((:do (code) (fn2-checkpoint-page-issue-op budget) :effects ((:acquire (:operation)))
      :accept () :case (((:issued) (:set (pending 1)) (:next :wait)
                        (:charge :bytes 4096 :steps *fn2-work-stage* :descriptors 1))
                       ((:exhausted :yield) (:yield))
                       (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
    ((:yield))))
  (:wait :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code phase) (fn2-checkpoint-page-phase-op))
   (:cond ((equal phase *fn2-checkpoint-page-phase-uncertain*)
           (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
          ((equal phase *fn2-checkpoint-page-phase-complete*)
           (:set (pending 0)) (:next :return) (:charge :steps *fn2-work-small* :runnable t))
          ((equal phase *fn2-checkpoint-page-phase-write*)
           (:set (pending 0)) (:next :issue) (:charge :steps *fn2-work-small* :runnable t))
          (t (:idle))))
  (:return :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code producer) (fn2-checkpoint-page-return))
   (:next :done) (:wake-row producer) (:charge :steps *fn2-work-small*))
  (:done (:idle))
  (:uncertain :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-page-fail-op)) (:set (stopped 1)) (:stop :checkpoint)))
 :observes ((:write-result (:wake))))

; No handwritten core adapter. The shared arm generator emits the actual
; children, exact whole-result core faces, observations and run machinery.
(defmacro fn2-checkpoint-page-worker-events ()
 '(progn
   (defun fn2-checkpoint-page-take-children (fn2-checkpoint-page-worker fn2-checkpoint-page fn2-machines
                                           fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-pool)
    (declare (xargs :stobjs (fn2-checkpoint-page-worker fn2-checkpoint-page fn2-machines
                             fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-pool)
     :guard (and (fn2-checkpoint-page-worker-wfp fn2-checkpoint-page-worker)
                 (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-machines-wfp fn2-machines)
                 (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
                 (fn2-extents-wfp fn2-extents) (fn2-pool-wfp fn2-pool))))
    (b* (((unless (and (< 0 (fn2-checkpoint-page-worker-rows fn2-checkpoint-page-worker))
                       (< *fn2-checkpoint-page-worker-kind* (fn2-machines-kind-bases-length fn2-machines))
                       (member-equal (fn2-checkpoint-page-worker-phase 0 fn2-checkpoint-page-worker)
                        (list *fn2-checkpoint-page-worker-state-free* *fn2-checkpoint-page-worker-state-done*))
                       (fn2-checkpoint-page-live-p fn2-checkpoint-page fn2-csnapshot fn2-checkpoint-construction fn2-extents)
                       (equal (fn2-checkpoint-page-phase 0 fn2-checkpoint-page) *fn2-checkpoint-page-phase-context*)
                       (equal (fn2-checkpoint-page-transferred 0 fn2-checkpoint-page) 0)))
          (mv :busy *fn2-none* 0 fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool))
         (id (fn2-machines-kind-basesi *fn2-checkpoint-page-worker-kind* fn2-machines))
         (generation (fn2-checkpoint-page-worker-generation 0 fn2-checkpoint-page-worker))
         ((unless (and (natp id) (< id (fn2-machines-rows fn2-machines)) (posp generation)
                       (equal (fn2-machines-kind id fn2-machines) *fn2-checkpoint-page-worker-kind*)
                       (equal (fn2-machines-slot id fn2-machines) 0)
                       (not (and (equal (fn2-checkpoint-page-owner-kind 0 fn2-checkpoint-page) *fn2-checkpoint-page-worker-kind*)
                                 (equal (fn2-checkpoint-page-owner-slot 0 fn2-checkpoint-page) id)
                                 (equal (fn2-checkpoint-page-owner-gen 0 fn2-checkpoint-page) generation)))))
          (mv :owner *fn2-none* 0 fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool))
         (slot (fn2-checkpoint-page-slot 0 fn2-checkpoint-page)) (gen (fn2-checkpoint-page-gen 0 fn2-checkpoint-page))
         ((mv code fn2-pool)
          (fn2-pool-hand slot gen (fn2-checkpoint-page-owner-kind 0 fn2-checkpoint-page)
           (fn2-checkpoint-page-owner-slot 0 fn2-checkpoint-page) (fn2-checkpoint-page-owner-gen 0 fn2-checkpoint-page)
           *fn2-checkpoint-page-worker-kind* id generation fn2-pool))
         ((unless (eq code :ok))
          (mv code *fn2-none* 0 fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool))
         ((mv code fn2-pool) (fn2-pool-accept-hand slot gen *fn2-checkpoint-page-worker-kind* id generation fn2-pool))
         (fn2-checkpoint-page (fn2-checkpoint-page-put 0
          (io-owner-kind *fn2-checkpoint-page-worker-kind*) (io-owner-slot id) (io-owner-gen generation)
          (transferred (if (eq code :ok) 1 0))
          (phase (if (eq code :ok) *fn2-checkpoint-page-phase-context* *fn2-checkpoint-page-phase-uncertain*))))
         (fn2-checkpoint-page-worker (fn2-checkpoint-page-worker-put 0
          (pending 0) (stopped 0)
          (phase (if (eq code :ok) *fn2-checkpoint-page-worker-state-context* *fn2-checkpoint-page-worker-state-uncertain*)))))
     (mv (if (eq code :ok) :ok :uncertain) id generation fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool)))

   (defun fn2-checkpoint-page-return-children (fn2-checkpoint-page-worker fn2-checkpoint-page fn2-machines
                                             fn2-csnapshot fn2-checkpoint-construction fn2-extents
                                             fn2-checkpoint-page-verified fn2-pool)
    (declare (xargs :stobjs (fn2-checkpoint-page-worker fn2-checkpoint-page fn2-machines
                             fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-pool)
     :guard (and (fn2-checkpoint-page-worker-wfp fn2-checkpoint-page-worker)
                 (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-machines-wfp fn2-machines)
                 (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
                 (fn2-extents-wfp fn2-extents) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified)
                 (fn2-pool-wfp fn2-pool))))
    (b* (((unless (and (< 0 (fn2-checkpoint-page-worker-rows fn2-checkpoint-page-worker))
                       (< 0 (fn2-checkpoint-page-rows fn2-checkpoint-page))
                       (< *fn2-checkpoint-page-worker-kind* (fn2-machines-kind-bases-length fn2-machines))))
          (mv :bounds *fn2-none* fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool))
         (id (fn2-machines-kind-basesi *fn2-checkpoint-page-worker-kind* fn2-machines))
         (generation (fn2-checkpoint-page-worker-generation 0 fn2-checkpoint-page-worker))
         (producer (fn2-checkpoint-page-owner-slot 0 fn2-checkpoint-page))
         ((unless (and (natp id) (< id (fn2-machines-rows fn2-machines))
                       (equal (fn2-machines-kind id fn2-machines) *fn2-checkpoint-page-worker-kind*)
                       (equal (fn2-machines-slot id fn2-machines) 0)
                       (equal (fn2-checkpoint-page-worker-phase 0 fn2-checkpoint-page-worker) *fn2-checkpoint-page-worker-state-return*)
                       (equal (fn2-checkpoint-page-worker-pending 0 fn2-checkpoint-page-worker) 0)
                       (equal (fn2-checkpoint-page-transferred 0 fn2-checkpoint-page) 1)
                       (equal (fn2-checkpoint-page-io-owner-kind 0 fn2-checkpoint-page) *fn2-checkpoint-page-worker-kind*)
                       (equal (fn2-checkpoint-page-io-owner-slot 0 fn2-checkpoint-page) id)
                       (equal (fn2-checkpoint-page-io-owner-gen 0 fn2-checkpoint-page) generation)
                       (< producer (fn2-machines-rows fn2-machines))
                       (equal (fn2-machines-kind producer fn2-machines) (fn2-checkpoint-page-owner-kind 0 fn2-checkpoint-page))
                       (fn2-checkpoint-page-complete-p
                        (fn2-checkpoint-page-token 0 fn2-checkpoint-page)
                        (fn2-checkpoint-page-owner-kind 0 fn2-checkpoint-page) producer
                        (fn2-checkpoint-page-owner-gen 0 fn2-checkpoint-page)
                        (fn2-checkpoint-page-role 0 fn2-checkpoint-page) (fn2-checkpoint-page-ordinal 0 fn2-checkpoint-page)
                        (fn2-checkpoint-page-extent 0 fn2-checkpoint-page)
                        fn2-checkpoint-page fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified)))
          (mv :identity *fn2-none* fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool))
         (slot (fn2-checkpoint-page-slot 0 fn2-checkpoint-page)) (gen (fn2-checkpoint-page-gen 0 fn2-checkpoint-page))
         ((mv code fn2-pool)
          (fn2-pool-hand slot gen *fn2-checkpoint-page-worker-kind* id generation
           (fn2-checkpoint-page-owner-kind 0 fn2-checkpoint-page) producer
           (fn2-checkpoint-page-owner-gen 0 fn2-checkpoint-page) fn2-pool))
         ((unless (eq code :ok))
          (mv code *fn2-none* fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool))
         ((mv code fn2-pool)
          (fn2-pool-accept-hand slot gen (fn2-checkpoint-page-owner-kind 0 fn2-checkpoint-page) producer
           (fn2-checkpoint-page-owner-gen 0 fn2-checkpoint-page) fn2-pool))
         (fn2-checkpoint-page (if (eq code :ok)
          (fn2-checkpoint-page-put 0 (transferred 0)
           (io-owner-kind (fn2-checkpoint-page-owner-kind 0 fn2-checkpoint-page))
           (io-owner-slot producer) (io-owner-gen (fn2-checkpoint-page-owner-gen 0 fn2-checkpoint-page)))
          (fn2-checkpoint-page-set-phase 0 *fn2-checkpoint-page-phase-uncertain* fn2-checkpoint-page)))
         (fn2-checkpoint-page-worker (fn2-checkpoint-page-worker-set-phase 0
          (if (eq code :ok) *fn2-checkpoint-page-worker-state-done* *fn2-checkpoint-page-worker-state-uncertain*) fn2-checkpoint-page-worker)))
     (mv (if (eq code :ok) :ok :uncertain) producer fn2-checkpoint-page-worker fn2-checkpoint-page fn2-pool)))

   (fn2-checkpoint-page-preserves fn2-checkpoint-page-take-children
    (fn2-checkpoint-page-worker fn2-checkpoint-page fn2-machines fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-pool)
    :hyps ((fn2-checkpoint-page-workerp fn2-checkpoint-page-worker) (fn2-checkpoint-pagep fn2-checkpoint-page) (fn2-machinesp fn2-machines) (fn2-csnapshotp fn2-csnapshot) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-poolp fn2-pool) (fn2-checkpoint-page-worker-wfp fn2-checkpoint-page-worker) (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-machines-wfp fn2-machines) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-pool-wfp fn2-pool))
    :specs (("-CHECKPOINT-PAGE-WORKER-TYPE" fn2-checkpoint-page-workerp 3)
            ("-CHECKPOINT-PAGE-WORKER-WFP" fn2-checkpoint-page-worker-wfp 3)
            ("-CHECKPOINT-PAGE-WORKER-ROWS" fn2-checkpoint-page-worker-rows 3 :frame fn2-checkpoint-page-worker)
            ("-CHECKPOINT-PAGE-TYPE" fn2-checkpoint-pagep 4)
            ("-CHECKPOINT-PAGE-WFP" fn2-checkpoint-page-wfp 4)
            ("-CHECKPOINT-PAGE-ROWS" fn2-checkpoint-page-rows 4 :frame fn2-checkpoint-page)
            ("-POOL-TYPE" fn2-poolp 5)
            ("-POOL-WFP" fn2-pool-wfp 5)
            ("-POOL-ROWS" fn2-pool-rows 5 :frame fn2-pool)))

   (fn2-checkpoint-page-preserves fn2-checkpoint-page-return-children
    (fn2-checkpoint-page-worker fn2-checkpoint-page fn2-machines fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-pool)
    :hyps ((fn2-checkpoint-page-workerp fn2-checkpoint-page-worker) (fn2-checkpoint-pagep fn2-checkpoint-page) (fn2-machinesp fn2-machines) (fn2-csnapshotp fn2-csnapshot) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-checkpoint-page-verifiedp fn2-checkpoint-page-verified) (fn2-poolp fn2-pool) (fn2-checkpoint-page-worker-wfp fn2-checkpoint-page-worker) (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-machines-wfp fn2-machines) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-pool-wfp fn2-pool))
    :specs (("-CHECKPOINT-PAGE-WORKER-TYPE" fn2-checkpoint-page-workerp 2)
            ("-CHECKPOINT-PAGE-WORKER-WFP" fn2-checkpoint-page-worker-wfp 2)
            ("-CHECKPOINT-PAGE-WORKER-ROWS" fn2-checkpoint-page-worker-rows 2 :frame fn2-checkpoint-page-worker)
            ("-CHECKPOINT-PAGE-TYPE" fn2-checkpoint-pagep 3)
            ("-CHECKPOINT-PAGE-WFP" fn2-checkpoint-page-wfp 3)
            ("-CHECKPOINT-PAGE-ROWS" fn2-checkpoint-page-rows 3 :frame fn2-checkpoint-page)
            ("-POOL-TYPE" fn2-poolp 4)
            ("-POOL-WFP" fn2-pool-wfp 4)
            ("-POOL-ROWS" fn2-pool-rows 4 :frame fn2-pool)))

   (defmachine-arms fn2-checkpoint-page-worker :children)
   (defmachine-arms fn2-checkpoint-page-worker :wrappers)
   (defmachine-run fn2-checkpoint-page-worker)))
