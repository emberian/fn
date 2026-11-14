; The generated packet writer owns every packet lease and its private checker
; interval. Production activation is unreachable-in-composition until the actual
; frozen C cut/map/manifest builder and B installation producer hand it a job.
; There is deliberately no start API accepting a caller's checked candidate.
(in-package "ACL2")
(include-book "checkpoint-writer-ops")
(include-book "machine-arms")
(fn2-book-layer :b)

(defcost fn2-checkpoint-writer-reserve :child fn2-checkpoint-writer-reserve-children :answers t
 :tables (fn2-core-pool fn2-core-control) :effects :per-use
 :doc "Preflight and acquire all three packet windows atomically, with no same-rank hold-and-wait.")
(defcost fn2-checkpoint-writer-release :child fn2-checkpoint-writer-release-children :answers t
 :tables (fn2-core-pool fn2-core-control) :effects :per-use
 :doc "Release the private packet bundle only after covering fence and physical completion.")
(defcost fn2-checkpoint-writer-checker :child fn2-checkpoint-writer-checker-children :answers (:ok :bounds)
 :doc "The final private format row and its generated 128-field stripe.")
(defcost fn2-checkpoint-writer-phase :child fn2-checkpoint-writer-phase-children :answers (:ok :bounds)
 :doc "Observe only the exact operation-tracked publication state.")
(defcost fn2-checkpoint-writer-begin :child fn2-checkpoint-writer-begin-children :answers t :bytes 96
 :tables (fn2-core-checkpoint-publication fn2-core-checkpoint-bytes fn2-core-digests)
 :doc "Derive the actual installed batch seal and checked boot geometry; first checkpoint only.")
(defcost fn2-checkpoint-writer-context :child fn2-checkpoint-writer-context-children :answers t :bytes 32
 :tables (fn2-core-fc-context fn2-core-digests)
 :doc "Set private checker context only outside a live continuation.")
(defcost fn2-checkpoint-writer-pack :child fn2-checkpoint-publication-pack :answers t :bytes 8192
 :tables (fn2-core-checkpoint-publication fn2-core-fields fn2-core-pool)
 :doc "Generate one private padded anchor packet and retain exact encoded length.")
(defcost fn2-checkpoint-writer-seal :child fn2-checkpoint-publication-seal-step :answers t :bytes 4096
 :tables (fn2-core-checkpoint-publication fn2-core-fc fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests)
 :doc "One bounded actual anchor sealing step on the stored output lease.")
(defcost fn2-checkpoint-writer-check :child fn2-checkpoint-publication-check-packet :answers t :bytes 4096
 :tables (fn2-core-checkpoint-publication fn2-core-fc fn2-core-b3 fn2-core-fields fn2-core-pool fn2-core-digests)
 :doc "One bounded actual anchor verification step, exact evidence before writable mask.")
(defcost fn2-checkpoint-writer-issue :child fn2-checkpoint-publication-step :answers t :bytes 4096 :descriptors 1
 :tables (fn2-core-checkpoint-publication fn2-core-pool fn2-core-ops fn2-core-control)
 :effects :per-use
 :doc "Issue at most one real write or covering fence; physical harvest owns completion.")

(defmachine fn2-checkpoint-writer
 :states (:free :reserve :begin :pack :seal-context :seal
          :check-context :check :publish :wait :release :done :uncertain)
 :fields ((pending :u32) (stopped :bool) (candidate :u32)
          (first-slot :u32) (first-gen :u60) (second-slot :u32) (second-gen :u60)
          (scratch-slot :u32) (scratch-gen :u60) (which :bool) (encoded-length :u32)
          (checker-row :u32) (field-base :u32))
 :holds ((:begin :storage-window) (:pack :storage-window) (:seal-context :storage-window) (:seal :storage-window)
         (:check-context :storage-window) (:check :storage-window) (:publish :storage-window) (:wait :storage-window)
         (:release :storage-window) (:uncertain :storage-window))
 :budget (:bytes 16384 :steps 32 :descriptors 1)
 :stops (:bounds :checkpoint :pool)
 :capacity (if (posp (fn2-b-checkpoint-capacity profile)) 1 0)
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free) (:reserve) (:begin) (:pack)
        (:seal-context) (:seal) (:check-context) (:check) (:publish) (:wait)
        (:release) (:done) (:uncertain))
 :observes ((:write-result) (:fence-result)))

(defmachine-arms fn2-checkpoint-writer :declare
 :arms
 ((:free (:idle))
  (:reserve :on-refusal ((:stop :pool))
   (:do (code s0 g0 s1 g1 ss gs)
        (fn2-checkpoint-writer-reserve *fn2-checkpoint-writer-kind* id row-generation)
    :effects ((:acquire (:storage-window))) :accept ()
    :case (((:ok) (:set (first-slot s0) (first-gen g0) (second-slot s1) (second-gen g1)
                        (scratch-slot ss) (scratch-gen gs) (which 0)) (:next :begin)
            (:charge :steps *fn2-work-small* :runnable t))
           ((:exhausted) (:yield))
           ((:partial) (:set (first-slot s0) (first-gen g0) (second-slot s1) (second-gen g1)
                             (scratch-slot ss) (scratch-gen gs))
            (:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
           (:otherwise (:stop :pool)))))
  (:begin :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-writer-begin row-candidate row-first-slot row-first-gen row-second-slot row-second-gen
                                            *fn2-checkpoint-writer-kind* id row-generation))
   (:do (code checker base) (fn2-checkpoint-writer-checker))
   (:set (checker-row checker) (field-base base)) (:next :pack)
   (:charge :bytes 96 :steps *fn2-work-stage* :runnable t))
  (:pack :on-refusal ((:stop :checkpoint))
   (:do (code len) (fn2-checkpoint-writer-pack row-which row-field-base row-scratch-slot row-scratch-gen))
   (:set (encoded-length len)) (:next :seal-context)
   (:charge :bytes 8192 :steps *fn2-work-stage* :runnable t))
  (:seal-context :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-writer-context row-which)) (:next :seal)
   (:charge :bytes 32 :steps *fn2-work-small* :runnable t))
  (:seal :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-writer-seal row-which row-checker-row row-field-base 4096)
    :accept () :case (((:more) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                     ((:ok) (:next :check-context) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                     (:otherwise (:stop :checkpoint)))))
  (:check-context :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-writer-context row-which)) (:next :check)
   (:charge :bytes 32 :steps *fn2-work-small* :runnable t))
  (:check :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-writer-check row-which row-checker-row row-field-base row-encoded-length 4096)
    :accept () :case (((:more) (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                     ((:ok) (:if (equal row-which 0)
                             ((:set (which 1)) (:next :pack)) ((:next :publish)))
                            (:charge :bytes 4096 :steps *fn2-work-stage* :runnable t))
                     (:otherwise (:stop :checkpoint)))))
  ; No pack/context transition exists after the verified mask is complete.
  ; The two output leases stay private until exact write/write/fence harvest.
  (:publish :on-refusal ((:stop :checkpoint))
   (:do (code) (fn2-checkpoint-writer-issue) :effects ((:acquire (:operation)))
    :accept () :case (((:issued) (:set (pending 1)) (:next :wait)
                      (:charge :bytes 4096 :steps *fn2-work-stage* :descriptors 1))
                     ((:exhausted) (:yield))
                     ((:complete) (:next :release) (:charge :steps *fn2-work-small* :runnable t))
                     ((:more) (:next :wait) (:charge :steps *fn2-work-small*))
                     (:otherwise (:next :uncertain) (:charge :steps *fn2-work-small*)))))
  (:wait :on-refusal ((:stop :checkpoint))
   (:do (code phase) (fn2-checkpoint-writer-phase))
   (:cond ((equal phase *fn2-checkpoint-publication-phase-uncertain*) (:next :uncertain) (:charge :steps *fn2-work-small*))
          ((equal phase *fn2-checkpoint-publication-phase-complete*) (:next :release) (:charge :steps *fn2-work-small* :runnable t))
          ((equal row-pending 0) (:next :publish) (:charge :steps *fn2-work-small* :runnable t))
          (t (:idle))))
  (:release :on-refusal ((:stop :pool))
   (:if (equal row-pending 0)
    ((:do (code) (fn2-checkpoint-writer-release row-first-slot row-first-gen row-second-slot row-second-gen
                                               row-scratch-slot row-scratch-gen *fn2-checkpoint-writer-kind* id row-generation)
      :effects ((:release (:storage-window))))
     (:next :done) (:charge :steps *fn2-work-small*)) ((:idle))))
  (:done (:idle))
  (:uncertain (:stop :checkpoint)))
 :observes ((:write-result (:wake)) (:fence-result (:wake))))

(defmacro fn2-checkpoint-writer-events ()
 '(progn (defmachine-arms fn2-checkpoint-writer) (defmachine-run fn2-checkpoint-writer)))
