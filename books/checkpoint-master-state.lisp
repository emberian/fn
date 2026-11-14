; The actual C maintenance owner. It is created by executor genesis, but source
; activation stays disabled until selected-base recovery is qualified. All
; construction arms beyond admission are unreachable-in-composition meanwhile;
; their local contracts are not whole-machine acceptance/reclamation claims.
(in-package "ACL2")
(include-book "checkpoint-kind")
(include-book "machine-arms")
(fn2-book-layer :c)

; This is a source integration gate, never a startup/caller assertion. Enabling
; it requires the real selected semantic/physical base and suffix qualification.
(defconst *fn2-checkpoint-activation-qualified* nil)

(defwait :checkpoint-needed :ready fn2-checkpoint-needed-ready-p :grant fn2-checkpoint-needed-grant-one
 :tables (fn2-core-machines)
 :doc "Wake the actual parked maintenance owner from real checkpoint pressure and available pre-cut working resources.")

(defmachine fn2-checkpoint-master
 :states (:idle :disabled :catalog :reserve :workspaces :snapshot-begin :snapshot-poll :descriptor-begin
          :root1-begin :root1-source :root1-read :events-begin :events-source :events-read
          :page-bind :page-take :page-wait :page-consume
          :plan-begin :plan-count :plan-size :plan-reserve :plan-validate :freeze
          :map-begin :map-source :descriptor-source
          :barrier-begin :barrier-source :allocation-begin :allocation-source :allocation-submit :allocation-wait :allocation-empty
          :installation-begin :installation-source :installation-submit :installation-wait
          :retention-begin :retention-source :publish-start :publish-wait :release :release-complete :thaw :event-rearm :rearm :snapshot-release :done
          :admission-refused :refused :uncertain)
 :fields ((pending :u32) (stopped :bool) (token :u60)
          (scan :u32) (highest :u60) (candidate :u32) (candidate-found :bool) (checkpoint :u60)
          (page-slot :u32) (page-gen :u60) (scratch-slot :u32) (scratch-gen :u60) (read-slot :u32) (read-gen :u60)
          (source :u8) (field-base :u32) (map-role :u8) (target :u32) (target-gen :u60)
          (batch :u60) (event :u60) (covered :u60) (retirement-seen :u60))
 :holds ((:workspaces :storage-window) (:snapshot-begin :storage-window) (:snapshot-poll :storage-window)
         (:descriptor-begin :storage-window) (:root1-begin :storage-window) (:root1-source :storage-window)
         (:root1-read :storage-window) (:events-begin :storage-window) (:events-source :storage-window) (:events-read :storage-window)
         (:page-bind :storage-window) (:page-take :storage-window) (:page-wait :storage-window) (:page-consume :storage-window)
         (:plan-begin :storage-window) (:plan-count :storage-window) (:plan-size :storage-window)
         (:plan-reserve :storage-window) (:plan-validate :storage-window) (:freeze :storage-window)
         (:map-begin :storage-window) (:map-source :storage-window) (:descriptor-source :storage-window)
         (:barrier-begin :storage-window) (:barrier-source :storage-window) (:allocation-begin :storage-window)
         (:allocation-source :storage-window) (:allocation-submit :storage-window) (:allocation-wait :storage-window) (:allocation-empty :storage-window)
         (:installation-begin :storage-window) (:installation-source :storage-window) (:installation-submit :storage-window) (:installation-wait :storage-window)
         (:retention-begin :storage-window) (:retention-source :storage-window) (:publish-start :storage-window)
         (:publish-wait :storage-window) (:release :storage-window) (:release-complete :storage-window) (:refused :storage-window) (:uncertain :storage-window))
 :budget (:bytes 16384 :steps 32 :descriptors 4)
 :stops (:checkpoint :pool :bounds)
 :capacity (if (posp (fn2-b-checkpoint-capacity profile)) 1 0)
 :initial ((generation fn2-commit-initial-generation) (phase *fn2-checkpoint-master-state-idle*)
           (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :genesis ((:charge :steps *fn2-work-small* :runnable t))
 :arms ((:idle) (:disabled) (:catalog) (:reserve) (:workspaces) (:snapshot-begin) (:snapshot-poll) (:descriptor-begin)
        (:root1-begin) (:root1-source) (:root1-read) (:events-begin) (:events-source) (:events-read)
        (:page-bind) (:page-take) (:page-wait) (:page-consume)
        (:plan-begin) (:plan-count) (:plan-size) (:plan-reserve) (:plan-validate) (:freeze)
        (:map-begin) (:map-source) (:descriptor-source)
        (:barrier-begin) (:barrier-source) (:allocation-begin) (:allocation-source) (:allocation-submit) (:allocation-wait) (:allocation-empty)
        (:installation-begin) (:installation-source) (:installation-submit) (:installation-wait)
        (:retention-begin) (:retention-source) (:publish-start) (:publish-wait) (:release) (:release-complete) (:thaw) (:event-rearm) (:rearm) (:snapshot-release) (:done)
        (:admission-refused) (:refused) (:uncertain))
 :observes ((:read-result)))
