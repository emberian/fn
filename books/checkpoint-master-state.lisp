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
; Byte quota for the real root1 callback. Structural step accounting remains
; a separate leaf contract; these inequalities do not establish it.
(defconst *fn2-checkpoint-root1-turn-bytes* (+ *fn2-c-read-callback-bytes* 4096))
(defconst *fn2-checkpoint-master-byte-budget* (+ 16384 (* 2 *fn2-c-read-callback-bytes*)))
(assert-event (<= (+ *fn2-c-read-callback-bytes* *fn2-checkpoint-root1-turn-bytes*)
                 *fn2-checkpoint-master-byte-budget*))


(defwait :checkpoint-needed :ready fn2-checkpoint-needed-ready-p :grant fn2-checkpoint-needed-grant-one
 :tables (fn2-core-machines)
 :doc "Wake the actual parked maintenance owner from real checkpoint pressure and available pre-cut working resources.")

(defmachine fn2-checkpoint-master
 :states (:idle :disabled :catalog :reserve :workspaces :snapshot-begin :snapshot-poll :directory :abort-empty :abort-snapshot :abort-working :abort-complete :descriptor-begin
          :root1-begin :root1-source :root1-read :events-begin :events-source :events-read
          :page-bind :page-take :page-wait :page-accept-return :page-consume
          :plan-begin :plan-count :plan-size :plan-reserve :plan-validate :freeze
          :map-begin :map-source :descriptor-source
          :barrier-begin :barrier-source :allocation-begin :allocation-source :allocation-submit :allocation-wait :allocation-empty
          :installation-begin :installation-source :installation-submit :installation-wait
          :retention-begin :retention-source :publish-start :publish-wait :release :release-complete :thaw :event-rearm :rearm :snapshot-release :teardown-begin :teardown-source :teardown-submit :teardown-wait :teardown-drop :teardown-holding-uncertain :teardown-uncertain :teardown-retained :done
          :admission-refused :refused :uncertain :loan-uncertain
          :summary-authority-begin :summary-authority-copy :rebase-begin :rebase-source :rebase-consume :rebase-archive
          :teardown-transfer-begin :teardown-transfer-copy :teardown-select
          :teardown-cold-next :teardown-cold-begin :teardown-cold-copy :teardown-cold-ack
          :inventory-transfer)
 :fields ((pending :u32) (stopped :bool) (token :u60)
          (scan :u32) (highest :u60) (candidate :u32) (candidate-found :bool) (checkpoint :u60)
          (page-slot :u32) (page-gen :u60) (scratch-slot :u32) (scratch-gen :u60) (read-slot :u32) (read-gen :u60)
          (source :u8) (field-base :u32) (map-role :u8) (target :u32) (target-gen :u60)
          (teardown-extent :u32) (teardown-epoch :u60) (teardown-allocation :u60)
          (batch :u60) (event :u60) (covered :u60) (retirement-seen :u60) (attempt-retirement :u60) (debt-scan :u32))
 :holds ((:teardown-wait :storage-window) (:teardown-holding-uncertain :storage-window)
         (:workspaces :storage-window :storage-window)
         (:directory :storage-window :storage-window) (:abort-snapshot :storage-window :storage-window)
         (:abort-working :storage-window :storage-window) (:abort-complete :storage-window :storage-window)
         (:descriptor-begin :storage-window :storage-window) (:root1-begin :storage-window :storage-window) (:root1-source :storage-window :storage-window)
         (:root1-read :storage-window :storage-window) (:events-begin :storage-window :storage-window) (:events-source :storage-window :storage-window) (:events-read :storage-window :storage-window)
         (:page-bind :storage-window :storage-window) (:page-take :storage-window :storage-window) (:page-wait :storage-window) (:page-accept-return :storage-window) (:page-consume :storage-window :storage-window)
         (:plan-begin :storage-window :storage-window) (:plan-count :storage-window :storage-window) (:plan-size :storage-window :storage-window)
         (:plan-reserve :storage-window :storage-window) (:plan-validate :storage-window :storage-window) (:freeze :storage-window :storage-window)
         (:map-begin :storage-window :storage-window) (:map-source :storage-window :storage-window) (:descriptor-source :storage-window :storage-window)
         (:barrier-begin :storage-window :storage-window) (:barrier-source :storage-window :storage-window) (:allocation-begin :storage-window :storage-window)
         (:allocation-source :storage-window :storage-window) (:allocation-submit :storage-window :storage-window) (:allocation-wait :storage-window :storage-window) (:allocation-empty :storage-window :storage-window)
         (:installation-begin :storage-window :storage-window) (:installation-source :storage-window :storage-window) (:installation-submit :storage-window :storage-window) (:installation-wait :storage-window :storage-window)
         (:retention-begin :storage-window :storage-window) (:retention-source :storage-window :storage-window) (:publish-start :storage-window :storage-window)
         (:publish-wait :storage-window :storage-window) (:release :storage-window :storage-window) (:release-complete :storage-window :storage-window) (:refused :storage-window :storage-window) (:uncertain :storage-window :storage-window) (:loan-uncertain :storage-window)
          (:summary-authority-begin :storage-window :storage-window) (:summary-authority-copy :storage-window :storage-window)
          (:rebase-begin :storage-window :storage-window) (:rebase-source :storage-window :storage-window) (:rebase-consume :storage-window :storage-window) (:rebase-archive :storage-window :storage-window))
 :budget-cost (:bytes *fn2-checkpoint-master-byte-budget* :steps 32 :descriptors 4)
 :stops (:checkpoint :pool :bounds)
 :capacity (if (posp (fn2-b-checkpoint-capacity profile)) 1 0)
 :initial ((generation fn2-commit-initial-generation) (phase *fn2-checkpoint-master-state-idle*)
           (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :genesis ((:charge :steps *fn2-work-small* :runnable t))
 :arms ((:idle) (:disabled) (:catalog) (:reserve) (:workspaces) (:snapshot-begin) (:snapshot-poll) (:directory) (:abort-empty) (:abort-snapshot) (:abort-working) (:abort-complete) (:descriptor-begin)
        (:root1-begin) (:root1-source) (:root1-read) (:events-begin) (:events-source) (:events-read)
        (:page-bind) (:page-take) (:page-wait) (:page-accept-return) (:page-consume)
        (:plan-begin) (:plan-count) (:plan-size) (:plan-reserve) (:plan-validate) (:freeze)
        (:map-begin) (:map-source) (:descriptor-source)
        (:barrier-begin) (:barrier-source) (:allocation-begin) (:allocation-source) (:allocation-submit) (:allocation-wait) (:allocation-empty)
        (:installation-begin) (:installation-source) (:installation-submit) (:installation-wait)
        (:retention-begin) (:retention-source) (:publish-start) (:publish-wait) (:release) (:release-complete) (:thaw) (:event-rearm) (:rearm) (:snapshot-release) (:teardown-begin) (:teardown-source) (:teardown-submit) (:teardown-wait) (:teardown-drop) (:teardown-holding-uncertain) (:teardown-uncertain) (:teardown-retained) (:done)
        (:admission-refused) (:refused) (:uncertain) (:loan-uncertain)
          (:summary-authority-begin) (:summary-authority-copy) (:rebase-begin) (:rebase-source) (:rebase-consume) (:rebase-archive)
          (:teardown-transfer-begin) (:teardown-transfer-copy) (:teardown-select)
          (:teardown-cold-next) (:teardown-cold-begin) (:teardown-cold-copy) (:teardown-cold-ack)
          (:inventory-transfer))
 :observes ((:read-result)))
