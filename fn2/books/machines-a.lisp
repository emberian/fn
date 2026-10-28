; Layer A machine declarations. The directory carries only (kind, slot);
; every machine field lives in its kind's own struct of arrays.
(in-package "ACL2")
(include-book "machines")
(include-book "profile")

(in-theory (disable fn2-profile-generation-start fn2-profile-generation-limit
                    fn2-profile-accept-credits fn2-profile-c
                    fn2-profile-run-bytes fn2-profile-run-steps fn2-profile-run-descriptors))

(defmachine fn2-listener
 :states (:accepting :closing)
 :fields ((cap-index :u32) (cap-nonce :u32) (pending :u32) (stopped :bool) (event-ready :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-accept-credits profile)
 :initial ((generation gen) (ready-prev 4294967295) (ready-next 4294967295)
            (phase *fn2-listener-state-accepting*))
 :observes ((:accept-result (fn2-listener-observe-accept id outcome aux0 aux1 fn2-core))
            (:close-result (let ((fn2-core (fn2-listener-put-core id
                             (phase *fn2-listener-state-accepting*) (event-ready 0))))
                             (mv id fn2-core))))
 :continuations
 ((:accepting (fn2-listener-step id t budget fn2-core))
  (:closing (fn2-listener-step id nil budget fn2-core))))

(defmachine fn2-echo
 :states (:free :command :reply :closing :draining :retired)
 :fields ((cap-index :u32) (cap-nonce :u32) (pool-slot :u32) (pool-gen :u60)
          (off :u32) (length :u32) (pending :u32) (borrows :u32)
          (next-free :u32) (stopped :bool) (mode :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 :initial ((generation gen) (ready-prev 4294967295) (ready-next 4294967295)
            (pool-slot 4294967295) (next-free (if (< (+ slot 1) n) (+ base slot 1) 4294967295)))
 :observes ((:receive-result (fn2-echo-observe-receive id outcome count fn2-core))
            (:send-result (fn2-echo-observe-send id outcome count fn2-core))
            (:borrow-released (let ((fn2-core (fn2-machine-write-borrows id
                 (fn2-machine-pool-borrows (fn2-machine-pool-slot id fn2-core) fn2-core) fn2-core)))
                 (mv id fn2-core)))
            (:close-result (let ((fn2-core (fn2-echo-put-core id (phase *fn2-echo-state-draining*))))
                             (mv id fn2-core))))
 :continuations
 ((:free (fn2-machine-idle id fn2-core))
  (:command (fn2-connection-submit id *fn2-echo-state-command* budget fn2-core))
  (:reply (fn2-connection-reply id budget fn2-core))
  (:closing (fn2-connection-submit id *fn2-echo-state-closing* budget fn2-core))
  (:draining (fn2-connection-drain id fn2-core))
  (:retired (fn2-machine-idle id fn2-core))))

(defmachine fn2-scribe
 :states (:free :reserve :fill :patch :write :write-result :fence :fence-result :reset :read :read-result :verify :next :stopped)
 :fields ((pool-slot :u32) (pool-gen :u60) (pending :u32) (borrows :u32)
          (sequence :u32) (cursor :u32) (checksum :u32) (completed :u32)
          (verified :u32) (stopped :bool) (event :u8) (outcome :u8)
          (count :u32) (aux0 :u32) (aux1 :u32) (event-ready :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((generation gen) (ready-prev 4294967295) (ready-next 4294967295)
            (pool-slot 4294967295) (sequence 1))
 :observes ((:write-result (fn2-scribe-observe id event outcome count aux0 aux1 fn2-core))
            (:fence-result (fn2-scribe-observe id event outcome count aux0 aux1 fn2-core))
            (:read-result (fn2-scribe-observe id event outcome count aux0 aux1 fn2-core)))
 :continuations
 ((:free (fn2-machine-idle id fn2-core))
  (:reserve (fn2-scribe-reserve id fn2-core))
  (:fill (fn2-scribe-fill-run id fn2-core))
  (:patch (fn2-scribe-patch id fn2-core))
  (:write (if (and (natp budget) (< 0 budget)) (fn2-scribe-write id fn2-core) (fn2-machine-yield id fn2-core)))
  (:write-result (fn2-scribe-result id fn2-core))
  (:fence (if (and (natp budget) (< 0 budget)) (fn2-scribe-fence id fn2-core) (fn2-machine-yield id fn2-core)))
  (:fence-result (fn2-scribe-result id fn2-core))
  (:reset (fn2-scribe-reset id fn2-core))
  (:read (if (and (natp budget) (< 0 budget)) (fn2-scribe-read id fn2-core) (fn2-machine-yield id fn2-core)))
  (:read-result (fn2-scribe-result id fn2-core))
  (:verify (fn2-scribe-verify-run id fn2-core))
  (:next (fn2-scribe-next id fn2-core))
  (:stopped (fn2-machine-idle id fn2-core))))
