; Layer A machine declarations. The directory carries only (kind, slot);
; every machine field lives in its kind's own struct of arrays.
(in-package "ACL2")
(include-book "machines")
(include-book "profile")

(in-theory (disable fn2-profile-generation-start fn2-profile-generation-limit
                    fn2-profile-accept-credits fn2-profile-c))

(defun fn2-machine-initial-generation (slot base n gen)
  (declare (xargs :guard t) (ignore slot base n)) gen)
(defun fn2-machine-initial-next-free (slot base n gen)
  (declare (xargs :guard t) (ignore gen))
  (if (< (+ (nfix slot) 1) (nfix n)) (+ (nfix base) (nfix slot) 1) *fn2-none*))

(defmachine fn2-listener
 :states (:accepting :closing)
 :fields ((cap-index :u32) (cap-nonce :u32) (pending :u32) (stopped :bool) (event-ready :bool) (mode :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-accept-credits profile)
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (phase *fn2-listener-state-accepting*) (mode 1))
 :observes ((:accept-result fn2-listener-observe-accept) (:close-result fn2-listener-observe-close))
 :continuations ((:accepting fn2-listener-step) (:closing fn2-listener-step)))

(defmachine fn2-echo
 :states (:free :command :reply :closing :draining :retired)
 :fields ((cap-index :u32) (cap-nonce :u32) (pool-slot :link) (pool-gen :u60)
          (off :u32) (length :u32) (pending :u32) (borrows :u32)
          (next-free :link) (stopped :bool) (mode :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (pool-slot *fn2-none*) (next-free fn2-machine-initial-next-free))
 :observes ((:receive-result fn2-echo-observe-receive) (:send-result fn2-echo-observe-send)
            (:borrow-released fn2-echo-observe-release) (:close-result fn2-echo-observe-close))
 :continuations ((:free fn2-connection-idle) (:command fn2-connection-submit)
                 (:reply fn2-connection-reply) (:closing fn2-connection-submit)
                 (:draining fn2-connection-drain) (:retired fn2-connection-idle)))

(defmachine fn2-scribe
 :states (:free :reserve :fill :patch :write :write-result :fence :fence-result :reset :read :read-result :verify :next :stopped)
 :fields ((pool-slot :link) (pool-gen :u60) (pending :u32) (borrows :u32)
          (sequence :u32) (cursor :u32) (checksum :u32) (completed :u32)
          (verified :u32) (stopped :bool) (event :u8) (outcome :u8)
          (count :u32) (aux0 :u32) (aux1 :u32) (event-ready :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (pool-slot *fn2-none*) (sequence 1))
 :observes ((:write-result fn2-scribe-observe) (:fence-result fn2-scribe-observe) (:read-result fn2-scribe-observe))
 :continuations ((:free fn2-scribe-idle) (:reserve fn2-scribe-reserve) (:fill fn2-scribe-fill-run)
                 (:patch fn2-scribe-patch) (:write fn2-scribe-write) (:write-result fn2-scribe-result)
                 (:fence fn2-scribe-fence) (:fence-result fn2-scribe-result) (:reset fn2-scribe-reset)
                 (:read fn2-scribe-read) (:read-result fn2-scribe-result) (:verify fn2-scribe-verify-run)
                 (:next fn2-scribe-next) (:stopped fn2-scribe-idle)))
