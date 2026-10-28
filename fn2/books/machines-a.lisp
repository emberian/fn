; Layer A machine declarations. The directory carries only (kind, slot);
; every machine field lives in its kind's own struct of arrays.
(in-package "ACL2")
(include-book "machines")
(include-book "profile")

(in-theory (disable fn2-profile-generation-start fn2-profile-generation-limit
                    fn2-profile-accept-credits fn2-profile-c
                    fn2-profile-run-bytes fn2-profile-run-steps fn2-profile-run-descriptors))

(defun fn2-machine-initial-generation (slot base n gen)
  (declare (xargs :guard t) (ignore slot base n)) gen)
(defun fn2-machine-initial-next-free (slot base n gen)
  (declare (xargs :guard t) (ignore gen))
  (if (< (+ (nfix slot) 1) (nfix n)) (+ (nfix base) (nfix slot) 1) 4294967295))

(defmachine fn2-listener
 :states (:accepting :closing)
 :fields ((cap-index :u32) (cap-nonce :u32) (pending :u32) (stopped :bool) (event-ready :bool) (mode :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-accept-credits profile)
 :initial ((generation fn2-machine-initial-generation) (ready-prev 4294967295) (ready-next 4294967295)
           (phase *fn2-listener-state-accepting*) (mode 1))
 :observes ((:accept-result fn2-listener-observe-accept) (:close-result fn2-listener-observe-close))
 :continuations ((:accepting fn2-listener-step) (:closing fn2-listener-step)))

(defmachine fn2-echo
 :states (:free :command :reply :closing :draining :retired)
 :fields ((cap-index :u32) (cap-nonce :u32) (pool-slot :u32) (pool-gen :u60)
          (off :u32) (length :u32) (pending :u32) (borrows :u32)
          (next-free :u32) (stopped :bool) (mode :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 :initial ((generation fn2-machine-initial-generation) (ready-prev 4294967295) (ready-next 4294967295)
           (pool-slot 4294967295) (next-free fn2-machine-initial-next-free))
 :observes ((:receive-result fn2-echo-observe-receive) (:send-result fn2-echo-observe-send)
            (:borrow-released fn2-echo-observe-release) (:close-result fn2-echo-observe-close))
 :continuations ((:free fn2-connection-idle) (:command fn2-connection-submit)
                 (:reply fn2-connection-reply) (:closing fn2-connection-submit)
                 (:draining fn2-connection-drain) (:retired fn2-connection-idle)))

(defmachine fn2-scribe
 :states (:free :reserve :fill :patch :write :write-result :fence :fence-result :reset :read :read-result :verify :next :stopped)
 :fields ((pool-slot :u32) (pool-gen :u60) (pending :u32) (borrows :u32)
          (sequence :u32) (cursor :u32) (checksum :u32) (completed :u32)
          (verified :u32) (stopped :bool) (event :u8) (outcome :u8)
          (count :u32) (aux0 :u32) (aux1 :u32) (event-ready :bool))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((generation fn2-machine-initial-generation) (ready-prev 4294967295) (ready-next 4294967295)
           (pool-slot 4294967295) (sequence 1))
 :observes ((:write-result fn2-scribe-observe) (:fence-result fn2-scribe-observe) (:read-result fn2-scribe-observe))
 :continuations ((:free fn2-scribe-idle) (:reserve fn2-scribe-reserve) (:fill fn2-scribe-fill-run)
                 (:patch fn2-scribe-patch) (:write fn2-scribe-write) (:write-result fn2-scribe-result)
                 (:fence fn2-scribe-fence) (:fence-result fn2-scribe-result) (:reset fn2-scribe-reset)
                 (:read fn2-scribe-read) (:read-result fn2-scribe-result) (:verify fn2-scribe-verify-run)
                 (:next fn2-scribe-next) (:stopped fn2-scribe-idle)))

(fn2-machine-index-events)
(in-theory (disable fn2-machine-local-id))

(defcolumns fn2-machines ((kind :u8) (slot :u32))
 :init-name fn2-machines-columns-init
 :extra-fields
  ((fn2-machines-accept-count :type (unsigned-byte 32) :initially 0)
   (fn2-machines-connection-count :type (unsigned-byte 32) :initially 0)
   (fn2-machines-free-head :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-gen-limit :type (unsigned-byte 60) :initially 0)
   (fn2-machines-wake-id :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-pool-wait-id :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-wait-head :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-wait-tail :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-refusals :type (unsigned-byte 60) :initially 0)
   (fn2-machines-active-count :type (unsigned-byte 32) :initially 0)))

(defun fn2-machines-init-rows (left profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :measure (nfix left)
                  :guard (and (natp left) (<= left (fn2-machines-rows fn2-machines))
                              (fn2-profilep profile) (fn2-machines-wfp fn2-machines))))
  (if (or (zp left) (> left (fn2-machines-rows fn2-machines))) fn2-machines
    (mv-let (kind slot) (fn2-machine-local-id (- left 1) profile)
      (let* ((fn2-machines (fn2-machines-set-kind (- left 1) (if (unsigned-byte-p 8 kind) kind 255) fn2-machines))
             (fn2-machines (fn2-machines-set-slot (- left 1) (if (unsigned-byte-p 32 slot) slot 0) fn2-machines)))
        (fn2-machines-init-rows (- left 1) profile fn2-machines)))))
(fn2-machines-shape fn2-machines-init-rows (left profile))

(defun fn2-machines-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile)
       ; Resident capacities vary with the profile. These continuations use
       ; the simultaneous quanta recorded in their declarations.
       (equal (fn2-profile-run-bytes profile) 4096)
       (equal (fn2-profile-run-steps profile) 32)
       (equal (fn2-profile-run-descriptors profile) 4)
       (unsigned-byte-p 32 (fn2-profile-accept-credits profile))
       (unsigned-byte-p 32 (fn2-profile-c profile))
       (< (fn2-machine-index-count profile)
          4294967296)))

(defun fn2-machines-init (profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :guard (fn2-machines-profilep profile)))
  (let* ((a (fn2-profile-accept-credits profile)) (c (fn2-profile-c profile))
         (n (fn2-machine-index-count profile))
         (fn2-machines (fn2-machines-columns-init n fn2-machines))
         (fn2-machines (update-fn2-machines-accept-count a fn2-machines))
         (fn2-machines (update-fn2-machines-connection-count c fn2-machines))
         (fn2-machines (update-fn2-machines-free-head a fn2-machines))
         (fn2-machines (update-fn2-machines-refusals 0 fn2-machines))
         (fn2-machines (update-fn2-machines-active-count 0 fn2-machines))
         (fn2-machines (update-fn2-machines-gen-limit
                        (fn2-profile-generation-limit profile) fn2-machines))
         (fn2-machines (update-fn2-machines-wake-id 4294967295 fn2-machines))
         (fn2-machines (update-fn2-machines-pool-wait-id 4294967295 fn2-machines))
         (fn2-machines (update-fn2-machines-wait-head 4294967295 fn2-machines))
         (fn2-machines (update-fn2-machines-wait-tail 4294967295 fn2-machines)))
    (fn2-machines-init-rows n profile fn2-machines)))
(defthm fn2-machines-init-type
  (implies (and (fn2-machinesp fn2-machines) (fn2-machines-profilep profile))
           (fn2-machinesp (fn2-machines-init profile fn2-machines))))
(defthm fn2-machines-init-wfp
  (implies (fn2-machines-profilep profile)
           (fn2-machines-wfp (fn2-machines-init profile fn2-machines))))
(in-theory (disable fn2-machines-init fn2-machines-profilep))
(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-machines-init-rows
    fn2-machines-profilep fn2-machines-init) (w state)))
