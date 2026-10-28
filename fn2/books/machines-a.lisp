; Layer A resident machine rows. Global indices are listener credits, then
; connection rows, then the single storage probe. No per-machine allocation.
(in-package "ACL2")
(include-book "columns")
(include-book "profile")
(in-theory (disable fn2-profile-generation-start fn2-profile-generation-limit
                    fn2-profile-accept-credits fn2-profile-c
                    fn2-profile-run-bytes fn2-profile-run-steps
                    fn2-profile-run-descriptors))

(defcolumns fn2-machines
  ((phase :u8) (generation :u60) (principal-slot :u16)
   (account-ref :u32) (ready-prev :u32) (ready-next :u32)
   (wait-reason :u8) (deadline :u60)
   (kind (:enum fn2-machine-kind (:listener :echo :null :scribe)))
   (cap-index :u32) (cap-nonce :u32) (pool-slot :u32) (pool-gen :u60)
   (off :u32) (length :u32) (pending :u32) (borrows :u32)
   (next-free :u32) (sequence :u32) (cursor :u32) (checksum :u32)
   (completed :u32) (verified :u32) (stopped :bool)
   (event :u8) (outcome :u8) (count :u32) (aux0 :u32) (aux1 :u32)
   (event-ready :bool))
  :rows-bound 4294967296
  :init-name fn2-machines-columns-init
  :extra-fields
  ((fn2-machines-accept-count :type (unsigned-byte 32) :initially 0)
   (fn2-machines-connection-count :type (unsigned-byte 32) :initially 0)
   (fn2-machines-free-head :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-gen-limit :type (unsigned-byte 60) :initially 0)
   (fn2-machines-echo-mode :type (unsigned-byte 1) :initially 1)
   (fn2-machines-wake-id :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-pool-wait-id :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-wait-head :type (unsigned-byte 32) :initially 4294967295)
   (fn2-machines-wait-tail :type (unsigned-byte 32) :initially 4294967295)))

; 0 free/inactive, 1 accepting, 2 command/receive, 3 reply/send,
; 4 closing, 5 draining, 6 retired. Scribe owns phase codes 16..31.
(defconst *fn2-machine-free* 0)
(defconst *fn2-machine-accepting* 1)
(defconst *fn2-machine-command* 2)
(defconst *fn2-machine-reply* 3)
(defconst *fn2-machine-closing* 4)
(defconst *fn2-machine-draining* 5)
(defconst *fn2-machine-retired* 6)

(defun fn2-machines-put-bindings (fields)
  (if (atom fields) nil
    (cons `(fn2-machines
            (,(fn2-columns-col-name 'fn2-machines
                (fn2-columns-pre "SET-" (caar fields)))
             slot ,(cadar fields) fn2-machines))
          (fn2-machines-put-bindings (cdr fields)))))
(defmacro fn2-machines-put (&rest fields)
  `(let* ,(fn2-machines-put-bindings fields) fn2-machines))

(defmacro fn2-machines-shape (name args)
  `(progn
     (defthm ,(fn2-columns-sym name "-TYPE")
       (implies (and (fn2-machinesp fn2-machines) (fn2-machines-wfp fn2-machines))
                (fn2-machinesp (,name ,@args fn2-machines))))
     (defthm ,(fn2-columns-sym name "-WFP")
       (implies (fn2-machines-wfp fn2-machines)
                (fn2-machines-wfp (,name ,@args fn2-machines))))
     (defthm ,(fn2-columns-sym name "-ROWS")
       (equal (fn2-machines-rows (,name ,@args fn2-machines))
              (fn2-machines-rows fn2-machines)))
     (defthm ,(fn2-columns-sym name "-RAW-ROWS")
       (equal (nth *fn2-machines-rows* (,name ,@args fn2-machines))
              (nth *fn2-machines-rows* fn2-machines))
       :hints (("Goal" :use ,(fn2-columns-sym name "-ROWS"))))
     (in-theory (disable ,name))))

(defun fn2-machines-init-row (slot accepts connections gen fn2-machines)
  (declare (xargs :stobjs fn2-machines :guard (fn2-machines-wfp fn2-machines)))
  (if (not (and (natp slot) (< slot (fn2-machines-rows fn2-machines))
                (unsigned-byte-p 32 accepts) (unsigned-byte-p 32 connections)
                (unsigned-byte-p 60 gen))) fn2-machines
    (fn2-machines-put
      (phase (if (< slot accepts) 1 0)) (generation gen)
      (principal-slot 0) (account-ref 0)
      (ready-prev 4294967295) (ready-next 4294967295)
      (wait-reason 0) (deadline 0)
      (kind (cond ((< slot accepts) 0)
                  ((< slot (+ accepts connections)) 1) (t 3)))
      (cap-index 0) (cap-nonce 0) (pool-slot 4294967295) (pool-gen 0)
      (off 0) (length 0) (pending 0) (borrows 0)
      (next-free (if (and (<= accepts slot)
                         (< (+ 1 slot) (+ accepts connections))
                         (< (+ 1 slot) 4294967296)) (+ 1 slot) 4294967295))
      (sequence 1) (cursor 0) (checksum 0) (completed 0) (verified 0)
      (stopped 0) (event 0) (outcome 0) (count 0) (aux0 0) (aux1 0)
      (event-ready 0))))
(fn2-machines-shape fn2-machines-init-row (slot accepts connections gen))

(defun fn2-machines-init-rows (left accepts connections gen fn2-machines)
  (declare (xargs :stobjs fn2-machines
                  :guard (and (natp left) (fn2-machines-wfp fn2-machines))
                  :measure (nfix left)))
  (if (zp left) fn2-machines
    (let ((fn2-machines (fn2-machines-init-row
                         (- left 1) accepts connections gen fn2-machines)))
      (fn2-machines-init-rows (- left 1) accepts connections gen fn2-machines))))
(fn2-machines-shape fn2-machines-init-rows (left accepts connections gen))

(defun fn2-machines-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile)
       ; These first machines implement the declared simultaneous quanta.
       ; Profiles may vary residency; changing quanta requires a machine DSL
       ; lowering that parameterizes every structural continuation too.
       (equal (fn2-profile-run-bytes profile) 4096)
       (equal (fn2-profile-run-steps profile) 32)
       (equal (fn2-profile-run-descriptors profile) 4)
       (unsigned-byte-p 32 (fn2-profile-accept-credits profile))
       (unsigned-byte-p 32 (fn2-profile-c profile))
       (< (+ (fn2-profile-accept-credits profile) (fn2-profile-c profile) 1)
          4294967296)))

(defun fn2-machines-init (profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :guard (fn2-machines-profilep profile)))
  (let* ((a (fn2-profile-accept-credits profile)) (c (fn2-profile-c profile))
         (n (+ a c 1))
         (fn2-machines (fn2-machines-columns-init n fn2-machines))
         (fn2-machines (update-fn2-machines-accept-count a fn2-machines))
         (fn2-machines (update-fn2-machines-connection-count c fn2-machines))
         (fn2-machines (update-fn2-machines-free-head a fn2-machines))
         (fn2-machines (update-fn2-machines-gen-limit
                        (fn2-profile-generation-limit profile) fn2-machines))
         (fn2-machines (update-fn2-machines-echo-mode 1 fn2-machines))
         (fn2-machines (update-fn2-machines-wake-id 4294967295 fn2-machines))
         (fn2-machines (update-fn2-machines-pool-wait-id 4294967295 fn2-machines))
         (fn2-machines (update-fn2-machines-wait-head 4294967295 fn2-machines))
         (fn2-machines (update-fn2-machines-wait-tail 4294967295 fn2-machines)))
    (fn2-machines-init-rows n a c (fn2-profile-generation-start profile) fn2-machines)))
(defthm fn2-machines-init-type
  (implies (and (fn2-machinesp fn2-machines) (fn2-machines-profilep profile))
           (fn2-machinesp (fn2-machines-init profile fn2-machines))))
(defthm fn2-machines-init-wfp
  (implies (fn2-machines-profilep profile)
           (fn2-machines-wfp (fn2-machines-init profile fn2-machines))))
(in-theory (disable fn2-machines-init fn2-machines-profilep))
(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-machines-init-row fn2-machines-init-rows
    fn2-machines-profilep fn2-machines-init) (w state)))
