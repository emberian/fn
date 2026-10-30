; The native adapter's scalar entry points over the live core (layer doc
; 4.1.3). Only the pool's byte array crosses the raw-representation boundary
; (fn2/host/adapter.lisp takes its SAP); every descriptor, loan and post goes
; through these guard-verified functions, so the adapter decides nothing.
(in-package "ACL2")
(include-book "executor")
(include-book "../sim/sim")

(local (in-theory (enable fn2-core-wfp)))

(defmacro fn2-host-ops-update (name target args)
  `(defun ,name (,@args fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
       (fn2-ops) (,target ,@args fn2-ops) fn2-core)))
(fn2-host-ops-update fn2-host-post-result fn2-post-result
  (cell slot gen evkind outcome reason count aux0 aux1))
(fn2-host-ops-update fn2-host-post-accept-result fn2-post-accept-result
  (slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3))
(fn2-host-ops-update fn2-host-post-clock fn2-post-clock (mono real flags))
(fn2-host-ops-update fn2-host-post-signal fn2-post-signal (bits))
(fn2-host-ops-update fn2-host-count-stray fn2-count-stray ())

(defmacro fn2-host-ops-code-update (name target args)
  `(defun ,name (,@args fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
       (code fn2-ops) (,target ,@args fn2-ops) (mv code fn2-core))))
(fn2-host-ops-code-update fn2-host-outbox-ack fn2-outbox-ack (n))
(fn2-host-ops-code-update fn2-host-op-finish fn2-op-finish (slot gen))

(defun fn2-host-outbox-queued (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (count) (fn2-outbox-queued fn2-ops) count))

(defun fn2-host-stray (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (count) (fn2-ops-stray fn2-ops) count))

(defun fn2-host-outbox-peek (k fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code slot gen) (fn2-outbox-peek k fn2-ops) (mv code slot gen)))

; Fixed-width multiple values: no descriptor list and no byte list. A slot
; outside the table is the adapter's error, answered :bounds with no fields.
(defun fn2-host-action (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code kind cap-index cap-nonce range-slot range-gen range-off range-len
          storage-offset fua may-release cancel-slot cancel-gen
          wake-deadline wake-observation-gen)
    (if (not (fn2-op-slotp slot fn2-ops))
        (mv :bounds 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (b* (((mv cap-index cap-nonce) (fn2-op-capability slot fn2-ops))
           ((mv range-slot range-gen range-off range-len) (fn2-op-range slot fn2-ops))
           ((mv storage-offset fua) (fn2-op-storage slot fn2-ops))
           ((mv cancel-slot cancel-gen) (fn2-op-cancel-target slot fn2-ops))
           ((mv wake-deadline wake-observation-gen) (fn2-op-wake slot fn2-ops)))
        (mv :ok (fn2-op-kind slot fn2-ops) cap-index cap-nonce
            range-slot range-gen range-off range-len storage-offset fua
            (fn2-op-may-release slot fn2-ops) cancel-slot cancel-gen
            wake-deadline wake-observation-gen)))
    (mv code kind cap-index cap-nonce range-slot range-gen range-off range-len
        storage-offset fua may-release cancel-slot cancel-gen
        wake-deadline wake-observation-gen)))

(local
 (in-theory
  (disable fn2-ops-rows fn2-ops-gen fn2-ops-phase fn2-ops-kind
           fn2-ops-range-slot fn2-ops-range-gen fn2-ops-range-off fn2-ops-range-len
           fn2-ops-owner-kind fn2-ops-owner-slot fn2-ops-owner-gen
           fn2-pool-rows fn2-pool-gen fn2-pool-cap fn2-pool-base
           fn2-pool-data-length fn2-pool-lease-off fn2-pool-lease-len
           fn2-pool-state fn2-pool-out-count fn2-pool-fill
           fn2-pool-ownerp fn2-pool-input-code)))

; Validate the whole physical loan before exposing its SAP offset. This is
; bounded row access, not a traversal or whole-state invariant check. Both
; queued (take) and submitted (physical execution) descriptors may be checked.
(defun fn2-host-op-span (op gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))
              (fn2-pool (fn2-core-pool fn2-core)))
    (code address length)
    (cond
     ((not (and (natp op) (< op (fn2-ops-rows fn2-ops)))) (mv :bounds 0 0))
     ((not (equal gen (fn2-ops-gen op fn2-ops))) (mv :stale 0 0))
     ((not (or (equal (fn2-ops-phase op fn2-ops) *fn2-op-phase-queued*)
               (equal (fn2-ops-phase op fn2-ops) *fn2-op-phase-submitted*)))
      (mv :state 0 0))
     (t
      (let* ((kind (fn2-ops-kind op fn2-ops))
             (input (or (equal kind *fn2-action-receive*)
                        (equal kind *fn2-action-read*)
                        (equal kind *fn2-action-entropy*)))
             (output (or (equal kind *fn2-action-send*)
                         (equal kind *fn2-action-write*)))
             (slot (fn2-ops-range-slot op fn2-ops))
             (rgen (fn2-ops-range-gen op fn2-ops))
             (off (fn2-ops-range-off op fn2-ops))
             (len (fn2-ops-range-len op fn2-ops)))
        (cond
         ((not (or input output)) (mv :ok 0 0))
         ((not (< slot (fn2-pool-rows fn2-pool))) (mv :bounds 0 0))
         ((not (equal rgen (fn2-pool-gen slot fn2-pool))) (mv :stale 0 0))
         ((or (> (+ off len) (fn2-pool-cap slot fn2-pool))
              (> (+ (fn2-pool-base slot fn2-pool) off len)
                 (fn2-pool-data-length fn2-pool)))
          (mv :bounds 0 0))
         ((if input
              (not (and (eq (fn2-pool-input-code slot rgen op gen fn2-pool) :ok)
                        (equal off (fn2-pool-lease-off slot fn2-pool))
                        (equal len (fn2-pool-lease-len slot fn2-pool))))
            (not (and (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-out*)
                      (< 0 (fn2-pool-out-count slot fn2-pool))
                      (<= (+ off len) (fn2-pool-fill slot fn2-pool))
                      (fn2-pool-ownerp slot (fn2-ops-owner-kind op fn2-ops)
                        (fn2-ops-owner-slot op fn2-ops)
                        (fn2-ops-owner-gen op fn2-ops) fn2-pool))))
          (mv :owner 0 0))
         (t (mv :ok (+ (fn2-pool-base slot fn2-pool) off) len))))))
    (mv code address length)))

; Result normalization (layer doc 4.1.2, 4.1.3): a physical outcome (CODE one
; of :ok :eof :reset :closed :cancelled :no-space :failed; COUNT the octets
; moved, or an Accept's capability index; AUX an Accept's nonce) as the
; simulator's own normalizer states it, so every native completion is one
; the simulator could post.
(defun fn2-host-result (kind code count aux len cancelled)
  (declare (xargs :guard (natp len)))
  (fn2-sim-terminal-values kind code count aux len nil cancelled))

; The configured listener (layer doc 4.1.4): the served profile's
; :listener-address (an IPv4 address as a u32, network order; default
; 127.0.0.1) and :listener-port (a u16; 0 asks the kernel for an ephemeral
; port, which the node reports). Read like :listener-targets, by key; a value
; outside its width is a named refusal to start, never a clamp.
(defconst *fn2-host-loopback* #x7f000001)
(defun fn2-host-listener-bind (profile)
  (declare (xargs :guard t))
  (let ((address (if (assoc-equal :listener-address (and (alistp profile) profile))
                     (fn2-profile-get :listener-address profile) *fn2-host-loopback*))
        (port (if (assoc-equal :listener-port (and (alistp profile) profile))
                  (fn2-profile-get :listener-port profile) 0)))
    (cond ((not (unsigned-byte-p 32 address)) (mv :listener-address 0 0))
          ((not (unsigned-byte-p 16 port)) (mv :listener-port 0 0))
          (t (mv :ok address port)))))

(defun fn2-host-stop-reason (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-stop-reason fn2-core))
(defun fn2-host-idle-deadline (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-idle-deadline fn2-core))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
    fn2-host-count-stray fn2-host-stray fn2-host-outbox-ack fn2-host-op-finish
    fn2-host-outbox-queued fn2-host-outbox-peek fn2-host-action
    fn2-host-op-span fn2-host-result fn2-host-listener-bind fn2-host-stop-reason fn2-host-idle-deadline) (w state)))
