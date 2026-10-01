;;; PARKED at stage 0 (2026-10-01; planning/design-store-representation-2026-10-01.md
;;; section 4, MODE 2026-10-01 section 3): the receiver-turn, index-connection
;;; and admission-input host functions of host/native/owner.lisp (Codex,
;;; e3f6720ef and after).  No loaded host line calls any of them; their leaves
;;; fnn-receiver-publish-fill and fnn-receiver-backing are defined nowhere, and
;;; their counterparts fn-owner-rx-* and fn-owner-index-* are outside both
;;; image worlds (host_check --world).  No build loads this file (the structs
;;; they use stay in owner.lisp); the receiver turn returns to the served path
;;; with its producer (codex-era-architecture-review section 5, F03:
;;; KEEP-PARKED -> KEEP-AND-WIRE: a real fn-owner-runtime-receiver-source,
;;; the fnn-owner-run startup and the handle-chunk routing).

(in-package "ACL2")

;; Internal constructor subject for startup funding. This does not issue a
;; receiver or establish installation; the paired core install follows it.
(defun fnn-owner-receiver-runtime-make
    (provider token range-callback fence-callback limits)
  (%make-fnn-owner-receiver-runtime
   :provider provider :token token :range-callback range-callback
   :fence-callback fence-callback :limits limits))

(defun fnn-owner-receiver-turn-runtime-make
    (token current turn-start copy-next copy-ack fence limits &optional parser)
  (%make-fnn-owner-receiver-turn-runtime
   :capacity-token token :current current :turn-start turn-start
   :copy-next copy-next :copy-ack copy-ack :fence fence :limits limits :parser parser))

(defun fnn-owner-connection-open-locked (service kind family address peer)
  "Return CID and its directly retained native node. No retained-path fallback."
  (unless (fnn-owner-connection-selected-p service)
    (return-from fnn-owner-connection-open-locked
      (values (case kind
                (:reader (fnn-owner-core 'fn-owner-open))
                (:exposure (fnn-owner-core 'fn-owner-exposure-open family address peer))
                (:peer (fnn-owner-core 'fn-owner-open-peer peer))
                (otherwise (fnn-fixed-callback-fail 'fnn-owner-connection-open-locked :unknown-open-kind kind))) nil)))
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (fnn-owner-receiver-turn-runtime-p
              (fnn-owner-service-receiver-runtime service))
      (fnn-fixed-callback-fail 'fn-owner-index-rx-open :receiver-startup-incomplete nil))
    (when (fnn-owner-service-connection-raw-token service)
      (fnn-fixed-callback-fail 'fn-owner-index-connection-start :raw-token-already-held nil))
    (multiple-value-bind (erp word token fuel mio pool state)
        (fnn-core-mv 'fn-owner-index-connection-start
          (funcall (fnn-owner-service-connection-start service)
                   kind family address peer
                   (fnn-owner-service-connection-mio service)
                   (fnn-owner-service-connection-pool service) *the-live-state*))
      (declare (ignore state))
      ;; ANY acquired result survives even a simultaneous error/refusal. This
      ;; assignment precedes inspecting ERP/WORD and all subsequent allocation.
      (setf (fnn-owner-service-connection-raw-token service) token
            (fnn-owner-service-connection-mio service) mio
            (fnn-owner-service-connection-pool service) pool
            (fnn-owner-service-connection-fuel service) fuel)
      (when erp (fnn-fixed-callback-fail 'fn-owner-index-connection-start :issuer-error erp))
      (unless (eq word :reserved)
        (when token (fnn-fixed-callback-fail 'fn-owner-index-connection-start :issuer-retained word))
        (fnn-refuse "connection issuer refused: ~a" word))
      (unless token (fnn-fixed-callback-fail 'fn-owner-index-connection-start :issuer-token-missing nil))
      (let ((node (fnn-connection-custody-publish-raw service)))
        (multiple-value-bind (open-erp result mio1 pool1 state1)
            (fnn-core-mv 'fn-owner-index-rx-open
              (funcall (fnn-owner-service-connection-open service)
                       kind family address peer token fuel mio
                       (fnn-owner-receiver-turn-runtime-provider
                         (fnn-owner-service-receiver-runtime service))
                       (fnn-owner-receiver-turn-runtime-turn
                         (fnn-owner-service-receiver-runtime service))
                       (fnn-owner-receiver-turn-runtime-current
                         (fnn-owner-service-receiver-runtime service))
                       pool *the-live-state*))
          (declare (ignore state1))
          (setf (fnn-owner-service-connection-mio service) mio1
                (fnn-owner-service-connection-pool service) pool1)
          (when open-erp (fnn-fixed-callback-fail 'fn-owner-index-rx-open :open-error open-erp))
          (case (first result)
            (:opened
             (setf (fnn-connection-custody-cid node) (second result)
                   (fnn-connection-custody-phase node) :live)
             (values (second result) node))
            ((:refused :unavailable :stale)
             (when (third result) (fnn-fixed-callback-fail 'fn-owner-index-rx-open :refused-retained result))
             ;; This result means the composed open actually aborted/released.
             (fnn-connection-custody-released service node)
             (values nil nil))
            (otherwise (fnn-fixed-callback-fail 'fn-owner-index-rx-open :open-unresolved result))))))))

(defun fnn-owner-connection-repin-joined-locked (service old new word)
  "Transport the actual completion word; never infer acceptance from scalars."
  (case word
    (:committed-repin-released
     (fnn-connection-custody-released service old)
     (setf (fnn-connection-custody-phase new) :live
           (fnn-connection-custody-cid new) (fnn-connection-custody-cid old))
     new)
    (:committed-repin-held
     (setf (fnn-connection-custody-phase old) :retiring
           (fnn-connection-custody-phase new) :live
           (fnn-connection-custody-cid new) (fnn-connection-custody-cid old))
     new)
    (:committed-repin-aborted
     ;; Only the receipt's persisted actual abort/release disposition permits
     ;; forgetting this prepared NEW node. OLD remains the active endpoint.
     (fnn-connection-custody-released service new)
     old)
    ;; Ordinary commit carries no authority over a separately pending NEW.
    (:committed old)
    (otherwise (fnn-fixed-callback-fail 'fnn-owner-connection-repin-joined-locked :repin-unresolved word))))

;;; Fixed-arity physical copy quantum. Caller holds owner then extent locks,
;;; and supplies startup-installed selected callbacks/live paired stobjs.
;;; The guarded core emits all endpoints; native never derives a copy range.
;;; This adapter is inactive until the paired controller/startup carry lands.
(defun fnn-owner-incoming-copy-step
    (job next-callback ack-callback controller pool)
  (multiple-value-bind (word start count end controller1 pool1)
      (fnn-core-mv 'fn-owner-incoming-copy-next
        (funcall next-callback (fnn-owner-admission-job-input-token job)
                 controller pool))
    (case word
      (:copy
       (handler-case
           ;; Capacity was installed under retained charge before START.
           ;; This quantum replaces bytes only; it never reserves/resizes.
           (replace (the fnn-octets (svref (fnn-live-octets) 0))
                    (fnn-owner-admission-job-source-vector job)
                    :start1 start :end1 end :start2 start :end2 end)
         (serious-condition (cause)
           ;; A partial replacement is ambiguous. The core cancels mechanics,
           ;; retaining holder/charge; no catch/unwind releases aliases.
           (fnn-core-mv 'fn-owner-incoming-copy-ack
             (funcall ack-callback
                      (fnn-owner-admission-job-input-token job)
                      start count end :uncertain controller1 pool1))
           (error cause)))
       ;; The core acknowledgement has its own execution fault boundary.
       ;; Never retry it after a callback mutated state and then escaped.
       (fnn-core-mv 'fn-owner-incoming-copy-ack
         (funcall ack-callback (fnn-owner-admission-job-input-token job)
                  start count end :copied controller1 pool1)))
      ((:complete :setup-unavailable) (values word controller1 pool1))
      (t (fnn-fixed-callback-fail 'fn-owner-incoming-copy-next
                                  :invalid-copy-word word)))))

;; Startup assembly subject, not yet called by owner-run. DEMAND must be
;; the admitted constructor census before this can become a served factory.
;; Caller holds owner exclusion; the extent lock serializes the SAME pool.
(defun fnn-owner-receiver-startup
    (service instance demand limits creator turn-creator reserve-callback install-callback
             range-callback fence-callback pool)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (when (fnn-owner-service-receiver-runtime service)
      (fnn-fixed-callback-fail 'fn-owner-rx-capacity-reserve
                               :receiver-startup-already-retained nil))
    (multiple-value-bind (word token pool1)
        (fnn-core-mv 'fn-owner-rx-capacity-reserve
          (funcall reserve-callback instance demand pool))
      (unless (eq word :admitted)
        (return-from fnn-owner-receiver-startup (values word nil pool1)))
      ;; Retain the acquired token before any subsequent constructor can
      ;; escape. A partial/unknown setup remains held; no automatic refund.
      (setf (fnn-owner-service-receiver-runtime service) token)
      (let ((runtime (fnn-owner-receiver-runtime-make
                      nil token range-callback fence-callback limits)))
        (setf (fnn-owner-service-receiver-runtime service) runtime)
        (let ((provider (fnn-core-mv 'create-fn-rx-provider (funcall creator))))
          (setf (fnn-owner-receiver-runtime-provider runtime) provider)
          ;; The independent custody controller is retained before install
          ;; promotes the complete startup allocation to permanent U.
          (setf (fnn-owner-receiver-runtime-turn runtime)
                (fnn-core-mv 'create-fn-receiver-turn (funcall turn-creator)))
          (multiple-value-bind (installed provider1 turn1 pool2)
              (fnn-core-mv 'fn-owner-rx-capacity-install-turn
                (funcall install-callback token provider
                         (fnn-owner-receiver-runtime-turn runtime) pool1))
            (setf (fnn-owner-receiver-runtime-provider runtime) provider1
                  (fnn-owner-receiver-runtime-turn runtime) turn1)
            (unless (eq installed :installed)
              (fnn-fixed-callback-fail 'fn-owner-rx-capacity-install-turn
                                       :receiver-install-incomplete installed))
            (values installed runtime pool2)))))))

;; CURRENT is an already baseline-funded core object. Retain it before
;; RESERVE can mutate the pool or escape; its issued token remains inside it.
;; No native ledger projection or fabricated installed Boolean is accepted.
(defun fnn-owner-receiver-current-startup
    (service demand limits current creator turn-creator
             reserve-callback allocation-callback install-callback
             turn-start-callback next-callback ack-callback fence-callback current-fence-callback pool
             &optional parser-callback)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (when (fnn-owner-service-receiver-runtime service)
      (fnn-fixed-callback-fail 'fn-owner-rx-current-reserve
                               :receiver-startup-already-retained nil))
    (handler-case
        (progn
    (setf (fnn-owner-service-receiver-runtime service) current)
    (multiple-value-bind (word token current1 pool1)
        (fnn-core-mv 'fn-owner-rx-current-reserve
          (funcall reserve-callback demand current pool))
      (setf (fnn-owner-service-receiver-runtime service) current1)
      (unless (eq word :admitted)
        (return-from fnn-owner-receiver-current-startup (values word nil pool1)))
      (multiple-value-bind (allocation current2 pool2)
          (fnn-core-mv 'fn-owner-rx-current-allocation-begin
            (funcall allocation-callback token current1 pool1))
        (setf (fnn-owner-service-receiver-runtime service) current2)
        (unless (eq allocation :allocate)
          (fnn-fixed-callback-fail 'fn-owner-rx-current-allocation-begin
                                   :receiver-allocation-incomplete allocation))
        (let ((runtime (fnn-owner-receiver-turn-runtime-make
                        token current2 turn-start-callback next-callback
                        ack-callback fence-callback limits parser-callback)))
          (setf (fnn-owner-service-receiver-runtime service) runtime)
          (let ((provider (fnn-core-mv 'create-fn-rx-provider (funcall creator))))
            (setf (fnn-owner-receiver-turn-runtime-provider runtime) provider)
            (setf (fnn-owner-receiver-turn-runtime-turn runtime)
                  (fnn-core-mv 'create-fn-receiver-turn (funcall turn-creator)))
            (multiple-value-bind (installed provider1 turn1 current3 pool3)
                (fnn-core-mv 'fn-owner-rx-current-install
                  (funcall install-callback token provider
                           (fnn-owner-receiver-turn-runtime-turn runtime)
                           current2 pool2))
              (setf (fnn-owner-receiver-turn-runtime-provider runtime) provider1
                    (fnn-owner-receiver-turn-runtime-turn runtime) turn1
                    (fnn-owner-receiver-turn-runtime-current runtime) current3)
              (unless (eq installed :installed)
                (fnn-fixed-callback-fail 'fn-owner-rx-current-install
                                         :receiver-install-incomplete installed))
              (values installed runtime pool3)))))))
      (serious-condition (cause)
        ;; The control owns any token even if reserve escaped before returning
        ;; it. Fence that actual control, then any constructed provider. A
        ;; fence escape must reach the enclosing shared fail-stop boundary.
        (let* ((retained (fnn-owner-service-receiver-runtime service))
               (runtimep (fnn-owner-receiver-turn-runtime-p retained))
               (controller (if runtimep
                               (fnn-owner-receiver-turn-runtime-current retained)
                             retained)))
          (multiple-value-bind (ignored fenced pool1)
              (fnn-core-mv 'fn-owner-rx-current-fence-current
                (funcall current-fence-callback controller pool))
            (declare (ignore ignored pool1))
            (if runtimep
                (setf (fnn-owner-receiver-turn-runtime-current retained) fenced)
              (setf (fnn-owner-service-receiver-runtime service) fenced)))
          (when (and runtimep (fnn-owner-receiver-turn-runtime-provider retained))
            (fnn-core-mv 'fn-rxp-fence
              (funcall fence-callback
                       (fnn-owner-receiver-turn-runtime-capacity-token retained)
                       (fnn-owner-receiver-turn-runtime-provider retained)))))
        (error cause)))))

;; Private primitive observation for an already issued exact range. This
;; projection is permitted while readiness is revoked; public consumers must
;; still pass the core current/filled gate. No allocation, reserve or resize.
;; :COPIED is returned only after BOTH actual primitive operations complete.
(defun fnn-receiver-range-copy (incoming provider start end)
  (declare (type fnn-octets incoming))
  (replace (the fnn-octets (fnn-receiver-backing provider))
           incoming :start1 start :end1 end :start2 start :end2 end)
  (fnn-receiver-publish-fill provider end)
  :copied)

;; Selected turn copy adapter. Caller holds shared owner exclusion; this
;; function holds extent exclusion through authorization, physical publication
;; and ACK. It does not return/settle custody or authorize a STATE consumer.
(defun fnn-owner-receiver-turn-copy
    (incoming ticket provider turn pool next-callback ack-callback limits fuel)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (multiple-value-bind (word start end left provider1 turn1 pool1)
        (fnn-core-mv 'fn-owner-rx-turn-copy-next
          (funcall next-callback ticket (length incoming) limits fuel
                   provider turn pool))
      (case word
        (:receive-copy
         ;; Only the primitive is inside this handler. ACK is invoked once:
         ;; a mutate-and-throw acknowledgement must never be retried.
         (handler-case
             (fnn-receiver-range-copy incoming provider1 start end)
           (serious-condition (cause)
             (fnn-core-mv 'fn-owner-rx-turn-copy-ack
               (funcall ack-callback ticket start end :uncertain
                        provider1 turn1 pool1))
             (error cause)))
         (multiple-value-bind (ack provider2 turn2 pool2)
             (fnn-core-mv 'fn-owner-rx-turn-copy-ack
               (funcall ack-callback ticket start end :copied
                        provider1 turn1 pool1))
           (values ack left provider2 turn2 pool2)))
        ((:receiver-unavailable :bad-receive-range
          :receive-quantum-full :receive-yield)
         (values word left provider1 turn1 pool1))
        (t (fnn-fixed-callback-fail 'fn-owner-rx-turn-copy-next
                                  :invalid-receive-word word))))))

;; Internal callable turn step. This returns only the newly issued core
;; ticket; a busy/refused start cannot borrow a previous request's ticket.
(defun fnn-owner-receiver-turn-start (service cid node demand)
  ;; Caller holds owner mutex. Read all stobjs from the same service/runtime;
  ;; no separately supplied pool, capacity identity or holder is installed.
  (let ((runtime (fnn-owner-service-receiver-runtime service)))
    (unless (fnn-owner-receiver-turn-runtime-p runtime)
      (fnn-fixed-callback-fail 'fn-owner-rx-connection-turn-start
                               :receiver-startup-incomplete nil))
    (unless node
      (fnn-fixed-callback-fail 'fn-owner-rx-connection-turn-start
                               :connection-custody-missing nil))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (multiple-value-bind (word ticket mio turn pool state)
          (fnn-core-mv 'fn-owner-rx-connection-turn-start
            (funcall (fnn-owner-receiver-turn-runtime-turn-start runtime)
                     cid (fnn-connection-custody-token node)
                     (fnn-owner-service-connection-fuel service) demand
                     (fnn-owner-service-connection-mio service)
                     (fnn-owner-receiver-turn-runtime-provider runtime)
                     (fnn-owner-receiver-turn-runtime-turn runtime)
                     (fnn-owner-receiver-turn-runtime-current runtime)
                     (fnn-owner-service-connection-pool service) *the-live-state*))
        (declare (ignore state))
        (setf (fnn-owner-service-connection-mio service) mio
              (fnn-owner-service-connection-pool service) pool
              (fnn-owner-receiver-turn-runtime-turn runtime) turn)
        (values word ticket pool)))))

(defun fnn-owner-receiver-turn-copy-runtime (service incoming ticket fuel pool)
  (let ((runtime (fnn-owner-service-receiver-runtime service)))
    (unless (fnn-owner-receiver-turn-runtime-p runtime)
      (fnn-fixed-callback-fail 'fn-owner-rx-turn-copy-next
                               :receiver-startup-incomplete nil))
    (multiple-value-bind (word left provider turn pool1)
        (fnn-owner-receiver-turn-copy
         incoming ticket (fnn-owner-receiver-turn-runtime-provider runtime)
         (fnn-owner-receiver-turn-runtime-turn runtime) pool
         (fnn-owner-receiver-turn-runtime-copy-next runtime)
         (fnn-owner-receiver-turn-runtime-copy-ack runtime)
         (fnn-owner-receiver-turn-runtime-limits runtime) fuel)
      (setf (fnn-owner-receiver-turn-runtime-provider runtime) provider
            (fnn-owner-receiver-turn-runtime-turn runtime) turn)
      (values word left runtime pool1))))

;;; SOURCE-NOTREADY: separate receiver physical effect. Selected callbacks
;;; and the sanctioned SAME-provider backing bridge are installed at startup.
;;; Reservation, constructor correspondence, and bulk effect funding remain
;;; prerequisites; this function is not called by the served scheduler yet.
;;; Caller must be inside fnn-owner-shared-action-locked: if the fence itself
;;; faults, that boundary stops all consumers before releasing the owner lock.
(defun fnn-owner-receiver-fill
    (incoming token provider range-callback fence-callback limits fuel)
  ;; Exclusion covers authorization, replacement, fill publication and fence.
  ;; The held POST input is never a receiver destination.
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (handler-case
        (multiple-value-bind (word start end left provider1)
            (fnn-core-mv 'fn-rxp-fill-range
              (funcall range-callback token (length incoming) limits fuel provider))
          (case word
            (:receive-copy
             ;; Core endpoints and installed room authorize this exact effect.
             ;; Publish the fill only after REPLACE completed; no reserve/resize.
             (fnn-receiver-range-copy incoming provider1 start end)
             (values word left provider1))
            ((:receiver-unavailable :bad-receive-range
              :receive-quantum-full :receive-yield)
             (values word left provider1))
            (t (fnn-fixed-callback-fail 'fn-rxp-fill-range
                                      :invalid-receive-word word))))
      (serious-condition (cause)
        ;; Partial bytes are not a valid previous receive. Successful fencing
        ;; revokes readiness before extent unlock. Fence failure propagates to
        ;; the outer shared owner fence; keep object and permanent U charged.
        ;; There is no retry, refund, or consumer continuation on this path.
        (fnn-core-mv 'fn-rxp-fence
          (funcall fence-callback token provider))
        (error cause)))))

;;; Physical adapter for core-issued retained admission actions. Caller owns
;;; the service mutex. It never creates another durable intent or reservation
;;; after a yield; the outer scheduler must retain this envelope until joins.
;;; The whole fill action remains an unqualified setup obstruction until the
;;; bounded incoming range producer replaces it. No caller activates it yet.
(defun fnn-owner-receiver-fill-runtime (service incoming fuel)
  "Use the exact startup-retained provider and selected scalar callbacks."
  (let ((runtime (fnn-owner-service-receiver-runtime service)))
    (unless (fnn-owner-receiver-runtime-p runtime)
      (fnn-fixed-callback-fail 'fn-rxp-fill-range
                               :receiver-startup-incomplete nil))
    (multiple-value-bind (word left provider)
        (fnn-owner-receiver-fill
         incoming (fnn-owner-receiver-runtime-token runtime)
         (fnn-owner-receiver-runtime-provider runtime)
         (fnn-owner-receiver-runtime-range-callback runtime)
         (fnn-owner-receiver-runtime-fence-callback runtime)
         (fnn-owner-receiver-runtime-limits runtime) fuel)
      (setf (fnn-owner-receiver-runtime-provider runtime) provider)
      (values word left runtime))))

(defun fnn-owner-admission-input-action (service job action)
  (flet ((pool (name &rest args)
           (sb-thread:with-mutex (*fnn-extent-lock*)
             (apply #'fnn-core-page-read-pool name args))))
    (case (if (consp action) (car action) action)
      ((:yield :continue :demand) action)
      (:reserve-input
       (let ((result (pool 'fn-owner-incoming-reserve (second action))))
         (when (eq (first result) :admitted)
           ;; Retain the acquired token before any fill can allocate/throw.
           (setf (fnn-owner-admission-job-input-token job) (second result)
                 (fnn-owner-service-admission-job service) job))
         (first result)))
      (:fill-input
       (handler-case
           (progn
             (setf (fnn-owner-admission-job-input-backing job)
                   (svref (fnn-live-octets) 0))
             (fnn-octets-fill (fnn-owner-admission-job-source-vector job)
                              (fnn-owner-admission-job-input-token job))
             :filled)
         (error (cause)
           ;; Cancellation keeps the row/charge and BOTH backing references:
           ;; JOB owns the sampled old array; the live stobj owns the current.
           (let ((word (first (pool 'fn-owner-incoming-cancel
                                  (fnn-owner-admission-job-input-token job)))))
             (setf (fnn-owner-admission-job-outcome job) word)
             (values word cause)))))
      (:seal-input
       (first (pool 'fn-owner-incoming-seal
                    (fnn-owner-admission-job-input-token job))))
      (:cancel-input
       (first (pool 'fn-owner-incoming-cancel
                    (fnn-owner-admission-job-input-token job))))
      (:terminal
       ;; A semantic terminal result is retained evidence, not permission to
       ;; refund input or resolve the durable intent before lease settlement.
       (setf (fnn-owner-admission-job-outcome job) (second action)))
      (:release-input
       (let ((word (first (pool 'fn-owner-incoming-release
                              (fnn-owner-admission-job-input-token job)
                              (second action) (third action)))))
         (when (eq word :released)
           (setf (fnn-owner-service-admission-job service) nil))
         word))
      (otherwise (fnn-fault "malformed retained admission action")))))

