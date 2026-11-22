; The native adapter's scalar entry points over the live core (layer doc
; 4.1.3). Only the pool's byte array crosses the raw-representation boundary
; (host/adapter.lisp takes its SAP); every descriptor, loan and post goes
; through these guard-verified functions, so the adapter decides nothing.
(in-package "ACL2")
(include-book "executor")
(include-book "device-boundary")
(include-book "assembly-attach")
(include-book "host-result")
(include-book "host-ops")
; Native TLS calls the guarded transport controller and its ownership ledger.
(include-book "host-codec")
(include-book "host-compress")

(local (in-theory (enable fn2-core-wfp)))

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


; An existing transport operation may finish after the core stops. This checks
; its retained submitted incarnation, not fresh admission through host-action.


; SSL partial records complete one bounded prefix of the descriptor. A WANT
; retry selects the same prefix. The core owns the loan and the codec envelope
; owns its physical request identity; neither address nor size comes from raw.




; Result normalization (layer doc 4.1.2, 4.1.3): a physical outcome (CODE one
; of :ok :eof :reset :closed :cancelled :no-space :failed; COUNT the octets
; moved, or an Accept's capability index; AUX an Accept's nonce) as the
; simulator's own normalizer states it, so every native completion is one
; the simulator could post.
; fn2-host-result is defined in the scalar host-result leaf.

;; The configured listeners (layer doc 4.1.4): the served profile's
;; :listener-address (an IPv4 address as a u32, network order; default
;; 127.0.0.1) and :listener-port (a u16; 0 asks the kernel for an ephemeral
;; port, which the node reports), and :listener-path, the owner-only (0600)
;; Unix-domain socket beside it (absent: none). The path is absolute, has no
;; NUL and fits sockaddr_un's sun_path with its terminator on both targets
;; (103 octets: Darwin's 104). Read like :listener-targets, by key; a value
;; outside its width is a named refusal to start, never a clamp. Both sockets
;; are the one listener capability: an Accept takes whichever is ready.
(defconst *fn2-host-loopback* #x7f000001)
(defconst *fn2-host-path-max* 103)
(defun fn2-host-listener-pathp (path)
  (declare (xargs :guard t))
  (and (stringp path) (< 1 (length path)) (<= (length path) *fn2-host-path-max*)
       (eql (char path 0) #\/)
       (not (member (code-char 0) (coerce path 'list)))))
(defun fn2-host-listener-bind (profile)
  (declare (xargs :guard t))
  (let* ((profile (and (alistp profile) profile))
         (address (if (assoc-equal :listener-address profile)
                      (fn2-profile-get :listener-address profile) *fn2-host-loopback*))
         (port (if (assoc-equal :listener-port profile)
                   (fn2-profile-get :listener-port profile) 0))
         (pathp (consp (assoc-equal :listener-path profile)))
         (path (fn2-profile-get :listener-path profile)))
    (cond ((not (unsigned-byte-p 32 address)) (mv :listener-address 0 0 nil))
          ((not (unsigned-byte-p 16 port)) (mv :listener-port 0 0 nil))
          ((and pathp (not (fn2-host-listener-pathp path))) (mv :listener-path 0 0 nil))
          (t (mv :ok address port (and pathp path))))))

(defun fn2-host-tls-settings (profile)
 (declare (xargs :guard t))
 (cond ((not (fn2-tls-profilep profile)) (mv :tls-profile nil nil 0 0 0 0 0 nil nil))
       ((not (or (fn2-tls-requested-p profile) (fn2-peer-tls-requested-p profile)))
        (mv :off nil nil 0 0 0 0 0 nil nil))
       (t (mv :ok (fn2-profile-get :tls-certificate profile) (fn2-profile-get :tls-key profile)
              (fn2-tls-setting :tls-window 16384 profile) *fn2-tls-io-bytes* *fn2-tls-minimum-version* (fn2-codec-seed-capacity profile)
              (fn2-tls-setting :tls-handshake-turns 65536 profile)
              (fn2-profile-get :peer-pull-ca-file profile) (fn2-profile-get :peer-pull-tls-name profile)))))

(defun fn2-host-compress-settings (profile)
 (declare (xargs :guard t))
 (let ((capacity (fn2-codec-seed-capacity profile)))
  (cond ((not (fn2-compress-profilep profile)) (mv :compress-profile 0 0 0 0 0))
        ((not (fn2-profile-get :compress-enabled profile)) (mv :off 0 0 0 0 0))
        ((not (and (posp capacity) (unsigned-byte-p 32 capacity)))
         (mv :compress-profile 0 0 0 0 0))
        (t (mv :ok (fn2-profile-get :compress-input-quantum profile)
                   (fn2-profile-get :compress-output-quantum profile)
                   (fn2-profile-get :compress-expansion-ratio profile)
                   (fn2-profile-get :compress-expansion-burst profile) capacity)))))

; The sticky stop (fn2-core-stopped-p): the adapter's test before it touches
; a core it did not just turn.
(defun fn2-host-stopped-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-stopped-p fn2-core))
(defun fn2-host-stop-reason (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-stop-reason fn2-core))
; Preserve the kind-specific stop information in the native diagnostic.
(defun fn2-host-stop-details (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv (fn2-core-stop-kind fn2-core) (fn2-core-stop-detail fn2-core)))

; Decode this stop from the declaration that also generates the boot arms.
(make-event
 (let ((detail (position-eq :recovery (fn2-machine-declared 'fn2-boot :stops (w state)))))
  (if (natp detail)
      (value `(defconst *fn2-host-boot-recovery-detail* ,detail))
    (er soft 'fn2-host-boot-refusal "Boot has no declared :recovery stop."))))

(defun fn2-host-boot-refusal-class
 (stopped reason kind detail snapshot phase rclass dirty ambiguous assume witness)
 (declare (xargs :guard t))
 (if (and (equal stopped t)
          (equal reason *fn2-stop-reason-kind*)
          (equal kind *fn2-boot-kind*)
          (equal detail *fn2-host-boot-recovery-detail*)
          (eq snapshot :ok)
          (equal phase *fn2-recovery-machine-state-done*)
          (equal rclass *fn2-rec-class-unknown*)
          (equal dirty 1) (equal ambiguous 0)
          (equal assume *fn2-rec-assume-fence*)
          (equal witness 0))
     :broad-dirty-tail-unknown
   :other-stop))
(in-theory (disable fn2-host-boot-refusal-class))

(defun fn2-host-boot-refusal (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (let* ((id (fn2-machine-kind-base *fn2-recovery-machine-kind* fn2-core))
        (snapshot (fn2-recovery-machine-snapshot-read-code id fn2-core)))
  (if (not (eq snapshot :ok)) :other-stop
   (fn2-host-boot-refusal-class
    (fn2-core-stopped-p fn2-core) (fn2-core-stop-reason fn2-core)
    (fn2-core-stop-kind fn2-core) (fn2-core-stop-detail fn2-core)
    snapshot (fn2-machine-phase id fn2-core) (fn2-machine-rc-class id fn2-core)
    (fn2-machine-rc-dirty id fn2-core) (fn2-machine-rc-ambiguous id fn2-core)
    (fn2-machine-rc-assume id fn2-core) (fn2-machine-rc-witness id fn2-core)))))
(defun fn2-host-idle-deadline (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-idle-deadline fn2-core))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
    fn2-host-count-stray fn2-host-stray fn2-host-outbox-ack fn2-host-op-finish
    fn2-host-outbox-queued fn2-host-outbox-peek fn2-host-action
    fn2-host-op-span fn2-host-codec-op fn2-host-codec-cancel-target fn2-host-tls-record-next
    fn2-host-tls-mark-closed fn2-host-tls-cancel-result
    fn2-host-compress-start-op fn2-host-compress-record-next fn2-host-compress-close-owner
    fn2-host-compress-close-child fn2-host-compress-input-prefix
    fn2-host-compress-mark-closed fn2-host-compress-cancel-result fn2-host-result fn2-host-listener-pathp fn2-host-listener-bind fn2-host-tls-settings fn2-host-tls-role fn2-host-compress-settings fn2-host-tls-span fn2-host-tls-stage-span fn2-host-tls-next-turn fn2-host-stopped-p fn2-host-stop-reason fn2-host-stop-details fn2-host-boot-refusal-class fn2-host-boot-refusal fn2-host-idle-deadline) (w state)))
