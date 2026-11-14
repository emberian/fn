;;; A5r: the native event loop over the served core (layer doc 4.1.3).
;;; Raw SBCL, loaded by a session script after the certified books
;;; (books/host-boundary.lisp, which gives the scalar entry points) and
;;; host/ffi.lisp. One executor and a bounded file-device worker. The loop implements physical scheduling
;;; and reports observations through the core's own posting entries; every
;;; cell's words come from the logical normalizer fn2-host-result. A byte
;;; enters the core only when fn2-turn harvests its result.
(in-package "ACL2")
(load "host/device.lisp")
(load "host/tls.lisp")

;; Op record states.
(defconstant +fn2-n-free+ 0)
(defconstant +fn2-n-waiting+ 1)
(defconstant +fn2-n-closed-waiting+ 2)  ; its capability was closed under it
(defconstant +fn2-n-completed+ 3)

(defstruct fn2-nop
  (state 0 :type fixnum) (gen 0) (kind 0 :type fixnum) (cap 0) (nonce 0)
  (address 0 :type fixnum) (len 0 :type fixnum) (target 0) (target-gen 0)
  (outcome 0) (reason 0) (count 0) (aux0 0) (aux1 0)
  (tls-started nil) (tls-seed-offset 0) (tls-finished nil) (tls-count 0)
  (family :none) (port 0) (w0 0) (w1 0) (w2 0) (w3 0) (octets nil) (offset 0) (fua 0))

;; A capability: index 0 is the listener (its TCP socket, and the owner-only
;; Unix-domain socket beside it when the profile names :listener-path: one
;; capability, so the listener machine is the same for both); connections from 1.
(defstruct fn2-ncap
  (fd -1 :type fixnum) (nonce 0) (family :none) (port 0) (w0 0) (w1 0) (w2 0) (w3 0)
  (rx 0) (eof nil) (tx 0) (closed nil) (seq 0) tls (tls-selected nil))

(defstruct fn2-nhost
  core bytes ops caps mux (listen-port 0)
  tls-config (tls-window 0) (tls-quantum 0) (tls-seed-capacity 0) (tls-turns 0)
  ;; Memory device for existing seeded sessions. An image session uses
  ;; STORAGE's FIFO worker instead; the memory table makes no durability claim.
  (device (make-hash-table))
  storage (storage-pending 0)
  ;; the Unix-domain listener socket (-1: none), its path, and which of the
  ;; two sockets an Accept tries first when both are ready (alternating)
  (local-fd -1 :type fixnum) (local-path nil) (local-first nil)
  completions (chead 0 :type fixnum) (ctail 0 :type fixnum) (pending 0 :type fixnum)
  (harvest-limit 1) (action-limit 1)
  ;; test instruments: the boundary trace (ENVELOPE), death cuts, the session
  trace (trace-count 0 :type fixnum) (boundaries 0 :type fixnum) (kill-at 0 :type fixnum)
  (boundary-lock (sb-thread:make-mutex :name "fn2 death boundary"))
  (control-fd -1 :type fixnum) control-window (control-text "")
  sync (stop nil) (signal 0) (iterations 0) (accepts 0)
  ;; port -> the incarnation (index . nonce) an "open PORT" bound it to: client
  ;; ports are reused over a long session, incarnations never.
  (bindings (make-hash-table)))

(defvar *fn2-n-signal* 0)
(defvar *fn2-n-signal-mux* nil)

(defun fn2-n-family-code (family)
  (case family (:inet *fn2-peer-family-inet*) (:inet6 *fn2-peer-family-inet6*)
    (:local *fn2-peer-family-local*) (t *fn2-peer-family-none*)))

;;; The boundary trace: a preallocated vector; overflow refuses the run.
(defun fn2-n-record (host entry)
  (let ((trace (fn2-nhost-trace host)))
    (when trace
      (when (>= (fn2-nhost-trace-count host) (length trace))
        (error "fn2 native: boundary trace full at ~d entries (the run is refused, not truncated)"
               (length trace)))
      (setf (svref trace (fn2-nhost-trace-count host)) entry)
      (incf (fn2-nhost-trace-count host)))))
(defun fn2-n-trace-list (host)
  (let ((trace (fn2-nhost-trace host)))
    (and trace (coerce (subseq trace 0 (fn2-nhost-trace-count host)) 'list))))

(defun fn2-n-boundary (host label)
  "Death cuts at every take, ack, syscall and post: FN2_KILL_AT=N exits at the Nth."
  (sb-thread:with-mutex ((fn2-nhost-boundary-lock host))
    (incf (fn2-nhost-boundaries host))
    (when (= (fn2-nhost-boundaries host) (fn2-nhost-kill-at host))
      (format t "FN2 KILL boundary=~d label=~a~%" (fn2-nhost-boundaries host) label)
      (finish-output)
      (sb-ext:exit :code 86 :abort t))))

(defun fn2-n-octets (host address count)
  "The octets a syscall moved, copied out of the pool for the trace only."
  (when (fn2-nhost-trace host)
    (let ((bytes (fn2-nhost-bytes host)))
      (loop for i from address below (+ address count) collect (aref bytes i)))))

;;; Completion: the physical outcome normalized by the logic, queued in
;;; completion order for posting at the top of the next iteration.
(defun fn2-n-complete (host slot code count &optional (aux 0) (cancelled nil) octets)
  (let ((op (aref (fn2-nhost-ops host) slot)) (queue (fn2-nhost-completions host)))
    (assert (or (= (fn2-nop-state op) +fn2-n-waiting+) (= (fn2-nop-state op) +fn2-n-closed-waiting+)))
    (assert (< (fn2-nhost-pending host) (length queue)))
    (multiple-value-bind (outcome reason count aux0 aux1)
        (fn2-host-result (fn2-nop-kind op) code count aux (fn2-nop-len op) cancelled)
      (setf (fn2-nop-outcome op) outcome (fn2-nop-reason op) reason (fn2-nop-count op) count
            (fn2-nop-aux0 op) aux0 (fn2-nop-aux1 op) aux1 (fn2-nop-octets op) octets
            (fn2-nop-state op) +fn2-n-completed+
            (aref queue (fn2-nhost-ctail host)) slot
            (fn2-nhost-ctail host) (mod (1+ (fn2-nhost-ctail host)) (length queue)))
      (incf (fn2-nhost-pending host)))))

(defun fn2-n-cap (host op)
  "The live capability record OP names, or nil (a stale nonce never reaches an fd)."
  (let ((index (fn2-nop-cap op)) (caps (fn2-nhost-caps host)))
    (and (< index (length caps))
         (let ((cap (aref caps index)))
           (and (>= (fn2-ncap-fd cap) 0) (= (fn2-ncap-nonce cap) (fn2-nop-nonce op)) cap)))))

(defun fn2-n-new-cap (host fd family port w0 w1 w2 w3)
  "A fresh (index, nonce): an index is reused only with a larger nonce; one at 2^32-1 retires."
  (let ((caps (fn2-nhost-caps host)))
    (loop for i from 1 below (length caps)
          for cap = (aref caps i)
          when (and (= (fn2-ncap-fd cap) -1) (< (fn2-ncap-nonce cap) #xffffffff))
            do (setf (aref caps i)
                     (make-fn2-ncap :fd fd :nonce (1+ (fn2-ncap-nonce cap)) :family family :port port
                                    :w0 w0 :w1 w1 :w2 w2 :w3 w3 :seq (incf (fn2-nhost-accepts host))))
               (return-from fn2-n-new-cap (values i (1+ (fn2-ncap-nonce cap)))))
    ;; Capacity covers every accept credit, so this is a host defect: stop by name.
    (fn2-native-close fd)
    (error "fn2 native: capability table exhausted")))

(defun fn2-n-sap (host address)
  (sb-sys:sap+ (sb-sys:vector-sap (fn2-nhost-bytes host)) address))

;;; One syscall for a waiting op whose descriptor is ready. EAGAIN leaves it
;;; waiting (the simulator's zero-progress would-block); never a failure.
(defun fn2-n-again-p (errno) (or (= errno 35) (= errno 11) (= errno 4)))

(defun fn2-n-tls-op-p (op cap)
 (or (= (fn2-nop-kind op) *fn2-action-tls-start*)
     (and cap (fn2-ncap-tls-selected cap)
          (or (= (fn2-nop-kind op) *fn2-action-receive*) (= (fn2-nop-kind op) *fn2-action-send*)))))
(defun fn2-n-op-interest (op cap)
 (if (fn2-n-tls-op-p op cap)
     (if (and cap (fn2-ncap-tls cap)) (fn2-native-tls-interest (fn2-ncap-tls cap)) 1)
   (if (= (fn2-nop-kind op) *fn2-action-send*) 4 1)))
(defun fn2-n-tls-kick-p (op cap)
 (and (fn2-n-tls-op-p op cap)
      (or (not (fn2-nop-tls-started op))
          (and cap (fn2-ncap-tls cap) (fn2-native-tls-kick (fn2-ncap-tls cap))))))
(defun fn2-n-tls-work-p (host)
 (loop for op across (fn2-nhost-ops host)
       thereis (and (= (fn2-nop-state op) +fn2-n-waiting+)
                    (fn2-n-tls-kick-p op (fn2-n-cap host op)))))

(defun fn2-n-tls-handshake-ready (host slot cap)
 (let* ((op (aref (fn2-nhost-ops host) slot)) (tls (fn2-ncap-tls cap)))
  (unless (fn2-nop-tls-started op)
   (multiple-value-bind (code ledger)
       (fn2-tls-transport-start (fn2-ncap-nonce cap) slot (fn2-nop-gen op)
         (fn2-nop-len op) (fn2-nhost-tls-seed-capacity host)
         (fn2-nhost-tls-quantum host) (fn2-nhost-tls-turns host)
         (create-fn2-tls-transport))
    (unless (eq code :ok)
     (fn2-n-complete host slot :failed 0)
     (return-from fn2-n-tls-handshake-ready nil))
    (setf (fn2-native-tls-transport tls) ledger (fn2-nop-tls-started op) t)))
  (multiple-value-bind (status kick interest)
      (fn2-native-tls-handshake-step tls (fn2-ncap-fd cap) host
        (fn2-nhost-bytes host) (fn2-nop-address op) (fn2-ncap-nonce cap) slot (fn2-nop-gen op))
   (setf (fn2-native-tls-kick tls) kick (fn2-native-tls-interest tls) interest)
   (case status
    (:done
     ;; The ledger's completion predicate releases the original RX loan only
     ;; after copying its entire span. Owned staging survives for records.
     (multiple-value-bind (code copied fed il io ol oo ledger)
         (fn2-tls-transport-handoff (fn2-ncap-nonce cap) slot (fn2-nop-gen op)
                                    (fn2-native-tls-transport tls))
      (setf (fn2-native-tls-transport tls) ledger)
      (if (eq code :ok)
          (progn
           (setf (fn2-native-tls-seed-length tls) copied
                 (fn2-native-tls-seed-offset tls) fed
                 (fn2-native-tls-input-length tls) il (fn2-native-tls-input-offset tls) io
                 (fn2-native-tls-output-length tls) ol (fn2-native-tls-output-offset tls) oo)
           (fn2-n-complete host slot :ok (fn2-nop-len op)))
        (fn2-n-complete host slot :failed 0))))
    ((:ok :blocked) nil)
    (otherwise (fn2-n-complete host slot :failed 0))))))

(defun fn2-n-tls-ready (host slot cap)
 "One bounded transport turn: at most one feed, drain/send, and SSL call."
 (let* ((op (aref (fn2-nhost-ops host) slot)) (kind (fn2-nop-kind op))
        (handshake (= kind *fn2-action-tls-start*)))
  (unless (fn2-ncap-tls cap)
   (unless (and handshake (fn2-nhost-tls-config host) (not (fn2-ncap-tls-selected cap)))
    (fn2-n-complete host slot :failed 0)
    (return-from fn2-n-tls-ready nil))
   (fn2-n-boundary host "tls-start")
   (setf (fn2-ncap-tls-selected cap) t)
   (setf (fn2-ncap-tls cap)
         (fn2-native-tls-open (fn2-nhost-tls-config host) (fn2-nhost-tls-window host) (fn2-nhost-tls-quantum host) (fn2-nhost-tls-seed-capacity host) (fn2-nhost-tls-turns host)))
   (unless (fn2-ncap-tls cap)
    (fn2-n-complete host slot :failed 0)
    (return-from fn2-n-tls-ready nil)))
  (when handshake
   (return-from fn2-n-tls-ready (fn2-n-tls-handshake-ready host slot cap)))
  (let* ((tls (fn2-ncap-tls cap)) (handle (fn2-native-tls-handle tls))
         (fd (fn2-ncap-fd cap)) (bytes (fn2-nhost-bytes host)) (fed-seed nil))
   (setf (fn2-nop-tls-started op) t (fn2-native-tls-kick tls) nil)
   (when handshake
    (multiple-value-bind (code remaining) (fn2-host-tls-next-turn (fn2-native-tls-turns-left tls))
     (setf (fn2-native-tls-turns-left tls) remaining)
     (unless (eq code :ok)
      (fn2-n-complete host slot :failed 0)
      (return-from fn2-n-tls-ready nil))))
   (when (eq (fn2-native-tls-flush tls fd host) :failed)
    (fn2-n-complete host slot :failed 0)
    (return-from fn2-n-tls-ready nil))
   ;; Copy only this descriptor's validated span, one quantum per turn. The
   ;; ACL2 profile reserves a class-zero RX-sized transport buffer per live
   ;; connection. Its lifetime extends past handshake-token reclamation.
   (when (and handshake (< (fn2-nop-tls-seed-offset op) (fn2-nop-len op)))
    (let* ((seed (fn2-native-tls-seed tls)) (off (fn2-nop-tls-seed-offset op))
           (n (fn2-native-tls-stage-span (fn2-nop-len op) off (length seed) (fn2-nhost-tls-quantum host))))
     (replace seed bytes :start1 off :end1 (+ off n)
              :start2 (+ (fn2-nop-address op) off) :end2 (+ (fn2-nop-address op) off n))
     (incf (fn2-nop-tls-seed-offset op) n)
     (setf (fn2-native-tls-seed-length tls) (fn2-nop-tls-seed-offset op))
     (when (< (fn2-nop-tls-seed-offset op) (fn2-nop-len op))
      (setf (fn2-native-tls-kick tls) t)
      (return-from fn2-n-tls-ready nil))))
   ;; Feed staging before reading the socket, even after handshake completion.
   ;; A suffix containing encrypted application records belongs to the next
   ;; Receive; it no longer borrows the connection's mutable RX range.
   (when (< (fn2-native-tls-seed-offset tls) (fn2-native-tls-seed-length tls))
    (let* ((seed (fn2-native-tls-seed tls)) (off (fn2-native-tls-seed-offset tls))
           (n (fn2-native-tls-span (fn2-native-tls-seed-length tls) off
                   (fn2-tls-%input-room handle) (fn2-nhost-tls-quantum host))))
     (when (plusp n)
      (sb-sys:with-pinned-objects (seed)
       (let ((fed (fn2-tls-%feed handle (sb-sys:sap+ (sb-sys:vector-sap seed) off) n)))
        (unless (= fed n) (error "fn2 TLS: staged-input BIO capacity contract failed"))
        (setf fed-seed t)
        (incf (fn2-native-tls-seed-offset tls) fed))))))
   (unless (fn2-nop-tls-finished op)
    (if handshake (fn2-n-boundary host "tls-handshake") (fn2-n-boundary host "tls-record"))
    (multiple-value-bind (code count)
        (if handshake
            (values (fn2-tls-%handshake handle) (fn2-nop-len op))
          (sb-sys:with-pinned-objects (bytes)
           (fn2-native-tls-record tls (= kind *fn2-action-send*)
                                  (fn2-n-sap host (fn2-nop-address op)) (fn2-nop-len op))))
     (case code
      (0 (setf (fn2-nop-tls-finished op) t (fn2-nop-tls-count op) count))
      ((1 2)
       (setf (fn2-native-tls-interest tls) (if (= code 1) 1 4))
       ;; Consume buffered TLS data before reading the fd: an EOF must not
       ;; discard an application record already held by OpenSSL.
       (when (= code 1)
        (if fed-seed (setf (fn2-native-tls-kick tls) t)
          (when (= (fn2-native-tls-seed-offset tls) (fn2-native-tls-seed-length tls))
           (case (fn2-native-tls-fill tls fd host)
            (:progress (setf (fn2-native-tls-kick tls) t))
            (:failed (fn2-n-complete host slot :failed 0)
                     (return-from fn2-n-tls-ready nil)))))))
      (3 (if (= kind *fn2-action-receive*)
             (progn (setf (fn2-ncap-eof cap) t) (fn2-n-complete host slot :eof 0))
           (fn2-n-complete host slot :failed 0))
         (return-from fn2-n-tls-ready nil))
      (otherwise (fn2-n-complete host slot :failed 0) (return-from fn2-n-tls-ready nil)))))
   (cond ((and (fn2-nop-tls-finished op) (fn2-native-tls-output-empty-p tls) (or (not handshake) (= (fn2-nop-tls-seed-offset op) (fn2-nop-len op))))
          (let ((count (fn2-nop-tls-count op)))
           (cond ((= kind *fn2-action-receive*) (incf (fn2-ncap-rx cap) count))
                 ((= kind *fn2-action-send*) (incf (fn2-ncap-tx cap) count)))
           (fn2-n-complete host slot :ok count 0 nil
             (and (not handshake) (fn2-n-octets host (fn2-nop-address op) count)))))
         (t
          (when (fn2-nop-tls-finished op) (setf (fn2-native-tls-interest tls) 4))
          (when (not (fn2-native-tls-output-empty-p tls))
           (setf (fn2-native-tls-interest tls) (logior (fn2-native-tls-interest tls) 4)))
          ;; Retained bytes can progress without a new kernel readability edge.
          (when (and (< (fn2-native-tls-seed-offset tls) (fn2-native-tls-seed-length tls))
                     (plusp (fn2-tls-%input-room handle)))
           (setf (fn2-native-tls-kick tls) t)))))))

(defun fn2-n-start-ready (host slot cap)
  (let* ((op (aref (fn2-nhost-ops host) slot)) (kind (fn2-nop-kind op)) (fd (fn2-ncap-fd cap)))
    (when (fn2-n-tls-op-p op cap)
      (fn2-n-tls-ready host slot cap)
      (return-from fn2-n-start-ready nil))
    (fn2-n-boundary host "syscall")
    (cond
      ((= kind *fn2-action-accept*)
       (multiple-value-bind (new errno family port w0 w1 w2 w3) (fn2-n-accept host cap)
         (cond ((and (minusp new) (fn2-n-again-p errno)) nil)
               ((minusp new) (fn2-n-complete host slot :failed 0))
               (t (multiple-value-bind (index nonce) (fn2-n-new-cap host new family port w0 w1 w2 w3)
                    (setf (fn2-nop-family op) family (fn2-nop-port op) port
                          (fn2-nop-w0 op) w0 (fn2-nop-w1 op) w1 (fn2-nop-w2 op) w2 (fn2-nop-w3 op) w3)
                    (fn2-n-complete host slot :ok index nonce))))))
      ((= kind *fn2-action-receive*)
       (sb-sys:with-pinned-objects ((fn2-nhost-bytes host))
         (multiple-value-bind (n errno) (fn2-native-recv fd (fn2-n-sap host (fn2-nop-address op)) (fn2-nop-len op))
           (cond ((and (minusp n) (fn2-n-again-p errno)) nil)
                 ((minusp n) (fn2-n-complete host slot (if (= errno #+linux 104 #+darwin 54) :reset :closed) 0))
                 ((zerop n) (setf (fn2-ncap-eof cap) t) (fn2-n-complete host slot :eof 0 0 nil nil))
                 (t (incf (fn2-ncap-rx cap) n)
                    (fn2-n-complete host slot :ok n 0 nil (fn2-n-octets host (fn2-nop-address op) n)))))))
      ((= kind *fn2-action-send*)
       (sb-sys:with-pinned-objects ((fn2-nhost-bytes host))
         (multiple-value-bind (n errno) (fn2-native-send fd (fn2-n-sap host (fn2-nop-address op)) (fn2-nop-len op))
           (cond ((and (minusp n) (fn2-n-again-p errno)) nil)
                 ((minusp n) (fn2-n-complete host slot (if (= errno #+linux 104 #+darwin 54) :reset :closed) 0))
                 (t (incf (fn2-ncap-tx cap) n)
                    (fn2-n-complete host slot :ok n 0 nil (fn2-n-octets host (fn2-nop-address op) n)))))))
      (t (error "fn2 native: op kind ~d is not readiness-driven" kind)))))

;;; The listener capability's Accept: one accept(2) on whichever of its two
;;; sockets is ready, alternating when both are, so neither starves. A
;;; connection on the Unix socket carries its peer's uid and gid.
(defun fn2-n-accept (host cap)
  (let* ((mux (fn2-nhost-mux host)) (local (fn2-nhost-local-fd host))
         (tcp-ready (fn2-native-mux-ready-p mux 0 1))
         (local-ready (and (>= local 0) (fn2-native-mux-ready-p mux (fn2-native-mux-local-index mux) 1)))
         (use-local (if (and tcp-ready local-ready) (fn2-nhost-local-first host) local-ready)))
    (when (and tcp-ready local-ready) (setf (fn2-nhost-local-first host) (not use-local)))
    (if use-local (fn2-native-accept-local local) (fn2-native-accept (fn2-ncap-fd cap)))))

;;; The memory device: an octet at OFFSET (0 where nothing was written).
(defun fn2-n-device-unit (host unit)
  (or (gethash unit (fn2-nhost-device host))
      (setf (gethash unit (fn2-nhost-device host))
            (make-array 4096 :element-type '(unsigned-byte 8) :initial-element 0))))
(defun fn2-n-device-ref (host offset)
  (let ((u (gethash (floor offset 4096) (fn2-nhost-device host))))
    (if u (aref u (mod offset 4096)) 0)))
(defun fn2-n-device-set (host offset byte)
  (setf (aref (fn2-n-device-unit host (floor offset 4096)) (mod offset 4096)) byte))
(defun fn2-n-device-put (host store)
  "STORE's writes ((OFFSET . OCTETS) ...) on the device (the seeded store's sources)."
  (dolist (w (reverse store))
    (loop for b in (cdr w) for i from (car w) do (fn2-n-device-set host i b))))

(defun fn2-n-storage-kind (kind)
  (cond ((= kind *fn2-action-read*) :read)
        ((= kind *fn2-action-write*) :write)
        ((= kind *fn2-action-fence*) :fence)))

(defun fn2-n-storage-submit (host slot)
  (let ((op (aref (fn2-nhost-ops host) slot)))
    (unless (eq (fn2-device-request (fn2-n-storage-kind (fn2-nop-kind op)) (fn2-nop-fua op)
                                    (fn2-device-backend (fn2-nhost-storage host))) :perform)
      (fn2-n-complete host slot :unsupported 0)
      (return-from fn2-n-storage-submit nil))
    (fn2-n-boundary host "device-submit")
    (fn2-device-submit
     (fn2-nhost-storage host)
     (make-fn2-device-job :slot slot :gen (fn2-nop-gen op)
       :kind (fn2-n-storage-kind (fn2-nop-kind op)) :bytes (fn2-nhost-bytes host)
       :address (fn2-nop-address op) :length (fn2-nop-len op) :offset (fn2-nop-offset op)))
    (incf (fn2-nhost-storage-pending host))))

(defun fn2-n-storage-completions (host)
  (when (fn2-nhost-storage host)
    (dotimes (i (fn2-nhost-harvest-limit host))
      (declare (ignore i))
      (let ((job (fn2-device-take-completion (fn2-nhost-storage host))))
        (unless job (return))
        (let ((op (aref (fn2-nhost-ops host) (fn2-device-job-slot job))))
          (assert (= (fn2-nop-gen op) (fn2-device-job-gen job)))
          (fn2-n-boundary host "device-return")
          (multiple-value-bind (code count)
              (fn2-device-io-observation (fn2-device-job-result job) (fn2-device-job-errno job))
            (fn2-n-complete host (fn2-device-job-slot job) code count 0 nil
              (and (eq (fn2-device-job-kind job) :read)
                   (fn2-n-octets host (fn2-device-job-address job) count))))
          (decf (fn2-nhost-storage-pending host)))))))

;;; Ops started at take: Close, Cancel, Read, Write, Fence, and the kinds with no facility.
(defun fn2-n-start-now (host slot)
  (let* ((op (aref (fn2-nhost-ops host) slot)) (kind (fn2-nop-kind op)))
    (cond
      ((and (fn2-nhost-storage host) (fn2-n-storage-kind kind))
       (fn2-n-storage-submit host slot))
      ((= kind *fn2-action-close*)
       (let ((cap (fn2-n-cap host op)))
         (fn2-n-boundary host "syscall")
         (when cap
           (fn2-native-mux-interest (fn2-nhost-mux host) (fn2-nop-cap op) (fn2-ncap-fd cap) 0)
           (fn2-native-tls-close (fn2-ncap-tls cap))
           (setf (fn2-ncap-tls cap) nil)
           (fn2-native-close (fn2-ncap-fd cap))
           (setf (fn2-ncap-fd cap) -1 (fn2-ncap-closed cap) t)
           ;; Other waiting uses keep their loans until the core cancels them;
           ;; no syscall ran for them, so no result is invented.
           (loop for other across (fn2-nhost-ops host)
                 when (and (not (eq other op)) (= (fn2-nop-state other) +fn2-n-waiting+)
                           (eql (fn2-nop-cap other) (fn2-nop-cap op)) (eql (fn2-nop-nonce other) (fn2-nop-nonce op)))
                   do (setf (fn2-nop-state other) +fn2-n-closed-waiting+)))
         ;; Close always completes (the vocabulary has no failure for it).
         (fn2-n-complete host slot :ok 0)))
      ((= kind *fn2-action-cancel*)
       (let* ((target (fn2-nop-target op)) (ops (fn2-nhost-ops host))
              (other (and (< target (length ops)) (/= target slot) (aref ops target))))
         (if (and other
                  ;; A submitted blocking storage call cannot be cancelled.
                  ;; Its real result retains the loan; Cancel reports too late.
                  (not (and (fn2-nhost-storage host) (fn2-n-storage-kind (fn2-nop-kind other))))
                  (eql (fn2-nop-gen other) (fn2-nop-target-gen op))
                  (or (= (fn2-nop-state other) +fn2-n-waiting+) (= (fn2-nop-state other) +fn2-n-closed-waiting+)))
             (progn
                    ;; A cancelled SSL read/write may retain library retry
                    ;; state. Destroy it before releasing the loan; remember
                    ;; TLS selection so later I/O cannot fall back to plaintext.
                    (let ((cap (fn2-n-cap host other)))
                      (when (and cap (fn2-n-tls-op-p other cap))
                        (setf (fn2-ncap-tls-selected cap) t)
                        (fn2-native-tls-close (fn2-ncap-tls cap))
                        (setf (fn2-ncap-tls cap) nil)))
                    (fn2-n-complete host target :cancelled 0)
                    (fn2-n-complete host slot :ok 0 0 t))
           (fn2-n-complete host slot :ok 0 0 nil))))
      ((= kind *fn2-action-write*)
       ;; the loaned octets onto the device at the storage offset
       (let ((bytes (fn2-nhost-bytes host)) (address (fn2-nop-address op)) (off (fn2-nop-offset op)))
         (dotimes (i (fn2-nop-len op)) (fn2-n-device-set host (+ off i) (aref bytes (+ address i))))
         (fn2-n-complete host slot :ok (fn2-nop-len op))))
      ((= kind *fn2-action-read*)
       ;; the device's octets into the leased span
       (let ((bytes (fn2-nhost-bytes host)) (address (fn2-nop-address op)) (off (fn2-nop-offset op)))
         (dotimes (i (fn2-nop-len op)) (setf (aref bytes (+ address i)) (fn2-n-device-ref host (+ off i))))
         (fn2-n-complete host slot :ok (fn2-nop-len op) 0 nil (fn2-n-octets host address (fn2-nop-len op)))))
      ((= kind *fn2-action-fence*)
       ;; every write completed at take: the fence has nothing outstanding
       (fn2-n-complete host slot :ok 0))
      ((= kind *fn2-action-connect*)
       ;; No facility in layer A: explicit failure, never a simulated success.
       (fn2-n-complete host slot :failed 0))
      (t (error "fn2 native: op kind ~d has no backend" kind)))))

(defun fn2-n-resultless-p (kind)
  (or (= kind *fn2-action-arm-wake*) (= kind *fn2-action-trace*) (= kind *fn2-action-service-posture*)))
(defun fn2-n-readiness-p (kind)
  (or (= kind *fn2-action-accept*) (= kind *fn2-action-receive*) (= kind *fn2-action-send*)
      (= kind *fn2-action-tls-start*)))

;;; Take the outbox prefix: peek, copy the descriptor and its validated span,
;;; acknowledge (from here the op is submitted and ours to execute).
(defun fn2-n-take (host)
  (let ((core (fn2-nhost-core host)))
    (dotimes (i (min (fn2-nhost-action-limit host) (fn2-host-outbox-queued core)))
      (declare (ignore i))
      (multiple-value-bind (code slot gen) (fn2-host-outbox-peek 0 core)
        (assert (eq code :ok))
        (let ((op (aref (fn2-nhost-ops host) slot)))
          (assert (= (fn2-nop-state op) +fn2-n-free+))
          (multiple-value-bind (acode kind cap nonce rslot rgen off len storage-offset fua may-release
                                cslot cgen deadline observation-gen)
              (fn2-host-action slot core)
            (assert (eq acode :ok))
            (multiple-value-bind (span address span-len) (fn2-host-op-span slot gen core)
              (unless (eq span :ok) (error "fn2 native: descriptor ~d has no valid span (~s)" slot span))
              (setf op (make-fn2-nop :state +fn2-n-waiting+ :gen gen :kind kind :cap cap :nonce nonce
                                     :address address :len span-len :target cslot :target-gen cgen
                                     :offset storage-offset :fua fua))
              (setf (aref (fn2-nhost-ops host) slot) op))
            (fn2-n-record host (list :take slot gen kind cap nonce rslot rgen off len storage-offset fua
                                     may-release cslot cgen deadline observation-gen))
            (fn2-n-boundary host "take")
            (multiple-value-bind (ack c) (fn2-host-outbox-ack 1 core)
              (declare (ignore c))
              (assert (eq ack :ok)))
            (fn2-n-record host (list :ack 1))
            (fn2-n-boundary host "ack")
            (cond ((fn2-n-resultless-p kind)
                   (multiple-value-bind (fin c) (fn2-host-op-finish slot gen core)
                     (declare (ignore c))
                     (assert (eq fin :ok)))
                   (fn2-n-record host (list :finish slot gen))
                   (setf (fn2-nop-state op) +fn2-n-free+))
                  ((fn2-n-readiness-p kind) nil)
                  (t (fn2-n-start-now host slot)))))))))

;;; Post at most H completed results in completion order. A stray from this
;;; adapter is an adapter defect: stop by name.
(defun fn2-n-post-completions (host)
  (let ((core (fn2-nhost-core host)) (queue (fn2-nhost-completions host)))
    (dotimes (i (min (fn2-nhost-pending host) (fn2-nhost-harvest-limit host)))
      (declare (ignore i))
      (let* ((slot (aref queue (fn2-nhost-chead host))) (op (aref (fn2-nhost-ops host) slot))
             (kind (fn2-nop-kind op)) (stray (fn2-host-stray core))
             (accept (= kind *fn2-action-accept*))
             (done (eql (fn2-nop-outcome op) *fn2-outcome-done*))
             (family (if (and accept done) (fn2-n-family-code (fn2-nop-family op)) *fn2-peer-family-none*))
             (peer (if (and accept done)
                       (list (fn2-nop-port op) (fn2-nop-w0 op) (fn2-nop-w1 op) (fn2-nop-w2 op) (fn2-nop-w3 op))
                     (list 0 0 0 0 0)))
             (event (fn2-terminal-event kind)))
        (if accept
            (fn2-host-post-accept-result slot (fn2-nop-gen op) (fn2-nop-outcome op) (fn2-nop-reason op)
                                         (fn2-nop-aux0 op) (fn2-nop-aux1 op) family
                                         (nth 0 peer) (nth 1 peer) (nth 2 peer) (nth 3 peer) (nth 4 peer) core)
          (fn2-host-post-result 0 slot (fn2-nop-gen op) event (fn2-nop-outcome op) (fn2-nop-reason op)
                                (fn2-nop-count op) (fn2-nop-aux0 op) (fn2-nop-aux1 op) core))
        (unless (= stray (fn2-host-stray core))
          (error "fn2 native: the core refused our post of op ~d (kind ~d): an adapter defect" slot kind))
        (fn2-n-record host (list :post 0 slot (fn2-nop-gen op) event (fn2-nop-outcome op) (fn2-nop-reason op)
                                 (fn2-nop-count op) (fn2-nop-aux0 op) (fn2-nop-aux1 op) family peer
                                 (fn2-nop-octets op)))
        (setf (aref (fn2-nhost-ops host) slot) (make-fn2-nop)
              (fn2-nhost-chead host) (mod (1+ (fn2-nhost-chead host)) (length queue)))
        (decf (fn2-nhost-pending host))
        (fn2-n-boundary host "post")))))

;;; Interests: a waiting Accept or Receive wants readable, a Send writable.
(defun fn2-n-interests (host)
  (let* ((caps (fn2-nhost-caps host)) (masks (make-array (length caps) :initial-element 0)))
    (loop for op across (fn2-nhost-ops host)
          when (and (= (fn2-nop-state op) +fn2-n-waiting+) (fn2-n-readiness-p (fn2-nop-kind op)))
            do (let ((cap (fn2-n-cap host op)))
                 (unless cap (error "fn2 native: a waiting op names a dead capability ~d" (fn2-nop-cap op)))
                 (setf (aref masks (fn2-nop-cap op))
                       (logior (aref masks (fn2-nop-cap op)) (fn2-n-op-interest op cap)))))
    (dotimes (i (length caps))
      (fn2-native-mux-interest (fn2-nhost-mux host) i (fn2-ncap-fd (aref caps i)) (aref masks i)))
    ;; The Unix-domain socket is capability 0's: it wants what the listener wants.
    (when (>= (fn2-nhost-local-fd host) 0)
      (fn2-native-mux-interest (fn2-nhost-mux host) (fn2-native-mux-local-index (fn2-nhost-mux host))
                               (fn2-nhost-local-fd host) (aref masks 0)))))

(defun fn2-n-cap-ready-p (host index mask)
  (let ((mux (fn2-nhost-mux host)))
    (or (fn2-native-mux-ready-p mux index mask)
        (and (= index 0) (>= (fn2-nhost-local-fd host) 0)
             (fn2-native-mux-ready-p mux (fn2-native-mux-local-index mux) mask)))))

;;; For each ready capability, one syscall for one of its waiting ops.
(defun fn2-n-ready (host)
  (let ((used (make-array (length (fn2-nhost-caps host)) :initial-element nil)) (any nil))
    (dotimes (slot (length (fn2-nhost-ops host)))
      (let ((op (aref (fn2-nhost-ops host) slot)))
        (when (and (= (fn2-nop-state op) +fn2-n-waiting+) (fn2-n-readiness-p (fn2-nop-kind op)))
          (let ((cap (fn2-n-cap host op)) (index (fn2-nop-cap op)))
            (when (and cap (not (aref used index))
                       (or (fn2-n-tls-kick-p op cap) (fn2-n-cap-ready-p host index (fn2-n-op-interest op cap))))
              (setf (aref used index) t any t)
              (fn2-n-start-ready host slot cap))))))
    any))

(defun fn2-n-control-numbers (text count)
  "Parse the harness's decimal counters, never Lisp syntax. TEXT is bounded."
  (let ((pos 0) (values nil) (end (length text)))
    (dotimes (field count)
      (loop while (and (< pos end) (char= (char text pos) #\Space)) do (incf pos))
      (let ((start pos) (value 0))
        (loop while (and (< pos end) (digit-char-p (char text pos) 10))
              do (setf value (+ (* value 10) (digit-char-p (char text pos) 10)))
                 (incf pos))
        (unless (and (> pos start) (<= (- pos start) 20)
                     (or (= pos end) (char= (char text pos) #\Space)))
          (error "fn2 native: invalid decimal control field"))
        (push value values)))
    (loop while (and (< pos end) (char= (char text pos) #\Space)) do (incf pos))
    (unless (= pos end) (error "fn2 native: extra control fields"))
    (nreverse values)))

(defun fn2-n-control-line (host line)
  (cond ((string= line "stop") (setf (fn2-nhost-stop host) t))
        ((and (> (length line) 5) (string= line "sync " :end1 5))
         (setf (fn2-nhost-sync host) (append (fn2-n-control-numbers (subseq line 5) 3) '(nil))))
        ((and (> (length line) 5) (string= line "open " :end1 5))
         (setf (fn2-nhost-sync host) (append (fn2-n-control-numbers (subseq line 5) 1) '(0 0 t))))
        ((string= line "") nil)
        (t (error "fn2 native: unknown control line ~s" line))))

;;; Harness-only input (control-fd=-1 on the served node). A command has at
;;; most three 20-digit decimal fields. Bound retained input before appending;
;;; fragmented or malicious input cannot grow an unbounded Lisp string.
(defun fn2-n-control-octet (host byte)
  (let ((text (fn2-nhost-control-text host)))
    (if (= byte 10)
        (progn
          (fn2-n-control-line host (string-trim '(#\Return #\Space) text))
          (setf (fn2-nhost-control-text host) ""))
      (progn
        (when (>= (length text) 96) (error "fn2 native: control line too long"))
        (unless (or (= byte 13) (<= 32 byte 126))
          (error "fn2 native: non-ASCII control input"))
        (setf (fn2-nhost-control-text host) (concatenate 'string text (string (code-char byte))))))))

(defun fn2-n-control-read (host)
  (let ((fd (fn2-nhost-control-fd host)) (window (fn2-nhost-control-window host)))
    (multiple-value-bind (n errno) (fn2-native-syscall (%fn2-native-read fd window 4096))
      (declare (ignore errno))
      (cond ((zerop n) (setf (fn2-nhost-stop host) t))
            ((plusp n)
             (dotimes (i n) (fn2-n-control-octet host (sb-sys:sap-ref-8 window i))))))))

(defun fn2-n-cap-by-port (host port &optional openp)
  "The incarnation PORT names: for an open, the newest one accepted with that peer
port that is not the incarnation the port was bound to before (and bind it);
otherwise the bound one. Values: (index . cap) or nil."
  (let* ((caps (fn2-nhost-caps host)) (bound (gethash port (fn2-nhost-bindings host))))
    (if openp
        (let ((best nil))
          (loop for i from 1 below (length caps)
                for cap = (aref caps i)
                when (and (eql (fn2-ncap-port cap) port) (plusp (fn2-ncap-seq cap))
                          (not (equal bound (cons i (fn2-ncap-nonce cap))))
                          (or (null best) (> (fn2-ncap-seq cap) (fn2-ncap-seq (cdr best)))))
                  do (setf best (cons i cap)))
          (when best (setf (gethash port (fn2-nhost-bindings host)) (cons (car best) (fn2-ncap-nonce (cdr best)))))
          best)
      (and bound (let ((cap (aref caps (car bound))))
                   (and (eql (fn2-ncap-nonce cap) (cdr bound)) (cons (car bound) cap)))))))
(defun fn2-n-cap-receiving-p (host index nonce)
  (loop for op across (fn2-nhost-ops host)
        thereis (and (= (fn2-nop-state op) +fn2-n-waiting+) (= (fn2-nop-kind op) *fn2-action-receive*)
                     (eql (fn2-nop-cap op) index) (eql (fn2-nop-nonce op) nonce))))

;;; Quiescence for the pending sync: the iteration just ended with nothing
;;; queued, the turn idle, the outbox empty, nothing ready; and the named
;;; connection has delivered what its client sent, or closed, or reads no more.
(defun fn2-n-quiet-check (host status ready)
  (let ((sync (fn2-nhost-sync host)) (core (fn2-nhost-core host)))
    (when (and sync (eq status :idle) (not ready) (zerop (fn2-nhost-pending host))
               (zerop (fn2-nhost-storage-pending host))
               (zerop (fn2-host-outbox-queued core)))
      (destructuring-bind (port sent eof openp) sync
        (let ((found (fn2-n-cap-by-port host port openp)))
          ;; An open binds once; it then waits on that incarnation like a sync.
          (when (and found openp) (setf (fourth (fn2-nhost-sync host)) nil))
          (when found
            (let* ((index (car found)) (cap (cdr found))
                   (delivered (and (>= (fn2-ncap-rx cap) sent) (or (eql eof 0) (fn2-ncap-eof cap)))))
              (when (or (fn2-ncap-closed cap) delivered
                        (not (fn2-n-cap-receiving-p host index (fn2-ncap-nonce cap))))
                (format t "@@FN2SS quiet ~d ~d ~d:~d@@~%" (fn2-ncap-tx cap) (if (fn2-ncap-closed cap) 1 0)
                        index (fn2-ncap-nonce cap))
                (finish-output)
                (setf (fn2-nhost-sync host) nil)))))))))

(defun fn2-n-iteration (host)
  "One loop iteration (layer doc 4.1.3, steps 1-6). Returns the turn status.
A stopped core is a recovery boundary: no clock, completion, signal, turn or
take reaches it after the stopping turn (the core refuses them all anyway)."
  (let ((core (fn2-nhost-core host)))
    (when (fn2-host-stopped-p core)
      (return-from fn2-n-iteration :stop))
    (let ((mono (fn2-native-clock t)) (real (fn2-native-clock nil)))
      (fn2-host-post-clock mono real 1 core)
      (fn2-n-record host (list :clock mono real 1)))
    (fn2-n-storage-completions host)
    (fn2-n-post-completions host)
    (when (or (plusp *fn2-n-signal*) (fn2-nhost-stop host))
      (unless (plusp (fn2-nhost-signal host))
        (setf (fn2-nhost-signal host) 1)
        (fn2-host-post-signal 1 core)
        (fn2-n-record host (list :signal 1))))
    (multiple-value-bind (status nobs nvisits nactions c) (fn2-turn core)
      (declare (ignore nobs nvisits nactions c))
      (fn2-n-record host (list :turn status))
      (incf (fn2-nhost-iterations host))
      (if (eq status :stop) status
        (progn
          (fn2-n-take host)
          (fn2-n-interests host)
          (let* ((deadline (fn2-host-idle-deadline core))
                 (timeout (cond ((or (not (eq status :idle)) (plusp (fn2-nhost-pending host)) (fn2-n-tls-work-p host)) 0)
                                ((fn2-nhost-sync host) 2)
                                ((>= deadline *fn2-no-deadline*) -1)
                                (t (min 1000 (max 0 (floor (- deadline (fn2-native-clock t)) 1000)))))))
            (fn2-native-mux-wait (fn2-nhost-mux host) timeout)
            (when (and (>= (fn2-nhost-control-fd host) 0) (fn2-native-mux-control-ready-p (fn2-nhost-mux host)))
              (fn2-n-control-read host))
            (let ((ready (fn2-n-ready host)))
              (fn2-n-quiet-check host status ready)))
          status)))))

(defun fn2-n-signal-handler (signal info context)
  (declare (ignore signal info context))
  ;; No core function runs in a handler: the sticky bit, then the mux wake.
  (setf *fn2-n-signal* 1)
  (when *fn2-n-signal-mux* (fn2-native-mux-signal *fn2-n-signal-mux*)))

(defun fn2-n-live-core ()
  (or (cdr (assoc 'fn2-core (user-stobj-alist *the-live-state*)))
      (error "fn2 native: the certified core stobj is absent")))

(defun fn2-n-open-host (profile core &key (control-fd -1) (trace-capacity 0) (kill-at 0)
                                      device-path create-size memory-store)
  "Open I/O for an initialized CORE. MEMORY-STORE supplies test-device writes;
the image launcher always opens its persisted device instead."
  (when (and device-path memory-store)
    (error "fn2 native: image startup cannot use a memory fixture"))
  (when (and create-size (not (eq (fn2-image-create-request create-size profile) :ok)))
    (error "fn2 image create: geometry"))
  (multiple-value-bind (bind address port path) (fn2-host-listener-bind profile)
   (unless (eq bind :ok) (error "fn2 native: refused to start: the profile's ~(~a~) is out of range" bind))
  (let* ((n (fn2-profile-o profile))
         (ncaps (+ 1 (fn2-profile-c profile) (fn2-profile-accept-credits profile) n)))
    (multiple-value-bind (lfd lport) (fn2-native-listen port address)
      (let ((host (make-fn2-nhost
                   :core core
                   ;; The one raw nested access: the pool's byte array, for SAPs.
                   :bytes (svref (svref core *fn2-core-pool*) *fn2-pool-datai*)
                   :ops (let ((v (make-array n))) (dotimes (i n v) (setf (aref v i) (make-fn2-nop))))
                   :caps (let ((v (make-array ncaps))) (dotimes (i ncaps v) (setf (aref v i) (make-fn2-ncap))))
                   :mux (make-fn2-native-mux ncaps) :listen-port lport
                   :completions (make-array (* 2 n) :initial-element 0)
                   :harvest-limit (fn2-profile-h profile) :action-limit (fn2-profile-aturn profile)
                   :trace (and (plusp trace-capacity) (make-array trace-capacity :initial-element nil))
                   :kill-at kill-at :control-fd control-fd
                   :control-window (fn2-native-window 4096))))
        (assert (typep (fn2-nhost-bytes host) '(simple-array (unsigned-byte 8) (*))))
        (setf (fn2-ncap-fd (aref (fn2-nhost-caps host) 0)) lfd)
        (handler-case
          (progn
        (multiple-value-bind (code certificate key window quantum minimum seed-capacity turns) (fn2-host-tls-settings profile)
          (case code
            (:off nil)
            (:ok
             (sb-alien:load-shared-object
               (or (sb-ext:posix-getenv "FN2_TLS_LIBRARY")
                   #+darwin "build/lib/libfn2-tls.dylib" #-darwin "build/lib/libfn2-tls.so"))
             (let ((config (fn2-tls-%config certificate key minimum)))
               (when (zerop (sb-sys:sap-int config)) (error "fn2 native: TLS configuration refused"))
               (setf (fn2-nhost-tls-config host) config
                     (fn2-nhost-tls-window host) window (fn2-nhost-tls-quantum host) quantum
                     (fn2-nhost-tls-seed-capacity host) seed-capacity (fn2-nhost-tls-turns host) turns)))
            (otherwise (error "fn2 native: TLS profile refused"))))
        (unless device-path (fn2-n-device-put host memory-store))
        (when device-path
          (multiple-value-bind (fd size backend) (fn2-device-open device-path :create-size create-size)
            (multiple-value-bind (code cap observed-size observed-backend)
                (fn2-device-open-observation fd size backend)
              (unless (eq code :ok)
                (fn2-native-close fd)
                (error "fn2 native: invalid device observation"))
              (setf (fn2-nhost-storage host)
                    (fn2-device-start cap observed-size observed-backend n
                      (lambda () (fn2-native-mux-signal (fn2-nhost-mux host)))
                      (lambda (label) (fn2-n-boundary host label)))))))
        (when path
          (setf (fn2-nhost-local-fd host) (fn2-native-listen-local path)
                (fn2-nhost-local-path host) path))
        (when (>= control-fd 0) (fn2-native-mux-watch-control (fn2-nhost-mux host) control-fd))
        (setf *fn2-n-signal* 0 *fn2-n-signal-mux* (fn2-nhost-mux host))
        (sb-sys:enable-interrupt sb-unix:sigterm #'fn2-n-signal-handler)
        (sb-sys:enable-interrupt sb-unix:sigint #'fn2-n-signal-handler)
        (when device-path
                (multiple-value-bind (code c)
                    (fn2-boot-start (not (null create-size)) (fn2-device-size (fn2-nhost-storage host)) core)
                  (declare (ignore c))
                  (unless (eq code :ok) (error "fn2 image boot: ~s" code)))
                (loop for status = (fn2-boot-status core)
                      until (eq status :ready)
                      do (when (eq status :failed)
                           (error "fn2 image boot stopped: ~d" (fn2-host-stop-reason core)))
                         (fn2-n-iteration host)))
        host)
          (error (condition) (fn2-n-destroy host) (error condition))))))))

(defun fn2-n-make-host (profile &key (control-fd -1) (trace-capacity 0) (kill-at 0)
                                  device-path create-size)
  "Initialize the live core and open its configured listeners and device."
  (when device-path (setf profile (fn2-image-profile profile)))
  (let ((core (fn2-n-live-core)))
    (fn2-init-executor profile :echo nil core)
    (fn2-n-open-host profile core :control-fd control-fd :trace-capacity trace-capacity
                     :kill-at kill-at :device-path device-path :create-size create-size)))

(defun fn2-n-run (host)
  "Iterate until the core stops (a signal or a stop control posts the sticky signal)."
  (loop for status = (fn2-n-iteration host) until (eq status :stop))
  (fn2-host-stop-reason (fn2-nhost-core host)))

(defun fn2-n-destroy (host)
  ;; No completion claims at teardown; socket operations die with the descriptors.
  (setf *fn2-n-signal-mux* nil)
  (when (fn2-nhost-storage host) (fn2-device-stop (fn2-nhost-storage host)))
  (loop for cap across (fn2-nhost-caps host)
        do (fn2-native-tls-close (fn2-ncap-tls cap))
           (setf (fn2-ncap-tls cap) nil)
        when (>= (fn2-ncap-fd cap) 0) do (fn2-native-close (fn2-ncap-fd cap)))
  (when (fn2-nhost-tls-config host)
    (fn2-tls-%config-free (fn2-nhost-tls-config host))
    (setf (fn2-nhost-tls-config host) nil))
  (when (>= (fn2-nhost-local-fd host) 0)
    (fn2-native-close (fn2-nhost-local-fd host))
    (fn2-native-unlink-local (fn2-nhost-local-path host)))
  (fn2-native-unmap (fn2-nhost-control-window host) 4096)
  (fn2-native-mux-destroy (fn2-nhost-mux host)))
