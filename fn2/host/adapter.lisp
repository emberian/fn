;;; A5r: the native event loop over the served core (layer doc 4.1.3).
;;; Raw SBCL, loaded by a session script after the certified books
;;; (fn2/books/host-boundary.lisp, which gives the scalar entry points) and
;;; fn2/host/ffi.lisp. One thread. The loop implements physical scheduling
;;; and reports observations through the core's own posting entries; every
;;; cell's words come from the logical normalizer fn2-host-result. A byte
;;; enters the core only when fn2-turn harvests its result.
(in-package "ACL2")

;; Op record states.
(defconstant +fn2-n-free+ 0)
(defconstant +fn2-n-waiting+ 1)
(defconstant +fn2-n-closed-waiting+ 2)  ; its capability was closed under it
(defconstant +fn2-n-completed+ 3)

(defstruct fn2-nop
  (state 0 :type fixnum) (gen 0) (kind 0 :type fixnum) (cap 0) (nonce 0)
  (address 0 :type fixnum) (len 0 :type fixnum) (target 0) (target-gen 0)
  (outcome 0) (reason 0) (count 0) (aux0 0) (aux1 0)
  (family :none) (port 0) (w0 0) (w1 0) (w2 0) (w3 0) (octets nil))

;; A capability: index 0 is the listener; connections from 1.
(defstruct fn2-ncap
  (fd -1 :type fixnum) (nonce 0) (family :none) (port 0) (w0 0) (w1 0) (w2 0) (w3 0)
  (rx 0) (eof nil) (tx 0) (closed nil))

(defstruct fn2-nhost
  core bytes ops caps mux (listen-port 0)
  completions (chead 0 :type fixnum) (ctail 0 :type fixnum) (pending 0 :type fixnum)
  (harvest-limit 1) (action-limit 1)
  ;; test instruments: the boundary trace (ENVELOPE), death cuts, the session
  trace (trace-count 0 :type fixnum) (boundaries 0 :type fixnum) (kill-at 0 :type fixnum)
  (control-fd -1 :type fixnum) control-window (control-text "")
  sync (stop nil) (signal 0) (iterations 0))

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
  (incf (fn2-nhost-boundaries host))
  (when (= (fn2-nhost-boundaries host) (fn2-nhost-kill-at host))
    (format t "FN2 KILL boundary=~d label=~a~%" (fn2-nhost-boundaries host) label)
    (finish-output)
    (sb-ext:exit :code 86 :abort t)))

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
                                    :w0 w0 :w1 w1 :w2 w2 :w3 w3))
               (return-from fn2-n-new-cap (values i (1+ (fn2-ncap-nonce cap)))))
    ;; Capacity covers every accept credit, so this is a host defect: stop by name.
    (fn2-native-close fd)
    (error "fn2 native: capability table exhausted")))

(defun fn2-n-sap (host address)
  (sb-sys:sap+ (sb-sys:vector-sap (fn2-nhost-bytes host)) address))

;;; One syscall for a waiting op whose descriptor is ready. EAGAIN leaves it
;;; waiting (the simulator's zero-progress would-block); never a failure.
(defun fn2-n-again-p (errno) (or (= errno 35) (= errno 11) (= errno 4)))

(defun fn2-n-start-ready (host slot cap)
  (let* ((op (aref (fn2-nhost-ops host) slot)) (kind (fn2-nop-kind op)) (fd (fn2-ncap-fd cap)))
    (fn2-n-boundary host "syscall")
    (cond
      ((= kind *fn2-action-accept*)
       (multiple-value-bind (new errno family port w0 w1 w2 w3) (fn2-native-accept fd)
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

;;; Ops started at take: Close, Cancel, and the kinds with no facility.
(defun fn2-n-start-now (host slot)
  (let* ((op (aref (fn2-nhost-ops host) slot)) (kind (fn2-nop-kind op)))
    (cond
      ((= kind *fn2-action-close*)
       (let ((cap (fn2-n-cap host op)))
         (fn2-n-boundary host "syscall")
         (when cap
           (fn2-native-mux-interest (fn2-nhost-mux host) (fn2-nop-cap op) (fn2-ncap-fd cap) 0)
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
         (if (and other (eql (fn2-nop-gen other) (fn2-nop-target-gen op))
                  (or (= (fn2-nop-state other) +fn2-n-waiting+) (= (fn2-nop-state other) +fn2-n-closed-waiting+)))
             (progn (fn2-n-complete host target :cancelled 0)
                    (fn2-n-complete host slot :ok 0 0 t))
           (fn2-n-complete host slot :ok 0 0 nil))))
      ((or (= kind *fn2-action-connect*) (= kind *fn2-action-tls-start*))
       ;; No facility in layer A: explicit failure, never a simulated success.
       (fn2-n-complete host slot :failed 0))
      (t (error "fn2 native: op kind ~d has no backend yet (storage arrives with B's durable POST)" kind)))))

(defun fn2-n-resultless-p (kind)
  (or (= kind *fn2-action-arm-wake*) (= kind *fn2-action-trace*) (= kind *fn2-action-service-posture*)))
(defun fn2-n-readiness-p (kind)
  (or (= kind *fn2-action-accept*) (= kind *fn2-action-receive*) (= kind *fn2-action-send*)))

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
                                     :address address :len span-len :target cslot :target-gen cgen))
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
                       (logior (aref masks (fn2-nop-cap op)) (if (= (fn2-nop-kind op) *fn2-action-send*) 4 1)))))
    (dotimes (i (length caps))
      (fn2-native-mux-interest (fn2-nhost-mux host) i (fn2-ncap-fd (aref caps i)) (aref masks i)))))

;;; For each ready capability, one syscall for one of its waiting ops.
(defun fn2-n-ready (host)
  (let ((used (make-array (length (fn2-nhost-caps host)) :initial-element nil)) (any nil))
    (dotimes (slot (length (fn2-nhost-ops host)))
      (let ((op (aref (fn2-nhost-ops host) slot)))
        (when (and (= (fn2-nop-state op) +fn2-n-waiting+) (fn2-n-readiness-p (fn2-nop-kind op)))
          (let ((cap (fn2-n-cap host op)) (index (fn2-nop-cap op)))
            (when (and cap (not (aref used index))
                       (fn2-native-mux-ready-p (fn2-nhost-mux host) index
                                               (if (= (fn2-nop-kind op) *fn2-action-send*) 4 1)))
              (setf (aref used index) t any t)
              (fn2-n-start-ready host slot cap))))))
    any))

;;; The session's control input (layer doc 4.1.4): "sync PORT SENT EOF" and "stop".
(defun fn2-n-control-read (host)
  (let ((fd (fn2-nhost-control-fd host)) (window (fn2-nhost-control-window host)))
    (multiple-value-bind (n errno) (fn2-native-syscall (%fn2-native-read fd window 4096))
      (declare (ignore errno))
      (cond ((zerop n) (setf (fn2-nhost-stop host) t))       ; the session went away
            ((plusp n)
             (let ((text (concatenate 'string (fn2-nhost-control-text host)
                                      (map 'string #'code-char (loop for i below n collect (sb-sys:sap-ref-8 window i))))))
               (loop for at = (position #\Newline text)
                     while at
                     do (let ((line (string-trim '(#\Return #\Space) (subseq text 0 at))))
                          (setf text (subseq text (1+ at)))
                          (cond ((string= line "stop") (setf (fn2-nhost-stop host) t))
                                ((and (> (length line) 5) (string= (subseq line 0 5) "sync "))
                                 (with-input-from-string (in (subseq line 5))
                                   (setf (fn2-nhost-sync host) (list (read in) (read in) (read in)))))
                                ((string= line "") nil)
                                (t (error "fn2 native: unknown control line ~s" line)))))
               (setf (fn2-nhost-control-text host) text)))))))

(defun fn2-n-cap-by-port (host port)
  (let ((caps (fn2-nhost-caps host)) (best nil))
    ;; The newest incarnation with that peer port (closed ones included).
    (loop for i from 1 below (length caps)
          for cap = (aref caps i)
          when (and (eql (fn2-ncap-port cap) port) (or (>= (fn2-ncap-fd cap) 0) (fn2-ncap-closed cap)))
            do (setf best (cons i cap)))
    best))
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
               (zerop (fn2-host-outbox-queued core)))
      (destructuring-bind (port sent eof) sync
        (let ((found (fn2-n-cap-by-port host port)))
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
  "One loop iteration (layer doc 4.1.3, steps 1-6). Returns the turn status."
  (let ((core (fn2-nhost-core host)))
    (let ((mono (fn2-native-clock t)) (real (fn2-native-clock nil)))
      (fn2-host-post-clock mono real 1 core)
      (fn2-n-record host (list :clock mono real 1)))
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
                 (timeout (cond ((or (not (eq status :idle)) (plusp (fn2-nhost-pending host))) 0)
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

(defun fn2-n-make-host (profile &key (port 0) (control-fd -1) (trace-capacity 0) (kill-at 0))
  "Initialize the live core with PROFILE, bind 127.0.0.1:PORT, and return the host."
  (let* ((core (fn2-n-live-core))
         (n (fn2-profile-o profile))
         (ncaps (+ 1 (fn2-profile-c profile) (fn2-profile-accept-credits profile) n)))
    (fn2-init-executor profile :echo nil core)
    (multiple-value-bind (lfd lport) (fn2-native-listen port)
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
        (when (>= control-fd 0) (fn2-native-mux-watch-control (fn2-nhost-mux host) control-fd))
        (setf *fn2-n-signal* 0 *fn2-n-signal-mux* (fn2-nhost-mux host))
        (sb-sys:enable-interrupt sb-unix:sigterm #'fn2-n-signal-handler)
        (sb-sys:enable-interrupt sb-unix:sigint #'fn2-n-signal-handler)
        host))))

(defun fn2-n-run (host)
  "Iterate until the core stops (a signal or a stop control posts the sticky signal)."
  (loop for status = (fn2-n-iteration host) until (eq status :stop))
  (fn2-host-stop-reason (fn2-nhost-core host)))

(defun fn2-n-destroy (host)
  ;; No completion claims at teardown; socket operations die with the descriptors.
  (setf *fn2-n-signal-mux* nil)
  (loop for cap across (fn2-nhost-caps host) when (>= (fn2-ncap-fd cap) 0) do (fn2-native-close (fn2-ncap-fd cap)))
  (fn2-native-unmap (fn2-nhost-control-window host) 4096)
  (fn2-native-mux-destroy (fn2-nhost-mux host)))
