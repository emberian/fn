;;; Explicit BP retained-session projection; one physical owner, no threads.
(in-package "ACL2")
(defstruct (fnn-bp-session-bank (:conc-name fnn-bpsb-)) grant ledger (held (make-hash-table :test #'eq)) slots incoming-cursor outgoing-cursor)
(defstruct (fnn-bp-session-grant (:conc-name fnn-bpsg-)) row socket conn
  turn finish result peer (close-attempted nil) (connecting nil))
(defvar *fnn-bp-session-bank* nil)

(defun fnn-bp-session-profile (root)
 (let* ((path (fnn-join root (fnn-core 'fn-bpsp-file-name)))
        (present (fnn-lstat path))
        (profile (fnn-core 'fn-bpsp-read
                  (and present (fnn-octet-list
                    (fnn-read-regular-bounded path (fnn-core 'fn-bpsp-read-bound)))))))
  (unless profile (fnn-refuse "BP session profile refused in ~a" path)) profile))

(defun fnn-bp-session-install (bp owner transfer segment)
 "Capture installed profiles and runtime space before any session/socket."
 (let* ((profile (fnn-bp-session-profile (fnn-bps-root bp)))
        (node (fnn-bps-node-profile bp))
        (store (fnn-owner-service-store owner))
        (core (fnn-heap-core-octets))
        (grant (fnn-core 'fn-bpsp-startup profile
                 (fnn-core 'fn-bpsp-captured-wire-span transfer (fnn-core 'fn-bpnpf-bundle-octets node)) segment
                 (sb-ext:dynamic-space-size)
                 (fnn-core 'fn-heap-figure-octets (fnn-store-config store) core +fnn-gc-nursery-octets+)
                 (fnn-core 'fn-bpsp-held-projection
                  (fnn-core 'fn-bpnpf-held-octets node)
                  (fnn-core 'fn-bpnpf-rows node)
                  (fnn-core 'fn-bpnpf-adu-octets node))))
        (bank (make-fnn-bp-session-bank :grant grant
                  :ledger (fnn-core 'create-fn-resource-ledger))))
  (unless (eq (first grant) :hold)
   (fnn-refuse "BP session funding refused ~s" grant))
  ;; Retain the private instance before any mutating call can escape.
  (setq *fnn-bp-session-bank* bank)
  (destructuring-bind (word ledger)
    (fnn-call 'fn-bpsg-install grant (fnn-bpsb-ledger bank))
   (setf (fnn-bpsb-ledger bank) ledger)
   (unless (eq word :installed) (fnn-refuse "BP session bank refused ~a" word)))
  (fnn-out "BP session funding installed inbound=~d outbound=~d resident=~d"
           (fifth grant) (sixth grant) (second grant))
  (setf (fnn-bpsb-slots bank) (make-array (fnn-core 'fn-bpsg-slots grant) :initial-element nil))
  bank))

(defun fnn-bp-session-acquire (bank class)
 "Reserve one candidate before accept/connect or context construction."
 (destructuring-bind (word row next-cursor ledger)
  (fnn-call 'fn-bpsg-acquire-turn (fnn-bpsb-grant bank) class
    (ecase class
     (:incoming (fnn-bpsb-incoming-cursor bank))
     (:outgoing (fnn-bpsb-outgoing-cursor bank)))
    (fnn-bpsb-ledger bank))
  (setf (fnn-bpsb-ledger bank) ledger)
  ;; ACL2 normalizes, advances and wraps the position. It is not authority.
  (ecase class
   (:incoming (setf (fnn-bpsb-incoming-cursor bank) next-cursor))
   (:outgoing (setf (fnn-bpsb-outgoing-cursor bank) next-cursor)))
  (case word
   (:drawn (let ((grant (make-fnn-bp-session-grant :row row)))
             (setf (gethash grant (fnn-bpsb-held bank)) t
                   (aref (fnn-bpsb-slots bank) (second row)) grant)
             (values grant word)))
   ((:bp-session-yield :bp-session-capacity) (values nil word))
   (otherwise (fnn-refuse "BP context reservation refused ~a" word)))))

(defun fnn-bp-session-observe (bank grant observation)
 (let ((answer (fnn-core 'fn-bpsg-step (fnn-bpsg-row grant) observation)))
  (setf (fnn-bpsg-row grant) (second answer))
  (case (first answer)
   (:retain nil)
   (:settle
    (destructuring-bind (word ledger)
     (fnn-call 'fn-bpsg-return (fnn-bpsg-row grant) (fnn-bpsb-ledger bank))
     (setf (fnn-bpsb-ledger bank) ledger)
     (unless (eq word :settled)
      (fnn-fault "BP session custody settlement refused ~a" word))
     (setf (aref (fnn-bpsb-slots bank) (second (fnn-bpsg-row grant))) nil)
     (remhash grant (fnn-bpsb-held bank))))
   (otherwise (fnn-fault "BP session custody observation unavailable")))))

(defun fnn-bp-session-close (bank grant)
 "Close once; ambiguous closure retains its grant and cannot be retried."
 (cond
  ((fnn-bpsg-close-attempted grant) nil)
  ((null (fnn-bpsg-socket grant))
   (setf (fnn-bpsg-close-attempted grant) t)
   (fnn-bp-session-observe bank grant :no-socket))
  (t
   (let ((socket (fnn-bpsg-socket grant)))
    (setf (fnn-bpsg-close-attempted grant) t (fnn-bpsg-socket grant) nil)
    (multiple-value-bind (ignored receipt condition) (fnn-socket-shut socket)
     (declare (ignore ignored))
     (if (eq receipt :closed) (fnn-bp-session-observe bank grant :socket-closed)
       (fnn-indeterminate "BP socket physical return unobserved; custody held: ~a" condition)))))))

(defun fnn-bp-session-release-context (bank grant)
 (let ((conn (fnn-bpsg-conn grant)))
  (cond
   ((not conn) (fnn-bp-session-observe bank grant :no-context))
   ((eq (fnn-core 'fn-bpsg-release-ready
          (fnn-tclc-finished conn) (fnn-tclc-source-pending conn)
          (fnn-tclc-source-root conn) (fnn-tclc-source-token conn)
          (fnn-tclc-held conn) (fnn-tclc-tx-messages conn) (fnn-tclc-tx-data conn)) t)
    ;; No callback/publication is possible after the controller's terminal.
    ;; Remove every context/closure alias before the logical release receipt.
    (setf (fnn-tclc-session conn) nil (fnn-tclc-carry conn) nil
          (fnn-tclc-pending conn) nil (fnn-tclc-on-ready conn) nil
          (fnn-bpsg-conn grant) nil (fnn-bpsg-turn grant) nil (fnn-bpsg-finish grant) nil)
    (fnn-bp-session-observe bank grant :released-context))
   (t nil))))

(defun fnn-bp-session-retire-ordinary-context (grant)
 ;; Abort has already removed every future host TURN/FINISH invocation.
 (let ((conn (fnn-bpsg-conn grant)))
  (when (and conn
        (eq (fnn-core 'fn-bpsg-context-abort-plan
              (fnn-tclc-source-pending conn) (fnn-tclc-source-root conn)
              (fnn-tclc-source-token conn) (fnn-tclc-source-held conn)
              (fnn-tclc-fenced conn)) :retire-context))
   ;; No unreleased ACK may be flushed during the logical close. Existing
   ;; FNBS/Store/FNRJ durable facts outlive these private volatile aliases.
   (fnn-tcl-drop conn)
   (fnn-tcl-turn-lost conn)
   (setf (fnn-tclc-finished conn) t (fnn-tclc-carry conn) nil
         (fnn-tclc-pending conn) nil (fnn-tclc-on-ready conn) nil
         (fnn-tclc-input-buffer conn) nil (fnn-tclc-input-vector conn) nil
         (fnn-tclc-input-octets conn) nil (fnn-tclc-input-materialize-end conn) nil
         (fnn-tclc-source-more conn) nil)
   t)))

(defvar *fnn-bp-session-stranded-roots* nil)

(defun fnn-bp-session-abort-all (bank &optional (signal-condition t))
 ;; All independent receipts are attempted, even when one physical return is
 ;; unobserved. No condition creates a receipt or forgets the retained token.
 (let ((held (loop for grant being the hash-keys of (fnn-bpsb-held bank) collect grant))
       (first-condition nil))
  (dolist (grant held)
   ;; This single writer removes the source continuation before retiring only
   ;; an ACL2-authorized private pre-publication operation. Unknown/publishing
   ;; dependencies remain discoverable; physical close has its own receipt.
   (setf (fnn-bpsg-turn grant) nil (fnn-bpsg-finish grant) nil)
   (handler-case (fnn-bp-session-retire-private-source grant)
    (serious-condition (c) (unless first-condition (setq first-condition c))))
   (handler-case (fnn-bp-session-retire-ordinary-context grant)
    (serious-condition (c) (unless first-condition (setq first-condition c))))
   (handler-case (fnn-bp-session-close bank grant)
    (serious-condition (c) (unless first-condition (setq first-condition c))))
   (handler-case (fnn-bp-session-release-context bank grant)
    (serious-condition (c) (unless first-condition (setq first-condition c)))))
  (when (and signal-condition first-condition) (error first-condition))
  first-condition))

(defun fnn-bp-session-loop (bank control listeners begin once service pending)
 "One writer: one installed listener attempt, one retained slot, one local turn."
 (let ((slot 2) (phase 0) (accepted nil) (once-tail nil) (listener-index 0)
       (work-credit 0) turn-status turn-action)
  (loop
   (setq turn-status nil turn-action nil)
   (when control (fnn-bpnc-pump control))
   (let* ((live (fnn-bplc-live listeners))
          (index (and (consp live) (not (and once accepted))
                   (let ((at (fnn-core 'fn-bpsched-listener-index listener-index (length live))))
                     (and (fnn-poll-readable (list (fnn-socket-fd (nth at live))) 0) at)))))
    (setq listener-index (+ listener-index 1))
    (when index
     (let ((grant (fnn-bp-session-acquire bank :incoming)))
      (when grant
       (let ((plan (fnn-core 'fn-bpsched-accept-plan (fnn-bplc-model listeners)
                            index (fnn-bpsg-row grant) (fnn-bpsb-ledger bank))))
        (unless plan (fnn-fault "ACL2 refused funded BP listener acceptance"))
        (let ((socket (fnn-accept-attempt (nth index live))))
         (if (keywordp socket)
          (progn (fnn-bp-session-observe bank grant :no-context)
                 (fnn-bp-session-close bank grant))
          (progn
           (setf (fnn-bpsg-socket grant) socket)
           (setq accepted t)
           (setf (fnn-bplc-model listeners)
                 (fnn-core 'fn-bpsched-listener-step (fnn-bplc-model listeners)
                   (list :retained-accepted (fnn-core 'fn-bpsg-key (fnn-bpsg-row grant)) plan)))
           (fnn-out "~a" (fnn-core 'fn-bplc-runtime-line (fnn-bplc-model listeners)))
           (funcall begin grant socket)))))))))
   ;; Direct-index slot rotation avoids rebuilding/scanning the active roster.
   (let ((grant (aref (fnn-bpsb-slots bank) slot)))
    (when (and grant (fnn-bpsg-turn grant))
     (multiple-value-setq (turn-status turn-action) (funcall (fnn-bpsg-turn grant)))
     (when (eq turn-status :done)
      (let ((key (fnn-core 'fn-bpsg-key (fnn-bpsg-row grant)))
            (incoming (eq (fourth (fnn-bpsg-row grant)) :incoming)))
       (let* ((finish (fnn-bpsg-finish grant))
              (continued nil))
        ;; A terminal controller cannot publish twice while another dependency
        ;; still holds custody. Fragment rearm installs the next continuation.
        (setf (fnn-bpsg-turn grant) nil (fnn-bpsg-finish grant) nil)
        (setq continued (and finish (eq (funcall finish grant) :continue)))
        (unless continued
         (fnn-bp-session-close bank grant)
         (fnn-bp-session-release-context bank grant)))
       (when incoming
        (setf (fnn-bplc-model listeners)
              (fnn-core 'fn-bpsched-listener-step (fnn-bplc-model listeners)
                        (list :retained-closed key)))
        (when once (setq once-tail 8 phase 0)))))))
   (setq slot (fnn-core 'fn-bpsched-next-slot slot (length (fnn-bpsb-slots bank))))
   (funcall service (fnn-core 'fn-bpsched-service phase))
   (setq phase (fnn-core 'fn-bpsched-next phase))
   (when (and once-tail (plusp once-tail)) (decf once-tail))
   (when (and once accepted once-tail (zerop once-tail)
              (zerop (hash-table-count (fnn-bpsb-held bank)))
              (not (funcall pending))) (return))
   (setq work-credit (fnn-core 'fn-bpsched-work-credit turn-status turn-action
                              work-credit (length (fnn-bpsb-slots bank))))
   (sb-thread:thread-yield)
   (when (fnn-core 'fn-bpsched-idle-p work-credit) (fnn-bp-session-idle-wait)))))

(defun fnn-bp-session-idle-wait () (sleep 0.001))

(defun fnn-bp-session-start (bank host port params tag spool ready finish &optional supplied)
 "An outgoing context with a retained connect/handshake/session continuation."
 (let ((grant (or supplied (fnn-bp-session-acquire bank :outgoing))))
  (unless grant (return-from fnn-bp-session-start nil))
  (let ((phase :connect)
        (deadline (fnn-core 'fn-bpsched-deadline (fnn-tcl-now) (fnn-bpsb-grant bank))))
   (setf (fnn-bpsg-result grant) :uncertain
         (fnn-bpsg-finish grant)
         (lambda (job) (funcall finish job (fnn-bpsg-result job)))
         (fnn-bpsg-turn grant)
         (lambda ()
          (block turn
          (when (fnn-core 'fn-bpsched-timeout-p (fnn-tcl-now) deadline)
           (when (fnn-bpsg-conn grant)
            (setf (fnn-bpsg-result grant) (or (fnn-tclc-outcome (fnn-bpsg-conn grant)) :uncertain))
            (fnn-tcl-turn-lost (fnn-bpsg-conn grant))
            (fnn-tcl-turn (fnn-bpsg-conn grant)))
           (return-from turn :done))
          (case phase
           ((:connect :connecting)
            ;; Only the physical connect helper is transport-scoped.
            (handler-case
             (if (eq phase :connect)
              (multiple-value-bind (socket status) (fnn-peer-connect-start host port)
               (setf (fnn-bpsg-socket grant) socket)
               (setq phase (if (eq status :connected) :begin :connecting)) :work)
              (let ((status (fnn-connect-poll (fnn-bpsg-socket grant))))
               (if (eq status :wait) :wait (progn (setq phase :begin) :work))))
             ((or fnn-os-error fnn-peer-dial-error sb-bsd-sockets:socket-error) ()
              (setf (fnn-bpsg-result grant) (if (fnn-bpsg-socket grant) :uncertain :failed))
              :done)))
           (:begin
            (fnn-tcl-begin (fnn-socket-fd (fnn-bpsg-socket grant)) :active params tag spool
             :expect 0 :refuse-inbound t :on-ready ready
             :retain (lambda (conn) (setf (fnn-bpsg-conn grant) conn)))
            (setq phase :session) :work)
           (:session
            (let* ((*fnn-tcl-progress* nil) (conn (fnn-bpsg-conn grant)))
             (multiple-value-bind (result action) (fnn-tcl-turn conn)
              (when (eq result :done)
               (setf (fnn-bpsg-result grant) (or (fnn-tclc-outcome conn) :uncertain)))
              (values result action))))
           (otherwise (fnn-fault "BP retained connect phase unavailable"))))))
   grant)))

(defun fnn-bp-session-rearm (bank grant host port params tag spool ready finish)
 "Continue the same unfinished operation after affirmative physical close."
 (let ((conn (fnn-bpsg-conn grant)))
  (unless (and conn (eq (fnn-core 'fn-bpsg-release-ready
    (fnn-tclc-finished conn) (fnn-tclc-source-pending conn) (fnn-tclc-source-root conn)
    (fnn-tclc-source-token conn) (fnn-tclc-held conn)
    (fnn-tclc-tx-messages conn) (fnn-tclc-tx-data conn)) t))
   (fnn-fault "BP fragment operation cannot release its old context"))
  (fnn-bp-session-close bank grant)
  (setf (fnn-tclc-session conn) nil (fnn-tclc-carry conn) nil
        (fnn-tclc-pending conn) nil (fnn-tclc-on-ready conn) nil
        (fnn-bpsg-conn grant) nil)
  (fnn-bp-session-observe bank grant :rearm-socket)
  (setf (fnn-bpsg-close-attempted grant) nil)
  (fnn-bp-session-start bank host port params tag spool ready finish grant)))

(defun fnn-bp-session-send-effect (bank service effect grant expected)
 "Retained real base-job sender, including successive BP fragments."
 (let* ((route (second effect)) (key (fourth effect)) (wire (fifth effect))
        (attempt (fnn-core 'fn-bpnj-attempt-token (fnn-bps-state service) key))
        (params (fnn-tcl-params (fnn-bps-route-node route) expected
                  (fnn-bps-route-keepalive route) (fnn-bps-route-segment-mru route)
                  (fnn-bps-route-transfer-mru route)))
        (fragments nil) (index 1) (plan-refused nil))
  (labels ((complete (job outcome)
            (let ((conn (fnn-bpsg-conn job)))
             (when conn (fnn-tcl-summary conn))
             (setq outcome (if plan-refused :refused
                            (fnn-core 'fn-bpfs-fragment-outcome index outcome)))
             (cond
              ((and (eq outcome :accepted) fragments)
               (let ((fragment (pop fragments)))
                (incf index)
                (fnn-bp-session-rearm bank job (fnn-bps-route-host route) (fnn-bps-route-port route)
                 params "bp-service" (fnn-bps-root service)
                 (lambda (connection) (setf (fnn-tclc-pending connection) (cons "bp-service" fragment)))
                 #'complete)
                :continue))
              (t
               (setf (fnn-bps-transfer service) outcome)
               (let ((old-scope (fnn-bps-transfer-scope service)))
                (setf (fnn-bps-transfer-scope service) :connection)
                (unwind-protect
                 (fnn-bps-drive-effects service
                  (fnn-bps-foundation-step service (list :job-result key attempt outcome)))
                 (setf (fnn-bps-transfer-scope service) old-scope))))))))
   (fnn-bp-session-start bank (fnn-bps-route-host route) (fnn-bps-route-port route)
    params "bp-service" (fnn-bps-root service)
    (lambda (connection)
     (let* ((mtu (fnn-core 'fn-tcl-negotiated-transfer-mtu
                  (fnn-core 'fn-tcl-session-negotiated (fnn-tclc-session connection))))
            (plan (fnn-core 'fn-bpfs-plan wire mtu)))
      (case (first plan)
       (:whole (setf (fnn-tclc-pending connection) (cons "bp-service" wire)))
       (:fragments
        (setf (fnn-tclc-pending connection) (cons "bp-service" (second plan)))
        (setq fragments (cddr plan)))
       (otherwise (setq plan-refused t)))))
    #'complete grant))))

;;; Private operation materializes the exact received segment chain in bounded
;;; cursor turns. Its authority is the actual retained incoming grant, never a
;;; native fabricated SAMEPRS provider row. The publication callback remains
;;; the existing BP durable custody implementation.
(defstruct fnn-bpsrx key cursor buffer octet-buffer (offset 0) count connection
  materialize-end materialize-octets (phase :copy))
(defun fnn-bp-session-source-start (grant conn id chain count limit)
 (unless (eq conn (fnn-bpsg-conn grant)) (fnn-fault "BP received context mismatch"))
 (let ((plan (fnn-core 'fn-bpsrx-start (fnn-bpsg-row grant) id count limit chain)))
  (case (first plan)
   (:source-operation
    (let ((buffer (create-fn-octets$c)))
     ;; Already prepaid by the incoming session projection. Allocator/GC
     ;; latency remains unbounded. No read is issued until the exact source
     ;; cursor has affirmatively filled all COUNT cells.
     (fn-octets$c-reserve (third plan) buffer)
     (setf (svref buffer 1) (third plan))
     (list :source-yield
      (make-fnn-bpsrx :key (second plan) :count (third plan)
       :cursor (fourth plan) :connection conn :octet-buffer buffer :buffer (svref buffer 0)))))
   ((:refused :uncertain) plan)
   (otherwise (fnn-fault "BP received operation unavailable")))))
(defun fnn-bp-session-source-turn (grant conn job)
 (unless (and (typep job 'fnn-bpsrx) (eq conn (fnn-bpsrx-connection job))
              (eq conn (fnn-bpsg-conn grant)))
  (fnn-fault "BP received continuation context mismatch"))
 (unless (eq (fnn-core 'fn-bpsrx-authorizedp (fnn-bpsrx-key job)
                     (fnn-bpsg-row grant) (fnn-bpsrx-cursor job)) t)
  (return-from fnn-bp-session-source-turn '(:uncertain :session-incarnation)))
 (case (fnn-bpsrx-phase job)
  (:copy
   (let* ((answer (fnn-core 'fn-bpsrx-turn (fnn-bpsrx-key job) (fnn-bpsg-row grant)
                          (fnn-bpsrx-cursor job)))
          (word (first answer)) (bytes (third answer)))
    (setf (fnn-bpsrx-cursor job) (second answer))
    (when bytes
     (let ((vector (fnn-octets bytes)))
      (replace (fnn-bpsrx-buffer job) vector :start1 (fnn-bpsrx-offset job))
      (setf (fnn-bpsrx-offset job) (fnn-core 'fn-tsc-at 3 (second answer)))))
    (case word
     (:source-complete
      (setf (fnn-bpsrx-phase job) :convert
            (fnn-bpsrx-materialize-end job) (fnn-bpsrx-count job))
      (list :source-yield job))
     (:refused '(:refused :private-source-corrupt))
     (:uncertain '(:uncertain :session-incarnation))
     (:yield (list :source-yield job))
     (otherwise (fnn-fault "BP received cursor outcome unavailable")))))
  (:convert
   (if (plusp (fnn-bpsrx-materialize-end job))
    (let ((answer (fnn-core 'fn-tcim-turn (fnn-bpsrx-materialize-end job)
                           (fnn-bpsrx-materialize-octets job) (fnn-bpsrx-octet-buffer job))))
     (setf (fnn-bpsrx-materialize-end job) (first answer)
           (fnn-bpsrx-materialize-octets job) (second answer)))
    (setf (fnn-bpsrx-phase job) :publish))
   (list :source-yield job))
  (:publish
   ;; Consume publication exactly once, including throwing outcomes. The
   ;; native source escape fences/retains the job and END ACK on uncertainty.
   (setf (fnn-bpsrx-phase job) :publishing)
   (fnn-tcl-deliver-transfer conn (fnn-tclc-source-id conn)
                            (fnn-bpsrx-materialize-octets job)))
  (otherwise (fnn-fault "BP received publication cannot be retried"))))

(defun fnn-bp-session-retire-private-source (grant)
 (let* ((conn (fnn-bpsg-conn grant))
        (job (and conn (fnn-tclc-source-token conn))))
  (when (and (typep job 'fnn-bpsrx) (eq conn (fnn-bpsrx-connection job)))
   (let ((plan (fnn-core 'fn-bpsrx-abort-plan (fnn-bpsrx-key job)
                        (fnn-bpsg-row grant) (fnn-bpsrx-cursor job) (fnn-bpsrx-phase job))))
    (when (eq (first plan) :retire-private-source)
     ;; :publishing was installed before entering the external durable callback.
     ;; There is no background worker or surviving continuation in this private
     ;; operation. Clear its buffers/root and every future output alias before
     ;; release-context can issue its logical receipt. No held ACK is emitted.
     (setf (fnn-bpsrx-phase job) :retired (fnn-bpsrx-cursor job) nil
           (fnn-bpsrx-buffer job) nil (fnn-bpsrx-octet-buffer job) nil
           (fnn-bpsrx-materialize-octets job) nil (fnn-bpsrx-connection job) nil
           (fnn-tclc-source-pending conn) nil (fnn-tclc-source-root conn) nil
           (fnn-tclc-source-token conn) nil (fnn-tclc-source-held conn) nil
           (fnn-tclc-source-id conn) nil (fnn-tclc-source-count conn) nil (fnn-tclc-held conn) nil
           (fnn-tclc-source-more conn) nil
           (fnn-tclc-tx-messages conn) nil (fnn-tclc-tx-data conn) nil
           (fnn-tclc-pending conn) nil (fnn-tclc-on-ready conn) nil
           (fnn-tclc-input-buffer conn) nil (fnn-tclc-input-vector conn) nil
           (fnn-tclc-input-octets conn) nil (fnn-tclc-input-materialize-end conn) nil
           (fnn-tclc-finished conn) t (fnn-tclc-fenced conn) t
           (fnn-tclc-outcome conn) :uncertain)
     t)))))
