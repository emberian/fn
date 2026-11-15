;;; Actual raw-DEFLATE dispatcher -> public input receipt -> replay consumer.
;;; Requires qualified tests/input-prefix-unit, node host books, host/adapter.
;;; The retained compressed seed is an explicit fixture effect; allocation and
;;; decoding use the selected real C primitive. SOCKETP additionally exercises
;;; a private nonblocking socketpair and actual EAGAIN/rearm/fill observations.
;;; This does not test an upgrade
;;; reply, authentication, socket framing, TLS stacking or peer cryptography.
(in-package "ACL2")
(defun fn2-native-compress-input-prefix-control (library &optional socketp)
 (sb-alien:load-shared-object library)
 (multiple-value-bind (ready slot generation taken caps core)
     (fn2-input-prefix-fixture (fn2-n-live-core))
  (declare (ignore taken caps))
  (assert (and ready (fn2-core-wfp core)))
  (multiple-value-bind (authorized kind cap nonce address length)
      (fn2-host-active-op slot generation core)
   (assert (and (eq authorized :ok) (= kind *fn2-action-receive*) (= length 4)))
   (let* ((ops (make-array (fn2-profile-o *fn2-profile-tiny*)))
          (compression (make-fn2-native-compress
           :seed (make-array 8 :element-type '(unsigned-byte 8)
                   :initial-contents '(114 115 7 0 0 0 255 255))
           :input (make-array 4 :element-type '(unsigned-byte 8) :initial-element 0)
           :output (make-array 7 :element-type '(unsigned-byte 8) :initial-element 0)))
          (native-cap (make-fn2-ncap :fd -1 :nonce nonce :compress compression))
          (host (make-fn2-nhost :core core
                 :bytes (svref (svref core *fn2-core-pool*) *fn2-pool-datai*)
                 :ops ops :trace (make-array 8 :initial-element nil)
                 :completions (make-array 16 :initial-element 0)))
          (before (copy-seq (fn2-nhost-bytes host)))
          (peer -1))
    (dotimes (i (length ops)) (setf (aref ops i) (make-fn2-nop)))
    (setf (aref ops slot) (make-fn2-nop :state +fn2-n-waiting+ :gen generation
                           :kind kind :cap cap :nonce nonce :address address :len length))
    (unwind-protect
     (progn
      (when socketp
       (sb-alien:with-alien ((pair (array sb-alien:int 2)))
        (fn2-native-require-call :compress-fixture-socketpair
          (%fn2-native-socketpair 1 1 0 (sb-alien:alien-sap pair)))
        (setf (fn2-ncap-fd native-cap) (sb-alien:deref pair 0)
              peer (sb-alien:deref pair 1)))
       (multiple-value-call #'fn2-native-required
         (fn2-native-configure-socket (fn2-ncap-fd native-cap)) :compress-fixture-reader)
       (multiple-value-call #'fn2-native-required
         (fn2-native-configure-socket peer) :compress-fixture-writer))
      (multiple-value-bind (code transport)
          (fn2-compress-transport-start cap nonce slot generation (if socketp 0 8) 8 4 7 16 128
                                       (fn2-native-compress-transport compression))
       (assert (eq code :ok))
       (setf (fn2-native-compress-transport compression) transport))
      ;; The declared seed effect is copied in two selected quantum-four turns.
      ;; No host-side cursor or codec decision selects the next lifecycle step.
      (loop repeat 4
       do (multiple-value-bind (status action offset count serial transport)
              (fn2-compress-transport-next 0 0 (fn2-native-compress-transport compression))
           (declare (ignore offset))
           (setf (fn2-native-compress-transport compression) transport)
           (if (eq status :done)
               (return)
             (progn
              (assert (eq status :act))
              (let ((raw (case action
                          (8 (sb-sys:sap-int (fn2-deflate-%new)))
                          (1 count)
                          (otherwise (error "Unexpected fixture lifecycle action ~S" action)))))
               (multiple-value-bind (observed kick updated)
                   (fn2-compress-transport-observe-lifecycle cap nonce slot generation serial raw 0 0 transport)
                (declare (ignore kick)) (assert (eq observed :ok))
                (setf (fn2-native-compress-transport compression) updated)))))))
      (multiple-value-bind (code copied fed il io ol oo transport)
          (fn2-compress-transport-handoff cap nonce slot generation (fn2-native-compress-transport compression))
       (declare (ignore il io ol oo))
       (assert (and (eq code :ok) (= copied (if socketp 0 8)) (= fed 0)))
       (setf (fn2-native-compress-transport compression) transport))
      (when socketp
       ;; Empty decode requests input; the completed empty recv is observed as
       ;; its exact signed EAGAIN packet, not retained as a TLS child epoch.
       (dotimes (i 2)
        (declare (ignore i))
        (multiple-value-bind (status count)
            (fn2-native-compress-record-step host slot compression native-cap)
         (assert (and (eq status :progress) (= count 0)))))
       (let* ((transport (fn2-native-compress-transport compression))
              (blocked-serial (fn2-compress-transport-serial 0 transport))
              (compressed (fn2-native-compress-seed compression)))
        (assert (and (= (fn2-compress-transport-pending 0 transport) 0)
                     (= (fn2-compress-transport-raw-negative 0 transport) 1)
                     (member (fn2-compress-transport-raw-errno 0 transport) '(11 35))
                     (= (fn2-compress-operation-sink-progress 0 (fn2-native-compress-op-record (aref ops slot))) 0)
                     (null (fn2-n-trace-list host))))
        (sb-sys:with-pinned-objects (compressed)
         (multiple-value-bind (sent errno)
             (fn2-native-send peer (sb-sys:vector-sap compressed) 8)
          (assert (and (= sent 8) (= errno 0)))))
        (multiple-value-bind (status count)
            (fn2-native-compress-record-step host slot compression native-cap)
         (assert (and (eq status :progress) (= count 0)
                      (= (fn2-compress-transport-serial 0 (fn2-native-compress-transport compression))
                         (+ 1 blocked-serial))
                      (= (fn2-compress-transport-input-length 0 (fn2-native-compress-transport compression)) 4))))))
      ;; This is the real upper host selector, C decoder, observer and emitter.
      (multiple-value-bind (status count)
          (fn2-native-compress-record-step host slot compression native-cap)
       (assert (and (eq status :progress) (= count 0))))
      (let* ((trace (fn2-n-trace-list host)) (event (car trace))
             (after (fn2-nhost-bytes host)))
       (assert (and (= (length trace) 1)
                    (equal event (list :input-prefix slot generation 0 2 '(70 71)))))
       (assert (equalp after (concatenate '(simple-array (unsigned-byte 8) (*))
                              (subseq before 0 address) #(70 71) (subseq before (+ address 2)))))
       (assert (fn2-input-prefix-replay-control :ordinary event))
       (assert (fn2-input-prefix-replay-control :deferred event))
       (assert (fn2-input-prefix-replay-control :duplicate event))
       (assert (fn2-input-prefix-replay-control :after-close-ack event)))
      ;; Drive the actual adapter completion and core post, not only the
      ;; prefix projector. A partial Receive is DONE/count2 in the real ABI.
      (fn2-n-compress-ready host slot native-cap)
      (let ((op (aref ops slot)))
       (assert (and (= (fn2-nop-state op) +fn2-n-completed+)
                    (= (fn2-nop-outcome op) *fn2-outcome-done*)
                    (= (fn2-nop-reason op) *fn2-reason-none*)
                    (= (fn2-nop-count op) 2)
                    (= (fn2-ncap-rx native-cap) 2)
                    (= (fn2-nhost-pending host) 1))))
      (fn2-n-post-completions host)
      (let ((trace (fn2-n-trace-list host)))
       (assert (and (= (length trace) 2) (= (fn2-nhost-pending host) 0)
                    (equal (second trace)
                      (list :post 0 slot generation *fn2-event-receive-result*
                        *fn2-outcome-done* *fn2-reason-none* 2 0 0
                        *fn2-peer-family-none* '(0 0 0 0 0) '(70 71))))))
      t)
     (unwind-protect
       (fn2-native-compress-close host compression nil cap nonce)
      (when (>= (fn2-ncap-fd native-cap) 0) (fn2-native-close (fn2-ncap-fd native-cap)))
      (when (>= peer 0) (fn2-native-close peer))))))))
