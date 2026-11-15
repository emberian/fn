;;; Actual raw-DEFLATE dispatcher -> public input receipt -> replay consumer.
;;; Requires qualified tests/input-prefix-unit, node host books, host/adapter.
;;; The retained compressed seed is an explicit fixture effect; allocation and
;;; decoding use the selected real C primitive. This does not test an upgrade
;;; reply, authentication, socket framing, TLS stacking or peer cryptography.
(in-package "ACL2")
(defun fn2-native-compress-input-prefix-control (library)
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
                 :ops ops :trace (make-array 8 :initial-element nil)))
          (before (copy-seq (fn2-nhost-bytes host))))
    (dotimes (i (length ops)) (setf (aref ops i) (make-fn2-nop)))
    (setf (aref ops slot) (make-fn2-nop :state +fn2-n-waiting+ :gen generation
                           :kind kind :cap cap :nonce nonce :address address :len length))
    (unwind-protect
     (progn
      (multiple-value-bind (code transport)
          (fn2-compress-transport-start cap nonce slot generation 8 8 4 7 16 128
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
       (assert (and (eq code :ok) (= copied 8) (= fed 0)))
       (setf (fn2-native-compress-transport compression) transport))
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
      t)
     (fn2-native-compress-close host compression nil cap nonce))))))
