;;; Test-only real-fd worker → executor return → post → ACL2 replay bridge.
;;; Load after the qualified host boundary and native-fence-correspondence.
(in-package "ACL2")

(defun fn2-native-fence-read-byte (device)
  (let* ((bytes (make-array 1 :element-type '(unsigned-byte 8) :initial-element 0))
         (job (make-fn2-device-job :kind :read :bytes bytes :address 0 :length 1 :offset 0)))
    (fn2-device-perform device job)
    (assert (= (fn2-device-job-result job) 1))
    (assert (zerop (fn2-device-job-errno job)))
    (aref bytes 0)))

(defun fn2-native-fence-return-control ()
  (let* ((path (format nil "build/fence-return-~d-~d.img" (get-universal-time) (random 1000000)))
         (original-boundary (symbol-function 'fn2-n-boundary))
         (core (create-fn2-core)) (sim (create-fn2-sim)) (own (create-fn2-own))
         (device nil) (fd -1) (host nil) (phase :write) (fence-op nil)
         (worker-cut nil) (executor-cut nil) (writes nil)
         (initial-byte nil) (written-byte nil) (fenced-byte nil)
         (ready (sb-thread:make-semaphore :count 0)))
    (unwind-protect
      (progn
        (multiple-value-bind (ok op c s o) (fn2-native-cut-fixture nil core sim own)
          (declare (ignore op c s o)) (assert ok))
        (multiple-value-bind (opened size backend) (fn2-device-open path :create-size 1048576)
          (setf fd opened)
          ;; The relation covers offset zero's initial and written bytes, not
          ;; an unobserved claim about every byte of the new file.
          (setf initial-byte (fn2-native-fence-read-byte (%make-fn2-device :fd fd)))
          (assert (zerop initial-byte))
          (let* ((n (fn2-profile-o *fn2-profile-tiny*))
                 (ops (make-array n)))
            (dotimes (i n) (setf (aref ops i) (make-fn2-nop)))
            (setf host (make-fn2-nhost :core core :ops ops
                        :bytes (svref (svref core *fn2-core-pool*) *fn2-pool-datai*)
                        :completions (make-array (* 2 n) :initial-element 0)
                        :trace (make-array 16 :initial-element nil))))
          (setf (symbol-function 'fn2-n-boundary)
            (lambda (h label)
              (assert (eq h host))
              (when (and (eq phase :fence) (equal label "device-syscall-return"))
                ;; This actual worker cut precedes publication to DONE and
                ;; precedes the executor's four-field observation event.
                (assert (zerop (fn2-nhost-pending host)))
                (assert (= (fn2-nop-state (aref (fn2-nhost-ops host) fence-op)) +fn2-n-waiting+))
                (setf fenced-byte (fn2-native-fence-read-byte device))
                (assert (= fenced-byte 17))
                (setf worker-cut (nthcdr (length writes) (fn2-n-trace-list host)))
                (assert (equal (mapcar #'car worker-cut) '(:take :ack))))
              (when (and (eq phase :fence) (equal label "device-return"))
                (assert worker-cut)
                (assert (zerop (fn2-nhost-pending host)))
                (assert (= (fn2-nop-state (aref (fn2-nhost-ops host) fence-op)) +fn2-n-waiting+))
                (assert (fn2-native-fence-unposted fence-op core))
                (setf executor-cut (nthcdr (length writes) (fn2-n-trace-list host)))
                (assert (equal (mapcar #'car executor-cut) '(:take :ack :physical-return))))
              (funcall original-boundary h label)))
          (setf device
            (fn2-device-start fd size backend (length (fn2-nhost-ops host))
              (lambda () (sb-thread:signal-semaphore ready))
              (lambda (label) (fn2-n-boundary host label))))
          (setf (fn2-nhost-storage host) device)
          ;; Both operations are issued by ACL2 and copied/acknowledged by the
          ;; actual native adapter. The worker alone performs their syscalls.
          (fn2-n-take host)
          (assert (sb-thread:wait-on-semaphore ready :timeout 5))
          (fn2-n-storage-completions host)
          (fn2-n-post-completions host)
          (setf writes (fn2-n-trace-list host)
                written-byte (fn2-native-fence-read-byte device))
          (assert (= written-byte 17))
          (multiple-value-bind (code op gen c) (fn2-issue-fence 1 0 1 0 core)
            (declare (ignore gen c)) (assert (eq code :ok)) (setf fence-op op))
          (setf phase :fence)
          (fn2-n-take host)
          (assert (sb-thread:wait-on-semaphore ready :timeout 5))
          (fn2-n-storage-completions host)
          (assert executor-cut)
          (assert (= (fn2-nhost-pending host) 1))
          (fn2-n-post-completions host)
          (let* ((trace (fn2-n-trace-list host))
                 (fence (nthcdr (length writes) trace))
                 (native (nth 2 fence))
                 (changed (copy-tree fence)))
            (assert (fn2-native-fence-replay-check writes fence))
            (assert (fn2-native-fence-model-check native t))
            (assert (fn2-native-fence-model-check native nil))
            ;; Strict presence and actual syscall/result correlation matter.
            (assert (not (fn2-native-fence-replay-check writes
                           (append (take 2 fence) (nthcdr 3 fence)))))
            (assert (not (fn2-native-fence-replay-check writes
                           (append (take 3 fence) (nthcdr 2 fence)))))
            (setf (nth 2 (nth 2 changed)) -1)
            (assert (not (fn2-native-fence-replay-check writes changed)))
            (assert (not (fn2-native-fence-model-check (nth 2 changed) nil)))
            (setf changed (copy-tree fence))
            (incf (nth 1 (nth 1 (nth 2 changed))))
            (assert (not (fn2-native-fence-replay-check writes changed)))
            (setf changed (copy-tree fence))
            (setf (nth 5 (nth 3 changed)) *fn2-outcome-failed*)
            (assert (not (fn2-native-fence-replay-check writes changed)))
            (with-open-file (out (concatenate 'string path ".trace") :direction :output :if-exists :error)
              (write (list :write writes :fence fence
                           :footprint (list :visibility :os-visible :offset 0 :initial initial-byte
                                            :after-write written-byte :after-fence fenced-byte)
                           :worker-cut (list :label "device-syscall-return"
                                             :phase :physical-return-unpublished :trace worker-cut)
                           :executor-cut (list :label "device-return"
                                               :phase :raw-return-unposted :trace executor-cut)
                           :persistence-assumption 'fn2-a-fence-persists
                           :physical-subject 'fn2-device-perform
                           :model-subject 'fn2-sim-advance
                           :model-physical-subject 'fn2-sim-native-stage)
                     :stream out :readably t))
            (format t "NATIVE FENCE RETURN PASS image=~a trace=~a.trace: actual issued write17/fence, worker and executor unposted cuts, four-field replay/model projection and five mutations~%" path path))
          t))
      (setf (symbol-function 'fn2-n-boundary) original-boundary)
      (if device
          (progn
            (fn2-device-stop device)
            (assert (not (eq (sb-thread:join-thread (fn2-device-thread device)
                               :timeout 5 :default :timeout) :timeout))))
        (when (>= fd 0) (fn2-native-close fd))))))
