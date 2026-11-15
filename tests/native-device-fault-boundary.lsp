;;; Run through tools/acl2 in a qualified current closure; no image/socket.
(in-package "ACL2")
(include-book "books/host-boundary" :uncertified-okp nil)
:q
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(load "tests/fixtures/device-faults/control.lisp")
(let ((host nil))
  (fn2-device-fault-controls
   (lambda (stage job outcome reason count)
     (case stage
       (:prepare
        (let* ((kind (ecase (fn2-device-job-kind job)
                       (:write *fn2-action-write*) (:fence *fn2-action-fence*)))
               (device (%make-fn2-device :done (make-array 1 :initial-element nil)))
               (op (make-fn2-nop :state +fn2-n-waiting+ :gen (fn2-device-job-gen job)
                     :kind kind :len (fn2-device-job-length job))))
          (setf host (make-fn2-nhost :storage device :storage-pending 1
                       :ops (vector op) :completions (make-array 1 :initial-element nil)))))
       (:withheld
        ;; Physical success must not turn into a synthetic terminal result.
        (fn2-n-storage-completions host)
        (assert (= (fn2-nhost-storage-pending host) 1))
        (assert (zerop (fn2-nhost-pending host)))
        (assert (= (fn2-nop-state (aref (fn2-nhost-ops host) 0)) +fn2-n-waiting+)))
       (:deliver
        (let ((device (fn2-nhost-storage host)))
          (setf (aref (fn2-device-done device) 0) job (fn2-device-completed device) 1))
        (fn2-n-storage-completions host)
        (let ((op (aref (fn2-nhost-ops host) 0)))
          (assert (= (fn2-nop-outcome op)
                     (ecase outcome (:done *fn2-outcome-done*) (:failed *fn2-outcome-failed*))))
          (assert (= (fn2-nop-reason op)
                     (ecase reason (:none *fn2-reason-none*) (:io *fn2-reason-io*)
                       (:no-space *fn2-reason-no-space*) (:uncertain *fn2-reason-uncertain*))))
          (assert (= (fn2-nop-count op) count))
          (assert (= (fn2-nop-state op) +fn2-n-completed+)))
        (assert (zerop (fn2-nhost-storage-pending host)))
        (assert (= (fn2-nhost-pending host) 1))
        ;; An empty second poll cannot duplicate or erase the terminal.
        (fn2-n-storage-completions host)
        (assert (= (fn2-nhost-pending host) 1)))
       (otherwise (error "Unknown observer stage ~s" stage))))))
(format t "QUALIFIED DEVICE BOUNDARY PASS~%")
(sb-ext:exit :code 0)
