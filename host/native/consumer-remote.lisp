;;; Separate TLS FNCR ingress. No FNCT request is forwarded to owner control.
;;; Listener/bootstrap wiring waits for actual admission/custody installation.
(in-package "ACL2")

(defun fnn-remote-read-exact (channel count seconds)
  "Move exactly COUNT plaintext octets under one TLS I/O deadline.
The caller holds the genuine allocation grant for this exact extent."
  (let ((result (fnn-make-octets count)) (offset 0)
        (deadline (+ (fnn-now) (* seconds internal-time-units-per-second))))
    (loop while (< offset count) do
      (let ((remaining (fnn-seconds-to-deadline deadline)))
        (when (<= remaining 0) (return-from fnn-remote-read-exact :timeout))
        (let ((chunk (fnn-tls-read channel remaining
                                  (min +fnn-max-read+ (- count offset)))))
          (when (eq chunk :timeout) (return-from fnn-remote-read-exact :timeout))
          (when (zerop (length chunk)) (return-from fnn-remote-read-exact :closed))
          (replace result chunk :start1 offset)
          (incf offset (length chunk)))))
    result))

(defun fnn-remote-receive (channel g seconds run-with-admission)
  "Read one FNCR frame over an established TLS channel.
RUN-WITH-ADMISSION is the common native admission entry. It must execute the
supplied body inside an installed typed operation turn, with the borrowed
prefix retained in its source/custody. There is no Boolean grant or default
entry. A refused entry consumes no suffix. The current installer has no such
operation yet; this transport is not activated from bootstrap."
  (unless (and (fnn-tls-channel-p channel) (fnn-tls-channel-pointer channel))
    (return-from fnn-remote-receive '(:refused :protected-channel)))
  (let ((header-count (fnn-core 'fn-cre-header-octets)))
    (let ((header (funcall run-with-admission :remote-header header-count nil
                    (lambda () (fnn-remote-read-exact channel header-count seconds)))))
      (unless (vectorp header) (return-from fnn-remote-receive (fnn-core 'fn-cre-receive-failure header)))
      (let ((plan (fnn-core 'fn-cre-header-plan (fnn-octet-list header) t g)))
        (unless (eq (car plan) :receive) (return-from fnn-remote-receive plan))
        (funcall run-with-admission :remote-frame (second plan) header
         (lambda ()
          (let ((suffix (fnn-remote-read-exact channel (second plan) seconds)))
           (unless (vectorp suffix) (return-from fnn-remote-receive (fnn-core 'fn-cre-receive-failure suffix)))
           ;; Each client owns this concrete buffer across decoder yields.
           ;; Its exact allocation and both retained I/O extents are inside
           ;; the installed operation entry, never supplied Boolean funding.
           (let* ((buffer (create-fn-octets$c))
                  (n (+ (length header) (length suffix))))
            (fn-octets$c-reserve n buffer)
            (replace (the fnn-octets (svref buffer 0)) header)
            (replace (the fnn-octets (svref buffer 0)) suffix :start1 (length header))
            (setf (svref buffer 1) n)
            (list :remote-frame buffer (fnn-core 'fn-crb-open g buffer))))))))))

(defun fnn-remote-ingress (service channel request g)
  "Actual current-account ingress under the same serialized owner span.
No cached authentication result is used by a WAIT wake."
  (fnn-owner-serialized service nil
    (lambda () (fnn-owner-core 'fn-owner-remote-ingress request
      (and (fnn-tls-channel-p channel) (fnn-tls-channel-pointer channel) t) g))))

(defun fnn-remote-installed-entry (service kind count prefix body)
  "Read the genuine current common source under owner then extent.
The current installer has no positive native remote entry. COUNT, PREFIX and
BODY cannot grant authority, and BODY is never invoked while unavailable."
  (declare (ignore count prefix body))
  (fnn-owner-serialized service nil
   (lambda ()
    (sb-thread:with-mutex (*fnn-extent-lock*)
     (fnn-owner-core 'fn-owner-remote-operation-preflight kind
                     (fnn-live-page-read-pool))))))

(defun fnn-remote-receive-installed (service channel g seconds)
  "The concrete caller of the installed-source path, before allocation/I/O."
  (fnn-remote-receive channel g seconds
    (lambda (kind count prefix body)
     (fnn-remote-installed-entry service kind count prefix body))))
