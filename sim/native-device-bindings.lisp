; Scalar binding to the same normalizer used by fn2-host-result.
; Actual logical loan comparison and replay live in native-device-envelope.
(in-package "ACL2")
(include-book "native-device-effects")
(include-book "../books/device-boundary")
(include-book "../books/terminal-values")

(defun fn2-nde-kind (kind)
 (cond ((equal kind *fn2-action-read*) :read)
       ((equal kind *fn2-action-write*) :write)
       ((equal kind *fn2-action-fence*) :fence)
       (t nil)))
(defun fn2-nde-job (slot gen records)
 (if (atom records) nil
  (let ((r (car records)))
   (if (and (member-eq (car r) '(:submit :direct))
            (equal slot (nth 1 (nth 2 r))) (equal gen (nth 2 (nth 2 r))))
       r (fn2-nde-job slot gen (cdr records))))))
(defun fn2-nde-return (id records)
 (if (atom records) nil
  (if (and (eq (caar records) :return) (equal (nth 1 (car records)) id))
      (car records) (fn2-nde-return id (cdr records)))))
(defun fn2-nde-submitted-ids (records)
 (if (atom records) nil
  (if (member-eq (caar records) '(:submit :direct))
      (cons (nth 1 (car records)) (fn2-nde-submitted-ids (cdr records)))
    (fn2-nde-submitted-ids (cdr records)))))
(defun fn2-nde-take (slot gen trace)
 (if (atom trace) nil
  (if (and (eq (caar trace) :take) (equal (nth 1 (car trace)) slot)
           (equal (nth 2 (car trace)) gen))
      (car trace) (fn2-nde-take slot gen (cdr trace)))))
(defun fn2-nde-take-descriptor-p (take descriptor backend)
 (and (natp (nth 0 descriptor))
      (fn2-nde-descriptorp descriptor (nth 0 descriptor))
      (eq (nth 3 descriptor) (fn2-nde-kind (nth 3 take)))
      ; Tokens attest object identity at the selected host submission boundary.
      ; Their equality is not a proof of general host memory noninterference.
      (posp (nth 9 descriptor)) (equal (nth 8 descriptor) (nth 9 descriptor))
      (equal (nth 1 descriptor) (nth 1 take))
      (equal (nth 2 descriptor) (nth 2 take))
      (equal (nth 4 descriptor) (nth 10 take))
      (equal (nth 5 descriptor) (nth 9 take))
      (eq (fn2-device-request (fn2-nde-kind (nth 3 take)) (nth 11 take) backend) :perform)))
(defun fn2-nde-post-normalized-p (take post code count read-bytes)
 (declare (xargs :verify-guards nil))
 (mv-let (outcome reason n aux0 aux1)
  (fn2-sim-terminal-values (nth 3 take) code count 0 (nth 9 take) nil nil)
  (and (true-listp post) (equal (len post) 13) (eq (car post) :post)
       (equal (nth 10 post) 0) (equal (nth 11 post) '(0 0 0 0 0))
       (equal (nth 1 post) 0)
       (equal (nth 4 post) (fn2-terminal-event (nth 3 take)))
       (equal (nth 5 post) outcome) (equal (nth 6 post) reason)
       (equal (nth 7 post) n) (equal (nth 8 post) aux0) (equal (nth 9 post) aux1)
       (equal (nth 12 post) (if (eq (fn2-nde-kind (nth 3 take)) :read) read-bytes nil)))))
; Contextual hook: the actual envelope step has already validated the event.
; Unknown/non-device takes return T here, not a standalone trace verdict.
(defun fn2-nde-post-p (post trace records backend)
 (declare (xargs :verify-guards nil))
 (let* ((take (fn2-nde-take (nth 2 post) (nth 3 post) trace))
        (kind (fn2-nde-kind (nth 3 take))))
  (if (not kind) t
   (let* ((job (fn2-nde-job (nth 2 post) (nth 3 post) records))
          (returned (and job (fn2-nde-return (nth 1 job) records))))
    (if job
        (and returned
         (mv-let (code count) (fn2-device-io-observation (nth 2 returned) (nth 3 returned))
          (fn2-nde-post-normalized-p take post code count (nth 4 returned))))
      ; The selected file backend refuses FUA before queueing. Never use a
      ; failed ordinary Write as an excuse for missing physical evidence.
      (and (member-eq backend '(:fdatasync :fullfsync))
           (eq (fn2-device-request kind (nth 11 take) backend) :unsupported)
           (fn2-nde-post-normalized-p take post :unsupported 0 nil)))))))


; The actual consumer supplies these values from fn2-host-op-span, never from
; host arithmetic. The scalar relation has no independent authorization claim.
(defun fn2-nde-loan-span-p (descriptor code address length)
 (and (eq code :ok) (equal (nth 7 descriptor) address)
      (equal (nth 5 descriptor) length)
      (posp (nth 9 descriptor)) (equal (nth 8 descriptor) (nth 9 descriptor))))
