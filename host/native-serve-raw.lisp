;;; Image startup and the common listener lifecycle. Seed fixtures load separately.
(in-package "ACL2")

(defun fn2-nserve-dotted (text)
  "A dotted IPv4 quad as a u32, or nil."
  (let ((parts (ignore-errors
                (loop with start = 0
                      for dot = (position #\. text :start start)
                      collect (parse-integer text :start start :end dot)
                      while dot do (setf start (1+ dot))))))
    (and (= (length parts) 4) (every (lambda (p) (<= 0 p 255)) parts)
         (reduce (lambda (a p) (+ (* a 256) p)) parts :initial-value 0))))

(defun fn2-nserve-groups (text)
  "Trusted startup group names separated by newlines or commas, numbered from 1."
  (loop with start = 0 and len = (length text) and id = 0 and acc = nil
        while (<= start len)
        for end = (or (position-if (lambda (c) (or (char= c #\Newline) (char= c #\,)))
                                   text :start start)
                      len)
        for name = (string-trim '(#\Space #\Tab #\Return) (subseq text start end))
        when (plusp (length name))
          do (incf id) (push (cons name id) acc)
        do (setf start (1+ end))
        finally (return (nreverse acc))))

(defvar *fn2-nserve-base* nil
  "The launcher supplies its served profile before applying environment keys.")

(defun fn2-nserve-profile ()
  "The launcher's served profile, listener and owner from the environment.
FN2_OWNER_UID names the local control socket's owner (:owner-uid, E's carrier L); the
core rejects a present value that is not a u32; it never falls back to uid 0."
  (let* ((profile (or *fn2-nserve-base* (error "fn2 native: launcher profile absent")))
         (port (sb-ext:posix-getenv "FN2_LISTENER_PORT"))
         (address (sb-ext:posix-getenv "FN2_LISTENER_ADDRESS"))
         (path (sb-ext:posix-getenv "FN2_LISTENER_PATH"))
         (owner (sb-ext:posix-getenv "FN2_OWNER_UID"))
         (groups (sb-ext:posix-getenv "FN2_GROUPS"))
         (storage-fault-model (sb-ext:posix-getenv "FN2_STORAGE_FAULT_MODEL"))
         (peering (sb-ext:posix-getenv "FN2_PEERING")))
    (when storage-fault-model
      (setf profile (put-assoc-equal :storage-fault-model storage-fault-model profile)))
    (when owner
      (setf profile (put-assoc-equal :owner-uid (or (ignore-errors (parse-integer owner)) -1) profile)))
    (when port
      (setf profile (put-assoc-equal :listener-port (or (ignore-errors (parse-integer port)) -1) profile)))
    (when address
      (setf profile (put-assoc-equal :listener-address (or (fn2-nserve-dotted address) -1) profile)))
    (when path
      (setf profile (put-assoc-equal :listener-path path profile)))
    (when groups
      (setf profile (put-assoc-equal :groups (fn2-nserve-groups groups) profile)))
    (when peering
      (setf profile (put-assoc-equal :peering-interim
                                     (cond ((or (equal peering "1") (equal peering "true")) t)
                                           ((or (equal peering "0") (equal peering "false")) nil)
                                           (t :invalid))
                                     profile)))
    profile))

; The ready, refusal and stop lines each start a line (fn1's harness matches
; `LISTENING <port>` at a line's start; the raw REPL's prompt precedes this call).
(defun fn2-nserve-kill-at (text)
  "Bounded test instrumentation; zero disables process-death injection."
  (if (null text) 0
    (and (<= 1 (length text) 20)
         (every (lambda (c) (digit-char-p c 10)) text)
         (let ((n (car (fn2-n-control-numbers text 1))))
           (and (<= n most-positive-fixnum) n)))))

(defun fn2-nserve-main ()
  (let* ((profile (fn2-nserve-profile))
         (image (sb-ext:posix-getenv "FN2_IMAGE"))
         (initialize (equal (sb-ext:posix-getenv "FN2_IMAGE_MODE") "init"))
         (kill-at (fn2-nserve-kill-at (sb-ext:posix-getenv "FN2_KILL_AT")))
         (image-bytes (and initialize (ignore-errors (parse-integer (or (sb-ext:posix-getenv "FN2_IMAGE_BYTES") "")))))
         (capacity (or (ignore-errors (parse-integer (or (sb-ext:posix-getenv "FN2_ENVELOPE_TRACE") "0"))) 0)))
    (format t "~%NODE-PID ~d~%" (%fn2-native-getpid))
    (finish-output)
    (unless kill-at
      (format t "REFUSED kill-at~%") (finish-output)
      (return-from fn2-nserve-main 2))
    (unless image
      (format t "REFUSED image-missing~%") (finish-output)
      (return-from fn2-nserve-main 2))
    (when (and initialize (not image-bytes))
      (format t "REFUSED image-size~%") (finish-output)
      (return-from fn2-nserve-main 2))
    (multiple-value-bind (bind address port) (fn2-host-listener-bind profile)
      (declare (ignore address port))
      (unless (eq bind :ok)
        (format t "~%REFUSED ~(~a~)~%" bind) (finish-output)
        (return-from fn2-nserve-main 2)))
    (unless (fn2-core-profilep (if image (fn2-image-profile profile) profile))
      (format t "~%REFUSED profile~%") (finish-output)
      (return-from fn2-nserve-main 2))
    (format t "STORAGE-FAULT-MODEL ~a~%" (fn2-profile-storage-fault-model profile))
    (finish-output)
    (let ((host (handler-case
                 (fn2-n-make-host profile :trace-capacity capacity :kill-at kill-at
                                  :device-path image :create-size image-bytes)
                 (error (condition)
                   (format t "~%REFUSED ~a~%" condition) (finish-output)
                   (return-from fn2-nserve-main 2)))))
      (when initialize
        (fn2-n-destroy host)
        (format t "~%INITIALIZED~%") (finish-output)
        (return-from fn2-nserve-main 0))
      (fn2-nserve-run-host host))))

(defun fn2-nserve-run-host (host)
  "Announce the initialized listener, serve, report the stop, and close I/O."
  (when (plusp (fn2-nhost-kill-at host))
    (format t "~%BOUNDARY-READY ~d~%" (fn2-nhost-boundaries host)))
  (format t "~%LISTENING ~d~%" (fn2-nhost-listen-port host))
  (when (fn2-nhost-local-path host)
    (format t "LISTENING-LOCAL ~a~%" (fn2-nhost-local-path host)))
  (finish-output)
  (unwind-protect
       (let ((reason (fn2-n-run host)))
         (format t "STOPPED ~d~%" reason)
         (multiple-value-bind (kind detail) (fn2-host-stop-details (fn2-nhost-core host))
           (format t "STOP-DETAIL ~d ~d~%" kind detail))
         (finish-output)
         0)
    (fn2-n-destroy host)))
