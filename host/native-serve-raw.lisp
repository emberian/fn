;;; The raw half of tests/native-serve.lsp: the served core on a configured listener.
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
  "The served profile before the environment's keys; nil names the surface sessions'.
A driver that serves another profile over the same seeded store (tests/native-consumer.lsp)
sets it before fn2-nserve-main.")

(defun fn2-nserve-profile ()
  "The served profile, the listener and the owner from the environment (absent: the
profile's own). By default the surface sessions' (tests/seeded-store.lsp): the cursor's
profile less its posting, so the node serves reading over the store it seeds.
FN2_OWNER_UID names the local control socket's owner (:owner-uid, E's carrier L); the
core rejects a present value that is not a u32; it never falls back to uid 0."
  (let* ((profile (or *fn2-nserve-base* *fn2-ss-profile*))
         (port (sb-ext:posix-getenv "FN2_LISTENER_PORT"))
         (address (sb-ext:posix-getenv "FN2_LISTENER_ADDRESS"))
         (path (sb-ext:posix-getenv "FN2_LISTENER_PATH"))
         (owner (sb-ext:posix-getenv "FN2_OWNER_UID"))
         (groups (sb-ext:posix-getenv "FN2_GROUPS"))
         (peering (sb-ext:posix-getenv "FN2_PEERING")))
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
(defun fn2-nserve-main ()
  (let* ((profile (fn2-nserve-profile))
         (image (sb-ext:posix-getenv "FN2_IMAGE"))
         (initialize (equal (sb-ext:posix-getenv "FN2_IMAGE_MODE") "init"))
         (image-bytes (and initialize (ignore-errors (parse-integer (or (sb-ext:posix-getenv "FN2_IMAGE_BYTES") "")))))
         (capacity (or (ignore-errors (parse-integer (or (sb-ext:posix-getenv "FN2_ENVELOPE_TRACE") "0"))) 0)))
    (format t "~%NODE-PID ~d~%" (%fn2-native-getpid))
    (finish-output)
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
    (let ((host (handler-case
                 (if image
                   (fn2-n-make-host profile :trace-capacity capacity :device-path image :create-size image-bytes)
                   (fn2-n-make-host profile :trace-capacity capacity :seeds *fn2-ss-seeds*))
                 (error (condition)
                   (format t "~%REFUSED ~a~%" condition) (finish-output)
                   (return-from fn2-nserve-main 2)))))
      (when initialize
        (fn2-n-destroy host)
        (format t "~%INITIALIZED~%") (finish-output)
        (return-from fn2-nserve-main 0))
      (format t "~%LISTENING ~d~%" (fn2-nhost-listen-port host))
      (when (fn2-nhost-local-path host)
        (format t "LISTENING-LOCAL ~a~%" (fn2-nhost-local-path host)))
      (finish-output)
      (unwind-protect
           (let ((reason (fn2-n-run host)))
             (format t "STOPPED ~d~%" reason)
             (multiple-value-bind (kind detail) (fn2-host-stop-details (fn2-nhost-core host))
               (format t "STOP-DETAIL ~d ~d~%" kind detail))
             (when (plusp capacity)
               (format t "ENVELOPE ~s~%"
                       (car (fn2-ss-replay (fn2-n-trace-list host) profile *fn2-ss-seeds* nil))))
             (finish-output)
             0)
        (fn2-n-destroy host)))))
