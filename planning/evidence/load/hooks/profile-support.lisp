;;; Measurement-only helpers. Pre-encode each NUL-terminated namestring once;
;;; the access(2) poll on a pinned vector returns immediate integers, allocating
;;; no pathnames, strings, or stat structures inside the measurement window.
(in-package "ACL2")
(declaim (inline fn-load-access))
(sb-alien:define-alien-routine ("access" fn-load-access) sb-alien:int
  (path sb-alien:system-area-pointer) (mode sb-alien:int))
(defun fn-load-trigger-name (namestring)
  (sb-ext:string-to-octets namestring :external-format :utf-8 :null-terminate t))
(defun fn-load-trigger-present-p (bytes)
  (declare (type (simple-array (unsigned-byte 8) (*)) bytes)
           (optimize (speed 3) (safety 1)))
  (sb-sys:with-pinned-objects (bytes)
    (zerop (fn-load-access (sb-sys:vector-sap bytes) 0))))
(defun fn-load-json-string (value stream)
  (write-char #\" stream)
  (loop for c across value do
    (case c
      (#\" (write-string "\\\"" stream))
      (#\\ (write-string "\\\\" stream))
      (#\Newline (write-string "\\n" stream))
      (#\Return (write-string "\\r" stream))
      (#\Tab (write-string "\\t" stream))
      (otherwise (if (< (char-code c) 32)
                     (format stream "\\u~4,'0x" (char-code c))
                     (write-char c stream)))))
  (write-char #\" stream))
(defun fn-load-thread-samples (path)
  ;; REPORT extracts raw traces into *SAMPLES* before this is called. Keep even
  ;; exited syncer threads. Python subtracts by THREAD NAME, not function name.
  (let ((counts (make-hash-table :test 'equal)))
    (funcall (intern "MAP-TRACES" "SB-SPROF")
      (lambda (thread trace)
        ;; MAP-TRACES visits every extracted sample, including repeated traces;
        ;; TRACE-MULTIPLICITY belongs to raw SAP records, not this public handle.
        (let ((name "elsewhere"))
          ;; MAP-TRACE-PC-LOCS visits oldest to youngest; last is the self PC.
          (funcall (intern "MAP-TRACE-PC-LOCS" "SB-SPROF")
            (lambda (debug-fun pc)
              (setf name (if debug-fun
                             (prin1-to-string (sb-di:debug-fun-name debug-fun))
                             (format nil "(foreign #x~x)" pc)))) trace)
          (incf (gethash (list (or (sb-thread:thread-name thread) "unnamed") name) counts 0))))
      (symbol-value (intern "*SAMPLES*" "SB-SPROF")))
    (with-open-file (s path :direction :output :if-exists :supersede)
      (maphash (lambda (key count)
                 (write-string "{\"thread\":" s)
                 (fn-load-json-string (first key) s)
                 (write-string ",\"function\":" s)
                 (fn-load-json-string (second key) s)
                 (format s ",\"count\":~d}~%" count)) counts))))
