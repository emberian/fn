; tools/runtime_image/world-probe.lisp -- loaded into a native image's core
; before (acl2::sbcl-restart) by node_measure.py `probe'.  It counts, by
; encapsulation, every full call of the ACL2 functions through which code
; reads the logical world or evaluates through it (fgetprop, sgetprop,
; global-val, w, the ev family, trans-eval, ld, wormholes, translate), every
; executable-counterpart (*1*) call of an fn function, and the raw calls of
; named core subjects; every second it writes the table to RI_PROBE_OUT.  An
; inlined call is not seen; the ACL2 8.7 sources declare none of these
; inline.  A measurement only.
(in-package "ACL2")
(defvar *ri-counts* (make-hash-table :test 'equal))
(defvar *ri-lock* (sb-thread:make-mutex :name "ri"))
(defun ri-caller ()
  "The nearest frame above the probe whose function names an fn function."
  (let ((found nil))
    (sb-debug:map-backtrace
     (lambda (frame)
       (unless found
         (let* ((name (sb-di:debug-fun-name (sb-di:frame-debug-fun frame)))
                (n (and (symbolp name) (symbol-name name))))
           (when (and n (or (eql 0 (search "FN-" n)) (eql 0 (search "FNN-" n))))
             (setq found (format nil "~a::~a" (package-name (symbol-package name)) n)))))))
    (or found "?")))
(defun ri-wrap-world (sym key)
  (when (and sym (fboundp sym) (not (macro-function sym)))
    (sb-int:encapsulate sym 'ri-count
      (let ((k key))
        (lambda (fn &rest args)
          (let ((c (ri-caller)))
            (sb-thread:with-mutex (*ri-lock*)
              (incf (gethash k *ri-counts* 0))
              (incf (gethash (concatenate 'string k "<-" c) *ri-counts* 0))))
          (apply fn args))))))
(defun ri-wrap (sym key)
  (when (and sym (fboundp sym) (not (macro-function sym)) (not (special-operator-p sym)))
    (sb-int:encapsulate sym 'ri-count
      (let ((k key))
        (lambda (fn &rest args)
          (sb-thread:with-mutex (*ri-lock*) (incf (gethash k *ri-counts* 0)))
          (apply fn args))))))
(dolist (name '("FGETPROP" "SGETPROP" "GLOBAL-VAL" "W" "EV" "EV-REC" "EV-W" "EV-FNCALL"
                "EV-FNCALL-REC" "EV-FNCALL-W" "EV-FNCALL-GUARD-ER" "TRANS-EVAL"
                "TRANS-EVAL-DEFAULT-WARNING" "LD-FN" "LD-FN0" "LD-FN1" "WORMHOLE1"
                "TRANSLATE" "TRANSLATE1" "TRANSLATE11" "UNTRANSLATE" "FMT" "FMT1"
                "THROW-RAW-EV-FNCALL" "GUARD-RAW"))
  (ri-wrap-world (find-symbol name "ACL2") (concatenate 'string "world:" name)))
(dolist (name '("FN-SCAR-OCFG-READ-TLS-PREFIX" "FN-CCAR-OWN-FINISH" "FN-RCL-EXISTING-ACTION"
                "FN-OCL-PUBLISH" "FN-PCAR-SBUD-PREPARE" "FN-RCLB-EXISTING-ACTION"))
  (ri-wrap (find-symbol name "ACL2") (concatenate 'string "raw:" name)))
(do-symbols (s (find-package "ACL2_*1*_ACL2"))
  (when (and (eq (symbol-package s) (find-package "ACL2_*1*_ACL2"))
             (fboundp s)
             (let ((n (symbol-name s)))
               (or (eql 0 (search "FN-" n)) (eql 0 (search "FNN-" n)))))
    (ri-wrap s (concatenate 'string "*1*:" (symbol-name s)))))
(sb-thread:make-thread
 (lambda ()
   (let ((out (sb-ext:posix-getenv "RI_PROBE_OUT")))
     (loop
       (sleep 1)
       (when out
         (let ((rows nil))
           (sb-thread:with-mutex (*ri-lock*)
             (maphash (lambda (k v) (push (cons k v) rows)) *ri-counts*))
           (with-open-file (s (concatenate 'string out ".tmp") :direction :output
                              :if-exists :supersede)
             (dolist (r (sort rows #'string< :key #'car))
               (format s "~a ~d~%" (car r) (cdr r))))
           (rename-file (concatenate 'string out ".tmp") out))))))
 :name "ri-probe-writer")
