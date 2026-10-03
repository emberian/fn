;;; Explicit trusted developer-code attachment, separate from every fn protocol.
;;; Enabled only by FN_NATIVE_DEV_REPL=/absolute/private/path on a developer
;;; process. The socket's peer UID must match. This is a debugger, not a store
;;; interface or an ACL2 proof boundary; forms may deliberately change code/state.
(in-package "ACL2")

;; Earlier loads registered function objects. Remove our old objects before
;; DEFUN replaces them, then register symbols below so future reloads dedupe
;; and call the current definitions. Leave every other owner's hook intact.
(dolist (entry '((fnn-dev-repl-start *fnn-owner-start-hooks*)
                 (fnn-dev-repl-stop *fnn-owner-stop-hooks*)
                 (fnn-dev-repl-close *fnn-owner-close-hooks*)))
 (when (and (fboundp (first entry)) (boundp (second entry)))
  (setf (symbol-value (second entry))
        (remove (symbol-function (first entry)) (symbol-value (second entry))))))

(defvar *fnn-dev-repl* nil)
(defvar *fnn-dev-service* nil)
(defvar *fnn-dev-admission-failed* nil)
(defconstant +fnn-dev-repl-input+ 65536)
(defconstant +fnn-dev-repl-output+ 65536)

(defclass fnn-dev-output (sb-gray:fundamental-character-output-stream)
 ((text :initform (make-array +fnn-dev-repl-output+ :element-type 'character
                             :fill-pointer 0) :reader fnn-dev-output-text)
  (truncated :initform nil :accessor fnn-dev-output-truncated)))
(defmethod sb-gray:stream-write-char ((stream fnn-dev-output) char)
 (let ((text (fnn-dev-output-text stream)))
  (if (< (fill-pointer text) (array-dimension text 0))
      (vector-push char text)
    (setf (fnn-dev-output-truncated stream) t)))
 char)
(defmethod sb-gray:stream-line-column ((stream fnn-dev-output))
 (declare (ignore stream)) nil)
(defmethod sb-gray:stream-finish-output ((stream fnn-dev-output))
 (declare (ignore stream)) nil)
(defmethod sb-gray:stream-force-output ((stream fnn-dev-output))
 (declare (ignore stream)) nil)

(defun fnn-dev-read-form (text)
 "Read one explicitly submitted developer form; reader evaluation is disabled."
 (let ((*read-eval* nil) (*package* (find-package "ACL2"))
       (end (gensym "EOF")))
  (multiple-value-bind (form offset) (read-from-string text nil end)
   (when (eq form end) (error "No form supplied"))
   (unless (eq (read-from-string text nil end :start offset) end)
    (error "Send one form; use PROGN for a batch"))
   form)))

(defun fnn-dev-evaluate (service text)
 "Read outside O, then evaluate one developer form in an actual owner quantum.
Evaluation errors follow the owner's normal fault/fence boundary. Syntax errors
never enter O. *FNN-DEV-SERVICE* names this owner; nested owner entry is invalid."
 (let ((out (make-instance 'fnn-dev-output)) (status "OK"))
  (let ((*standard-output* out) (*error-output* out) (*trace-output* out)
        (*print-length* 64) (*print-level* 12) (*print-circle* t)
        (*package* (find-package "ACL2")) (*fnn-dev-service* service)
        (*fnn-dev-admission-failed* nil))
   (handler-case
    (let ((form (fnn-dev-read-form text)))
     (fnn-owner-serialized service nil
      (lambda ()
       (fnn-trace-span (:developer-eval)
        (dolist (value (multiple-value-list (eval form)))
         (write value :stream out :escape t) (terpri out)))) :inspect)
     (when *fnn-dev-admission-failed* (setf status "ERROR")))
    (serious-condition (condition)
     (setf status "ERROR")
     (format out "~a~%" condition))))
  (concatenate 'string status (string #\Newline)
               (fnn-dev-output-text out)
               (if (fnn-dev-output-truncated out)
                   (format nil "~%[output truncated]~%") ""))))

(defun fnn-dev-admit (forms &key (step-limit 200000))
 "Admit ordinary ACL2 events. A controlled LD refusal reports failure without
throwing across the owner fence; earlier successful events remain admitted.
STEP-LIMIT bounds prover steps per submitted form, not wall time or arbitrary
Lisp execution. NIL explicitly uses the world's ordinary prover allowance."
 (unless (or (null step-limit)
             (and (integerp step-limit) (<= 0 step-limit *default-step-limit*)))
  (setf *fnn-dev-admission-failed* t)
  (format *error-output* "Invalid ACL2 prover step limit: ~s~%" step-limit)
  (return-from fnn-dev-admit (values :refused :invalid-step-limit)))
 (let ((state *the-live-state*)
       (old-output (get *standard-co* *open-output-channel-key*)))
  ;; ACL2 channels retain stream objects, not the current *STANDARD-OUTPUT*
  ;; binding. Redirect its existing standard channel inside this owner quantum
  ;; and restore on every exit, so proof output also respects the capture bound.
  (unwind-protect
   (progn
    (setf (get *standard-co* *open-output-channel-key*) *standard-output*)
    (multiple-value-bind (erp reason new-state)
     (ld-fn (list (cons 'standard-oi
                       (if step-limit
                           (mapcar (lambda (form)
                                     (list 'with-prover-step-limit step-limit form))
                                   forms)
                         forms))
                  (cons 'standard-co *standard-co*)
                  (cons 'proofs-co *standard-co*)
                  (cons 'ld-prompt nil) (cons 'ld-error-action :return))
            state nil)
     (declare (ignore new-state))
     (if (and (not erp) (eq reason :eof))
         :admitted
      (progn
       (setf *fnn-dev-admission-failed* t)
       (format *error-output* "ACL2 admission incomplete: ~s~%" reason)
       (values :refused reason)))))
   (setf (get *standard-co* *open-output-channel-key*) old-output))))

(defun fnn-dev-repl-loop (control service)
 (loop
  (when (fnn-with-control (control) (fnn-control-state-stopping control)) (return))
  (handler-case
   (let ((socket (fnn-accept-observe (fnn-control-state-listener control) 1)))
    (unless (eq socket :timeout)
     (unwind-protect
      (when (fnn-with-control (control)
              (unless (fnn-control-state-stopping control)
               (setf (fnn-control-state-clients control) (list socket)) t))
       (when (fnn-control-peer-is-owner-p socket)
        (let ((frame (fnn-control-read-frame socket +fnn-dev-repl-input+)))
         (when (typep frame 'fnn-octets)
          (let* ((text (sb-ext:octets-to-string frame :external-format :utf-8))
                 (reply (fnn-dev-evaluate service text)))
           (fnn-send-all (fnn-socket-fd socket)
                         (sb-ext:string-to-octets reply :external-format :utf-8)
                         +fnn-control-io-seconds+))))))
      (fnn-with-control (control) (setf (fnn-control-state-clients control) nil))
      (fnn-socket-shut socket))))
   (serious-condition (condition)
    (unless (fnn-with-control (control) (fnn-control-state-stopping control))
     (fnn-err "developer REPL connection: ~a" condition))))))

(defun fnn-dev-listen (control)
 ;; Record ownership before chmod/listen can fail. START's one unwind closes
 ;; the descriptor and removes only this exact bound inode on partial startup.
 (let* ((path (fnn-control-state-path control))
        (socket (make-instance 'sb-bsd-sockets:local-socket :type :stream :protocol 0)))
  (setf (fnn-control-state-listener control) socket)
  (let ((old (sb-posix:umask #o077)))
   (unwind-protect (sb-bsd-sockets:socket-bind socket path) (sb-posix:umask old)))
  (let ((info (fnn-lstat path)))
   (unless (fnn-control-socket-path-p info) (error "Developer socket missing after bind"))
   (setf (fnn-control-state-device control) (sb-posix:stat-dev info)
         (fnn-control-state-inode control) (sb-posix:stat-ino info)))
  (sb-posix:chmod path #o600)
  (sb-bsd-sockets:socket-listen socket 1)
  socket))

(defun fnn-dev-unlink-owned (control)
 (let ((info (fnn-lstat (fnn-control-state-path control))))
  (when (and (fnn-control-socket-path-p info)
             (eql (sb-posix:stat-dev info) (fnn-control-state-device control))
             (eql (sb-posix:stat-ino info) (fnn-control-state-inode control)))
   (fnn-unlink (fnn-control-state-path control)))))

(defun fnn-dev-repl-start (service)
 (let ((path (fnn-developer-selector "FN_NATIVE_DEV_REPL")))
  (when path
   (unless (and (plusp (length path)) (char= (char path 0) #\/))
    (fnn-refuse "FN_NATIVE_DEV_REPL must name an absolute private socket path"))
   ;; Never remove another process's socket or any pre-existing file.
   (when (fnn-lstat path) (fnn-refuse "developer REPL path already exists"))
   (let ((control (%make-fnn-control-state :path path :service service)))
    (setf *fnn-dev-repl* control)
    (unwind-protect
     (progn
      (fnn-dev-listen control)
      (setf (fnn-control-state-accept-thread control)
            (sb-thread:make-thread (lambda () (fnn-dev-repl-loop control service))
                                   :name "fn trusted developer REPL")))
     (unless (fnn-control-state-accept-thread control)
      (when (fnn-control-state-listener control)
       (fnn-socket-shut (fnn-control-state-listener control)))
      (fnn-dev-unlink-owned control)
      (setf *fnn-dev-repl* nil)))))))

(defun fnn-dev-repl-stop (service)
 (declare (ignore service))
 (when *fnn-dev-repl*
  (let ((control *fnn-dev-repl*))
   (fnn-with-control (control)
    (setf (fnn-control-state-stopping control) t)
    (dolist (socket (fnn-control-state-clients control)) (fnn-socket-shutdown socket)))
   (when (fnn-control-state-listener control)
    (fnn-socket-shutdown (fnn-control-state-listener control))))))

(defun fnn-dev-repl-close (service)
 (fnn-dev-repl-stop service)
 (when *fnn-dev-repl*
  (let ((control *fnn-dev-repl*))
   (when (fnn-control-state-accept-thread control)
    (sb-thread:join-thread (fnn-control-state-accept-thread control)))
   (when (fnn-control-state-listener control)
    (fnn-socket-shut (fnn-control-state-listener control)))
   (fnn-dev-unlink-owned control))
  (setf *fnn-dev-repl* nil)))

(pushnew 'fnn-dev-repl-start *fnn-owner-start-hooks*)
(pushnew 'fnn-dev-repl-stop *fnn-owner-stop-hooks*)
(pushnew 'fnn-dev-repl-close *fnn-owner-close-hooks*)
