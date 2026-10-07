;;; The developer image's `eval': one Lisp form evaluated inside a running node's
;;; owner quantum, asked over the node's existing control socket
;;; (`fn operator CONFIG eval', tools/fn_dev.py repl --config).  Loaded by
;;; host/native/build.lisp only when FN_NATIVE_PROFILE=developer, together with
;;; books/developer-eval.lisp, which decides admission and renders the frames
;;; (fn-deval-*), the service-log lines (fn-olog-developer-eval-*) and the
;;; journal entry (fn-otm-eval-step).  A production image has neither this file
;;; nor that book; tests/test_developer_surface_absent.py checks it.
;;;
;;; This is a debugger, not a store interface or an ACL2 proof boundary: a form
;;; may deliberately change code and state.  Hence every use is logged before it
;;; runs, and the journal says that the run's decisions can no longer be
;;; replayed past it.
(in-package "ACL2")

(defvar *fnn-dev-service* nil)
(defvar *fnn-dev-admission-failed* nil)
;; ACL2's bound (books/developer-eval.lisp fn-deval-max-output-characters): the
;; reply frame is sized for it, so the host keeps no figure of its own.
(defconstant +fnn-dev-output-characters+ (fnn-core 'fn-deval-max-output-characters))

(defclass fnn-dev-output (sb-gray:fundamental-character-output-stream)
 ((text :initform (make-array +fnn-dev-output-characters+ :element-type 'character
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
 (let ((*read-eval* nil) (*readtable* (copy-readtable nil))
       (*package* (find-package "ACL2"))
       (end (gensym "EOF")))
  (multiple-value-bind (form offset) (read-from-string text nil end)
   (when (eq form end) (error "No form supplied"))
   (unless (eq (read-from-string text nil end :start offset) end)
    (error "Send one form; use PROGN for a batch"))
   form)))

(defun fnn-dev-evaluate (service text)
 "Read outside O, then evaluate one developer form in an actual owner quantum.
Answers (values STATUS OUTPUT): STATUS :ok or :error, OUTPUT the printed values
and everything the form wrote, at most +fnn-dev-output-characters+ characters.
Evaluation errors follow the owner's normal fault/fence boundary. Syntax errors
never enter O. *FNN-DEV-SERVICE* names this owner; nested owner entry is invalid."
 (let ((out (make-instance 'fnn-dev-output)) (status :ok))
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
     (when *fnn-dev-admission-failed* (setf status :error)))
    (serious-condition (condition)
     (setf status :error)
     (format out "~a~%" condition))))
  (values status
          (concatenate 'string
                       (fnn-dev-output-text out)
                       (if (fnn-dev-output-truncated out)
                           (format nil "~%[output truncated]~%") "")))))

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

(defun fnn-dev-load-file (path admitp step-limit)
 "Read trusted developer source with reader evaluation disabled. Read/open
failures are controlled inside the owner boundary; evaluation faults retain
normal fencing. Earlier evaluated/admitted forms are never rolled back."
 (let ((attempted 0) (completed 0) (stream nil))
  (labels ((refuse (reason condition)
             (setf *fnn-dev-admission-failed* t)
             (format *error-output*
                     "Developer file ~a: ~d top-level forms attempted, ~d completed; earlier evaluated/admitted prefix remains.~%"
                     reason attempted completed)
             (when condition (format *error-output* "~a~%" condition))
             (values (if (plusp attempted) :partial :refused)
                     reason attempted completed)))
   ;; Catch OPEN's file error only here, never a file/storage error signalled
   ;; while a form is being evaluated.
   (handler-case (setf stream (open path :direction :input))
    (file-error (condition)
     (return-from fnn-dev-load-file (refuse :open-error condition))))
   (unwind-protect
    (let ((*read-eval* nil) (*readtable* (copy-readtable nil))
          (*package* (find-package "ACL2"))
          (*load-pathname* (pathname path)) (*load-truename* (pathname stream))
          (end (gensym "EOF")))
     (loop
      (let ((form
             (handler-case (read stream nil end)
              (reader-error (condition)
               (return-from fnn-dev-load-file (refuse :reader-error condition)))
              (end-of-file (condition)
               (return-from fnn-dev-load-file (refuse :reader-error condition)))
              (stream-error (condition)
               (return-from fnn-dev-load-file (refuse :read-error condition))))))
       (when (eq form end)
        (return (values (if admitp :admitted :loaded) attempted completed)))
       (incf attempted)
       (if admitp
           (unless (eq (fnn-dev-admit (list form) :step-limit step-limit) :admitted)
            (return (refuse :acl2-refusal nil)))
         (progn
          (eval form)
          ;; A native module may itself use bounded ACL2 admission. Stop at
          ;; its explicit refusal, retaining whatever prefix it admitted.
          (when *fnn-dev-admission-failed*
           (return (refuse :acl2-refusal nil)))))
       (incf completed))))
    (close stream)))))

(defun fnn-dev-load (path)
 "Load trusted native developer forms with explicit partial-load reporting."
 (fnn-dev-load-file path nil nil))

(defun fnn-dev-admit-file (path &key (step-limit 200000))
 "Admit ordinary source events incrementally; read errors preserve the prefix."
 (fnn-dev-load-file path t step-limit))

;;; ---------------------------------------------------------------------------
;;; The server side: one more handler on the control socket's chain
;;; (host/native/control.lisp *fnn-hybrid-control-handler*), asked only for a
;;; frame ACL2's classifier names (books/native-control-kinds.lisp, with kind 40
;;; added by books/developer-eval.lisp).

(defun fnn-deval-journal (service uid octets)
 "The developer-eval entry (books/owner-time-journal.lisp fn-otm-eval-step),
offered to the journal writer under the gate mutex that numbers it, like
fnn-owner-journal-note."
 (let ((gate (fnn-owner-service-gate service)))
  (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
   (destructuring-bind (sched jline)
     (fnn-core 'fn-otm-eval-step (fnn-owner-gate-sched gate) uid octets)
    (setf (fnn-owner-gate-sched gate) sched)
    (fnn-journal-line jline)))))

(defun fnn-deval-form-digest (octets)
 "The BLAKE3 digest of the form's octets, from the control buffer in place
(ACL2's buffer digest, as `blake3' digests a file)."
 (fnn-with-control-buffer ()
  (fnn-core 'fn-blake3-of-prefixed-buffer-any nil (fnn-octets-ctl-fill octets))))

(defun fnn-deval-reply (status output)
 "ACL2's sealed reply frame for STATUS and the text OUTPUT, as a handler reply."
 (let ((reply (fnn-core 'fn-deval-reply-encode status
                        (fnn-octet-list
                         (sb-ext:string-to-octets output :external-format :utf-8)))))
  (unless (fnn-octet-list-p reply) (fnn-fault "ACL2 refused a developer-eval reply"))
  (list :sealed-reply reply)))

(defun fnn-deval-answer (service socket frame form)
 (multiple-value-bind (peer-ok uid) (fnn-control-peer-is-owner-p socket)
  (declare (ignore peer-ok))
  (let ((verdict (fnn-core 'fn-deval-admit *fnn-image-profile* uid (sb-posix:geteuid)
                           (length frame) (fnn-core 'fn-deval-max-frame-octets)
                           (and (fnn-owner-service-stopping service) t))))
   (if (not (eq verdict :admit))
       (progn
        (fnn-log-line (fnn-core 'fn-olog-developer-eval-refused-line (second verdict)))
        (fnn-deval-reply (fnn-core 'fn-deval-refusal-status verdict) ""))
     (let* ((vector (fnn-octets form))
            ;; a form that is not UTF-8 reads with the replacement character and
            ;; fails to read (or evaluates what it says): it never signals past
            ;; this handler, whose escape would fault the owner
            (text (sb-ext:octets-to-string vector :external-format '(:utf-8 :replacement #\?)))
            ;; RP-3's labelled mutation: the begin line and the journal entry
            ;; after the form, not before it.
            (late (fnn-developer-selector "FN_NATIVE_TEST_EVAL_BEGIN_LATE")))
      (flet ((begin ()
               (fnn-log-line (fnn-core 'fn-olog-developer-eval-begin-line uid (length vector)
                                       (fnn-deval-form-digest vector)
                                       (fnn-store-prepare-observation)))
               (fnn-deval-journal service uid (length vector))))
       ;; Before the form runs: the log line (so a form that faults the owner
       ;; leaves it) and the journal entry (so replay stops there).
       (unless late (begin))
       (let ((start (fnn-monotonic-ms)))
        (multiple-value-bind (status output) (fnn-dev-evaluate service text)
         (when late (begin))
         (let ((octets (length (sb-ext:string-to-octets output :external-format :utf-8))))
          (fnn-log-line (fnn-core 'fn-olog-developer-eval-end-line status octets
                                  start (fnn-monotonic-ms)))
          (fnn-deval-reply status output))))))))))

(defvar *fnn-deval-next-handler* *fnn-hybrid-control-handler*)

(defun fnn-deval-control-handle (service frame)
 (let ((form (and (typep frame 'fnn-octets)
                  (fnn-core 'fn-deval-request-decode (fnn-control-frame-octet-list frame)))))
  (if form
      (fnn-deval-answer service *fnn-control-peer-socket* frame form)
    (and *fnn-deval-next-handler*
         (funcall *fnn-deval-next-handler* service frame)))))

(setq *fnn-hybrid-control-handler* #'fnn-deval-control-handle)

;;; ---------------------------------------------------------------------------
;;; The client side: `fn operator CONFIG eval' reads one form from standard
;;; input, sends it as ACL2's kind-40 frame to the node's control socket, and
;;; prints the output of the kind-41 reply.  Exit: 0 evaluated, 1 the form
;;; failed, 2 refused by name (the reason on standard error), 3 no reply (the
;;; form may have run).

(defun fnn-deval-control-path (config-path)
 "The control socket the configuration names, from ACL2's plan of `status'."
 (let* ((config-octets (fnn-operator-read-config
                        config-path (fnn-core 'fn-native-config-host-max-octets)))
        (result (fnn-operator-run-at config-path config-octets
                                     (fnn-operator-argv-octets (list "status"))))
        (path-list (fnn-core 'fn-native-operator-host-result-status-control-path-octets
                             result)))
  (unless (and (fnn-octet-list-p path-list) (consp path-list))
   (error 'fnn-usage-error :message "the configuration names no control socket"))
  (fnn-octets-string (fnn-octets path-list))))

(defun fnn-deval-client (config-path)
 (let* ((form (fnn-octet-list (fnn-read-bounded-fd 0 (ash 1 20))))
        (request (fnn-core 'fn-deval-request-encode form)))
  (unless (fnn-octet-list-p request)
   (error 'fnn-usage-error :message "send one non-empty form of at most 65536 octets"))
  (multiple-value-bind (frame stage)
    (fnn-control-exchange (fnn-deval-control-path config-path) request nil 3600)
   (declare (ignore stage))
   (let ((read (and frame (fnn-core 'fn-deval-reply-read (fnn-octet-list frame)))))
    (cond
     ((not (consp read))
      (fnn-err "developer eval: no reply; the form may have run")
      3)
     (t
      (destructuring-bind (status output) read
       (write-sequence (fnn-octets output) *fnn-stdout*)
       (finish-output *fnn-stdout*)
       (case status
        (:ok 0)
        (:error 1)
        (otherwise (fnn-err "developer eval refused: ~(~a~)" status) 2)))))))))

(push (list "operator" "eval") *fnn-verb-words*)

(let ((next (fnn-verb-handler "operator")))
 (fnn-unregister-verb "operator")
 (fnn-register-verb "operator"
                    (lambda (config-path argv)
                     (if (equal argv '("eval"))
                         (fnn-deval-client config-path)
                       (funcall next config-path argv)))))
