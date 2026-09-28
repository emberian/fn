;;; The developer selectors, their one startup gate, the armed owner and the
;;; control stop cut, driven without an image.
;;;
;;; The functions under test are read out of host/native/io.lisp, owner.lisp,
;;; control.lisp and auth-admin.lisp and evaluated here, so this exercises the
;;; shipped definitions and not copies.  What they call that needs ACL2, a
;;; store or a socket is stubbed, and the stubs record what they were handed.
;;;
;;; The findings of planning/evidence/campaign-dabebb84-2026-09-22.md this
;;; holds, each as a case below:
;;;
;;;   F4-F6  a production image with any developer selector in its environment,
;;;          or a `store post' FAULT argument, exits 5 naming it from fnn-main
;;;          BEFORE fnn-dispatch; every selector reader answers NIL there; a
;;;          production control reply is the owner's own status, never :fault.
;;;   F1     the served owner (fnn-owner-run-normalized, the `operator run'
;;;          callee) and `store post' (fnn-command-post) arm the same store
;;;          fault from the same function, fnn-post-entry-fault.
;;;   F3     the control stop stops the calling thread before it can execute
;;;          its next instruction: a forked child whose worker thread writes
;;;          one octet right after the stop is observed stopped with nothing
;;;          written, twenty times, and writes the octet only after SIGCONT.
;;;   F7     FN_NATIVE_RECOVERY_FAULT selects the recovery program's own cuts.

(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-advance-frontier (store current-txid)
  (declare (ignorable store current-txid))
  (harness-stub-reached 'fnn-advance-frontier "host/native/io.lisp"))
(defun fnn-bridge-existing-action (msgid payload codes)
  (declare (ignorable msgid payload codes))
  (harness-stub-reached 'fnn-bridge-existing-action "host/native/io.lisp"))
(defun fnn-bridge-known-abort ()
  (harness-stub-reached 'fnn-bridge-known-abort "host/native/io.lisp"))
(defun fnn-bridge-next-txid ()
  (harness-stub-reached 'fnn-bridge-next-txid "host/native/io.lisp"))
(defun fnn-bridge-pending-record ()
  (harness-stub-reached 'fnn-bridge-pending-record "host/native/io.lisp"))
(defun fnn-bridge-prepare (msgid payload codes obligation subject evidence charge)
  (declare (ignorable msgid payload codes obligation subject evidence charge))
  (harness-stub-reached 'fnn-bridge-prepare "host/native/io.lisp"))
(defun fnn-bridge-refuse-reservation ()
  (harness-stub-reached 'fnn-bridge-refuse-reservation "host/native/io.lisp"))
(defun fnn-charge (length)
  (declare (ignorable length))
  (harness-stub-reached 'fnn-charge "host/native/io.lisp"))
(defun fnn-config-max-payload (store)
  (declare (ignorable store))
  (harness-stub-reached 'fnn-config-max-payload "host/native/io.lisp"))
(defun fnn-control-live-status-answer (service request)
  (declare (ignorable service request))
  (harness-stub-reached 'fnn-control-live-status-answer "host/native/control.lisp"))
(defun fnn-control-peer-is-owner-p (socket)
  (declare (ignorable socket))
  (harness-stub-reached 'fnn-control-peer-is-owner-p "host/native/control.lisp"))
(defun fnn-core-state (name &rest args)
  (declare (ignorable name args))
  (harness-stub-reached 'fnn-core-state "host/native/io.lisp"))
(defun fnn-finish (store)
  (declare (ignorable store))
  (harness-stub-reached 'fnn-finish "host/native/io.lisp"))
(defun fnn-group-codes-for (store groups)
  (declare (ignorable store groups))
  (harness-stub-reached 'fnn-group-codes-for "host/native/io.lisp"))
(defun fnn-metadata (msgid payload)
  (declare (ignorable msgid payload))
  (harness-stub-reached 'fnn-metadata "host/native/io.lisp"))
(defun fnn-owner-consumer-local-serialized (service operation first second)
  (declare (ignorable service operation first second))
  (harness-stub-reached 'fnn-owner-consumer-local-serialized "host/native/owner.lisp"))
(defun fnn-owner-consumer-local-wait (service operation consumer argument)
  (declare (ignorable service operation consumer argument))
  (harness-stub-reached 'fnn-owner-consumer-local-wait "host/native/owner.lisp"))
(defun fnn-owner-control-submit-serialized (service msgid groups payload)
  (declare (ignorable service msgid groups payload))
  (harness-stub-reached 'fnn-owner-control-submit-serialized "host/native/owner.lisp"))
(defun fnn-owner-disk-admit (service)
  (declare (ignorable service))
  (harness-stub-reached 'fnn-owner-disk-admit "host/native/owner.lisp"))
(defun fnn-owner-live-admin-serialized (service argv)
  (declare (ignorable service argv))
  (harness-stub-reached 'fnn-owner-live-admin-serialized "host/native/admin.lisp"))
(defun fnn-owner-moderation-serialized (service op login id reason)
  (declare (ignorable service op login id reason))
  (harness-stub-reached 'fnn-owner-moderation-serialized "host/native/owner.lisp"))
(defun fnn-owner-topic-local-serialized (service operation source-sequence quota observed-uid)
  (declare (ignorable service operation source-sequence quota observed-uid))
  (harness-stub-reached 'fnn-owner-topic-local-serialized "host/native/owner.lisp"))
(defun fnn-pending-sequence (value)
  (declare (ignorable value))
  (harness-stub-reached 'fnn-pending-sequence "host/native/io.lisp"))
(defun fnn-post-boundary (profile msgid payload-length group-count charge)
  (declare (ignorable profile msgid payload-length group-count charge))
  (harness-stub-reached 'fnn-post-boundary "host/native/io.lisp"))
(defun fnn-publish (store sequence record)
  (declare (ignorable store sequence record))
  (harness-stub-reached 'fnn-publish "host/native/io.lisp"))
(defun fnn-read-regular-bounded (path maximum)
  (declare (ignorable path maximum))
  (harness-stub-reached 'fnn-read-regular-bounded "host/native/io.lisp"))
(defun fnn-store-close (store)
  (declare (ignorable store))
  (harness-stub-reached 'fnn-store-close "host/native/io.lisp"))
(defun fnn-validate-post-boundary (verdict)
  (declare (ignorable verdict))
  (harness-stub-reached 'fnn-validate-post-boundary "host/native/io.lisp"))
;;; ---- derived stubs: END ----

(defparameter *failures* 0)
(defmacro check (form description)
  `(unless ,form
     (incf *failures*)
     (format t "FAIL: ~a~%  form: ~s~%" ,description ',form)))

(defun load-named (path names)
  "Evaluate the top-level forms of PATH whose defined name is in NAMES."
  (let ((found nil))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (car form) '(defun defparameter defvar defconstant
                                           define-condition defmacro))
                      (member (if (consp (cadr form)) (car (cadr form)) (cadr form))
                              names))
              do (eval form)
                 (push (cadr form) found)))
    (dolist (name names)
      (unless (member name found)
        (error "~a: ~a not found" path name)))))

;;; Stubs for what the deployed definitions call, defined first.
(defvar *log* nil)
(define-condition fnn-os-error (error) ())
(defun note (&rest event) (push event *log*))
;; fnn-main sets ACL2's invariant-risk mode first (served-readers, 057f9b08a).
(defvar *the-live-state* :live-state)
(defun f-put-global (key value state) (declare (ignore key value)) state)
(defun fnn-open-streams () nil)
(defun fnn-global (name) (declare (ignore name)) t)
(defun fnn-dispatch (argv) (note :dispatch argv) 0)
(defun fnn-err (control &rest args) (note :err (apply #'format nil control args)))
(defun fnn-out (control &rest args) (note :out (apply #'format nil control args)))
(defun fnn-exit (code) (throw 'exit code))
(defun fnn-%shutdown (fd how) (declare (ignore fd how)) nil)
(defconstant +fnn-shut-rdwr+ 2)
(defun fnn-os-fail (errno &optional path) (error "os-fail ~a ~a" errno path))
(defun fnn-ascii-octet-list (text) (map 'list #'char-code text))
(defun fnn-octets (x) (coerce x '(vector (unsigned-byte 8))))
(defun fnn-open-live-store (root writable &optional fault)
  (note :open root writable fault)
  (throw 'opened fault))
(defun fnn-core (name &rest args)
  (case name
    ;; fnn-main's GC trigger (reservation-after-flip: ACL2's
    ;; fn-heap-nursery-trigger); the stub answers the host's default.
    (fn-heap-nursery-trigger (second args))
    (t (error "unexpected core call ~a" name))))
;; host/native/io.lisp's exit-code constants call ACL2's fn-outcome-code
;; (books/outcome-class.lisp, PRF-143) at load, so it must exist before io.lisp
;; is read (PKT-561, PKT-614).  The table is the book's own quoted constant,
;; read from the book; the function is the book's body without its xargs.
(defun book-defconst-value (path name)
  (with-open-file (stream path)
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defconst) (eq (cadr form) name))
            do (return (eval (caddr form)))
          finally (error "~a: ~a not found" path name))))
(defparameter *fn-outcome-codes*
  (book-defconst-value "books/outcome-class.lisp" '*fn-outcome-codes*))
(defun fn-outcome-code (class)
  (let ((pair (assoc class *fn-outcome-codes* :test #'equal)))
    (if (consp pair) (cdr pair) 3)))

;;; ---------------------------------------------------------------------------
;;; The deployed definitions.

(load-named "host/native/io.lisp"
            '(+fnn-exit-ok+ +fnn-exit-refused+ +fnn-exit-uncertain+ +fnn-exit-fault+
              +fnn-exit-usage+ fnn-store-error fnn-store-fault fnn-store-indeterminate
              fnn-usage-error fnn-refuse fnn-fault fnn-indeterminate fnn-exit-code-for
              *fnn-image-profile* *fnn-sigterm-owner-active* *fnn-sigterm-requested*
              *fnn-sigterm-wakeup-fd* *fnn-sighup-count* +fnn-gc-nursery-octets+
              fnn-gc-nursery-octets
              fnn-developer-image-p fnn-dash-nil
              +fnn-developer-selectors+ fnn-developer-selector
              fnn-store-post-fault-argument fnn-developer-selector-refusal
              fnn-developer-selector-gate
              +fnn-init-model-cuts+ +fnn-init-publication-cuts+ +fnn-init-test-controls+
              fnn-init-test-fault
              +fnn-recovery-model-cuts+ fnn-recovery-test-fault
              +fnn-state-checkpoint-model-cuts+ fnn-state-checkpoint-test-fault
              +fnn-cli-faults+ +fnn-post-model-cuts+ +fnn-post-log-model-cuts+
              fnn-post-test-fault
              fnn-post-entry-fault fnn-command-post fnn-main))

(defun setenv (name value) (sb-posix:setenv name value 1))
(defun unsetenv (name) (sb-posix:unsetenv name))
(defun clear-selectors ()
  (dolist (name +fnn-developer-selectors+) (unsetenv name)))
(defmacro with-profile ((profile) &body body)
  `(let ((*fnn-image-profile* ,profile)) ,@body))
(defun run-main (argv)
  "Run the deployed fnn-main over ARGV; answer its exit code."
  (setq *log* nil)
  (let ((sb-ext:*posix-argv* (list* "fn-host" "--fn" argv)))
    (catch 'exit (fnn-main) :no-exit)))
(defun logged (kind) (remove kind *log* :key #'car :test-not #'eq))

;;; ---------------------------------------------------------------------------
;;; F4-F6: one gate, at process start, before any store.

(clear-selectors)
(with-profile (:production)
  (dolist (name +fnn-developer-selectors+)
    (clear-selectors)
    (setenv name "x")
    (let ((code (run-main (list "store" "/nonexistent" "recover"))))
      (check (eql code +fnn-exit-usage+)
             (format nil "production start with ~a exits 5" name))
      (check (null (logged :dispatch))
             (format nil "production start with ~a never dispatches" name))
      (check (search name (second (first (logged :err))))
             (format nil "production refusal names ~a" name)))
    ;; Each reader answers NIL on a production image, whatever the value.
    (check (null (fnn-developer-selector name))
           (format nil "production reads ~a as NIL" name)))
  (clear-selectors)
  ;; An empty value is still a set variable.
  (setenv "FN_NATIVE_POST_FAULT" "")
  (check (eql (run-main (list "store" "/x" "status")) +fnn-exit-usage+)
         "an empty selector is refused too")
  (clear-selectors)
  ;; The positional FAULT of `store ROOT post'.
  (let ((code (run-main (list "store" "/x" "post" "<a@b>" "/p" "-" "postpublish"
                              "fn.letters"))))
    (check (eql code +fnn-exit-usage+) "production store post FAULT exits 5")
    (check (null (logged :dispatch)) "production store post FAULT never dispatches")
    (check (search "FAULT argument" (second (first (logged :err))))
           "production refusal names the FAULT argument"))
  ;; Even the plain raw entry is unsupported before dispatch or Store I/O.
  (check (eql (run-main (list "store" "/x" "post" "<a@b>" "/p" "-" "-" "fn.letters"))
              +fnn-exit-usage+)
         "production store post without FAULT exits 5")
  (check (null (logged :dispatch)) "production store post never dispatches")
  (check (search "store post" (second (first (logged :err))))
         "production raw post refusal names its entry")
  (check (eql (run-main (list "store" "/x" "status")) 0)
         "production inspection dispatches")
  (check (logged :dispatch) "production inspection reaches dispatch")
  ;; Direct function callers are guarded before the store opens too.
  (check (eq :usage
             (handler-case (catch 'opened
                             (fnn-command-post "/x" "<a@b>" "/p" nil "postpublish"
                                               '("fn.letters")))
               (fnn-usage-error () :usage)))
         "production fnn-command-post refuses before opening"))

(with-profile (:developer)
  (clear-selectors)
  (setenv "FN_NATIVE_POST_FAULT" "log-fenced:kill")
  (check (eql (run-main (list "store" "/x" "status")) 0)
         "a developer image starts with a selector set")
  (check (logged :dispatch) "a developer image dispatches with a selector set")
  (check (equal (fnn-developer-selector "FN_NATIVE_POST_FAULT") "log-fenced:kill")
         "a developer image reads its selector")
  (clear-selectors)
  (check (eq :fault (handler-case (fnn-developer-selector "FN_NATIVE_NOT_REGISTERED")
                      (fnn-store-fault () :fault)))
         "an unregistered selector name is a fault, not a silent read"))

;;; ---------------------------------------------------------------------------
;;; F1: one fault function for both posting entries; F7: recovery cuts.

(with-profile (:developer)
  (clear-selectors)
  (setenv "FN_NATIVE_POST_FAULT" "log-fenced:kill")
  (check (equal (fnn-post-entry-fault nil)
                '(:log-fenced :fnn-test-kill "developer-only native post fault"))
         "FN_NATIVE_POST_FAULT arms a post cut")
  (setq *log* nil)
  (check (equal (catch 'opened (fnn-command-post "/x" "<a@b>" "/p" nil nil '("g")))
                (fnn-post-entry-fault nil))
         "store post opens its store with fnn-post-entry-fault's fault")
  (setenv "FN_NATIVE_RECOVERY_FAULT" "recover-barrier-1:kill")
  (check (eq :usage (handler-case (fnn-post-entry-fault nil)
                      (fnn-usage-error () :usage)))
         "two store fault selectors at once are a usage error")
  (clear-selectors)
  (dolist (cut +fnn-recovery-model-cuts+)
    (setenv "FN_NATIVE_RECOVERY_FAULT" (format nil "~a:kill" cut))
    (check (eq (first (fnn-post-entry-fault nil))
               (intern (string-upcase cut) :keyword))
           (format nil "FN_NATIVE_RECOVERY_FAULT selects ~a" cut)))
  ;; A format-9 store has no committed-history marker (M := D): the per-file
  ;; marker program's cuts are not recovery cuts.
  (setenv "FN_NATIVE_RECOVERY_FAULT" "marker-replaced:eio")
  (check (eq :fault (handler-case (fnn-post-entry-fault nil)
                      (fnn-store-fault () :fault)))
         "a marker cut is not a recovery cut")
  (setenv "FN_NATIVE_RECOVERY_FAULT" "recover-barrier:kill")
  (check (eq :fault (handler-case (fnn-post-entry-fault nil)
                      (fnn-store-fault () :fault)))
         "the unsuffixed recovery barrier is not a model cut")
  (clear-selectors)
  (check (equal (fnn-post-entry-fault "postpublish")
                (cdr (assoc "postpublish" +fnn-cli-faults+ :test #'string=)))
         "the positional FAULT arms its +fnn-cli-faults+ entry")
  (check (eq :usage (handler-case (fnn-post-entry-fault "nonesuch")
                      (fnn-usage-error () :usage)))
         "an unknown positional FAULT is a usage error"))

;;; The served owner: fnn-owner-run-normalized hands fnn-owner-run the same fault.
(defun fnn-octets-string (octets) (map 'string #'code-char octets))
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-octet-list-p (x) (listp x))
(defun fnn-tls-context-p (x) (declare (ignore x)) nil)
(deftype fnn-octets () '(vector (unsigned-byte 8)))
(defun fnn-core (name &rest args)
  (declare (ignore args))
  (case name
    (fn-native-config-host-listener-addresses (list (list :inet (list 127 0 0 1))))
    (t (error "unexpected core call ~a" name))))
(defvar *owner-run-fault* :unset)
(defun fnn-owner-run (root port once max &optional fault &rest more)
  (declare (ignore root port once max more))
  (setq *owner-run-fault* fault)
  0)
(defstruct (fnn-store) fault-point fault-class fault-message)
(load-named "host/native/owner.lisp"
            '(*fnn-owner-control-fault-consumed* fnn-owner-control-test-fault
              fnn-owner-control-arm-fault fnn-owner-control-disarm-fault
              fnn-owner-run-normalized fnn-command-owner))

(defun run-normalized ()
  (setq *owner-run-fault* :unset)
  (fnn-owner-run-normalized (fnn-octets (map 'list #'char-code "/store"))
                            (fnn-octets (map 'list #'char-code "127.0.0.1"))
                            119 nil 8)
  *owner-run-fault*)

(with-profile (:developer)
  (clear-selectors)
  (dolist (cut +fnn-post-model-cuts+)
    (setenv "FN_NATIVE_POST_FAULT" (format nil "~(~a~):kill" cut))
    (check (equal (run-normalized) (fnn-post-entry-fault nil))
           (format nil "the served owner is armed at ~a" cut))
    (check (eq (first (run-normalized)) cut)
           (format nil "the served owner's fault point is ~a" cut)))
  (clear-selectors)
  (setenv "FN_NATIVE_RECOVERY_FAULT" "recovery-stage-unlinked:eio")
  (check (equal (run-normalized) (fnn-post-entry-fault nil))
         "the served owner is armed at a recovery cut")
  (clear-selectors)
  ;; Only the served owner reaches fn-bs-scp-program's cuts, and only when no
  ;; posting-entry fault is selected.
  (dolist (cut +fnn-state-checkpoint-model-cuts+)
    (setenv "FN_NATIVE_STATE_CHECKPOINT_FAULT" (format nil "~a:kill" cut))
    (check (equal (run-normalized)
                  (list (intern (string-upcase cut) :keyword) :fnn-test-kill
                        "developer-only native state-checkpoint fault"))
           (format nil "the served owner is armed at the state-checkpoint cut ~a" cut)))
  (setenv "FN_NATIVE_POST_FAULT" "finish-durable:kill")
  (check (eq (first (run-normalized)) :finish-durable)
         "a posting-entry fault takes the store slot before a state-checkpoint cut")
  (clear-selectors)
  (check (null (run-normalized)) "an unselected developer owner has no fault")
  (setenv "FN_NATIVE_CONTROL_FAULT" "nonesuch")
  (check (eq :fault (handler-case (run-normalized) (fnn-store-fault () :fault)))
         "a malformed control fault is refused before the store opens")
  (clear-selectors)
  ;; The developer-only low-level `owner run' verb takes the same selectors.
  (setenv "FN_NATIVE_POST_FAULT" "finish-durable:kill")
  (fnn-command-owner "run" (list "/store" "0" "1" "8"))
  (check (eq (first *owner-run-fault*) :finish-durable)
         "owner run reads FN_NATIVE_POST_FAULT")
  (clear-selectors)
  (fnn-command-owner "run" (list "/store" "0" "1" "8" "recordbarrier"))
  (check (eq (first *owner-run-fault*) :log-written)
         "owner run's INJECT arms its +fnn-cli-faults+ entry"))

(with-profile (:production)
  (setenv "FN_NATIVE_POST_FAULT" "log-fenced:kill")
  (setenv "FN_NATIVE_CONTROL_FAULT" "postpublish")
  ;; Unreachable through fnn-main (the gate); the readers still honour nothing.
  (check (null (run-normalized)) "a production owner arms nothing")
  (check (null (fnn-owner-control-test-fault)) "a production owner has no control fault")
  (clear-selectors))

;;; A control fault displaces the owner's own store fault only for its one
;;; submission.
(with-profile (:developer)
  (clear-selectors)
  (setq *fnn-owner-control-fault-consumed* nil)
  (setenv "FN_NATIVE_CONTROL_FAULT" "postpublish")
  (let* ((store (make-fnn-store :fault-point :finish-durable :fault-class :fnn-test-kill
                                :fault-message "m"))
         (armed (fnn-owner-control-arm-fault store)))
    ;; postpublish arms the record log's log-fenced (+fnn-cli-faults+).
    (check (eq (fnn-store-fault-point store) :log-fenced)
           "the control fault is armed for its submission")
    (fnn-owner-control-disarm-fault store armed)
    (check (and (eq (fnn-store-fault-point store) :finish-durable)
                (eq (fnn-store-fault-class store) :fnn-test-kill))
           "disarming restores the owner's own store fault"))
  (clear-selectors))

;;; ---------------------------------------------------------------------------
;;; Control: the reply carries the owner's status; the stop is synchronous.

(defstruct (fnn-socket) fd)
(defvar *fnn-hybrid-control-handler* nil)
(defvar *sent* nil)
(defun fnn-control-state-service (control) (declare (ignore control)) :service)
(defun fnn-control-state-read-maximum (control) (declare (ignore control)) 4096)
(defun fnn-control-read-frame (socket maximum) (declare (ignore socket maximum)) :frame)
(defun fnn-control-answering (control socket) (declare (ignore control socket)) nil)
(defun fnn-control-send-reply (socket status)
  (declare (ignore socket))
  (note :reply status)
  (push status *sent*))
(defun fnn-owner-fault-service (&rest args) (note :owner-fault args))
(load-named "host/native/control.lisp"
            '(fnn-control-stop-cut-armed-p fnn-control-stop-calling-thread
              fnn-control-test-after-submit fnn-control-handle-client))
(defun fnn-core (name &rest args)
  (declare (ignore args))
  (case name
    (fn-native-control-host-max-frame 4096)
    (t (error "unexpected core call ~a" name))))

;;; The real stop is exercised in a forked child below; here it is recorded.
(defparameter *real-stop* #'fnn-control-stop-calling-thread)
(defun fnn-control-stop-calling-thread () (note :stop))

(defun handle (status)
  (setq *log* nil)
  (let ((*fnn-hybrid-control-handler* (lambda (service frame)
                                        (declare (ignore service frame))
                                        status)))
    (fnn-control-handle-client :control :socket))
  (reverse *log*))

(with-profile (:production)
  (clear-selectors)
  (setenv "FN_NATIVE_CONTROL_TEST_STOP" "after-submit")
  (dolist (status '(:accepted :duplicate :refused :uncertain))
    (check (equal (handle status) (list (list :reply status)))
           (format nil "a production reply carries ~a unchanged and never stops" status)))
  (clear-selectors))

(with-profile (:developer)
  (clear-selectors)
  (setenv "FN_NATIVE_CONTROL_TEST_STOP" "after-submit")
  (check (equal (handle :accepted)
                '((:out "CONTROL-SUBMITTED") (:stop) (:reply :accepted)))
         "a developer stop happens after the owner's answer and before its reply")
  (check (equal (handle :uncertain) '((:reply :uncertain)))
         "the stop cut is not taken on an uncertain answer")
  (check (equal (handle '(:consumer-reply :accepted (1 2)))
                '((:out "CONTROL-SUBMITTED") (:stop)
                  (:reply (:consumer-reply :accepted (1 2)))))
         "a consumer stop uses the inner status and preserves the whole reply")
  (check (equal (handle '(:consumer-poll-reply :accepted (1 2) (3 4)))
                '((:out "CONTROL-SUBMITTED") (:stop)
                  (:reply (:consumer-poll-reply :accepted (1 2) (3 4)))))
         "a poll stop uses the inner status and preserves its cursor and report")
  (check (equal (handle '(:consumer-reply :uncertain (1 2)))
                '((:reply (:consumer-reply :uncertain (1 2)))))
         "an uncertain consumer answer does not take the stop cut")
  (setenv "FN_NATIVE_CONTROL_TEST_STOP" "elsewhere")
  (check (eq :fault (handler-case (fnn-control-stop-cut-armed-p)
                      (fnn-store-fault () :fault)))
         "an unknown stop cut is refused")
  (clear-selectors))

;;; F3: pthread_kill of the calling thread stops that thread before its next
;;; instruction.  A child's worker thread stops itself and then writes one
;;; octet; the parent sees the child stopped with the pipe empty, continues
;;; it, and only then reads the octet.
(defun read-one (fd buffer)
  (sb-sys:with-pinned-objects (buffer)
    (sb-unix:unix-read fd (sb-sys:vector-sap buffer) 1)))

(defun stop-trial ()
  (multiple-value-bind (in out) (sb-posix:pipe)
    (let ((pid (sb-posix:fork)))
      (when (zerop pid)
        (sb-posix:close in)
        (let ((worker (sb-thread:make-thread
                       (lambda ()
                         (funcall *real-stop*)
                         (let ((octet (make-array 1 :element-type '(unsigned-byte 8)
                                                    :initial-element 88)))
                           (sb-unix:unix-write out octet 0 1))))))
          (sb-thread:join-thread worker)
          (sb-ext:exit :code 0 :abort t)))
      (sb-posix:close out)
      (multiple-value-bind (waited status) (sb-posix:waitpid pid sb-posix:wuntraced)
        (declare (ignore waited))
        (let ((stopped (sb-posix:wifstopped status))
              (early nil))
          (sb-posix:fcntl in sb-posix:f-setfl
                          (logior (sb-posix:fcntl in sb-posix:f-getfl) sb-posix:o-nonblock))
          (let ((buffer (make-array 1 :element-type '(unsigned-byte 8))))
            (setq early (eql 1 (read-one in buffer)))
            (sb-posix:kill pid sb-posix:sigcont)
            (sb-posix:fcntl in sb-posix:f-setfl
                            (logandc2 (sb-posix:fcntl in sb-posix:f-getfl)
                                      sb-posix:o-nonblock))
            (let ((late (eql 1 (read-one in buffer))))
              (sb-posix:waitpid pid 0)
              (sb-posix:close in)
              (list stopped early late))))))))

(dotimes (trial 20)
  (destructuring-bind (stopped early late) (stop-trial)
    (check stopped (format nil "trial ~d: the child is stopped" trial))
    (check (not early) (format nil "trial ~d: nothing after the stop ran before SIGCONT" trial))
    (check late (format nil "trial ~d: the worker resumed after SIGCONT" trial))))

;;; ---------------------------------------------------------------------------
;;; auth-admin reads through the same accessor.

(defun fnn-native-auth-admin-core (&rest args) (declare (ignore args)) nil)
(load-named "host/native/auth-admin.lisp"
            '(+fnn-native-auth-admin-test-cuts+ fnn-native-auth-admin-test-cut))
(clear-selectors)
(setenv "FN_NATIVE_AUTH_ADMIN_FAULT" "replace-returned:eio")
(with-profile (:production)
  (check (null (fnn-native-auth-admin-test-cut)) "production reads no auth-admin cut"))
(with-profile (:developer)
  (check (functionp (fnn-native-auth-admin-test-cut)) "developer arms the auth-admin cut"))
(clear-selectors)

(if (zerop *failures*)
    (format t "native developer selectors passed~%")
    (progn (format t "native developer selectors: ~d failure(s)~%" *failures*)
           (sb-ext:exit :code 1 :abort t)))
