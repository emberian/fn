;;; host/native/raw-trap.lisp -- D40 raw dispatch: the dispatch table and the
;;; trap, loaded FIRST in the raw block of every build script
;;; (host/native/build.lisp, build-dtn.lisp, build-store-test.lisp) and
;;; installed right after it loads, before any other raw host file.
;;;
;;; THE TRAP (raw-dispatch-3; Codex r34: a scan of the host's source cannot see
;;; an intern-built name, a defconstant initializer, a redefinition or an
;;; unscanned file, so the guarantee lives in the image, not the text).  At
;;; installation each raw-dispatched function OBJECT is captured and the
;;; symbol's function binding is REPLACED by a trap.  The trap runs the
;;; captured object only inside a dispatcher call's extent -- where the caller
;;; is ACL2 code: the raw body of a guard-verified function, or a *1*
;;; counterpart that has just checked its guard -- and otherwise signals
;;; fnn-raw-dispatch-trap.  So a host call of a raw-dispatched function that
;;; skips the dispatcher faults however it is spelled: a literal call compiled
;;; into a raw host file, funcall/apply of an interned or found symbol,
;;; symbol-function, a defconstant initializer or load-time form.
;;;
;;; What makes that hold (Codex r63):
;;;   F1  The dispatch table, the captured objects and the traps are LEXICAL
;;;       to the closure below.  Nothing returns a captured object: callers get
;;;       the dispatcher's answer (fnn-raw-dispatch-apply), a callback that
;;;       dispatches (fnn-raw-dispatch-callback), a symbol, or a boolean.
;;;   F2  This file loads before every other raw host file and the build
;;;       installs the traps right after it, so no raw host file and no
;;;       load-time form of one can capture a raw-dispatched function object
;;;       before its trap is in place.  (The ACL2 world loads before the raw
;;;       block; its raw bodies call by symbol, which reaches the trap.)
;;;   F3  The extent is a per-call capability, not a flag: each dispatcher call
;;;       mints a fresh token, records it as live for the calling thread in a
;;;       private table, binds it, and retires it on exit (unwind-protect).
;;;       The trap passes only for a live token of the current thread, so
;;;       binding *fnn-core-token* to anything else passes nothing, and a token
;;;       kept past its call is dead.  A callback (fnn-raw-dispatch-callback)
;;;       mints a token per call, as fnn-call does: holding one is holding a
;;;       dispatcher, which only the funded startup selection hands out.
;;;   F4  Installing over a recorded trap whose binding has changed (a
;;;       redefinition after installation) is refused: the new body is never
;;;       captured, and fnn-raw-dispatch-traps-intact refuses at the end of
;;;       the build and at every start (fnn-main).
;;; What the trap does not see: host code running INSIDE a live extent (an
;;; attachment or callback the core calls back into) -- none of the
;;; raw-dispatched functions is reachable that way by a host body today, and
;;; tools/raw_dispatch_rule.py (an early lint) refuses a host body that names
;;; one.  Host code that reaches into SBCL internals (closure environments)
;;; is outside any claim here.

(in-package "ACL2")

(define-condition fnn-store-error (error)
  ((message :initarg :message :reader fnn-message))
  (:report (lambda (c s) (write-string (fnn-message c) s))))
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-raw-dispatch-trap (fnn-store-fault) ())

(defvar *fnn-dispatch-counterpart* nil
  "T when the developer selector keeps the executable-counterpart path.  Safe
for any caller to set: the counterpart checks the entry's whole guard.")

(defvar *fnn-core-token* nil
  "The current dispatcher call's token.  Meaningful only while live in the
private table below; binding it grants nothing.")

(defun fnn-raw-trap-probe-target (x y)
  "The developer raw-traps probe's target (never an ACL2 function)."
  (values (- x y) (list x y)))

(defun fnn-raw-trap-fault (control &rest args)
  (error 'fnn-store-fault :message (apply #'format nil control args)))

(let ((dispatch (make-hash-table :test 'eq))     ; entry name -> raw symbol
      (captured (make-hash-table :test 'eq))     ; raw symbol -> function object
      (traps (make-hash-table :test 'eq))        ; raw symbol -> its trap
      (live (make-hash-table :test 'eq :synchronized t)) ; token -> thread
      (entry-check nil)                          ; io.lisp's fnn-entry-guard
      (session-check nil))                       ; io.lisp's fnn-developer-image-p
  (labels ((in-core-p ()
             (let ((token *fnn-core-token*))
               (and token (eq (gethash token live) sb-thread:*current-thread*))))
           (call-in-core (function args)
             (let ((token (list :fnn-core-token)))
               (setf (gethash token live) sb-thread:*current-thread*)
               (unwind-protect
                    (let ((*fnn-core-token* token))
                      (apply function args))
                 (remhash token live))))
           (trap-for (raw function)
             (lambda (&rest args)
               (if (in-core-p)
                   (apply function args)
                 (error 'fnn-raw-dispatch-trap
                        :message (format nil "raw-dispatch: ~(~a~) called outside the dispatcher (D40: only fnn-call may skip its carried guard)"
                                         raw)))))
           (install (raw)
             (let ((current (symbol-function raw))
                   (trap (gethash raw traps)))
               (cond ((null trap)
                      (let ((new (trap-for raw current)))
                        (setf (gethash raw captured) current
                              (gethash raw traps) new
                              (symbol-function raw) new)))
                     ((eq current trap) nil)
                     (t (fnn-raw-trap-fault
                         "raw-dispatch: ~(~a~) was redefined after its trap was installed; the new body is not captured"
                         raw))))
             raw)
           (counterpart (name)
             (let ((symbol (find-symbol (symbol-name name) "ACL2_*1*_ACL2")))
               (unless (and symbol (fboundp symbol))
                 (fnn-raw-trap-fault "ACL2 executable counterpart missing: ~a" name))
               symbol))
           (target (name)
             ;; the function a dispatcher call of NAME applies
             (let ((raw (and (not *fnn-dispatch-counterpart*) (gethash name dispatch))))
               (if raw (gethash raw captured) (counterpart name)))))

    (defun fnn-raw-trap-install (raw)
      "Capture RAW's function object and replace its binding by a trap;
idempotent; refuses a binding changed since its trap was recorded."
      (install raw))

    (defun fnn-raw-dispatch-set-hooks (check session)
      "Record io.lisp's entry guard and developer-image test, once."
      (when (or entry-check session-check)
        (fnn-raw-trap-fault "raw-dispatch: the dispatcher's hooks are already set"))
      (setq entry-check check session-check session)
      t)

    (defun fnn-raw-dispatch-apply (name &rest args)
      "The dispatcher: NAME's entry guard on ARGS, then its raw definition when
NAME is raw-dispatched and the counterpart selector is off, else its
executable counterpart, in a fresh extent."
      (unless entry-check
        (fnn-raw-trap-fault "raw-dispatch: no entry guard installed"))
      (funcall entry-check name args)
      (call-in-core (target name) args))

    (defun fnn-raw-dispatch-callback (name)
      "A callback that dispatches NAME's compiled raw definition, a fresh
extent per call; NIL when NAME is not raw-dispatched or not compiled."
      (let* ((raw (gethash name dispatch))
             (function (and raw (gethash raw captured))))
        (and function (compiled-function-p function)
             (lambda (&rest args) (call-in-core function args)))))

    (defun fnn-raw-session-extent (thunk)
      "Run THUNK (ACL2's loop: guard-checked *1* evaluation) in an extent, on
a developer image only."
      (unless (and session-check (funcall session-check))
        (fnn-raw-trap-fault "raw-dispatch: an ACL2 session extent is developer-only"))
      (call-in-core thunk nil))

    (defun fnn-raw-dispatch-target (name)
      "NAME's raw-dispatched function symbol, or NIL."
      (values (gethash name dispatch)))

    (defun fnn-dispatch-symbol (name)
      "The symbol whose definition a dispatcher call of NAME runs: its raw
symbol (bound to its trap) or its executable counterpart."
      (let ((raw (and (not *fnn-dispatch-counterpart*) (gethash name dispatch))))
        (or raw (counterpart name))))

    (defun fnn-raw-dispatch-captured-p (name)
      "T when a dispatcher call of NAME applies its captured object."
      (let ((raw (gethash name dispatch)))
        (and raw (not *fnn-dispatch-counterpart*)
             (eq (target name) (gethash raw captured)) t)))

    (defun fnn-raw-dispatch-names ()
      "The raw-dispatched entry names, sorted."
      (let ((names nil))
        (maphash (lambda (name raw) (declare (ignore raw)) (push name names)) dispatch)
        (sort names #'string< :key #'symbol-name)))

    (defun fnn-raw-dispatch-count () (hash-table-count dispatch))

    (defun fnn-raw-dispatch-traps-intact ()
      "Fault unless every raw-dispatched target's binding is still its trap; the count."
      (maphash (lambda (name raw)
                 (let ((trap (gethash raw traps)))
                   (unless (and trap (fboundp raw) (eq (symbol-function raw) trap))
                     (fnn-raw-trap-fault
                      "raw-dispatch: ~(~a~)'s target ~(~a~) is no longer trapped (redefined after installation)"
                      name raw))))
               dispatch)
      (hash-table-count traps))

    (defun fnn-raw-trap-self-probe ()
      "The mechanism on this image, whatever the table holds: a probe row is
installed as fnn-install-raw-dispatch installs one, called through the
dispatcher and directly, and removed (unwind-protect).  Three words."
      (let* ((raw 'fnn-raw-trap-probe-target)
             (probe 'fnn-raw-trap-probe)
             (original (symbol-function raw)))
        (flet ((outcome (thunk)
                 (handler-case (progn (funcall thunk) "returned")
                   (fnn-raw-dispatch-trap () "trapped")
                   (serious-condition () "passed"))))
          (unwind-protect
               (progn
                 (setf (gethash probe dispatch) raw)
                 (install raw)
                 (values (handler-case
                             (if (equal (multiple-value-list
                                         (let ((*fnn-dispatch-counterpart* nil))
                                           (fnn-raw-dispatch-apply probe 7 2)))
                                        '(5 (7 2)))
                                 "served" "wrong")
                           (serious-condition () "faulted"))
                         (outcome (lambda () (funcall raw 7 2)))
                         (outcome (lambda ()
                                    (funcall (intern (symbol-name raw) (symbol-package raw))
                                             7 2)))))
            (remhash probe dispatch)
            (remhash raw traps)
            (remhash raw captured)
            (setf (symbol-function raw) original)))))

    (defun fnn-install-raw-dispatch (&key (report t))
      "Fill the dispatch table from the fn-interfaces table of the loaded world:
the :raw-with and :raw-guarded entries, checked against the world; the count."
      (let ((wrld (w *the-live-state*)))
        (clrhash dispatch)
        (dolist (entry (table-alist 'fn-interfaces wrld))
          (let ((name (car entry))
                (theorems (cadr (assoc-keyword :raw-with (cdr entry))))
                (guarded (assoc-keyword :raw-guarded (cdr entry))))
            (when (or theorems guarded)
              (when guarded
                (let ((problem (fn-di-raw-guarded-problem name (cdr entry) wrld)))
                  (when problem
                    (error "fnn-install-raw-dispatch: ~a has a refused guarded declaration: ~s"
                           name problem))))
              ;; Recheck the loaded table at the dispatch installation boundary,
              ;; rather than assuming every table entry came from definterface.
              (let ((problem (and theorems (fn-di-raw-with-problem name (cdr entry) wrld))))
                (when problem
                  (error "fnn-install-raw-dispatch: ~a has a refused declaration: ~s"
                         name problem)))
              (multiple-value-bind (target-problem raw)
                  (if guarded (fn-di-raw-guarded-target name (cdr entry) wrld)
                    (values nil name))
                (when target-problem
                  (error "fnn-install-raw-dispatch: refused creator target for ~a: ~s" name target-problem))
                (when (and raw (macro-function raw))
                  (error "fnn-install-raw-dispatch: ~a resolved to a macro, not a raw function" name))
                (unless (and raw (fboundp raw))
                  (error "fnn-install-raw-dispatch: ~a has a raw declaration but no raw definition" name))
                (unless (eq (symbol-class name wrld) :common-lisp-compliant)
                  (error "fnn-install-raw-dispatch: ~a has a raw declaration but is ~a, not guard-verified"
                         name (symbol-class name wrld)))
                (when (and guarded (not (compiled-function-p (symbol-function raw))))
                  (error "fnn-install-raw-dispatch: ~a has no compiled guarded callback" name))
                (setf (gethash name dispatch) raw)
                (install raw)
                (when report
                  (format t "~&FN_RAW_DISPATCH ~(~a~) ~(~a~) invariant-risk=~a with=~(~a~)~%"
                          name (symbol-class name wrld)
                          (if (getpropc name 'invariant-risk nil wrld) "t" "nil")
                          (if guarded (cadr guarded) theorems)))))))
        (hash-table-count dispatch)))))
