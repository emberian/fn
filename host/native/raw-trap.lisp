;;; host/native/raw-trap.lisp -- D40 raw dispatch: the dispatch table, the
;;; per-thread extent and the trap.  Loaded FIRST in the raw block of every
;;; build script (host/native/build.lisp, build-dtn.lisp,
;;; build-store-test.lisp), which installs the table right after it
;;; (fnn-install-raw-dispatch) and before it loads any other raw host file.
;;;
;;; WHY A TRAP.  D40 lets the host run a :raw-with entry's guard-verified
;;; definition without evaluating its carried guard conjuncts, because the
;;; only way in is the dispatcher (fnn-call), whose entry guard runs first.
;;; A scan of the host's source (tools/raw_dispatch_rule.py) cannot see an
;;; intern-built name, a defconstant initializer, a redefinition or a file it
;;; never read (Codex r34), so the guarantee lives in the image: at
;;; installation each raw-dispatched function OBJECT is captured and the
;;; symbol's function binding is REPLACED by a trap.  The trap runs the
;;; captured object only inside a dispatcher extent -- where the caller is
;;; ACL2 code (the raw body of a guard-verified function, or a *1*
;;; counterpart that has just checked its guard) -- and otherwise signals
;;; fnn-raw-dispatch-trap.  A host call of a raw-dispatched function that
;;; skips the dispatcher therefore faults however it is spelled.
;;;
;;; THE EXTENT IS A PER-THREAD SLOT.  The slot is a special variable whose
;;; symbol is uninterned and held only by this file's closures: no package
;;; lookup, reader or intern reaches it, so no host form can name, bind or
;;; set it.  A dispatcher call binds it (PROGV) for the call's dynamic
;;; extent; SBCL keeps a special binding in the binding thread's own
;;; storage, so the trap's test is one thread-local read, with no table, no
;;; lock and no allocation on any call (the 10-02 form put a :synchronized
;;; hash-table write and remhash on every fnn-call: Codex r69 L1).  What a
;;; binding gives, and what it does not:
;;;   - it ends when the dispatcher call returns or unwinds: nothing kept
;;;     past the call grants anything (there is no token to keep);
;;;   - a thread started inside the extent does not inherit it: SBCL starts
;;;     every thread on the global value, which is NIL;
;;;   - binding a symbol of the same name grants nothing: it is another
;;;     symbol.
;;;
;;; What makes the rest hold (the Codex r63 and r69 findings):
;;;   r63 F1  The table, the captured objects, the traps and the callbacks
;;;           are LEXICAL to the closure below.  Nothing returns a captured
;;;           object: callers get the dispatcher's answer
;;;           (fnn-raw-dispatch-apply), a callback that enters the extent
;;;           itself (fnn-raw-dispatch-callback), a symbol or a boolean.
;;;   r63 F2  Every build script loads this file before any other raw host
;;;           file and installs right after it, so no raw host file and no
;;;           load-time form of one can capture a raw-dispatched function
;;;           object before its trap is in place (tests/
;;;           test_native_raw_dispatch_trap.py checks the three scripts).
;;;   r63 F4  Installing over a recorded trap whose binding has changed (a
;;;           redefinition after installation) is refused; the new body is
;;;           never captured; fnn-raw-dispatch-traps-intact refuses it at
;;;           the end of the build and at every start (fnn-main).
;;;   r69 F1  The entry guard is fnn-call's, run before the dispatcher and
;;;           outside fnn-call's handler: its fault keeps its class and text.
;;;   r69 F2  This file defines only its own condition, so a fixture that
;;;           loads io.lisp's forms alone keeps io.lisp's conditions.
;;;   r69 F4  Whether an ACL2 session may run in an extent (`fn acl2
;;;           session', developer images) is decided once, by
;;;           fnn-raw-trap-seal at image build, and held lexically: no
;;;           special variable rebinds it.  The seal also closes
;;;           installation, so nothing after the build re-blesses a binding.
;;;
;;; What the trap does not see: host code running INSIDE an extent (an
;;; attachment or callback the core calls back into) -- none of the
;;; raw-dispatched functions is reachable that way by a host body today,
;;; and tools/raw_dispatch_rule.py (the early lint) refuses a host body that
;;; names one; a call ACL2 compiled inline into its caller (the caller is
;;; then itself ACL2 code); host code that reaches into SBCL internals
;;; (closure environments, code constants), which is outside any claim here.

(in-package "ACL2")

(define-condition fnn-raw-dispatch-trap (error)
  ((message :initarg :message :reader fnn-raw-trap-message))
  (:report (lambda (c s) (write-string (fnn-raw-trap-message c) s))))

(defvar *fnn-dispatch-counterpart* nil
  "T when the developer selector keeps the executable-counterpart path.  Safe
for any caller to set: the counterpart evaluates the entry's whole guard.")

(defun fnn-raw-trap-fault (control &rest args)
  (error 'fnn-raw-dispatch-trap :message (apply #'format nil control args)))

(defun fnn-raw-trap-outside (raw)
  (fnn-raw-trap-fault
   "raw-dispatch: ~(~a~) called outside the dispatcher (D40: only fnn-call may skip its carried guard)"
   raw))

(defun fnn-raw-trap-probe-target (x y)
  "The raw-traps probe's target (never an ACL2 function)."
  (values (- x y) (list x y)))

;; The largest arity with an allocation-free trap and callback; an entry
;; with more formals (none today) gets the &rest form.
(defconstant +fnn-raw-trap-fixed-arity+ 16)

(let* ((slot (make-symbol "FNN-RAW-EXTENT"))   ; the per-thread slot
       (slots (list slot))
       (on (list t))
       (dispatch (make-hash-table :test 'eq))   ; entry name -> raw symbol
       (creators (make-hash-table :test 'eq))   ; entry name -> t (startup creators)
       (callbacks (make-hash-table :test 'eq))  ; entry name -> extent-entering closure
       (captured (make-hash-table :test 'eq))   ; raw symbol -> function object
       (traps (make-hash-table :test 'eq))      ; raw symbol -> its trap
       (arities (make-hash-table :test 'eq))    ; raw symbol -> formals count, -1 unknown
       (sealed nil)
       (session-p nil))
  (proclaim `(special ,slot))
  (setf (symbol-value slot) nil)
  (labels ((in-extent-p () (symbol-value slot))
           (refuse-sealed (what)
             (when sealed
               (fnn-raw-trap-fault "raw-dispatch: ~a after the image build sealed the table" what))))
    (macrolet ((by-arity (n (params) fixed rest)
                 ;; (case N (0 FIXED[params := ()]) ... (t REST)), FIXED a
                 ;; lambda over exactly K parameters for each K up to the bound
                 `(case ,n
                    ,@(loop for k from 0 to +fnn-raw-trap-fixed-arity+
                            collect (let ((ps (loop for i below k
                                                    collect (make-symbol (format nil "A~d" i)))))
                                      `(,k (lambda ,ps ,(subst ps params fixed)))))
                    (t ,rest))))
      (labels ((trap-for (raw function arity)
                 (by-arity arity (params)
                           (if (in-extent-p)
                               (funcall function . params)
                             (fnn-raw-trap-outside raw))
                           (lambda (&rest args)
                             (if (in-extent-p)
                                 (apply function args)
                               (fnn-raw-trap-outside raw)))))
               (callback-for (function arity)
                 (by-arity arity (params)
                           (progv slots on (funcall function . params))
                           (lambda (&rest args) (progv slots on (apply function args)))))
               (arity-of (raw)
                 (let ((formals (getpropc raw 'formals :none (w *the-live-state*))))
                   (if (eq formals :none) -1 (length formals))))
               (install (raw)
                 (let ((current (symbol-function raw))
                       (trap (gethash raw traps)))
                   (cond ((null trap)
                          (let* ((arity (arity-of raw))
                                 (new (trap-for raw current arity)))
                            (setf (gethash raw arities) arity
                                  (gethash raw captured) current
                                  (gethash raw traps) new
                                  (symbol-function raw) new)))
                         ((eq current trap) nil)
                         (t (fnn-raw-trap-fault
                             "raw-dispatch: ~(~a~) was redefined after its trap was installed; the new body is not captured"
                             raw))))
                 raw)
               (target (name)
                 ;; the function a dispatcher call of NAME applies
                 (let ((raw (and (or (gethash name creators) (not *fnn-dispatch-counterpart*))
                                 (gethash name dispatch))))
                   (if raw (gethash raw captured) (fnn-counterpart name)))))

        (defun fnn-raw-dispatch-reset ()
          "Empty the table before an installation; the traps stay installed."
          (refuse-sealed "a reset")
          (clrhash dispatch) (clrhash creators) (clrhash callbacks)
          t)

        (defun fnn-raw-trap-install (name raw &key creator)
          "Dispatch NAME to RAW's captured function object, replacing RAW's
binding by a trap (idempotent; refuses a binding changed since its trap was
recorded).  CREATOR: a startup creator, dispatched raw in either mode."
          (refuse-sealed "an installation")
          (install raw)
          (setf (gethash name dispatch) raw)
          (when creator (setf (gethash name creators) t))
          (let ((function (gethash raw captured)))
            (when (compiled-function-p function)
              (setf (gethash name callbacks) (callback-for function (gethash raw arities)))))
          raw)

        (defun fnn-raw-trap-seal (&key developer)
          "Close installation at the end of the image build, once.  DEVELOPER:
whether `fn acl2 session' may run ACL2's loop in an extent."
          (when sealed
            (fnn-raw-trap-fault "raw-dispatch: the table is already sealed"))
          ;; Assign the slot's thread-local storage index now, at build,
          ;; rather than on the first served call.
          (progv slots on (in-extent-p))
          (setq sealed t session-p (and developer t))
          (hash-table-count dispatch))

        (defun fnn-raw-trap-sealed-p () sealed)

        (defun fnn-raw-dispatch-apply (name args)
          "The dispatcher: NAME's captured raw definition when NAME is
raw-dispatched (and the counterpart selector is off, or NAME is a startup
creator), else its executable counterpart; applied to ARGS in an extent.
fnn-call runs the entry guard before it."
          (let ((function (target name)))
            (progv slots on (apply function args))))

        (defun fnn-raw-dispatch-callback (name)
          "A compiled closure that enters an extent and runs NAME's captured
raw definition (same arity, no allocation per call); NIL when NAME is not
raw-dispatched or its definition is not compiled."
          (values (gethash name callbacks)))

        (defun fnn-raw-session-extent (thunk)
          "Run THUNK (ACL2's loop: guard-checked *1* evaluation) in an extent,
on an image sealed as a developer image only."
          (unless (and sealed session-p)
            (fnn-raw-trap-fault "raw-dispatch: an ACL2 session extent is developer-only"))
          (progv slots on (funcall thunk)))

        (defun fnn-raw-dispatch-target (name)
          "NAME's raw-dispatched function symbol, or NIL."
          (values (gethash name dispatch)))

        (defun fnn-raw-dispatch-arity (name)
          "The formals count of NAME's raw target (its trap's arity), -1 when
the world gives none (the trap then takes any arguments); NIL when NAME is
not raw-dispatched."
          (let ((raw (gethash name dispatch)))
            (and raw (gethash raw arities))))

        (defun fnn-raw-dispatch-creator-p (name)
          (and (gethash name creators) t))

        (defun fnn-dispatch-symbol (name)
          "The symbol whose definition a dispatcher call of NAME runs: its raw
symbol (bound to its trap) or its executable counterpart."
          (let ((raw (and (or (gethash name creators) (not *fnn-dispatch-counterpart*))
                          (gethash name dispatch))))
            (or raw (fnn-counterpart name))))

        (defun fnn-raw-dispatch-captured-p (name)
          "T when a dispatcher call of NAME applies its captured object."
          (let ((raw (gethash name dispatch)))
            (and raw (eq (target name) (gethash raw captured)) t)))

        (defun fnn-raw-dispatch-names ()
          "The raw-dispatched entry names, sorted."
          (let ((names nil))
            (maphash (lambda (name raw) (declare (ignore raw)) (push name names)) dispatch)
            (sort names #'string< :key #'symbol-name)))

        (defun fnn-raw-dispatch-count () (hash-table-count dispatch))

        (defun fnn-raw-dispatch-traps-intact ()
          "Fault unless the table is sealed and every raw-dispatched target's
binding is still its trap; the count."
          (unless sealed
            (fnn-raw-trap-fault "raw-dispatch: the table was never sealed (fnn-raw-trap-seal)"))
          (maphash (lambda (name raw)
                     (let ((trap (gethash raw traps)))
                       (unless (and trap (fboundp raw) (eq (symbol-function raw) trap))
                         (fnn-raw-trap-fault
                          "raw-dispatch: ~(~a~)'s target ~(~a~) is no longer trapped (redefined after installation)"
                          name raw))))
                   dispatch)
          (hash-table-count dispatch))

        (defun fnn-raw-trap-self-probe ()
          "The mechanism on this image, whatever the table holds: a probe row is
installed as fnn-install-raw-dispatch installs one, called through the
dispatcher, through its callback, directly, by an interned symbol, under a
binding of a same-named symbol and from a thread started inside an extent,
then removed (unwind-protect).  Six words."
          (let* ((raw 'fnn-raw-trap-probe-target)
                 (probe 'fnn-raw-trap-probe)
                 (original (symbol-function raw)))
            (flet ((outcome (thunk)
                     (handler-case (progn (funcall thunk) "returned")
                       (fnn-raw-dispatch-trap () "trapped")
                       (serious-condition () "failed")))
                   (served (thunk)
                     (handler-case (if (equal (multiple-value-list (funcall thunk)) '(5 (7 2)))
                                       "served" "wrong")
                       (serious-condition () "faulted"))))
              (unwind-protect
                   (progn
                     (setf (gethash probe dispatch) raw)
                     (install raw)
                     (setf (gethash probe callbacks) (callback-for (gethash raw captured) 2))
                     (values
                      (served (lambda ()
                                (let ((*fnn-dispatch-counterpart* nil))
                                  (fnn-raw-dispatch-apply probe (list 7 2)))))
                      (served (lambda () (funcall (fnn-raw-dispatch-callback probe) 7 2)))
                      (outcome (lambda () (funcall raw 7 2)))
                      (outcome (lambda ()
                                 (funcall (intern (symbol-name raw) (symbol-package raw)) 7 2)))
                      (outcome (lambda ()
                                 (progv (list (make-symbol "FNN-RAW-EXTENT")) (list t)
                                   (funcall raw 7 2))))
                      (let ((result nil))
                        (progv slots on
                          (sb-thread:join-thread
                           (sb-thread:make-thread
                            (lambda () (setq result (outcome (lambda () (funcall raw 7 2))))))))
                        result)))
                (remhash probe dispatch)
                (remhash probe callbacks)
                (remhash raw traps)
                (remhash raw arities)
                (remhash raw captured)
                (setf (symbol-function raw) original)))))))))

(defun fnn-install-raw-dispatch (&key (report t))
  "Fill the dispatch table from the fn-interfaces table of the loaded world:
the :raw-with and :raw-guarded entries, each re-checked against the world;
the count.  An unknown or unverified target stops the build."
  (let ((wrld (w *the-live-state*)))
    (fnn-raw-dispatch-reset)
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
            ;; ACL2's loaded-world predicate limits the creator role to the
            ;; exact creator and its validated compiled target.
            (fnn-raw-trap-install name raw
                                  :creator (and (fn-di-raw-creatorp name (cdr entry) wrld) t))
            (when report
              (format t "~&FN_RAW_DISPATCH ~(~a~) ~(~a~) invariant-risk=~a with=~(~a~)~%"
                      name (symbol-class name wrld)
                      (if (getpropc name 'invariant-risk nil wrld) "t" "nil")
                      (if guarded (cadr guarded) theorems)))))))
    (fnn-raw-dispatch-count)))
