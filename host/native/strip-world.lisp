; host/native/strip-world.lisp -- the saved image's logical world, reduced
; to what execution reads (lane image-floor, HST-017).
;
; Loaded by host/native/build.lisp in raw Lisp after `:q', after the last
; event and immediately before save-exec.  The session has certified-book
; events only; the image never runs another event, never proves and never
; retracts (every entry is fn-native-entry through fnn-call).  What the prover,
; the undo stack and the history commands read is dropped; what the executable
; counterparts, guard checking, stobj and attachment dispatch, LP's start and
; error reporting read is kept, at its current value.  The kept list and the
; ACL2 8.7 source lines that read each property are in
; planning/evidence/image-floor-2026-09-26.md, section 2.
;
; It decides nothing ACL2 decides: no function body, guard, symbol-class or
; attachment changes; the compiled definitions are untouched (they live in
; symbol-function cells, not in the world).  The image's behaviour is checked
; by the native modules the lane's record names, on this image.
(in-package "ACL2")

(defparameter *fnn-world-execution-properties*
  '(;; The *1* dispatch: (symbol-class 'fn (w *the-live-state*)) decides
    ;; whether the guard-verified raw body runs (interface-raw.lisp,
    ;; oneify-cltl-code-1).
    symbol-class
    ;; Signatures read by the *1* guard-failure forms (save-ev-fncall-guard-er,
    ;; ev-fncall-guard-er), by ev-fncall and by translate of LP's return form.
    formals stobjs-in stobjs-out guard
    ;; Stobj dispatch: live-stobj checks, invariant-risk checks, accessor
    ;; arrays (update-wrld-structures), abstract and congruent stobjs.
    invariant-risk stobj stobj-function stobj-constant stobj-live-var
    absstobj-info congruent-stobj-rep accessor-names global-stobjs
    ;; Attachments and constrained functions: an unattached constrained call
    ;; reports through these; ev refuses a non-executable function by them.
    attachment constrainedp hereditarily-constrained-fnnames
    non-executablep predefined classicalp
    ;; Translate of the return-from-lp form and of any form LP reads.
    macro-args macro-body const
    ;; Tables (acl2-defaults-table, untrans-table, macro-aliases-table,
    ;; guard-msg-table, memoize-table, ...) and every world global at its
    ;; current value: global-val of an absent name is a hard error.
    table-alist table-guard global-value))

(defun fnn-strip-world (keep)
  "Replace the installed world by its current KEEP triples, over a new
bottom that keeps the event and command indices valid for event 0."
  (let* ((state *the-live-state*)
         (key *current-acl2-world-key*)
         (pair (get 'current-acl2-world 'acl2-world-pair))
         (wrld (w state))
         (seen (make-hash-table :test 'eq))
         (syms nil)
         (event0 nil) (command0 nil) (project nil)
         (triples nil))
    (unless (and pair (eq (car pair) wrld) (eq (cdr pair) key))
      (error "fnn-strip-world: the current world is not the installed one"))
    (dolist (trip wrld)
      (unless (gethash (car trip) seen)
        (setf (gethash (car trip) seen) t)
        (push (car trip) syms))
      ;; Event 0 and command 0 (enter-boot-strap-mode); the world also
      ;; holds a -1 landmark below them.
      (when (eq (cadr trip) 'global-value)
        (case (car trip)
          (event-landmark
           (when (eql 0 (access-event-tuple-number (cddr trip)))
             (setq event0 trip)))
          (command-landmark
           (when (eql 0 (access-command-tuple-number (cddr trip)))
             (setq command0 trip))))))
    (unless (and event0 command0)
      (error "fnn-strip-world: no event 0 or command 0 landmark"))
    (setq wrld nil)
    (dolist (s syms)
      (let ((kept nil))
        (dolist (entry (get s key))
          (let ((stack (cdr entry)))
            (when (and (member (car entry) keep)
                       (consp stack)
                       (not (eq (car stack) *acl2-property-unbound*)))
              ;; The value stack keeps its current value only: no retraction.
              (let ((doublet (list (car entry) (car stack))))
                (push doublet kept)
                (let ((trip (list* s (car entry) (car stack))))
                  (if (and (eq s 'project-dir-alist) (eq (car entry) 'global-value))
                      (setq project trip)
                      (push trip triples)))))))
        (if kept
            (setf (get s key) (nreverse kept))
            (remprop s key))))
    (unless project
      (error "fnn-strip-world: no project-dir-alist global"))
    ;; The bottom: command 0, event 0, then the project-dir-alist triple that
    ;; LP's replace-project-dir-alist finds by walking from event 0.
    (let* ((bottom (list (list* 'command-landmark 'global-value (cddr command0))
                         (list* 'event-landmark 'global-value (cddr event0))
                         project))
           (new (nconc triples bottom))
           (command-tail (last new 3))
           (event-tail (last new 2)))
      (flet ((set-global (name value)
               (let ((doublet (assoc-eq 'global-value (get name key))))
                 (unless doublet (error "fnn-strip-world: no global ~s" name))
                 (setf (cadr doublet) value)
                 (dolist (trip new)
                   (when (and (eq (car trip) name) (eq (cadr trip) 'global-value))
                     (setf (cddr trip) value))))))
        ;; Zap tables of one entry: event 0 and command 0 (lookup-world-index).
        (set-global 'event-index (list 0 event-tail))
        (set-global 'command-index (list 0 command-tail)))
      (setf (car pair) new)
      (f-put-global 'current-acl2-world new state))
    ;; Session state that holds old worlds: the undo ring, the proof-output
    ;; world stack (push-current-acl2-world, for pso) and its saved output.
    (f-put-global 'undone-worlds-kill-ring nil state)
    (f-put-global 'last-make-event-expansion nil state)
    (f-put-global 'acl2-world-alist nil state)
    (f-put-global 'saved-output-reversed nil state)
    (setq *bad-wrld* nil)
    (sb-ext:gc :full t)
    (length (w state))))
