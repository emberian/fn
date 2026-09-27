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
    ;; oneify-cltl-code-1).  48 of the 63 reads lane image-anatomy recorded.
    symbol-class
    ;; Signatures and guards: the *1* guard-failure forms
    ;; (save-ev-fncall-guard-er), ev-fncall, df-call, guard-raw.
    formals stobjs-in stobjs-out guard
    ;; Stobj dispatch: live-stobj and invariant-risk checks, abstract stobjs.
    invariant-risk absstobj-info stobj stobj-function
    ;; Attachments and constrained or built-in functions.
    attachment predefined constrainedp)
  "The execution properties, kept on every symbol that has them.")

(defparameter *fnn-world-read-pairs*
  '(;; LP's translate of the return-from-lp form (fn-native-entry state).
    (fn-native-entry . global-stobjs) (fn-native-entry . macro-body)
    (fn-native-entry . non-executablep)
    ;; Tables and world globals LP and translate read at start.
    (acl2-defaults-table . table-alist) (badge-table . table-alist)
    (boot-strap-flg . global-value) (known-package-alist . global-value)
    (operating-system . global-value) (project-dir-alist . global-value)
    (untouchable-fns . global-value)
    ;; lookup-world-index of event 0 and command 0 (the ACL2_SYSTEM_BOOKS
    ;; start path, replace-project-dir-alist): the landmarks' current values
    ;; and the indices, rebuilt below over the new world's bottom.
    (event-landmark . global-value) (command-landmark . global-value)
    (event-index . global-value) (command-index . global-value))
  "The other (symbol . property) pairs execution reads: lane image-anatomy's
recording of every world read across operator_verbs, hybrid_author,
starttls, implicit_tls and a guard violation (63 pairs, 48 of them
symbol-class), less those the execution properties cover, plus the start
path with ACL2_SYSTEM_BOOKS set.")

(defun fnn-world-keep-p (sym prop)
  (or (member prop *fnn-world-execution-properties* :test #'eq)
      (member (cons sym prop) *fnn-world-read-pairs* :test #'equal)))

(defun fnn-strip-world ()
  "Replace the installed world by its current kept triples (fnn-world-keep-p),
over a new bottom that keeps the event and command indices valid for event 0.
Returns the new world's length, the kept (symbol . property) pairs and the
omitted ones (a current value the rule dropped)."
  (let* ((state *the-live-state*)
         (key *current-acl2-world-key*)
         (pair (get 'current-acl2-world 'acl2-world-pair))
         (wrld (w state))
         (seen (make-hash-table :test 'eq))
         (syms nil)
         (event0 nil) (command0 nil) (project nil)
         (triples nil) (kept-keys nil) (omitted-keys nil))
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
            (when (and (not (fnn-world-keep-p s (car entry)))
                       (consp stack)
                       (not (eq (car stack) *acl2-property-unbound*)))
              (push (cons s (car entry)) omitted-keys))
            (when (and (fnn-world-keep-p s (car entry))
                       (consp stack)
                       (not (eq (car stack) *acl2-property-unbound*)))
              (push (cons s (car entry)) kept-keys)
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
    (values (length (w state)) kept-keys omitted-keys)))

(defun fnn-strip-build-residue ()
  "What the build session leaves that no node reads (lane image-anatomy's
census): the input-channel symbols of every file ACL2 opened while building
(85,001 on 2026-09-26, their plists holding the files' names and state),
ACL2's own documentation text, defconst's redundancy discriminators (the raw
values kept to recognise a re-submitted defconst; they keep the
documentation alive), the build-sized hons space and memoize call array.
Returns the counts it printed."
  (let ((channels 0) (discriminators 0)
        (p (find-package "ACL2-INPUT-CHANNEL")))
    ;; Closed channels only: every file the build read.  An open channel's
    ;; symbol (standard input, the live stdin of the saved process) keeps.
    (do-symbols (s p)
      (when (and (eq (symbol-package s) p)
                 (plusp (length (symbol-name s)))
                 (char= (char (symbol-name s) 0) #\/))
        (incf channels)
        (setf (symbol-plist s) nil)
        (unintern s p)))
    (sb-kernel:%set-symbol-global-value (quote *acl2-system-documentation*) nil)
    (do-all-symbols (s)
      (when (get s 'redundant-raw-lisp-discriminator)
        (incf discriminators)
        (remprop s 'redundant-raw-lisp-discriminator)))
    ;; A small hons space in place of the build's (ACL2's own constructor;
    ;; honsing stays correct, it only re-norms what it meets).  None at all
    ;; would make every start build a default-sized one.
    (setq *default-hs*
          (hl-hspace-init :str-ht-size 100 :nil-ht-size 100 :cdr-ht-size 100
                          :cdr-ht-eql-size 100 :addr-ht-size 100 :sbits-size 100
                          :other-ht-size 100 :fal-ht-size 100 :persist-ht-size 100))
    ;; The memoize call array is (2 x the most memoized functions)^2 counters;
    ;; ACL2's own resize path, to what the functions memoized now need.
    (let ((n (* 2 (+ 2 *max-symbol-to-fixnum*))))
      (when (< n *2max-memoize-fns*)
        (setq *2max-memoize-fns* n)
        (sync-memoize-call-array)))
    (list channels discriminators)))

;;; ---------------------------------------------------------------------------
;;; The dependency set (gpt-6's wave-5 review s.4).  The stripped image keeps
;;; exactly the (symbol . property) pairs the rule above selects from the
;;; certified session's world; the build writes that set beside the image,
;;; versioned, with the pairs the rule omitted, so that a qualification run
;;; (host/native/world-deps-check.lisp) can trap a world read outside the set
;;; and tell a property the full image never had (the default answer is the
;;; full image's too) from one this strip removed (the answers differ).
;;;
;;;   fn-world-deps 1
;;;   rule-properties P ...          *fnn-world-execution-properties*
;;;   rule-pairs (S . P) ...         *fnn-world-read-pairs*
;;;   kept N
;;;   omitted M
;;;   K S P                          N lines, sorted
;;;   O S P                          M lines, sorted

(defconstant +fnn-world-deps-version+ 1)

(defmacro fnn-with-world-key-printing (&body body)
  `(let ((*package* (find-package "ACL2")) (*print-pretty* nil)
         (*print-readably* nil) (*print-case* :upcase) (*print-escape* t)
         (*print-base* 10) (*print-radix* nil))
     ,@body))

(defun fnn-world-key-string (sym prop)
  "The one printed form of a (symbol . property) pair the build writes and
the check compares."
  (fnn-with-world-key-printing (format nil "~s ~s" sym prop)))

(defun fnn-write-world-deps (path kept omitted)
  (let ((k (sort (mapcar (lambda (c) (fnn-world-key-string (car c) (cdr c))) kept)
                 #'string<))
        (o (sort (mapcar (lambda (c) (fnn-world-key-string (car c) (cdr c))) omitted)
                 #'string<)))
    (with-open-file (s path :direction :output :if-exists :supersede
                            :external-format :utf-8)
      (fnn-with-world-key-printing
       (format s "fn-world-deps ~d~%" +fnn-world-deps-version+)
       (format s "rule-properties~{ ~s~}~%" *fnn-world-execution-properties*)
       (format s "rule-pairs~{ ~s~}~%" *fnn-world-read-pairs*)
       (format s "kept ~d~%omitted ~d~%" (length k) (length o))
       (dolist (line k) (format s "K ~a~%" line))
       (dolist (line o) (format s "O ~a~%" line))))
    (list (length k) (length o))))

(defun fnn-save-world-flavor (flavor image)
  "The world build.lisp saves: FLAVOR `full' keeps the certified session's
world untouched (the developer and reference images); `stripped' (or unset)
strips it and writes IMAGE.world-deps.  The marker line names which, and
tools/build_native_host.sh checks it against the flavor it asked for."
  (cond ((equal flavor "full")
         (format t "~&FN_NATIVE_WORLD_FULL triples=~d~%" (length (w *the-live-state*))))
        ((or (null flavor) (equal flavor "stripped"))
         (multiple-value-bind (n kept omitted) (fnn-strip-world)
           (let ((counts (fnn-write-world-deps (concatenate 'string image ".world-deps")
                                               kept omitted))
                 (residue (fnn-strip-build-residue)))
             (format t "~&FN_NATIVE_WORLD_STRIPPED triples=~d residue=~s deps=~d kept ~d omitted~%"
                     n residue (first counts) (second counts)))))
        (t (error "FN_NATIVE_WORLD must be full or stripped: ~s" flavor))))
