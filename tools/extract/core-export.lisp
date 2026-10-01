; tools/extract/core-export.lisp -- the front end's export for the Common
; Lisp product (lane extract-writable, 2026-09-28): the SBCL core with fn's
; functions and host/native, and nothing of ACL2.  Loaded after frontend.lisp
; in the extraction session (the image's world).
;
;   (xt-core-export TOKENS "build/core/core.json" "build/core/core-world.lisp" state)
;
; TOKENS: every word of host/native/*.lisp (tools/extract/core.sh scans
; them), upcased.  Writes
;   core.json        the IR (xt-extract-with) whose roots are the words that
;                    name an fn function of the world, every root a boundary
;                    function (host/native calls each through fnn-call), and
;                    the packages ("packages": name and imports);
;   core-world.lisp  what host/native and the extracted code read of ACL2's
;                    state and world at run time, as its values in this
;                    session: the state globals they name, the defconsts
;                    host/native names, and each root's formals, stobjs-in
;                    and guard (fnn-entry-guard-spec, fnn-trailing-kind).
(in-package "ACL2")
(program)
(set-state-ok t)

; ACL2 system names the Common Lisp runtime provides itself
; (tools/extract/clruntime.lisp): never roots.
(defconst *xt-core-runtime-names*
  '(w getpropc getprop user-stobj-alist f-get-global f-put-global f-boundp-global
    get-global put-global boundp-global stobjs-in stobjs-out symbol-class guard
    table-alist get-stobj-creator get-stobj-recognizer get-event global-symbol state-p state-p1
    hard-error illegal throw-nonexec-error fmt-to-comment-window cw-print-base-radix))

(defun xt-core-root-p (s w)
  (and (symbolp s)
       (not (equal (symbol-package-name s) "COMMON-LISP"))
       (not (member-eq s *xt-core-runtime-names*))
       (not (eq (getpropc s 'formals :none w) :none))
       (not (member-eq (cadr (xt-classify s w)) '(:blocker :prim :shim)))))

(defun xt-sym-names (syms)
  (if (endp syms) nil (cons (symbol-name (car syms)) (xt-sym-names (cdr syms)))))

(defun xt-core-roots (tokens w acc)
  (if (endp tokens) (reverse acc)
    (let ((s (intern-in-package-of-symbol (car tokens) 'xt-core-roots)))
      (xt-core-roots (cdr tokens) w
                     (if (and (xt-core-root-p s w) (not (member-eq s acc))) (cons s acc) acc)))))

; The live stobjs host/native fetches by name (user-stobj-alist): each stobj a
; word names, by its creator, so the closure holds it.
(defun xt-core-stobj-creators (tokens w acc)
  (if (endp tokens) (reverse acc)
    (let* ((s (intern-in-package-of-symbol (car tokens) 'xt-core-roots))
           (prop (getpropc s 'stobj nil w))
           ; (stobj-property (RECOGNIZER . CREATOR) ...)
           (creator (and (consp prop) (consp (cdr prop)) (consp (cadr prop)) (cdr (cadr prop)))))
      (xt-core-stobj-creators (cdr tokens) w
                              (if (and creator (symbolp creator) (not (member-eq creator acc)))
                                  (cons creator acc)
                                acc)))))

; The fn macros host/native's raw Lisp calls (a macro is expanded where the
; host file is compiled: (fn-profile-limit :gc-nursery-mib) in io.lisp): each
; exported with its lambda list and translated body, which cl.py emits as a
; Common Lisp macro; the body's callees join the roots.
(defun xt-core-macros (tokens w acc)
  (if (endp tokens) (reverse acc)
    (let* ((s (intern-in-package-of-symbol (car tokens) 'xt-core-roots))
           (n (symbol-name s))
           (body (getpropc s 'macro-body nil w)))
      (xt-core-macros (cdr tokens) w
                      (if (and body (< 3 (length n)) (equal (subseq n 0 3) "FN-")
                               (not (assoc-eq s acc)))
                          (cons (list s (getpropc s 'macro-args nil w) body) acc)
                        acc)))))

(defun xt-json-macros (macros first channel state)
  (if (endp macros) state
    (let* ((m (car macros))
           (state (if first state (princ$ "," channel state)))
           (state (princ$ "{\"name\":" channel state))
           (state (xt-json-sym (car m) channel state))
           (state (princ$ ",\"args\":" channel state))
           (state (xt-json-datum (cadr m) channel state))
           (state (princ$ ",\"body\":" channel state))
           (state (xt-json-term (caddr m) channel state))
           (state (princ$ "}" channel state)))
      (xt-json-macros (cdr macros) nil channel state))))

(defun xt-macro-callees (macros acc)
  (if (endp macros) acc
    (xt-macro-callees (cdr macros) (xt-callees (caddr (car macros)) acc))))

(defun xt-core-consts (tokens w acc)
  (if (endp tokens) (reverse acc)
    (let ((s (intern-in-package-of-symbol (car tokens) 'xt-core-roots)))
      (xt-core-consts (cdr tokens) w
                      (let ((c (getpropc s 'const nil w)) (n (symbol-name s)))
                        (if (and c (< 2 (length n)) (eql (char n 0) #\*)
                                 (eql (char n (1- (length n))) #\*)
                                 (not (member-eq s (strip-cars acc))))
                            (cons (cons s (unquote c)) acc)
                          acc))))))

; The state globals the extracted bodies name: (G 'SYM ...) for G a global
; accessor.
(defconst *xt-global-accessors*
  '(get-global f-get-global put-global f-put-global boundp-global f-boundp-global))

(mutual-recursion
 (defun xt-term-globals (term acc)
   (cond ((or (variablep term) (fquotep term)) acc)
         ((flambda-applicationp term)
          (xt-term-globals (lambda-body (ffn-symb term)) (xt-terms-globals (fargs term) acc)))
         (t (xt-terms-globals (fargs term)
                              (if (and (member-eq (ffn-symb term) *xt-global-accessors*)
                                       (consp (fargs term)) (quotep (fargn term 1))
                                       (symbolp (unquote (fargn term 1))))
                                  (add-to-set-eq (unquote (fargn term 1)) acc)
                                acc)))))
 (defun xt-terms-globals (terms acc)
   (if (endp terms) acc (xt-terms-globals (cdr terms) (xt-term-globals (car terms) acc)))))

(defun xt-entries-globals (entries acc)
  (if (endp entries) acc
    (xt-entries-globals (cdr entries)
                        (if (eq (cadr (car entries)) :defun)
                            (xt-term-globals (caddr (car entries)) acc)
                          acc))))

(defun xt-token-globals (tokens acc state)
  ; host/native's own (f-get-global 'fn-... state) reads
  (if (endp tokens) acc
    (let ((s (intern-in-package-of-symbol (car tokens) 'xt-core-roots)))
      (xt-token-globals (cdr tokens)
                        (if (and (boundp-global s state)
                                 (or (and (<= 3 (length (symbol-name s)))
                                          (equal (subseq (symbol-name s) 0 3) "FN-"))
                                     (member-eq s '(guard-checking-on check-invariant-risk))))
                            (add-to-set-eq s acc)
                          acc)
                        state))))

(defun xt-print (x channel state)
  (let ((state (print-object$ x channel state)))
    (newline channel state)))

(defun xt-print-globals (syms channel state)
  (cond ((endp syms) state)
        ((or (eq (car syms) 'current-acl2-world) (not (boundp-global (car syms) state)))
         (xt-print-globals (cdr syms) channel state))
        (t (let ((state (xt-print (list 'xl-set-global (list 'quote (car syms))
                                        (list 'quote (f-get-global (car syms) state)))
                                  channel state)))
             (xt-print-globals (cdr syms) channel state)))))

(defun xt-print-consts (consts channel state)
  (if (endp consts) state
    (let ((state (xt-print (list 'defparameter (caar consts) (list 'quote (cdar consts))) channel state)))
      (xt-print-consts (cdr consts) channel state))))

(defun xt-entry-fns (entries acc)
  (if (endp entries) (reverse acc)
    (xt-entry-fns (cdr entries)
                  (if (member-eq (cadr (car entries)) '(:defun :alias :stobj-prim))
                      (cons (car (car entries)) acc)
                    acc))))

(defun xt-props (roots w acc)
  (if (endp roots) (reverse acc)
    (xt-props (cdr roots) w
              (cons (list (car roots) (formals (car roots) w) (stobjs-in (car roots) w)
                          (guard (car roots) nil w))
                    acc))))

; Installation reads the selected world's declarations and their citations,
; not an inferred class or a host-created dispatch table.  Preserve raw
; property presence (including NIL), then add the system queries whose value
; is computed by ACL2 rather than stored verbatim.
(defun xt-interface-raw-roots (entries w)
  (if (endp entries) nil
    (let ((entry (car entries)))
      (if (and (or (assoc-keyword :raw-with (cdr entry))
                   (assoc-keyword :raw-guarded (cdr entry)))
               (xt-core-root-p (car entry) w))
          (cons (car entry) (xt-interface-raw-roots (cdr entries) w))
        (xt-interface-raw-roots (cdr entries) w)))))

(defun xt-interface-citations (entries)
  (if (endp entries) nil
    (append (cadr (assoc-keyword :raw-with (cdar entries)))
            (xt-interface-citations (cdr entries)))))

(defun xt-snapshot-stored-properties (name trips seen)
  (if (endp trips) nil
    (let ((trip (car trips)))
      (if (and (eq (car trip) name)
               (not (member-eq (cadr trip) seen))
               (member-eq (cadr trip)
                          '(formals stobjs-in guard symbol-class stobj
                            absstobj-info stobj-function unnormalized-body
                            theorem invariant-risk predefined const table-alist)))
          (let ((tail (xt-snapshot-stored-properties
                       name (cdr trips) (cons (cadr trip) seen))))
            (if (eq (cddr trip) *acl2-property-unbound*) tail
              (cons (cons (cadr trip) (cddr trip)) tail)))
        (xt-snapshot-stored-properties name (cdr trips) seen)))))

(defun xt-world-snapshot (names w)
  (if (endp names) nil
    (let* ((name (car names))
           (functionp (not (eq (getpropc name 'formals :none w) :none)))
           (stobjp (or (eq name 'state) (getpropc name 'stobj nil w)))
           (computed
            (append
             (and (eq name 'fn-interfaces)
                  (list (cons 'table-alist (table-alist name w))))
             (and functionp
                  (list (cons 'guard (guard name nil w))
                        (cons 'symbol-class (symbol-class name w))
                        (cons 'stobjs-out (stobjs-out name w))))
             (and stobjp
                  (list (cons :xl-stobj-event (get-event name w))
                        (cons :xl-stobj-creator (get-stobj-creator name w))
                        (cons :xl-stobj-recognizer (get-stobj-recognizer name w)))))))
      (cons (cons name (append computed (xt-snapshot-stored-properties name w nil)))
            (xt-world-snapshot (cdr names) w)))))

; The packages: each non-builtin package's imports, by (package . name).
(defun xt-sym-pairs (syms)
  (if (endp syms) nil
    (cons (cons (symbol-package-name (car syms)) (symbol-name (car syms)))
          (xt-sym-pairs (cdr syms)))))

(defun xt-json-pairs (pairs first channel state)
  (if (endp pairs) state
    (let* ((state (if first state (princ$ "," channel state)))
           (state (princ$ "[" channel state))
           (state (xt-json-string (caar pairs) channel state))
           (state (princ$ "," channel state))
           (state (xt-json-string (cdar pairs) channel state))
           (state (princ$ "]" channel state)))
      (xt-json-pairs (cdr pairs) nil channel state))))

(defun xt-json-packages (kpa first channel state)
  (if (endp kpa) state
    (let ((name (package-entry-name (car kpa))))
      (if (member-equal name '("COMMON-LISP" "KEYWORD"))
          (xt-json-packages (cdr kpa) first channel state)
        (let* ((state (if first state (princ$ "," channel state)))
               (state (princ$ "{\"name\":" channel state))
               (state (xt-json-string name channel state))
               (state (princ$ ",\"imports\":[" channel state))
               (state (xt-json-pairs (xt-sym-pairs (package-entry-imports (car kpa))) t channel state))
               (state (princ$ "]}" channel state)))
          (xt-json-packages (cdr kpa) nil channel state))))))

; The type declarations ACL2 compiled each function's raw definition with
; (the world's CLTL-COMMAND defuns: the user's (declare (type ...)) forms, as
; add-trip installed them): the Common Lisp product compiles the same
; definition with the same declarations, so SBCL knows what it knew in the
; image (a (unsigned-byte 32) word stays unboxed).  FN -> ((TYPE VAR ...) ...).
(defun xt-type-items (items acc)
  (cond ((endp items) (reverse acc))
        ((and (consp (car items)) (eq (caar items) 'type) (consp (cdar items)))
         (xt-type-items (cdr items) (cons (cdar items) acc)))
        (t (xt-type-items (cdr items) acc))))

(defun xt-decl-types (forms acc)
  (cond ((endp forms) acc)
        ((and (consp (car forms)) (eq (caar forms) 'declare))
         (xt-decl-types (cdr forms)
                        (append acc (xt-type-items (cdar forms) nil))))
        ((stringp (car forms)) (xt-decl-types (cdr forms) acc))
        (t acc)))

(defun xt-cltl-defs-types (defs table)
  (if (endp defs) table
    (let ((d (car defs)))
      (xt-cltl-defs-types (cdr defs)
                          (if (and (consp d) (symbolp (car d)) (consp (cdr d))
                                   (not (hons-get (car d) table)))
                              (let ((types (xt-decl-types (cddr d) nil)))
                                (hons-acons (car d) (or types :none) table))
                            table)))))

(defun xt-world-types (trips table)
  ; newest first: the first definition seen is the one installed
  (if (endp trips) table
    (let ((trip (car trips)))
      (xt-world-types (cdr trips)
                      (if (and (eq (car trip) 'cltl-command) (eq (cadr trip) 'global-value)
                               (consp (cddr trip)) (eq (car (cddr trip)) 'defuns))
                          (xt-cltl-defs-types (nthcdr 3 (cddr trip)) table)
                        table)))))

(defun xt-json-types (entries table first channel state)
  (if (endp entries) state
    (let* ((fn (car (car entries)))
           (types (cdr (hons-get fn table))))
      (if (or (null types) (eq types :none) (not (eq (cadr (car entries)) :defun)))
          (xt-json-types (cdr entries) table first channel state)
        (let* ((state (if first state (princ$ "," channel state)))
               (state (xt-json-sym fn channel state))
               (state (princ$ ":" channel state))
               (state (xt-json-datum types channel state)))
          (xt-json-types (cdr entries) table nil channel state))))))

(defun xt-core-export (tokens json-path lisp-path pkg-path state)
  (let* ((w (w state))
         (macros (xt-core-macros tokens w nil))
         (roots (append (xt-core-roots tokens w nil)
                        (xt-core-roots (xt-sym-names (xt-macro-callees macros nil)) w nil)
                        (xt-interface-raw-roots (table-alist 'fn-interfaces w) w)))
         (consts (xt-core-consts tokens w nil)))
    (mv-let (erp n state) (xt-extract-with roots (xt-core-stobj-creators tokens w nil) json-path state)
      (declare (ignore erp n))
      (mv-let (entries stobjs) (xt-walk-closed (append roots (xt-boundary-extra roots w nil)) 4 w)
        (let ((globals (xt-token-globals tokens (xt-entries-globals entries nil) state))
              (types (xt-world-types w nil)))
          (mv-let (channel state) (open-output-channel pkg-path :character state)
            (let* ((state (princ$ "{\"packages\":[" channel state))
                   (state (xt-json-packages (known-package-alist state) t channel state))
                   (state (princ$ "],\"types\":{" channel state))
                   (state (xt-json-types entries types t channel state))
                   (state (princ$ "},\"macros\":[" channel state))
                   (state (xt-json-macros macros t channel state))
                   (state (princ$ "]}" channel state))
                   (state (newline channel state))
                   (state (close-output-channel channel state)))
              (mv-let (channel state) (open-output-channel lisp-path :object state)
                (let* ((state (xt-print '(in-package "ACL2") channel state))
                       (state (xt-print-consts consts channel state))
                       (state (xt-print-globals globals channel state))
                       ; every function of the closure (host/native's fnn-call
                       ; may name any): formals, stobjs-in, guard
                       (state (xt-print (list 'xl-set-world-snapshot
                                              (list 'quote
                                                    (xt-world-snapshot
                                                     (remove-duplicates-eq
                                                      (append (xt-entry-fns entries nil)
                                                              (xt-stobj-closure-1 stobjs nil w)
                                                              (xt-interface-citations (table-alist 'fn-interfaces w))
                                                              '(state fn-interfaces *fn-entry-guard-kinds*)))
                                                     w)))
                                        channel state))
                       (state (close-output-channel channel state)))
                  (value (list :roots (len roots) :consts (len consts) :globals (len globals)
                               :functions (len entries))))))))))))
