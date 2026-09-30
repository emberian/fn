; tools/extract/frontend.lisp -- the extractor's front end.
;
; Reads the logical world (never source text) and writes the translated
; definitions an executable closure needs, as JSON, for a backend
; (tools/extract/chicken.py) to compile.  Loaded into a session that already
; holds the books and host files whose functions are to be extracted:
;
;   (ld "tools/extract/frontend.lisp")
;   (xt-extract '(fn-reader-model-octets ...) "build/extract/served.json" state)
;
; What it resolves, so no backend has to know ACL2's world:
;   * the executable body: `unnormalized-body' with each (mbe :logic L :exec E)
;     -- translated as (return-last 'mbe1-raw E L) -- resolved to E where the
;     function runs as raw Lisp (guard-verified or :program) and to L where it
;     runs its *1* logic (an :ideal function);  ec-call resolved to its call;
;   * an abstract stobj's exports and recognizer/creator to their :exec
;     (after any attach-stobj: `absstobj-info' already names the attachment);
;   * a constrained function to its defattach attachment;
;   * a defstobj's primitives to a field table (the backend implements the
;     accessors, updaters, array and resize primitives over records);
;   * ACL2's primitives (*primitive-formals-and-guards*) and a short list of
;     raw-Lisp-only functions (state globals, printing, errors) to "shim":
;     the backend's runtime implements exactly these.
; Anything else it cannot resolve is emitted as a "blocker" with its reason.
(in-package "ACL2")
(program)
(set-state-ok t)
(set-ld-redefinition-action '(:warn! . :overwrite) state)

; Functions whose logical definition is not what raw Lisp runs, or which read
; the live state: the runtime shim implements them.
(defconst *xt-shims*
  '(boundp-global f-boundp-global get-global f-get-global put-global f-put-global
    fmt-to-comment-window fmt-to-comment-window! fmt-to-comment-window+
    fmt-to-comment-window!+ cw-print-base-radix
    hard-error illegal throw-nonexec-error error1 er-cmp-fn
    return-last))

; ---------------------------------------------------------------------------
; JSON output.

(defun xt-hex-digit (n) (if (< n 10) (code-char (+ 48 n)) (code-char (+ 87 n))))

(defun xt-json-chars (i n s channel state)
  (declare (xargs :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      state
    (let* ((c (char s i)) (k (char-code c)))
      (let ((state (cond ((or (< k 32) (> k 126))
                          (let* ((state (princ$ "\\u00" channel state))
                                 (state (princ$ (xt-hex-digit (floor k 16)) channel state)))
                            (princ$ (xt-hex-digit (mod k 16)) channel state)))
                         ((or (eql c #\") (eql c #\\))
                          (let ((state (princ$ #\\ channel state)))
                            (princ$ c channel state)))
                         (t (princ$ c channel state)))))
        (xt-json-chars (1+ i) n s channel state)))))

(defun xt-json-string (s channel state)
  (let* ((state (princ$ #\" channel state))
         (state (xt-json-chars 0 (length s) s channel state)))
    (princ$ #\" channel state)))

(defun xt-symbol-string (sym)
  (concatenate 'string (symbol-package-name sym) "::" (symbol-name sym)))

(defun xt-json-sym (sym channel state)
  (xt-json-string (xt-symbol-string sym) channel state))

(mutual-recursion
 (defun xt-json-datum (x channel state)
   (cond ((integerp x) (princ$ x channel state))
         ((rationalp x)
          (let* ((state (princ$ "[\"r\"," channel state))
                 (state (princ$ (numerator x) channel state))
                 (state (princ$ "," channel state))
                 (state (princ$ (denominator x) channel state)))
            (princ$ "]" channel state)))
         ((complex-rationalp x)
          (let* ((state (princ$ "[\"x\"," channel state))
                 (state (xt-json-datum (realpart x) channel state))
                 (state (princ$ "," channel state))
                 (state (xt-json-datum (imagpart x) channel state)))
            (princ$ "]" channel state)))
         ((characterp x)
          (let* ((state (princ$ "[\"ch\"," channel state))
                 (state (princ$ (char-code x) channel state)))
            (princ$ "]" channel state)))
         ((stringp x)
          (let* ((state (princ$ "[\"s\"," channel state))
                 (state (xt-json-string x channel state)))
            (princ$ "]" channel state)))
         ((symbolp x)
          (let* ((state (princ$ "[\"y\"," channel state))
                 (state (xt-json-sym x channel state)))
            (princ$ "]" channel state)))
         ((consp x)
          (let* ((state (princ$ "[\"L\",[" channel state))
                 (state (xt-json-elems x t channel state)))
            state))
         (t (princ$ "[\"bad-atom\"]" channel state))))
 ; The elements of a list along its cdrs, then its atom tail.
 (defun xt-json-elems (x first channel state)
   (if (consp x)
       (let* ((state (if first state (princ$ "," channel state)))
              (state (xt-json-datum (car x) channel state)))
         (xt-json-elems (cdr x) nil channel state))
     (let* ((state (princ$ "]," channel state))
            (state (xt-json-datum x channel state)))
       (princ$ "]" channel state)))))

(defun xt-json-syms (syms first channel state)
  (if (consp syms)
      (let* ((state (if first state (princ$ "," channel state)))
             (state (if (car syms) (xt-json-sym (car syms) channel state)
                      (princ$ "null" channel state))))
        (xt-json-syms (cdr syms) nil channel state))
    state))

(defun xt-json-symlist (syms channel state)
  (let* ((state (princ$ "[" channel state))
         (state (xt-json-syms syms t channel state)))
    (princ$ "]" channel state)))

(mutual-recursion
 (defun xt-json-term (term channel state)
   (cond ((variablep term)
          (let* ((state (princ$ "[\"v\"," channel state))
                 (state (xt-json-sym term channel state)))
            (princ$ "]" channel state)))
         ((fquotep term)
          (let* ((state (princ$ "[\"q\"," channel state))
                 (state (xt-json-datum (unquote term) channel state)))
            (princ$ "]" channel state)))
         ((flambda-applicationp term)
          (let* ((state (princ$ "[\"l\"," channel state))
                 (state (xt-json-symlist (lambda-formals (ffn-symb term)) channel state))
                 (state (princ$ "," channel state))
                 (state (xt-json-term (lambda-body (ffn-symb term)) channel state))
                 (state (princ$ ",[" channel state))
                 (state (xt-json-terms (fargs term) t channel state)))
            (princ$ "]]" channel state)))
         (t
          (let* ((state (princ$ "[\"c\"," channel state))
                 (state (xt-json-sym (ffn-symb term) channel state))
                 (state (princ$ ",[" channel state))
                 (state (xt-json-terms (fargs term) t channel state)))
            (princ$ "]]" channel state)))))
 (defun xt-json-terms (terms first channel state)
   (if (consp terms)
       (let* ((state (if first state (princ$ "," channel state)))
              (state (xt-json-term (car terms) channel state)))
         (xt-json-terms (cdr terms) nil channel state))
     state)))

; ---------------------------------------------------------------------------
; Resolving the executable body.

(mutual-recursion
 ; EXECP: this function runs raw (its mbe's are :exec).  Returns the term.
 (defun xt-resolve (term execp)
   (cond ((or (variablep term) (fquotep term)) term)
         ((flambda-applicationp term)
          (fcons-term (make-lambda (lambda-formals (ffn-symb term))
                                   (xt-resolve (lambda-body (ffn-symb term)) execp))
                      (xt-resolve-list (fargs term) execp)))
         ((and (eq (ffn-symb term) 'return-last)
               (quotep (fargn term 1))
               (eq (unquote (fargn term 1)) 'mbe1-raw))
          (xt-resolve (if execp (fargn term 2) (fargn term 3)) execp))
         ((and (eq (ffn-symb term) 'return-last)
               (quotep (fargn term 1))
               (eq (unquote (fargn term 1)) 'ec-call1-raw))
          (xt-resolve (fargn term 3) execp))
         (t (fcons-term (ffn-symb term) (xt-resolve-list (fargs term) execp)))))
 (defun xt-resolve-list (terms execp)
   (if (consp terms)
       (cons (xt-resolve (car terms) execp) (xt-resolve-list (cdr terms) execp))
     nil)))

(mutual-recursion
 (defun xt-callees (term acc)
   (cond ((or (variablep term) (fquotep term)) acc)
         ((flambda-applicationp term)
          (xt-callees (lambda-body (ffn-symb term)) (xt-callees-list (fargs term) acc)))
         (t (xt-callees-list (fargs term)
                             (if (member-eq (ffn-symb term) acc) acc
                               (cons (ffn-symb term) acc))))))
 (defun xt-callees-list (terms acc)
   (if (consp terms)
       (xt-callees-list (cdr terms) (xt-callees (car terms) acc))
     acc)))

; ---------------------------------------------------------------------------
; Stobjs.

(defun xt-stobjs-out (fn w)
  (if (member-eq fn '(if return-last)) '(nil) (stobjs-out fn w)))

(defun xt-stobjs-in (fn w)
  (if (member-eq fn '(if return-last)) (make-list (len (formals fn w))) (stobjs-in fn w)))

(defun xt-stobj-of-cands (fn cands w)
  (if (consp cands)
      (let* ((st (car cands))
             (prop (getpropc st 'stobj nil w)))
        (if (and prop
                 (or (eq fn (access stobj-property prop :recognizer))
                     (eq fn (access stobj-property prop :creator))
                     (member-eq fn (access stobj-property prop :names))))
            st
          (xt-stobj-of-cands fn (cdr cands) w)))
    nil))

(defun xt-stobj-of (fn w)
  ; A stobj this function belongs to as a primitive, export, recognizer or
  ; creator, with the kind of that stobj.
  (let ((cands (remove-eq 'state (remove-eq nil (append (xt-stobjs-in fn w) (xt-stobjs-out fn w))))))
    (xt-stobj-of-cands fn cands w)))

; absstobj-info: (FOUNDATION (NAME LOGIC EXEC) ...) -- the recognizer and
; creator are the first two entries, the exports the rest.
(defun xt-absstobj-exec (fn st w)
  (let ((entry (assoc-eq fn (cdr (getpropc st 'absstobj-info nil w)))))
    (and entry (caddr entry))))

(defun xt-attachment (fn w)
  (let ((a (getpropc fn 'attachment nil w)))
    (cond ((null a) nil)
          ((and (consp a) (keywordp (car a))) nil) ; (:attachment-disallowed . why)
          ((symbolp a) (cdr (assoc-eq fn (getpropc a 'attachment nil w))))
          (t (cdr (assoc-eq fn a))))))

; ---------------------------------------------------------------------------
; The closure walk.  Each entry: (fn kind . data).

(defun xt-classify (fn w)
  (cond ((assoc-eq fn *primitive-formals-and-guards*) (list fn :prim))
        ((member-eq fn *xt-shims*) (list fn :shim))
        (t
         (let ((st (xt-stobj-of fn w)))
           (cond ((and st (getpropc st 'absstobj-info nil w))
                  (let ((exec (xt-absstobj-exec fn st w)))
                    (if exec (list fn :alias exec st)
                      (list fn :blocker "abstract stobj name without an :exec"))))
                 (st (list fn :stobj-prim st))
                 ((getpropc fn 'constrainedp nil w)
                  (let ((att (xt-attachment fn w)))
                    (if att (list fn :alias att nil)
                      (list fn :blocker "constrained function with no attachment"))))
                 ((getpropc fn 'non-executablep nil w)
                  (list fn :blocker "non-executable"))
                 ((getpropc fn 'unnormalized-body nil w)
                  (let* ((class (symbol-class fn w))
                         (execp (not (eq class :ideal))))
                    (list fn :defun
                          (xt-resolve (getpropc fn 'unnormalized-body nil w) execp)
                          class)))
                 (t (list fn :blocker "no body, not a primitive, not attached")))))))

(defun xt-walk (work seen out stobjs w)
  ; WORK: functions to visit; SEEN: fast alist of visited; OUT: entries.
  (declare (xargs :mode :program))
  (if (endp work)
      (mv (reverse out) stobjs)
    (let ((fn (car work)))
      (if (hons-get fn seen)
          (xt-walk (cdr work) seen out stobjs w)
        (let* ((seen (hons-acons fn t seen))
               (entry (xt-classify fn w))
               (kind (cadr entry))
               (next (case kind
                       (:defun (xt-callees (caddr entry) nil))
                       (:alias (list (caddr entry)))
                       (:stobj-prim nil)
                       (otherwise nil)))
               (st (case kind
                     (:stobj-prim (caddr entry))
                     (:alias (cadddr entry))
                     (otherwise nil)))
               (stobjs (if (and st (not (member-eq st stobjs))) (cons st stobjs) stobjs)))
          (xt-walk (append next (cdr work)) seen (cons entry out) stobjs w))))))

; A stobj's field table, for a defstobj: the field's type, initial value,
; resizability and primitive names.
(defun xt-field-names (field renaming arrayp)
  (if arrayp
      (list (defstobj-fnname field :accessor :array renaming)
            (defstobj-fnname field :updater :array renaming)
            (defstobj-fnname field :length :array renaming)
            (defstobj-fnname field :resize :array renaming)
            (defstobj-fnname field :recognizer :array renaming))
    (list (defstobj-fnname field :accessor :non-array renaming)
          (defstobj-fnname field :updater :non-array renaming)
          nil nil
          (defstobj-fnname field :recognizer :non-array renaming))))

(defun xt-keyword-value (key args default)
  (let ((tail (member-eq key args)))
    (if tail (cadr tail) default)))

(defun xt-strip-keyword-args (args)
  ; The field descriptors of a defstobj: everything before the first keyword.
  (if (or (endp args) (keywordp (car args))) nil
    (cons (car args) (xt-strip-keyword-args (cdr args)))))

(defun xt-table-field-names (field renaming)
  (list (defstobj-fnname field :accessor :stobj-table renaming)
        (defstobj-fnname field :updater :stobj-table renaming)
        (defstobj-fnname field :boundp :stobj-table renaming)
        (defstobj-fnname field :remove :stobj-table renaming)
        (defstobj-fnname field :count :stobj-table renaming)
        (defstobj-fnname field :clear :stobj-table renaming)
        (defstobj-fnname field :init :stobj-table renaming)))

(defun xt-world-stobj-names (tail w acc)
  (if (endp tail) acc
    (let ((entry (car tail)))
      (xt-world-stobj-names
       (cdr tail) w
       (if (and (eq (cadr entry) 'stobj)
                (not (member-eq (car entry) acc))
                (getpropc (car entry) 'stobj nil w))
           (cons (car entry) acc)
         acc)))))

(defun xt-json-field (d renaming first channel state)
  (let* ((field (if (consp d) (car d) d))
         (opts (if (consp d) (cdr d) nil))
         (type (xt-keyword-value :type opts t))
         (arrayp (and (consp type) (eq (car type) 'array)))
         (tablep (and (consp type) (eq (car type) 'stobj-table)))
         (names (xt-field-names field renaming arrayp))
         (state (if first state (princ$ "," channel state)))
         (state (princ$ "{\"field\":" channel state))
         (state (xt-json-sym field channel state))
         (state (princ$ ",\"type\":" channel state))
         (state (xt-json-datum type channel state))
         (state (princ$ ",\"init\":" channel state))
         (state (xt-json-datum (xt-keyword-value :initially opts nil) channel state))
         (state (princ$ ",\"resizable\":" channel state))
         (state (princ$ (if (xt-keyword-value :resizable opts nil) "true" "false") channel state))
         (state (princ$ ",\"names\":" channel state))
         (state (xt-json-symlist names channel state))
         (state (if tablep
                    (let ((state (princ$ ",\"table_names\":" channel state)))
                      (xt-json-symlist (xt-table-field-names field renaming) channel state))
                  state)))
    (princ$ "}" channel state)))

(defun xt-json-fields (ds renaming first channel state)
  (if (consp ds)
      (let ((state (xt-json-field (car ds) renaming first channel state)))
        (xt-json-fields (cdr ds) renaming nil channel state))
    state))

(defun xt-json-stobj (st first channel state)
  (let* ((w (w state))
         (prop (getpropc st 'stobj nil w))
         (abs (getpropc st 'absstobj-info nil w))
         (ev (get-event st w))
         (state (if first state (princ$ "," channel state)))
         (state (princ$ "{\"name\":" channel state))
         (state (xt-json-sym st channel state))
         (state (princ$ ",\"recognizer\":" channel state))
         (state (xt-json-sym (access stobj-property prop :recognizer) channel state))
         (state (princ$ ",\"creator\":" channel state))
         (state (xt-json-sym (access stobj-property prop :creator) channel state)))
    (if abs
        (let* ((state (princ$ ",\"abstract\":true,\"foundation\":" channel state))
               (state (xt-json-sym (car abs) channel state)))
          (princ$ "}" channel state))
      (let* ((args (cddr ev))
             (renaming (xt-keyword-value :renaming args nil))
             (state (princ$ ",\"abstract\":false,\"fields\":[" channel state))
             (state (xt-json-fields (xt-strip-keyword-args args) renaming t channel state)))
        (princ$ "]}" channel state)))))

(defun xt-json-stobjs (sts first channel state)
  (if (consp sts)
      (let ((state (xt-json-stobj (car sts) first channel state)))
        (xt-json-stobjs (cdr sts) nil channel state))
    state))

(defun xt-nested-stobj-types (ds w)
  (if (endp ds) nil
    (let* ((d (car ds))
           (type (xt-keyword-value :type (if (consp d) (cdr d) nil) t))
           (elt (if (and (consp type) (eq (car type) 'array)) (cadr type) type)))
      (if (and (symbolp elt) elt (getpropc elt 'stobj nil w))
          (cons elt (xt-nested-stobj-types (cdr ds) w))
        (xt-nested-stobj-types (cdr ds) w)))))

; Foundations of abstract stobjs and nested stobj field types are stobjs too.
(defun xt-stobj-closure-1 (sts acc w)
  (if (endp sts) acc
    (let ((st (car sts)))
      (if (member-eq st acc)
          (xt-stobj-closure-1 (cdr sts) acc w)
        (let* ((abs (getpropc st 'absstobj-info nil w))
               (ev (get-event st w))
               (more (if abs (list (car abs))
                       (xt-nested-stobj-types (xt-strip-keyword-args (cddr ev)) w))))
          (xt-stobj-closure-1 (append more (cdr sts)) (cons st acc) w))))))

; ---------------------------------------------------------------------------
; Emission.

(defun xt-json-entry (entry first channel state)
  (let* ((w (w state))
         (fn (car entry))
         (kind (cadr entry))
         (state (if first state (princ$ "," channel state)))
         (state (princ$ "{\"name\":" channel state))
         (state (xt-json-sym fn channel state))
         (state (princ$ ",\"kind\":\"" channel state))
         (state (princ$ (string-downcase (symbol-name kind)) channel state))
         (state (princ$ "\",\"formals\":" channel state))
         (state (xt-json-symlist (if (eq kind :prim)
                                     (formals fn w)
                                   (formals fn w))
                                 channel state))
         (state (princ$ ",\"stobjs_in\":" channel state))
         (state (xt-json-symlist (xt-stobjs-in fn w) channel state))
         (state (princ$ ",\"stobjs_out\":" channel state))
         (state (xt-json-symlist (xt-stobjs-out fn w) channel state))
         (state (princ$ ",\"predefined\":" channel state))
         (state (princ$ (if (getpropc fn 'predefined nil w) "true" "false") channel state))
         (state (case kind
                  (:defun
                   (let* ((state (princ$ ",\"class\":\"" channel state))
                          (state (princ$ (string-downcase (symbol-name (cadddr entry))) channel state))
                          (state (princ$ "\",\"invariant_risk\":" channel state))
                          (state (princ$ (if (getpropc fn 'invariant-risk nil w) "true" "false") channel state))
                          (state (princ$ ",\"guard\":" channel state))
                          (state (xt-json-term (guard fn nil w) channel state))
                          (state (princ$ ",\"body\":" channel state)))
                     (xt-json-term (caddr entry) channel state)))
                  (:alias
                   (let* ((state (princ$ ",\"guard\":" channel state))
                          (state (xt-json-term (xt-resolve (guard fn nil w) t) channel state))
                          (state (princ$ ",\"target\":" channel state))
                          (state (xt-json-sym (caddr entry) channel state))
                          ; how it was resolved: an abstract stobj's :exec
                          ; (the stobj named) or a defattach attachment
                          (state (princ$ ",\"via\":" channel state)))
                     (if (cadddr entry)
                         (let ((state (princ$ "{\"absstobj\":" channel state)))
                           (let ((state (xt-json-sym (cadddr entry) channel state)))
                             (princ$ "}" channel state)))
                       (princ$ "\"attachment\"" channel state))))
                  (:stobj-prim
                   (let* ((state (princ$ ",\"stobj\":" channel state)))
                     (xt-json-sym (caddr entry) channel state)))
                  (:blocker
                   (let* ((state (princ$ ",\"reason\":" channel state)))
                     (xt-json-string (caddr entry) channel state)))
                  (otherwise state))))
    (princ$ "}" channel state)))

(defun xt-json-entries (entries first channel state)
  (if (consp entries)
      (let ((state (xt-json-entry (car entries) first channel state)))
        (xt-json-entries (cdr entries) nil channel state))
    state))

;
; ---------------------------------------------------------------------------
; The boundary (lane extract-2, e1).  The host calls a root through fnn-call
; (host/native/io.lisp), which (1) checks the entry's ARITY and the KIND
; conjuncts of its guard (fnn-entry-guard: a conjunct (R v), v a non-stobj
; formal, R in *fn-entry-guard-kinds*), then (2) applies the entry's *1*
; counterpart, which under guard-checking t evaluates the entry's WHOLE
; guard before the raw body runs.  An extracted program must do both at its
; boundary and nothing inside it: an interior call's guard is a proved guard
; obligation of its caller.  The front end computes the kind checks exactly
; as fnn-entry-guard-spec does (same conjuncts, same order) and walks each
; boundary function's guard and recognizers into the closure.

(defun xt-guard-conjuncts (term)
  (if (and (consp term) (eq (car term) 'if) (equal (fourth term) *nil*))
      (append (xt-guard-conjuncts (second term)) (xt-guard-conjuncts (third term)))
    (list term)))

(defun xt-position (x l i)
  (cond ((endp l) nil) ((eq x (car l)) i) (t (xt-position x (cdr l) (1+ i)))))

(defun xt-kind-checks (cs formals stobjs kinds acc)
  ; fnn-entry-guard-spec's loop: each check (position formal recognizer kind),
  ; pushed, so ACC is in reverse conjunct order.
  (if (endp cs) acc
    (let* ((c (car cs))
           (pos (and (consp c) (symbolp (car c)) (consp (cdr c)) (null (cddr c))
                     (symbolp (cadr c)) (xt-position (cadr c) formals 0)))
           (kind (and pos (null (nth pos stobjs)) (assoc-eq (car c) kinds))))
      (xt-kind-checks (cdr cs) formals stobjs kinds
                      (if kind (cons (list pos (cadr c) (car c) (cdr kind)) acc) acc)))))

(defun xt-insert-by-pos (x l)
  ; stable insertion by position (SBCL's list sort is a stable merge sort)
  (if (or (endp l) (< (car x) (caar l))) (cons x l)
    (cons (car l) (xt-insert-by-pos x (cdr l)))))

(defun xt-sort-by-pos (l acc)
  (if (endp l) acc (xt-sort-by-pos (cdr l) (xt-insert-by-pos (car l) acc))))

(defun xt-entry-kinds (w)
  (let ((q (getpropc '*fn-entry-guard-kinds* 'const nil w)))
    (and (consp q) (eq (car q) 'quote) (cadr q))))

(defun xt-boundary-spec (fn w)
  ; (arity . checks) as fnn-entry-guard-spec; checks sorted by position.
  (let* ((formals (formals fn w))
         (stobjs (stobjs-in fn w))
         (checks (xt-kind-checks (xt-guard-conjuncts (guard fn nil w)) formals stobjs
                                 (xt-entry-kinds w) nil)))
    (cons (len formals) (xt-sort-by-pos checks nil))))

(defun xt-strip-nths (n l)
  (if (endp l) nil (cons (nth n (car l)) (xt-strip-nths n (cdr l)))))

(defun xt-boundary-extra (fns w acc)
  ; the guard's callees and the kind recognizers of each boundary function
  (if (endp fns) acc
    (let* ((fn (car fns))
           (g (xt-resolve (guard fn nil w) t))
           (spec (xt-boundary-spec fn w)))
      (xt-boundary-extra (cdr fns) w
                         (append (xt-callees g nil) (xt-strip-nths 2 (cdr spec)) acc)))))

(defun xt-json-check (c channel state)
  (let* ((state (princ$ "[" channel state))
         (state (princ$ (car c) channel state))
         (state (princ$ "," channel state))
         (state (xt-json-sym (cadr c) channel state))
         (state (princ$ "," channel state))
         (state (xt-json-sym (caddr c) channel state))
         (state (princ$ "," channel state))
         (state (xt-json-string (cadddr c) channel state)))
    (princ$ "]" channel state)))

(defun xt-json-checks (cs first channel state)
  (if (consp cs)
      (let* ((state (if first state (princ$ "," channel state)))
             (state (xt-json-check (car cs) channel state)))
        (xt-json-checks (cdr cs) nil channel state))
    state))

(defun xt-json-boundary (fns first channel state)
  (if (consp fns)
      (let* ((w (w state))
             (fn (car fns))
             (spec (xt-boundary-spec fn w))
             (state (if first state (princ$ "," channel state)))
             (state (princ$ "{\"name\":" channel state))
             (state (xt-json-sym fn channel state))
             (state (princ$ ",\"arity\":" channel state))
             (state (princ$ (car spec) channel state))
             (state (princ$ ",\"guard\":" channel state))
             (state (xt-json-term (xt-resolve (guard fn nil w) t) channel state))
             (state (princ$ ",\"checks\":[" channel state))
             (state (xt-json-checks (cdr spec) t channel state))
             (state (princ$ "]}" channel state)))
        (xt-json-boundary (cdr fns) nil channel state))
    state))

; ROOTS: the functions the host driver calls; every root is a boundary
; function (its guard is checked where the host calls it).  EXTRA: more roots
; the driver does not call (their guards are not checked: interior only).
; The guards a *1* body checks (tools/extract/chicken.py star1_call): an
; invariant-risk :program function's callees' guards, whose functions the
; program must hold too.
(defun xt-guard-callees (fns w acc)
  (if (endp fns) acc
    (xt-guard-callees (cdr fns) w
                      (if (getpropc (car fns) 'formals nil w)
                          (xt-callees (xt-resolve (guard (car fns) nil w) t) acc)
                        acc))))

(defun xt-risk-guard-fns (entries w acc)
  (if (endp entries) acc
    (let ((e (car entries)))
      (xt-risk-guard-fns
       (cdr entries) w
       (if (and (eq (cadr e) :defun) (eq (cadddr e) :program)
                (getpropc (car e) 'invariant-risk nil w))
           (xt-guard-callees (xt-callees (caddr e) nil) w acc)
         acc)))))

(defun xt-walk-closed (seeds n w)
  ; walk, then add the risky bodies' guard functions, to a fixpoint (N rounds)
  (mv-let (entries stobjs) (xt-walk seeds nil nil nil w)
    (let* ((more (xt-risk-guard-fns entries w nil))
           (new (set-difference-eq more (strip-cars entries))))
      (if (or (endp new) (zp n))
          (mv entries stobjs)
        (xt-walk-closed (append seeds new) (1- n) w)))))

; The host ports (lane extract-writable): a function of host/store-write-host.lisp
; (name FN-XW-...) is io.lisp's raw host code written in :program, and io.lisp
; calls every ACL2 entry through fnn-call.  So each fn- core function such a
; port function calls directly is a boundary function too: its guard is
; checked where the port calls it (tools/extract/chicken.py, port callers).
(defun xt-prefixp (prefix name)
  (and (<= (length prefix) (length name))
       (equal (subseq name 0 (length prefix)) prefix)))

(defun xt-port-fn-p (fn)
  (xt-prefixp "FN-XW-" (symbol-name fn)))

(defun xt-core-fn-p (fn w)
  (let ((n (symbol-name fn)))
    (and (xt-prefixp "FN-" n)
         (not (xt-prefixp "FN-XW-" n)) (not (xt-prefixp "FN-XO-" n)) (not (xt-prefixp "FN-HX-" n))
         (getpropc fn 'formals nil w)
         (not (getpropc fn 'constrainedp nil w)))))

(defun xt-core-callees (fns w acc)
  (cond ((endp fns) acc)
        ((or (member-eq (car fns) acc) (not (xt-core-fn-p (car fns) w)))
         (xt-core-callees (cdr fns) w acc))
        (t (xt-core-callees (cdr fns) w (cons (car fns) acc)))))

(defun xt-port-callees (entries w acc)
  (if (endp entries) (reverse acc)
    (let ((e (car entries)))
      (xt-port-callees (cdr entries) w
                       (if (and (eq (cadr e) :defun) (xt-port-fn-p (car e)))
                           (xt-core-callees (xt-callees (caddr e) nil) w acc)
                         acc)))))

(defun xt-extract-with (roots extra path state)
  (let ((w (w state)))
    (mv-let (entries0 stobjs0)
      (xt-walk-closed (append roots extra (xt-boundary-extra roots w nil)) 4 w)
      (declare (ignore stobjs0))
     (let ((boundary (append roots (set-difference-eq (xt-port-callees entries0 w nil) roots))))
     (mv-let (entries stobjs)
      (xt-walk-closed (append roots extra (xt-boundary-extra boundary w nil)) 4 w)
      (mv-let (channel state)
        (open-output-channel path :character state)
        (let* ((state (princ$ "{\"roots\":" channel state))
               (state (xt-json-symlist roots channel state))
               (state (princ$ ",\"boundary\":[" channel state))
               (state (xt-json-boundary boundary t channel state))
               (state (princ$ "],\"functions\":[" channel state))
               (state (xt-json-entries entries t channel state))
               (state (princ$ "],\"stobjs\":[" channel state))
               (state (xt-json-stobjs (xt-stobj-closure-1 stobjs nil w) t channel state))
               (state (princ$ "],\"stobj_names\":" channel state))
               ; A table may test a valid name whose creator is outside this
               ; executable closure. Export the actual live world registry,
               ; rather than guessing validity from reachable primitives.
               (state (xt-json-symlist (xt-world-stobj-names w w nil) channel state))
               (state (princ$ "}" channel state))
               (state (newline channel state))
               (state (close-output-channel channel state)))
          (value (len entries)))))))))

(defun xt-extract (roots path state)
  (xt-extract-with roots nil path state))
