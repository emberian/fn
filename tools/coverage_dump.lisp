; tools/coverage_dump.lisp -- what the certified world says about which
; symbols (lane coverage-crawler, 2026-09-29; tools/coverage.py reads it).
;
; Loaded into a session that already holds the image's world (books/
; image-world from its certificates, optionally the host :program files):
;
;   (ld "../tools/coverage_dump.lisp")           ; from proof_repl's cbd, books/
;   (cov-dump "/abs/path/coverage-world.json" state)
;
; It reads the LOGICAL WORLD, never source text, and writes one JSON object:
;
;   theorems   every name with a `theorem' property (defthm, defaxiom, and
;              what defrule/defkeystone expand to): its book (the innermost
;              `include-book-path' in force when the event was admitted; null
;              at the top level), the function symbols of its hypotheses and
;              of its conclusions (the translated formula split on `implies'
;              and on conjunctions), its rule classes, the event kind
;              `get-event' recorded, and every symbol in that event's :hints
;              and :instructions (what the proof was told to open or use);
;   functions  every name with a `formals' property: its book, its
;              symbol-class (:program, :ideal, :common-lisp-compliant), the
;              function symbols of its `unnormalized-body' (BOTH sides of
;              each mbe, since the body keeps (return-last 'mbe1-raw E L)),
;              its defattach attachment (tools/extract/frontend.lisp's
;              reading), and whether it is constrained or non-executable.
;
; A name is attributed to the book that first gave it the property, walking
; the world oldest-first; a redefinition keeps the first.  Function symbols
; come from ACL2's own `all-fnnames' over translated terms, so a lambda body
; counts and a quoted symbol does not.
;
; What it cannot say: whether a definition is ENABLED at a theorem (the
; theory in force is not recorded per event), only whether the proof's hints
; name it; tools/coverage.py says "by name only" for the rest.
(in-package "ACL2")
(program)
(set-state-ok t)
(ld "extract/frontend.lisp")

; ---------------------------------------------------------------------------
; The walk: oldest-first over the world's triples, tracking include-book-path.

(defun cov-walk (w book thms fns)
  ; W: triples, oldest first.  THMS, FNS: fast alists name -> book.
  (if (endp w)
      (mv thms fns)
    (let* ((tr (car w)) (name (car tr)) (prop (cadr tr)) (val (cddr tr)))
      (cond ((and (eq name 'include-book-path) (eq prop 'global-value))
             (cov-walk (cdr w) (if (consp val) (car val) nil) thms fns))
            ((and (eq prop 'theorem) (not (eq val *acl2-property-unbound*)))
             (cov-walk (cdr w) book
                       (if (hons-get name thms) thms (hons-acons name book thms))
                       fns))
            ((and (eq prop 'formals) (not (eq val *acl2-property-unbound*)))
             (cov-walk (cdr w) book thms
                       (if (hons-get name fns) fns (hons-acons name book fns))))
            (t (cov-walk (cdr w) book thms fns))))))

; ---------------------------------------------------------------------------
; A theorem's parts: ((hyps . concl) ...) from its translated formula.

(defun cov-parts (term hyps acc)
  (cond ((and (consp term) (eq (car term) 'implies))
         (cov-parts (caddr term) (cons (cadr term) hyps) acc))
        ((and (consp term) (eq (car term) 'if) (equal (cadddr term) *nil*))
         ; (if a b 'nil) is (and a b): two conclusions under the same hyps
         (cov-parts (caddr term) hyps (cov-parts (cadr term) hyps acc)))
        (t (cons (cons hyps term) acc))))

(defun cov-hyp-fns (parts acc)
  (if (endp parts) acc
    (cov-hyp-fns (cdr parts) (union-eq (all-fnnames-lst (car (car parts))) acc))))

(defun cov-concl-fns (parts acc)
  (if (endp parts) acc
    (cov-concl-fns (cdr parts) (union-eq (all-fnnames (cdr (car parts))) acc))))

(defun cov-symbols (x acc)
  (cond ((symbolp x)
         (if (or (null x) (eq x t) (keywordp x) (member-eq x acc)) acc (cons x acc)))
        ((consp x) (cov-symbols (cdr x) (cov-symbols (car x) acc)))
        (t acc)))

(defconst *cov-theorem-events* '(defthm defthmd defthmg defaxiom))

(defun cov-event-hints (ev)
  (if (and (consp ev) (member-eq (car ev) *cov-theorem-events*))
      (let ((rest (cddr ev)))
        (append (cadr (member-eq :hints rest))
                (cadr (member-eq :instructions rest))))
    nil))

; ---------------------------------------------------------------------------
; Emission.

(defun cov-book-string (book)
  ; An include-book-path entry is a full book name: a string, or for a
  ; community book a sysfile pair (:system . "std/portcullis.lisp").
  (cond ((stringp book) book)
        ((and (consp book) (keywordp (car book)) (stringp (cdr book)))
         (concatenate 'string ":" (string-downcase (symbol-name (car book))) "/" (cdr book)))
        (t nil)))

(defun cov-json-book (book channel state)
  (let ((s (cov-book-string book)))
    (if s (xt-json-string s channel state) (princ$ "null" channel state))))

(defun cov-json-bool (x channel state)
  (princ$ (if x "true" "false") channel state))

(defun cov-json-thm (name book first channel state)
  (let* ((w (w state))
         (formula (getpropc name 'theorem nil w))
         (parts (cov-parts formula nil nil))
         (classes (strip-cars (getpropc name 'classes nil w)))
         (ev (get-event name w))
         (kind (if (consp ev) (car ev) nil))
         (state (if first state (princ$ "," channel state)))
         (state (princ$ "{\"name\":" channel state))
         (state (xt-json-sym name channel state))
         (state (princ$ ",\"book\":" channel state))
         (state (cov-json-book book channel state))
         (state (princ$ ",\"hyps\":" channel state))
         (state (xt-json-symlist (cov-hyp-fns parts nil) channel state))
         (state (princ$ ",\"concl\":" channel state))
         (state (xt-json-symlist (cov-concl-fns parts nil) channel state))
         (state (princ$ ",\"classes\":" channel state))
         (state (xt-json-symlist classes channel state))
         (state (princ$ ",\"event\":" channel state))
         (state (if kind (xt-json-sym kind channel state) (princ$ "null" channel state)))
         (state (princ$ ",\"hinted\":" channel state))
         (state (xt-json-symlist (cov-symbols (cov-event-hints ev) nil) channel state)))
    (princ$ "}" channel state)))

(defun cov-json-fn (name book first channel state)
  (let* ((w (w state))
         (body (getpropc name 'unnormalized-body nil w))
         (att (xt-attachment name w))
         (state (if first state (princ$ "," channel state)))
         (state (princ$ "{\"name\":" channel state))
         (state (xt-json-sym name channel state))
         (state (princ$ ",\"book\":" channel state))
         (state (cov-json-book book channel state))
         (state (princ$ ",\"class\":" channel state))
         (state (xt-json-sym (symbol-class name w) channel state))
         (state (princ$ ",\"callees\":" channel state))
         (state (xt-json-symlist (if body (all-fnnames body) nil) channel state))
         (state (princ$ ",\"attachment\":" channel state))
         (state (if att (xt-json-sym att channel state) (princ$ "null" channel state)))
         (state (princ$ ",\"body\":" channel state))
         (state (cov-json-bool body channel state))
         (state (princ$ ",\"constrained\":" channel state))
         (state (cov-json-bool (getpropc name 'constrainedp nil w) channel state))
         (state (princ$ ",\"non_executable\":" channel state))
         (state (cov-json-bool (getpropc name 'non-executablep nil w) channel state)))
    (princ$ "}" channel state)))

(defun cov-emit-thms (alist first channel state)
  (if (endp alist) state
    (let ((state (cov-json-thm (caar alist) (cdar alist) first channel state)))
      (cov-emit-thms (cdr alist) nil channel state))))

(defun cov-emit-fns (alist first channel state)
  (if (endp alist) state
    (let ((state (cov-json-fn (caar alist) (cdar alist) first channel state)))
      (cov-emit-fns (cdr alist) nil channel state))))

(defun cov-dump (path state)
  (mv-let (thms fns)
    (cov-walk (reverse (w state)) nil nil nil)
    (let ((thms (reverse (fast-alist-free thms)))
          (fns (reverse (fast-alist-free fns))))
      (mv-let (channel state)
        (open-output-channel path :character state)
        (if (null channel)
            (prog2$ (cw "COV-DUMP cannot open ~s0~%" path) state)
          (let* ((state (princ$ "{\"cbd\":" channel state))
                 (state (xt-json-string (f-get-global 'connected-book-directory state)
                                        channel state))
                 (state (princ$ ",\"theorems\":[" channel state))
                 (state (cov-emit-thms thms t channel state))
                 (state (princ$ "],\"functions\":[" channel state))
                 (state (cov-emit-fns fns t channel state))
                 (state (princ$ "]}" channel state))
                 (state (newline channel state))
                 (state (close-output-channel channel state)))
            (prog2$ (cw "COV-DUMP ~x0 theorems ~x1 functions -> ~s2~%"
                        (len thms) (len fns) path)
                    state)))))))
