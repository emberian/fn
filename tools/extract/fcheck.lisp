; tools/extract/fcheck.lisp -- the ACL2 side of the per-function differential.
;
; For each candidate (FN ARGS) in a file tools/extract/fcheck.py wrote, ACL2
; evaluates FN's guard on ARGS; when the guard holds it evaluates FN on ARGS
; (magic-ev-fncall: the *1* function, guard checked, exactly what a call at
; the top level does) and writes the vector {fn, args, result} as JSON with
; frontend.lisp's datum encoder; the file ends with a completion trailer
; {done, candidates, ok, guard_false, error}.  The CHICKEN side runs the extracted
; function on the same ARGS and compares.  Load after frontend.lisp.
(in-package "ACL2")
(program)
(set-state-ok t)

(defun xt-dec-codes (xs)
  (if (consp xs) (cons (code-char (car xs)) (xt-dec-codes (cdr xs))) nil))

(mutual-recursion
 (defun xt-dec (x)
   (cond ((integerp x) x)
         ((atom x) nil)
         ((eq (car x) :r) (/ (cadr x) (caddr x)))
         ((eq (car x) :c) (code-char (cadr x)))
         ((eq (car x) :s) (coerce (xt-dec-codes (cadr x)) 'string))
         ((eq (car x) :y) (intern-in-package-of-symbol
                           (coerce (xt-dec-codes (caddr x)) 'string)
                           (pkg-witness (cadr x))))
         ((eq (car x) :l) (xt-dec-list (cadr x) (xt-dec (caddr x))))
         (t nil)))
 (defun xt-dec-list (xs tail)
   (if (consp xs) (cons (xt-dec (car xs)) (xt-dec-list (cdr xs) tail)) tail)))

(defun xt-dec-args (xs)
  (if (consp xs) (cons (xt-dec (car xs)) (xt-dec-args (cdr xs))) nil))

(defun xt-quote-all (xs)
  (if (consp xs) (cons (list 'quote (car xs)) (xt-quote-all (cdr xs))) nil))

(defun xt-json-datums (xs first channel state)
  (if (consp xs)
      (let* ((state (if first state (princ$ "," channel state)))
             (state (xt-json-datum (car xs) channel state)))
        (xt-json-datums (cdr xs) nil channel state))
    state))

; One candidate: :guard-false, :error, or the vector written.
(defun xt-fcheck-one (fn args channel state)
  (let* ((w (w state))
         (form (cons (list 'lambda (formals fn w) (guard fn nil w))
                     (xt-quote-all args))))
    (mv-let (erp gval state)
      (trans-eval-no-warning form 'xt-fcheck state t)
      (if (or erp (null (cdr gval)))
          (mv :guard-false state)
        (mv-let (erp val)
          (magic-ev-fncall fn args state nil t)
          (if erp
              (mv :error state)
            (let* ((state (princ$ "{\"fn\":" channel state))
                   (state (xt-json-sym fn channel state))
                   (state (princ$ ",\"args\":[" channel state))
                   (state (xt-json-datums args t channel state))
                   (state (princ$ "],\"result\":" channel state))
                   (state (xt-json-datum val channel state))
                   (state (princ$ "}" channel state))
                   (state (newline channel state)))
              (mv :ok state))))))))

(defun xt-fcheck-loop (entries channel ok gf er state)
  (if (endp entries)
      (mv (list ok gf er) state)
    (let* ((e (car entries))
           (fn (xt-dec (car e)))
           (args (xt-dec-args (cadr e))))
      (mv-let (r state)
        (xt-fcheck-one fn args channel state)
        (xt-fcheck-loop (cdr entries) channel
                        (if (eq r :ok) (1+ ok) ok)
                        (if (eq r :guard-false) (1+ gf) gf)
                        (if (eq r :error) (1+ er) er)
                        state)))))

(defun xt-fcheck (in out state)
  (mv-let (ich state) (open-input-channel in :object state)
    (mv-let (eofp entries state) (read-object ich state)
      (let ((state (close-input-channel ich state)))
        (if eofp (value :empty)
          (mv-let (och state) (open-output-channel out :character state)
            (mv-let (counts state)
              (xt-fcheck-loop entries och 0 0 0 state)
              ; The completion trailer: the gate (fcheck.py scheme) refuses a
              ; vector file without it, or whose counts do not add up to the
              ; candidates tools/extract/fcheck.py gen wrote.
              (let* ((state (princ$ "{\"done\":1,\"candidates\":" och state))
                     (state (princ$ (len entries) och state))
                     (state (princ$ ",\"ok\":" och state))
                     (state (princ$ (first counts) och state))
                     (state (princ$ ",\"guard_false\":" och state))
                     (state (princ$ (second counts) och state))
                     (state (princ$ ",\"error\":" och state))
                     (state (princ$ (third counts) och state))
                     (state (princ$ "}" och state))
                     (state (newline och state))
                     (state (close-output-channel och state)))
                (value counts)))))))))

; The session settings a run needs: a guard of an unused formal is a LET
; with an unused binding; ACL2's error text for each refused candidate is
; not wanted (the counts are).
(set-ignore-ok t)
