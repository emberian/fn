; Loaded-world owner-global authority closure, for source-bound threading.
; Program-only inspection. No source rewrite or proof assertion occurs here.
(in-package "ACL2")
(program)
(set-state-ok t)

(mutual-recursion
 (defun fn-ocw-callees (term acc)
   (cond ((or (variablep term) (fquotep term)) acc)
         ((flambda-applicationp term)
          (fn-ocw-callees (lambda-body (ffn-symb term))
                          (fn-ocw-callees-list (fargs term) acc)))
         (t (fn-ocw-callees-list
             (fargs term) (add-to-set-eq (ffn-symb term) acc)))))
 (defun fn-ocw-callees-list (terms acc)
   (if (endp terms) acc
     (fn-ocw-callees-list (cdr terms) (fn-ocw-callees (car terms) acc)))))

(mutual-recursion
 (defun fn-ocw-owner-globalp (term)
   (cond ((or (variablep term) (fquotep term)) nil)
         ((flambda-applicationp term)
          (or (fn-ocw-owner-globalp (lambda-body (ffn-symb term)))
              (fn-ocw-owner-globals-listp (fargs term))))
         (t (or (and (member-eq (ffn-symb term)
                                '(get-global put-global boundp-global1))
                     (consp (fargs term)) (fquotep (car (fargs term)))
                     (member-eq (unquote (car (fargs term)))
                                '(fn-owner fn-owner-retain-carry)))
                (fn-ocw-owner-globals-listp (fargs term))))))
 (defun fn-ocw-owner-globals-listp (terms)
   (and (consp terms)
        (or (fn-ocw-owner-globalp (car terms))
            (fn-ocw-owner-globals-listp (cdr terms))))))

(defun fn-ocw-functions (tail wrld acc)
  (if (endp tail) acc
    (let ((trip (car tail)))
      (fn-ocw-functions
       (cdr tail) wrld
       (if (and (eq (cadr trip) 'formals)
                (not (eq (cddr trip) *acl2-property-unbound*))
                (member-eq 'state (getpropc (car trip) 'formals nil wrld)))
           (add-to-set-eq (car trip) acc) acc)))))

(defun fn-ocw-direct (names wrld)
  (if (endp names) nil
    (let* ((fn (car names))
           (body (getpropc fn 'unnormalized-body nil wrld))
           (g (getpropc fn 'guard *t* wrld)))
      (if (or (member-eq fn '(fn-owner-ocfg fn-owner-core fn-owner-store
                              fn-owner-retain-carry fn-owner-retain-statep
                              fn-owner-install-ocfg fn-owner-install-open-ocfg
                              fn-owner-retain-carry-put))
              (and body (fn-ocw-owner-globalp body))
              (fn-ocw-owner-globalp g))
          (cons fn (fn-ocw-direct (cdr names) wrld))
        (fn-ocw-direct (cdr names) wrld)))))

(defun fn-ocw-grow-once (names touched wrld)
  (if (endp names) touched
    (let* ((fn (car names))
           (body (getpropc fn 'unnormalized-body nil wrld))
           (g (getpropc fn 'guard *t* wrld))
           (calls (fn-ocw-callees g
                                (if body (fn-ocw-callees body nil) nil))))
      (fn-ocw-grow-once
       (cdr names)
       (if (intersectp-eq calls touched) (add-to-set-eq fn touched) touched)
       wrld))))

(defun fn-ocw-close (fuel names touched wrld)
  (if (zp fuel) touched
    (let ((next (fn-ocw-grow-once names touched wrld)))
      (if (equal (len next) (len touched)) touched
        (fn-ocw-close (1- fuel) names next wrld)))))

(defun fn-ocw-rows (names wrld)
  (if (endp names) nil
    (let* ((fn (car names))
           (outs (stobjs-out fn wrld)))
      (cons (list fn (getpropc fn 'formals nil wrld)
                    (stobjs-in fn wrld) outs (symbol-class fn wrld)
                    (if (member-eq 'state outs) t nil))
            (fn-ocw-rows (cdr names) wrld)))))

(defun fn-ocw-snapshot (state)
  (declare (xargs :stobjs state))
  (let* ((wrld (w state))
         (names (fn-ocw-functions wrld wrld nil))
         (direct (fn-ocw-direct names wrld))
         (touched (fn-ocw-close (len names) names direct wrld)))
    (list :direct direct :functions (fn-ocw-rows touched wrld))))

(defun fn-ocw-write-snapshot (path state)
  (declare (xargs :stobjs state))
  (mv-let (channel state) (open-output-channel path :object state)
    (if (not channel) (er soft 'fn-ocw-write-snapshot "Cannot open ~x0" path)
      (let* ((state (print-object$ (fn-ocw-snapshot state) channel state))
             (state (close-output-channel channel state)))
        (value :written)))))
