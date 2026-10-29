; E2 experimental envelope. No writes to the planned layer-A FN2-SQUARES.
(in-package "ACL2")

(defun sq-get (key plist)
  (declare (xargs :verify-guards nil))
  (if (atom plist) nil
    (if (equal key (car plist)) (cadr plist)
      (sq-get key (cddr plist)))))

(defun sq-put (key value plist)
  (if (atom plist) (list key value)
    (if (equal key (car plist)) (cons key (cons value (cddr plist)))
      (cons (car plist) (cons (cadr plist) (sq-put key value (cddr plist)))))))

(defun sq-namep (x)
  (and (symbolp x) x (not (eq x t)) (not (keywordp x))))

(defun sq-resolved-functions-p (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) (null names)
    (and (sq-namep (car names))
         (not (eq (getpropc (car names) 'formals :missing world) :missing))
         (sq-resolved-functions-p (cdr names) world))))

; Contract roles name functions; side roles name a function or a pipeline.
(defun sq-endpoints (plist)
  (if (atom plist) nil
    (append (if (symbolp (cadr plist)) (list (cadr plist)) (cadr plist))
            (sq-endpoints (cddr plist)))))

; Qualified exceptions are exact: unknown or redundant unused roles fail too.
; Inspect translated calls, including lambda bodies, without unfolding helpers.
(defun sq-absent-roles (group plist calls)
  (if (atom plist) nil
    (append (and (not (subsetp-eq (sq-endpoints (list (car plist) (cadr plist)))
                                  calls))
                 (list (list group (car plist))))
            (sq-absent-roles group (cddr plist) calls))))

(defun sq-role-exceptions-p (unused absent)
  (and (true-listp unused) (no-duplicatesp-equal unused)
       (subsetp-equal unused absent) (subsetp-equal absent unused)))

(defun sq-statement-name (id)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name id) "$STATEMENT") id))

(defun sq-binding-id (binding)
  (sq-get :id (cdr binding)))

(defun sq-binding-ids (bindings)
  (if (atom bindings) nil
    (cons (sq-binding-id (car bindings)) (sq-binding-ids (cdr bindings)))))

(defun sq-row-event (owner template contract sides case payload)
  (declare (xargs :verify-guards nil))
  (let* ((contract (or (sq-get :contract payload) contract))
         (sides (or (sq-get :sides payload) sides))
         (template (or (sq-get :template payload) template))
         (id (sq-get :id payload))
         (statement (sq-statement-name id))
         (vars (sq-get :vars payload))
         (formula (sq-get :formula payload))
         (proof (or (sq-get :proof payload) '(:owed)))
         (checker (sq-get :checker payload))
         (teeth (sq-get :teeth payload)))
    (if (and (sq-namep id) (symbol-listp vars) (no-duplicatesp-eq vars)
             formula (not (eq formula t))
             (member-eq (sq-get :schema payload)
                        '(:g0 :g1 :g1q :g2 :route :crash :bound :invariant :assertion))
             (sq-namep (sq-get :positive teeth))
             (sq-namep (sq-get :negative teeth))
             (symbol-listp (sq-get :requires payload))
             (true-listp (sq-get :evidence payload))
             (or (not checker)
                 (and (sq-namep (sq-get :function checker))
                      (equal (sq-get :case checker) case)))
             (or (equal proof '(:owed))
                 (and (equal (len proof) 2) (eq (car proof) :proved)
                      (sq-namep (cadr proof)))))
        `(progn
           (defun-nx ,statement ,vars ,formula)
           (make-event
            (let* ((world (w state))
                   (translated (remove-guard-holders
                                (getpropc ',statement 'unnormalized-body nil world)
                                world))
                   (absent (append (sq-absent-roles :contract ',contract (all-fnnames translated))
                                   (sq-absent-roles :sides ',sides (all-fnnames translated))))
                   (proof ',proof)
                   (theorem (and (eq (car proof) :proved)
                                 (getpropc (cadr proof) 'theorem nil world))))
              (if (not (sq-role-exceptions-p ',(sq-get :unused-roles payload) absent))
                  (er soft 'defsquare "Row ~x0 has absent roles ~x1; declared unused roles ~x2."
                      ',id absent ',(sq-get :unused-roles payload))
                (if (and (not (equal translated '(quote t)))
                       (sq-resolved-functions-p (sq-endpoints ',contract) world)
                       (sq-resolved-functions-p (sq-endpoints ',sides) world)
                       (not (assoc-eq ',id (table-alist 'sq-squares world)))
                       (or (equal proof '(:owed))
                           (and theorem (equal theorem translated))))
                  (value
                   (list 'table 'sq-squares (list 'quote ',id)
                         (list 'quote
                               (list :id ',id :schema ',(sq-get :schema payload)
                                     :template ',template
                                     :owner '(:correspondence ,owner)
                                     :origin ',(sq-get :origin payload) :case ',case
                                     :boundary ',(sq-get :boundary payload)
                                     :contract ',contract :sides ',sides
                                     :unused-roles ',(sq-get :unused-roles payload)
                                     :statement ',statement :vars ',vars
                                     :formula ',formula :translated translated
                                     :requires ',(sq-get :requires payload)
                                     :checker ',(sq-get :checker payload)
                                     :teeth ',teeth :proof proof :checks nil
                                     :evidence ',(sq-get :evidence payload)))))
                (er soft 'defsquare
                    "Duplicate row ~x0 or theorem ~x1 does not have its stored translated formula."
                    ',id proof))))))
      (er hard 'defsquare "Malformed binding (or placeholder formula): ~x0" payload))))

(defun sq-row-events (owner template contract sides cases bindings)
  (declare (xargs :verify-guards nil))
  (if (atom cases) nil
    (let ((binding (assoc-equal (car cases) bindings)))
      (append (and binding
                   (list (sq-row-event owner template contract sides
                                       (car cases) (cdr binding))))
              (sq-row-events owner template contract sides (cdr cases) bindings)))))

(defun sq-missing-requires (ids world)
  (declare (xargs :verify-guards nil))
  (if (atom ids) nil
    (append (and (not (assoc-eq (car ids) (table-alist 'sq-squares world)))
                 (not (getpropc (car ids) 'theorem nil world))
                 (list (car ids)))
            (sq-missing-requires (cdr ids) world))))

(defun sq-required-obligations (bindings)
  (if (atom bindings) nil
    (union-eq (sq-get :requires (cdar bindings))
              (sq-required-obligations (cdr bindings)))))

(defun sq-expand (owner template cases bindings contract sides world)
  (declare (xargs :verify-guards nil))
  (let* ((bound (strip-cars bindings))
         (missing (set-difference-equal cases bound))
         (extra (set-difference-equal bound cases))
         (ids (sq-binding-ids bindings)))
    (if (and (sq-namep owner) (keywordp template) (consp contract) (consp sides)
             (not (assoc-eq owner (table-alist 'sq-coverage world)))
             (true-listp cases) (no-duplicatesp-equal cases)
             (alistp bindings) (no-duplicatesp-equal bound)
             (no-duplicatesp-eq ids) (not extra)
             (sq-resolved-functions-p (sq-endpoints contract) world)
             (sq-resolved-functions-p (sq-endpoints sides) world))
        `(progn
           ,@(sq-row-events owner template contract sides cases bindings)
           (make-event
            (let ((unresolved
                   (sq-missing-requires ',(sq-required-obligations bindings) (w state))))
              (value
               (list 'table 'sq-coverage (list 'quote ',owner)
                     (list 'quote (list :required ',cases :bound ',bound
                                        :unmatched ',missing
                                        :unresolved-requires unresolved))))))
           (value-triple
            (cw "SQ COVERAGE ~x0 required=~x1 bound=~x2 unmatched=~x3~%"
                ',owner ,(len cases) ,(len bound) ',missing)))
      (er hard 'defsquare
          "Invalid registry/bindings or unresolved contract/sides for ~x0; extra cases ~x1."
          owner extra))))

; Both expressions are evaluated once in the admitted world. The template
; produces payloads outside this macro; there is no Q1/Q4 dispatch here.
(defmacro defsquare (name &key template cases-from bindings contract sides)
  `(make-event
    (value (sq-expand ',name ',template ,cases-from ,bindings
                      ',contract ',sides (w state)))))

(defun sq-evidence-recordp (record)
  (and (sq-get :revision record) (sq-get :contract record)
       (sq-get :profile record) (sq-get :domain record)
       (sq-get :horizon record) (sq-get :unit record)
       (sq-get :location record)
       (natp (sq-get :reached record)) (natp (sq-get :exercised record))
       (<= (sq-get :exercised record) (sq-get :reached record))
       (member-eq (sq-get :verdict record) '(:pass :fail :unexercised))
       (iff (eq (sq-get :verdict record) :unexercised)
            (equal (sq-get :exercised record) 0))))

(defun sq-evidence-records-p (records)
  (if (atom records) (null records)
    (and (sq-evidence-recordp (car records))
         (sq-evidence-records-p (cdr records)))))

(defun sq-append-evidence-event (id records world)
  (declare (xargs :verify-guards nil))
  (let ((row (cdr (assoc-eq id (table-alist 'sq-squares world)))))
    (if (and row (sq-evidence-records-p records))
        `(table sq-squares ',id
                ',(sq-put :checks (append (sq-get :checks row) records) row))
      (er hard 'sq-append-evidence "Missing row or malformed evidence: ~x0" id))))

(defmacro sq-append-evidence (id records)
  `(make-event (value (sq-append-evidence-event ',id ',records (w state)))))
