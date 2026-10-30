; defsquare: a correspondence binds statements to the cases its sources
; catalogue, in the ONE obligation store fn2-squares (DSL-METATHEORY 3.1-3.2,
; 5.7). Adopted from the squares experiment E2 (fn2/experiments/squares/e2/
; defsquare.lisp): the same envelope, its rows written through fn2-declare
; under DM1's table guard, its coverage report recorded in the
; correspondence's own declaration row.
(in-package "ACL2")
(include-book "owed")

; Contract roles name functions; side roles name a function or a pipeline.
(defun fn2-square-endpoints (plist)
  (declare (xargs :verify-guards nil))
  (if (atom plist) nil
    (append (if (symbolp (cadr plist)) (list (cadr plist)) (cadr plist))
            (fn2-square-endpoints (cddr plist)))))
(defun fn2-square-resolvedp (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) (null names)
    (and (symbolp (car names)) (car names) (not (keywordp (car names)))
         (not (eq (getpropc (car names) 'formals :missing world) :missing))
         (fn2-square-resolvedp (cdr names) world))))

; A role is absent when one of its functions does not occur among the
; translated statement's calls (lambda bodies included, helpers not unfolded).
; Exceptions are exact: unknown, duplicate and redundant ones are refused.
(defun fn2-square-absent-roles (group plist calls)
  (declare (xargs :verify-guards nil))
  (if (atom plist) nil
    ; :independent names the row's independent contract (metadata, decision 1),
    ; not a function the statement calls.
    (append (and (not (eq (car plist) :independent))
                 (not (subsetp-eq (fn2-square-endpoints (list (car plist) (cadr plist))) calls))
                 (list (list group (car plist))))
            (fn2-square-absent-roles group (cddr plist) calls))))
(defun fn2-square-exceptionsp (unused absent)
  (declare (xargs :verify-guards nil))
  (and (true-listp unused) (no-duplicatesp-equal unused)
       (subsetp-equal unused absent) (subsetp-equal absent unused)))
; BODY and CALLS come from REMOVE-GUARD-HOLDERS and ALL-FNNAMES, evaluated in
; the generated MAKE-EVENT (both are system code, not callable from here).
(defun fn2-square-role-check (id body calls contract sides unused)
  (declare (xargs :verify-guards nil))
  (let ((absent (append (fn2-square-absent-roles :contract contract calls)
                        (fn2-square-absent-roles :sides sides calls))))
    (cond ((equal body ''t)
           (msg "Row ~x0 translates to the placeholder T." id))
          ((not (fn2-square-exceptionsp unused absent))
           (msg "Row ~x0 has absent roles ~x1; declared unused roles ~x2." id absent unused))
          (t nil))))

(defconst *fn2-square-schemas*
  '(:g0 :g1 :g1q :g2 :route :crash :bound :invariant :assertion))

; The case catalogue, assembled from the registry: every machine's labels in
; declaration order, then every operation set that contributes :cases (the
; generated router, then the executor). No catalogue is written by hand.
(defun fn2-case-rows (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (append (fn2-decl-get :cases (cdar rows)) (fn2-case-rows (cdr rows)))))
(defun fn2-case-catalogue (world)
  (declare (xargs :verify-guards nil))
  (append (fn2-case-rows (fn2-decl-rows :machine world))
          (fn2-case-rows (fn2-decl-rows :operation-set world))))
(defun fn2-case-source-in (label rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (member-equal label (fn2-decl-get :cases (cdar rows)))
        (fn2-decl-get :decl-id (cdar rows))
      (fn2-case-source-in label (cdr rows)))))
(defun fn2-case-source (label world)
  (declare (xargs :verify-guards nil))
  (or (fn2-case-source-in label (fn2-decl-rows :machine world))
      (fn2-case-source-in label (fn2-decl-rows :operation-set world))))

; One bound case. The payload's :contract, :sides and :template override the
; correspondence's (a row may bind a different boundary of the same square).
(defun fn2-square-row-event (owner template contract sides case source payload)
  (declare (xargs :verify-guards nil))
  (let* ((contract (or (fn2-decl-get :contract payload) contract))
         ; A binding's independent contract (decision 1) joins the correspondence's
         ; contract as metadata; the formula's roles stay the correspondence's.
         (contract (if (fn2-decl-get :independent payload)
                       (append contract (list :independent (fn2-decl-get :independent payload)))
                     contract))
         (sides (or (fn2-decl-get :sides payload) sides))
         (template (or (fn2-decl-get :template payload) template))
         (id (fn2-decl-get :id payload))
         (statement (and (symbolp id)
                         (intern-in-package-of-symbol
                          (concatenate 'string (symbol-name id) "$OWED") id)))
         (vars (fn2-decl-get :vars payload))
         (formula (fn2-decl-get :formula payload))
         (unused (fn2-decl-get :unused-roles payload))
         (checker (fn2-decl-get :checker payload))
         (teeth (fn2-decl-get :teeth payload)))
    (if (and (symbolp id) id (not (keywordp id)) (not (eq id t))
             (symbol-listp vars) (no-duplicatesp-eq vars)
             formula (not (eq formula t))
             (member-eq (fn2-decl-get :schema payload) *fn2-square-schemas*)
             (fn2-owed-teethp (list (fn2-decl-get :positive teeth) (fn2-decl-get :negative teeth)))
             (symbol-listp (fn2-decl-get :depends payload))
             (or (not checker)
                 (and (fn2-owed-teethp (list (fn2-decl-get :function checker)))
                      (equal (fn2-decl-get :case checker) case))))
        (fn2-declare (list :square id)
          (list :schema (fn2-decl-get :schema payload) :template template
                :owner (list :correspondence owner) :origin (fn2-decl-get :origin payload)
                :case case :case-source source :boundary (fn2-decl-get :boundary payload)
                :contract contract :sides sides :unused-roles unused
                ; A binding records what its two sides execute in common (decision 1):
                ; the declarations, and the shared functions by name.
                :shared (fn2-decl-get :shared payload)
                :shared-provenance (fn2-decl-get :shared-provenance payload)
                :claim (or (fn2-decl-get :claim payload) :semantic)
                :shared-handler-mutation (fn2-decl-get :shared-handler-mutation payload)
                :statement statement :vars vars :formula formula :teeth teeth
                :doc (fn2-decl-get :doc payload) :checker checker
                :depends (fn2-decl-get :depends payload)
                :proof (or (fn2-decl-get :proof payload) '(:owed)) :checks nil)
          (list (list :owner (list :correspondence owner) :at :coverage))
          `((defun-nx ,statement ,vars ,formula)
            (make-event
             (let* ((body (remove-guard-holders
                           (fn2-decl-statement-body ',statement (w state)) (w state)))
                    (problem (fn2-square-role-check ',id body (all-fnnames body)
                                                    ',contract ',sides ',unused)))
               (if problem (er soft 'defsquare "~@0" problem)
                 (value '(value-triple :roles-bound)))))))
      (er hard 'defsquare "Malformed binding for case ~x0 of ~x1: ~x2." case owner payload))))

; A requirement is a row with no statement: an obligation named, not stated.
(defun fn2-square-requirement-events (owner requirements)
  (declare (xargs :verify-guards nil))
  (if (atom requirements) nil
    (let ((r (car requirements)))
      (cons (fn2-declare (list :square (car r))
              (list :schema (fn2-decl-get :schema (cdr r)) :owner (list :correspondence owner)
                    :doc (fn2-decl-get :doc (cdr r)) :proof '(:owed) :checks nil)
              (list (list :owner (list :correspondence owner) :at :coverage)) nil)
            (fn2-square-requirement-events owner (cdr requirements))))))

(defun fn2-square-row-events (owner template contract sides cases bindings)
  (declare (xargs :verify-guards nil))
  (if (atom cases) nil
    (let ((binding (assoc-equal (car cases) bindings)))
      (append (and binding
                   (list (fn2-square-row-event owner template contract sides (car cases)
                           (fn2-decl-get :source (cdr binding)) (cdr binding))))
              (fn2-square-row-events owner template contract sides (cdr cases) bindings)))))
(defun fn2-square-binding-ids (bindings)
  (declare (xargs :verify-guards nil))
  (if (atom bindings) nil
    (cons (fn2-decl-get :id (cdar bindings)) (fn2-square-binding-ids (cdr bindings)))))
(defun fn2-square-depends (bindings)
  (declare (xargs :verify-guards nil))
  (if (atom bindings) nil
    (union-eq (fn2-decl-get :depends (cdar bindings)) (fn2-square-depends (cdr bindings)))))
; A dependency is unresolved while it names no stated row and no theorem.
(defun fn2-square-unresolved (ids world)
  (declare (xargs :verify-guards nil))
  (if (atom ids) nil
    (append (and (not (fn2-decl-get :statement (fn2-decl-row (list :square (car ids)) world)))
                 (not (getpropc (car ids) 'theorem nil world))
                 (list (car ids)))
            (fn2-square-unresolved (cdr ids) world))))
(defun fn2-square-requirementsp (requirements)
  (declare (xargs :verify-guards nil))
  (if (atom requirements) (null requirements)
    (and (consp (car requirements)) (symbolp (caar requirements)) (caar requirements)
         (not (keywordp (caar requirements)))
         (member-eq (fn2-decl-get :schema (cdar requirements)) *fn2-square-schemas*)
         (stringp (fn2-decl-get :doc (cdar requirements)))
         (fn2-square-requirementsp (cdr requirements)))))

(defun fn2-square-expand (name template cases bindings contract sides requirements world)
  (declare (xargs :verify-guards nil))
  (let* ((bound (strip-cars bindings))
         (missing (set-difference-equal cases bound))
         (extra (set-difference-equal bound cases))
         (ids (append (fn2-square-binding-ids bindings) (strip-cars requirements))))
    (cond
     ((not (and (symbolp name) name (not (keywordp name)) (keywordp template)
                (consp contract) (consp sides)))
      (er hard 'defsquare "Malformed correspondence ~x0." name))
     ((fn2-decl-row (list :correspondence name) world)
      (er hard 'defsquare "Correspondence ~x0 is already declared." name))
     ((not (and (true-listp cases) (no-duplicatesp-equal cases)))
      (er hard 'defsquare "Duplicate or malformed cases in ~x0: ~x1." name cases))
     ((not (and (alistp bindings) (no-duplicatesp-equal bound) (no-duplicatesp-eq ids)
                (fn2-square-requirementsp requirements)))
      (er hard 'defsquare "Duplicate bindings, rows or malformed requirements in ~x0." name))
     (extra (er hard 'defsquare "~x0 binds cases no source catalogues: ~x1." name extra))
     ((not (and (fn2-square-resolvedp (fn2-square-endpoints contract) world)
                (fn2-square-resolvedp (fn2-square-endpoints sides) world)))
      (er hard 'defsquare "Unresolved contract or side function in ~x0." name))
     (t
      `(progn
         ,@(fn2-square-requirement-events name requirements)
         ,@(fn2-square-row-events name template contract sides cases bindings)
         (make-event
          (let ((unresolved (fn2-square-unresolved ',(fn2-square-depends bindings) (w state))))
            (value
             (list 'progn
                   (fn2-declare '(:correspondence ,name)
                     (list :template ',template :contract ',contract :sides ',sides
                           :required ',cases :bound ',bound :unmatched ',missing
                           :unresolved-depends unresolved :rows ',ids)
                     nil nil)
                   (list 'value-triple
                         (list 'cw "FN2 SQUARE COVERAGE ~x0 required=~x1 bound=~x2 unmatched=~x3 unresolved=~x4~%"
                               '',name ,(len cases) ,(len bound) '',missing
                               (list 'quote unresolved))))))))))))

; :cases-from and :bindings are evaluated once, in the admitted world.
(defmacro defsquare (name &key template cases-from bindings contract sides requirements)
  `(make-event
    (value (fn2-square-expand ',name ',template ,cases-from ,bindings
                              ',contract ',sides ',requirements (w state)))))

(defun fn2-square-coverage (name world)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-decl-row (list :correspondence name) world)))
    (list :required (len (fn2-decl-get :required row)) :bound (len (fn2-decl-get :bound row))
          :unmatched (fn2-decl-get :unmatched row)
          :unresolved-depends (fn2-decl-get :unresolved-depends row))))

; Evidence is a separate dimension: an append replaces :checks and nothing
; else, and a checked row stays owed. The table guard validates the records.
(defun fn2-square-append-evidence-event (id records world)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-decl-row (list :square id) world)))
    (cond ((fn2-decl-sealed (list :square id) world)
           (er hard 'fn2-square-append-evidence "~x0: the evidence input is sealed." id))
          ((not (and row (fn2-decl-get :statement row) (fn2-square-checksp records)))
           (er hard 'fn2-square-append-evidence "Missing stated row or malformed evidence: ~x0." id))
          (t `(table fn2-squares ',id
                ',(fn2-decl-set :checks (append (fn2-decl-get :checks row) records) row))))))
; RECORDS is evaluated.
(defmacro fn2-square-append-evidence (id records)
  `(make-event (value (fn2-square-append-evidence-event ',id ,records (w state)))))
