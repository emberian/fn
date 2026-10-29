(in-package "ACL2")
(include-book "declare")

; Forward references name unit/checker functions: production books do not
; include their tests. fn2-assert-owed-teeth resolves and runs them there.
(defun fn2-owed-teethp (names)
  (if (atom names) (null names)
    (and (symbolp (car names)) (car names)
         (not (eq (car names) t)) (not (keywordp (car names)))
         (fn2-owed-teethp (cdr names)))))

(defun fn2-square-tooth-names (teeth)
  (declare (xargs :verify-guards nil))
  (if (keywordp (car teeth))
      (list (fn2-decl-get :positive teeth) (fn2-decl-get :negative teeth))
    teeth))

; The table guard applies to direct TABLE updates as well as the author view.
; A requirement can have no statement yet; it can never claim a proof/check.
(defun fn2-square-checksp (checks)
  (declare (xargs :verify-guards nil))
  (if (atom checks) (null checks)
    (let ((c (car checks)))
      (and (keyword-value-listp c)
           (fn2-decl-get :contract c) (fn2-decl-get :revision c)
           (fn2-decl-get :profile c) (fn2-decl-get :domain c)
           (natp (fn2-decl-get :horizon c)) (fn2-decl-get :unit c)
           (natp (fn2-decl-get :reached c)) (natp (fn2-decl-get :exercised c))
           (<= (fn2-decl-get :exercised c) (fn2-decl-get :reached c))
           (member-eq (fn2-decl-get :verdict c) '(:pass :fail :unchecked))
           (stringp (fn2-decl-get :location c))
           (fn2-square-checksp (cdr checks))))))
(defun fn2-square-sharedp (ids)
  (declare (xargs :verify-guards nil))
  (if (atom ids) (null ids)
    (and (true-listp (car ids)) (equal (len (car ids)) 2)
         (keywordp (caar ids)) (symbolp (cadar ids)) (cadar ids)
         (fn2-square-sharedp (cdr ids)))))
(defun fn2-square-rowp (name row world)
  (declare (xargs :verify-guards nil))
  (let* ((statement (fn2-decl-get :statement row))
         (vars (fn2-decl-get :vars row)) (body (fn2-decl-get :translated row))
         (proof (fn2-decl-get :proof row))
         (thm (and (symbolp (cadr proof)) (getpropc (cadr proof) 'theorem nil world))))
    (and (symbolp name) name (not (keywordp name)) (not (eq name t))
         (keyword-value-listp row)
         (member-eq (fn2-decl-get :schema row)
                    '(:g0 :g1 :g1q :g2 :route :crash :bound :invariant :assertion))
         (fn2-square-sharedp (fn2-decl-get :shared row))
         (or (not (fn2-decl-get :shared row))
             (and (member-eq (fn2-decl-get :claim row) '(:representation :compiler))
                  (member-eq (fn2-decl-get :schema row) '(:g0 :g1 :g2 :route)))
             (fn2-owed-teethp
               (list (fn2-decl-get :independent (fn2-decl-get :contract row))
                     (fn2-decl-get :shared-handler-mutation row))))
         (fn2-square-checksp (fn2-decl-get :checks row))
         (if statement
             (and (symbolp statement)
                  (equal vars (getpropc statement 'formals :missing world))
                  body (equal body (fn2-decl-statement-body statement world))
                  (consp (fn2-decl-get :teeth row))
                  (fn2-owed-teethp (fn2-square-tooth-names (fn2-decl-get :teeth row))))
           (and (not body) (not (fn2-decl-get :formula row))
                (not (fn2-decl-get :checks row))))
         (or (equal proof '(:owed))
             (and statement (true-listp proof) (equal (len proof) 2)
                  (eq (car proof) :proved) thm
                  (or (equal thm body) (equal thm (cons statement vars))))))))
(table fn2-squares nil nil :guard (fn2-square-rowp key val world))

; :claim distinguishes refinement from independent semantic validation.
; Co-located B books pass :layer :b explicitly, as can every registrar payload.
(defmacro defthm-owed (name vars formula &key teeth doc (schema ':assertion)
                           contract from shared (claim ':semantic) shared-handler-mutation
                           template origin case case-source boundary sides checker layer)
  (if (and (consp teeth) (fn2-owed-teethp teeth))
      (let ((statement (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name name) "$OWED") name)))
        (fn2-declare (list :owed name)
          (append (and layer (list :layer layer))
            (list :schema schema :template template :owner (or from (list :owed name))
                  :origin origin :case case :case-source case-source :boundary boundary
                  :contract contract :sides sides :shared shared :claim claim
                  :shared-handler-mutation shared-handler-mutation
                  :statement statement :vars vars :formula formula :teeth teeth :doc doc
                  :checker checker :proof '(:owed) :checks nil))
          (and from (fn2-decl-table (car from)) (list (list :owner from :at
                           (if (eq (car from) :operation-set) :core :coverage))))
          `((defun-nx ,statement ,vars ,formula))))
    (er hard 'defthm-owed
        "~x0 requires :teeth to name evaluating functions, not prose or forms." name)))

(defun fn2-square-owed-rows (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (equal (fn2-decl-get :proof (cdar rows)) '(:owed))
        (cons (car rows) (fn2-square-owed-rows (cdr rows)))
      (fn2-square-owed-rows (cdr rows)))))
(defun fn2-owed-names (world)
  (declare (xargs :verify-guards nil))
  (strip-cars (fn2-square-owed-rows (fn2-decl-rows :square world))))
(defun fn2-square-coveredp (checks)
  (declare (xargs :verify-guards nil))
  (and (consp checks)
       (or (and (eq (fn2-decl-get :verdict (car checks)) :pass)
                (posp (fn2-decl-get :exercised (car checks))))
           (fn2-square-coveredp (cdr checks)))))
; Counts are requirements, bound statements, admitted proofs, checked rows.
(defun fn2-square-counts (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) '(0 0 0 0)
    (let ((r (cdar rows)) (rest (fn2-square-counts (cdr rows))))
      (list (+ 1 (nth 0 rest))
            (+ (if (fn2-decl-get :statement r) 1 0) (nth 1 rest))
            (+ (if (eq (car (fn2-decl-get :proof r)) :proved) 1 0) (nth 2 rest))
            (+ (if (fn2-square-coveredp (fn2-decl-get :checks r)) 1 0) (nth 3 rest))))))
(defun fn2-owed-tooth-events (teeth world)
  (declare (xargs :verify-guards nil))
  (if (atom teeth) nil
    (if (and (getpropc (car teeth) 'symbol-class nil world)
             (equal (getpropc (car teeth) 'formals :missing world) nil))
        (cons `(assert-event (equal (,(car teeth)) t))
              (fn2-owed-tooth-events (cdr teeth) world))
      (er hard 'fn2-assert-owed-teeth
          "Tooth ~x0 must name an existing zero-argument evaluating function."
          (car teeth)))))
(defun fn2-owed-check-events (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((entry (fn2-decl-row (list :square (car names)) world)))
      (if entry
          (append (fn2-owed-tooth-events (fn2-square-tooth-names (fn2-decl-get :teeth entry)) world)
                  (fn2-owed-check-events (cdr names) world))
        (er hard 'fn2-assert-owed-teeth "Unknown obligation ~x0." (car names))))))
(defmacro fn2-assert-owed-teeth (&rest names)
  `(make-event
    (value (cons 'progn (fn2-owed-check-events ',names (w state))))))

(defun fn2-square-group (row)
  (declare (xargs :verify-guards nil))
  (list (fn2-decl-get :owner row) (fn2-decl-get :case-source row)
        (fn2-decl-get :schema row)))
(defun fn2-square-groups (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (fn2-square-group (cdar rows)) (fn2-square-groups (cdr rows)))))
(defun fn2-square-group-rows (group rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (equal group (fn2-square-group (cdar rows)))
        (cons (car rows) (fn2-square-group-rows group (cdr rows)))
      (fn2-square-group-rows group (cdr rows)))))
