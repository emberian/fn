; One producer footprint over arbitrary column frames. Callees compose
; independently of consumers' view names. A local composed proof and an
; existing row frame intersect at the owning table; neither bound is lost.
(in-package "ACL2")
(include-book "machines")

(defun fn2-column-setter-events (kind cols j)
 (declare (xargs :verify-guards nil))
 (if (atom cols) nil
  (let* ((set (fn2-arm-frame-setter kind (caar cols)))
         (raw (fn2-columns-pre "UPDATE-" (fn2-columns-sym (fn2-columns-col-name kind (caar cols)) "$AI"))))
   (cons `(defthm ,(fn2-columns-pre "FN2-COLUMN-KIDS-OF-" set)
     (implies (and (fn2-arm-kids 0 free a tbl) (member-equal ,j free))
              (fn2-arm-kids 0 free a (,set i v tbl)))
     :hints (("Goal" :in-theory (union-theories '(,set ,raw update-nth-array) (theory 'fn2-arm-frame-base))
              :use ((:instance fn2-arm-kids-update (i 0) (k ,j) (b tbl)
                      (v (update-nth i v (nth ,j tbl))))))))
    (fn2-column-setter-events kind (cdr cols) (+ 1 j))))))

(defun fn2-column-wholes (children)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil (cons (list :whole (car children)) (fn2-column-wholes (cdr children)))))

(defun fn2-column-contract-name (fn)
 (declare (xargs :verify-guards nil))
 (fn2-columns-sym fn "-COLUMN-FOOTPRINT"))

(defun fn2-column-base-event (fn kind world)
 (declare (xargs :verify-guards nil))
 (let* ((e (fn2-arm-frame-known fn kind world))
        (rowp (member-eq (car e) '(:arm :row :write)))
        (tk (if (eq (car e) :arm) (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world)
              (fn2-arm-frame-entry-tk e world)))
        (cs (if (eq (car e) :arm) (caddr e) (fn2-arm-frame-entry-j e)))
        (ch (if (eq (car e) :arm) (cadr e) (fn2-arm-frame-entry-s e)))
        (spec (append (and rowp (list (list :columns tk cs))) (fn2-column-wholes ch)))
        (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
        (name (fn2-column-contract-name fn))
        (row '(fn2-machine-slot id fn2-core)))
 `(progn
   (defthm ,name
    (implies (and (fn2-column-frame table columns children c0 fn2-core) (natp table)
                  (fn2-column-footprint-allows ',spec table columns children))
             (fn2-column-frame table columns children c0 ,out))
    :hints (("Goal" :in-theory
             (union-theories '(fn2-column-footprint-allows subsetp-equal
               fn2-column-frame-child ,@(and (eq (car e) :child) (list fn)))
              (theory 'fn2-arm-frame-base))
             :do-not-induct t
             :use ,(if (eq (car e) :child) nil
              (if rowp
               `((:instance ,(fn2-arm-frame-lemma fn e "-ARM-ROW-FRAME" kind world)
                   (fn2-arm-tb ,tk) (fn2-arm-row ,row) (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                 (:instance fn2-arm-row-frame-refl (table ,tk) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                 (:instance fn2-column-frame-after-row (a c0) (b fn2-core) (c ,out) (tb ,tk) (row ,row) (cs ',cs) (ch ',ch)))
               `((:instance ,(fn2-arm-frame-lemma fn e "-ARM-KIDS" kind world) (fn2-arm-free ',ch) (fn2-arm-c0 fn2-core))
                 (:instance fn2-arm-kids-refl (i 0) (free ',ch) (a fn2-core))
                 (:instance fn2-column-frame-after-kids (a c0) (b fn2-core) (c ,out) (free ',ch)))))))
    :rule-classes :rewrite)
   (in-theory (disable ,name))
   (table fn2-column-contracts ',fn ',spec))))

(defun fn2-column-setter-names (kind fields)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (cons (fn2-columns-pre "FN2-COLUMN-KIDS-OF-" (fn2-arm-frame-setter kind (car fields)))
    (fn2-column-setter-names kind (cdr fields)))))

(defun fn2-column-field-indices (fields names)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (let ((index (position-eq (car fields) names)))
   (if (not (natp index)) (er hard? 'fn2-defcolumn-footprint "Unknown column ~x0." (car fields))
    (cons index (fn2-column-field-indices (cdr fields) names))))))

(defun fn2-column-core-open (indices children)
 (declare (xargs :verify-guards nil))
 (if (atom indices) nil
  (let ((reader (car (nth (car indices) children))))
   (list* reader (fn2-columns-pre "UPDATE-" reader) (fn2-column-core-open (cdr indices) children)))))

(defun fn2-column-available-runes (fns world)
 (declare (xargs :verify-guards nil))
 (if (atom fns) nil
  (let ((name (fn2-column-contract-name (car fns))))
   (append (and (getpropc name 'theorem nil world) (list name))
           (fn2-column-available-runes (cdr fns) world)))))

(defun fn2-column-precise-event (fn layout fields kind world)
 (declare (xargs :verify-guards nil))
 (let* ((e (fn2-arm-frame-known fn kind world))
        (cols (fn2-column-field-indices fields (strip-cars (fn2-view-layout layout world))))
        (children (unquote (getpropc '*fn2-core-children* 'const nil world)))
        (table (fn2-view-child layout children 0))
        (child (car (nth table children)))
        (updater (fn2-columns-pre "UPDATE-" child))
        (free (remove-equal table (fn2-arm-frame-entry-kids e world)))
        (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
        (name (fn2-columns-sym fn "-PRECISE-COLUMN-FRAME")))
 `(progn
  (defthm ,name
   (fn2-column-frame ,table ',cols ',free fn2-core ,out)
   :rule-classes nil
   :hints (("Goal" :in-theory
    (union-theories '(,fn ,child ,updater
      ,@(fn2-column-setter-names layout fields)
      fn2-column-frame-table fn2-column-frame-child fn2-column-frame-refl
      ,@(fn2-column-available-runes (fn2-arm-frame-body-callees fn world) world) 
      fn2-column-footprint-allows subsetp-equal
      ,@(fn2-column-core-open free children))
      (theory 'fn2-arm-frame-base)) :do-not-induct t)))
  (table fn2-column-precisions ',fn '(:table ,table :columns ,cols :children ,free :theorem ,name)))))

(defun fn2-column-precise-contract-event (fn kind world)
 (declare (xargs :verify-guards nil))
 (let* ((e (fn2-arm-frame-known fn kind world))
        (p (cdr (assoc-eq fn (table-alist 'fn2-column-precisions world))))
        (ptb (fn2-arm-get :table p)) (pcs (fn2-arm-get :columns p)) (pch (fn2-arm-get :children p))
        (rowp (member-eq (car e) '(:row :write)))
        (tk (fn2-arm-frame-entry-tk e world)) (cs (fn2-arm-frame-entry-j e))
        (ch (fn2-arm-frame-entry-s e))
        (spec (append (list (list :columns ptb pcs))
                (and rowp (list (list :columns tk cs)))
                (fn2-column-wholes (remove-equal ptb ch))))
        (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
        (name (fn2-column-contract-name fn)) (row '(fn2-machine-slot id fn2-core)))
 `(progn
   (defthm ,name
    (implies (and (fn2-column-frame table columns children c0 fn2-core) (natp table)
                  (fn2-column-footprint-allows ',spec table columns children))
             (fn2-column-frame table columns children c0 ,out))
    :hints (("Goal" :in-theory
             (union-theories '(fn2-column-footprint-allows subsetp-equal)
              (theory 'fn2-arm-frame-base))
             :do-not-induct t
             :use ((:instance ,(fn2-arm-get :theorem p))
                   (:instance fn2-column-frame-after-column (a c0) (b fn2-core) (c ,out)
                      (tb ,ptb) (cs ',pcs) (ch ',pch))
                   ,@(and rowp
                    `((:instance ,(fn2-arm-frame-lemma fn e "-ARM-ROW-FRAME" kind world)
                       (fn2-arm-tb ,tk) (fn2-arm-row ,row) (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                      (:instance fn2-arm-row-frame-refl (table ,tk) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                      (:instance fn2-column-frame-after-row (a c0) (b fn2-core) (c ,out) (tb ,tk) (row ,row) (cs ',cs) (ch ',ch)))))))
    :rule-classes :rewrite)
   (in-theory (disable ,name))
   (table fn2-column-contracts ',fn ',spec))))

(defun fn2-column-spec-add (entry spec)
 (declare (xargs :verify-guards nil))
 (cond ((atom spec) (list entry))
       ((equal (cadr entry) (cadar spec))
        (cons (if (or (eq (car entry) :whole) (eq (caar spec) :whole))
                  (list :whole (cadr entry))
                (list :columns (cadr entry) (union-equal (caddr entry) (caddar spec)))) (cdr spec)))
       (t (cons (car spec) (fn2-column-spec-add entry (cdr spec))))))

(defun fn2-column-spec-normalize (spec)
 (declare (xargs :verify-guards nil))
 (if (atom spec) nil (fn2-column-spec-add (car spec) (fn2-column-spec-normalize (cdr spec)))))

(defun fn2-column-spec-refine (table columns spec)
 (declare (xargs :verify-guards nil))
 (if (atom spec) nil
  (cons (if (equal (cadar spec) table) (list :columns table columns) (car spec))
        (fn2-column-spec-refine table columns (cdr spec)))))

(defun fn2-column-spec-finer-p (children spec)
 (declare (xargs :verify-guards nil))
 (if (atom spec) nil
  (or (and (eq (caar spec) :columns) (member-equal (cadar spec) children))
      (fn2-column-spec-finer-p children (cdr spec)))))

(defun fn2-column-spec-children (spec)
 (declare (xargs :verify-guards nil))
 (if (atom spec) nil
  (cons (cadar spec) (fn2-column-spec-children (cdr spec)))))

(defun fn2-column-callee-specs (fns world)
 (declare (xargs :verify-guards nil))
 (if (atom fns) nil
  (let ((entry (assoc-eq (car fns) (table-alist 'fn2-column-contracts world))))
   (if (not entry) (er hard? 'fn2-column-callee-specs "Missing producer contract: ~x0." (car fns))
    (append (cdr entry) (fn2-column-callee-specs (cdr fns) world))))))

(defun fn2-column-callee-runes (fns)
 (declare (xargs :verify-guards nil))
 (if (atom fns) nil (cons (fn2-column-contract-name (car fns)) (fn2-column-callee-runes (cdr fns)))))

(defun fn2-column-compose-event (fn kind world)
 (declare (xargs :verify-guards nil))
 (let* ((callees (fn2-arm-frame-body-callees fn world))
        (e (fn2-arm-frame-known fn kind world))
        (tk (if (eq (car e) :arm) (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world) (fn2-arm-frame-entry-tk e world)))
        (cs (if (eq (car e) :arm) (caddr e) (fn2-arm-frame-entry-j e)))
        (ch (if (eq (car e) :arm) (cadr e) (fn2-arm-frame-entry-s e)))
        (rowp (and (member-eq (car e) '(:arm :row :write)) (not (member-equal tk ch))))
        (rawspec (fn2-column-spec-normalize (fn2-column-callee-specs callees world)))
        (spec (if rowp (fn2-column-spec-refine tk cs rawspec) rawspec))
        (row '(fn2-machine-slot id fn2-core)) (call (cons fn (formals fn world)))
        (recursive (member-eq fn (fn2-arm-frame-callees (getpropc fn 'unnormalized-body nil world) world nil)))
        (out (fn2-arm-frame-out-term fn call world)) (name (fn2-column-contract-name fn))
        (rawname (fn2-columns-sym name "-COMPOSED"))
        (base `(union-theories '(fn2-column-footprint-allows subsetp-equal
                  fn2-column-member-cons fn2-column-frame-refl)
                  (theory 'fn2-arm-frame-base)))
        (raw `(defthm ,(if rowp rawname name)
                (implies (and (fn2-column-frame table columns children c0 fn2-core) (natp table)
                              (fn2-column-footprint-allows ',rawspec table columns children))
                         (fn2-column-frame table columns children c0 ,out))
                :hints (("Goal" :in-theory (union-theories '(,fn ,@(fn2-column-callee-runes callees)) ,base)
                          ,@(if recursive `(:induct ,call) '(:do-not-induct t)))))))
 `(encapsulate nil
  ,(if rowp `(local ,raw) raw)
  ,@(and rowp
    `((defthm ,name
       (implies (and (fn2-column-frame table columns children c0 fn2-core) (natp table)
                     (fn2-column-footprint-allows ',spec table columns children))
                (fn2-column-frame table columns children c0 ,out))
       :hints (("Goal" :in-theory ,base :cases ((equal table ,tk)))
               ("Subgoal 2" :in-theory ,base :do-not-induct t :use ((:instance ,rawname)))
               ("Subgoal 1" :in-theory ,base :do-not-induct t
                :use ((:instance ,rawname (c0 fn2-core) (children (cons table children)))
                      (:instance ,(fn2-arm-frame-lemma fn e "-ARM-ROW-FRAME" kind world)
                        (fn2-arm-tb ,tk) (fn2-arm-row ,row) (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                      (:instance fn2-arm-row-frame-refl (table ,tk) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                      (:instance fn2-column-frame-reconcile-row (a fn2-core) (b ,out) (row ,row) (cs ',cs) (ch ',ch))
                      (:instance fn2-column-frame-trans (a c0) (b fn2-core) (c ,out))))))))
  (in-theory (disable ,name))
  (table fn2-column-contracts ',fn ',spec))))

(defun fn2-column-event (fn kind world)
 (declare (xargs :verify-guards nil))
 (let* ((e (fn2-arm-frame-known fn kind world))
        (children (if (eq (car e) :arm) (cadr e) (fn2-arm-frame-entry-s e))))
  (cond ((assoc-eq fn (table-alist 'fn2-column-contracts world)) '(value-triple :already))
        ((assoc-eq fn (table-alist 'fn2-column-precisions world)) (fn2-column-precise-contract-event fn kind world))
        ((or (eq (car e) :child)
             (not (getpropc fn 'unnormalized-body nil world))
             (and (member-eq (car e) '(:op :row :write :arm))
              (let ((spec (fn2-column-callee-specs (fn2-arm-frame-body-callees fn world) world)))
               (and (not (fn2-column-spec-finer-p children spec))
                    (subsetp-equal children (fn2-column-spec-children spec)))))) (fn2-column-base-event fn kind world))
        (t (fn2-column-compose-event fn kind world)))))

(defun fn2-column-events (fns kind)
 (declare (xargs :verify-guards nil))
 (if (atom fns) nil
  (cons `(make-event (value (fn2-column-event ',(car fns) ',kind (w state))))
        (fn2-column-events (cdr fns) kind))))

(defmacro fn2-defcolumn-footprint (fn &key kind layout columns)
 `(progn
   (make-event (value (fn2-column-precise-event ',fn ',layout ',columns ',kind (w state))))
   (make-event (value (fn2-column-precise-contract-event ',fn ',kind (w state))))))

(defun fn2-column-view-children (select children)
 (declare (xargs :verify-guards nil))
 (if (atom select) nil
  (cons (fn2-view-child (caar select) children 0) (fn2-column-view-children (cdr select) children))))

(defun fn2-column-view-table (spec observed fallback)
 (declare (xargs :verify-guards nil))
 (if (atom spec) fallback
  (if (and (eq (caar spec) :columns) (member-equal (cadar spec) observed)) (cadar spec)
   (fn2-column-view-table (cdr spec) observed fallback))))

(defun fn2-column-view-free (spec table)
 (declare (xargs :verify-guards nil))
 (if (atom spec) nil
  (if (and (eq (caar spec) :columns) (equal (cadar spec) table))
      (fn2-column-view-free (cdr spec) table)
    (cons (cadar spec) (fn2-column-view-free (cdr spec) table)))))

(defun fn2-column-view-columns (spec table)
 (declare (xargs :verify-guards nil))
 (if (atom spec) nil
  (if (and (eq (caar spec) :columns) (equal (cadar spec) table)) (caddar spec)
   (fn2-column-view-columns (cdr spec) table))))

(defun fn2-column-bindings (formals actuals)
 (declare (xargs :verify-guards nil))
 (if (atom formals) nil
  (cons (list (car formals) (car actuals)) (fn2-column-bindings (cdr formals) (cdr actuals)))))

; Consumer hint support below is for unparameterized carrier views. Row
; and bounded-range view projections remain available directly from DEFVIEW.
(defun fn2-column-projection-uses (view call world)
 (declare (xargs :verify-guards nil))
 (let* ((fn (car call)) (spec (cdr (assoc-eq fn (table-alist 'fn2-column-contracts world))))
        (entry (cdr (assoc-eq view (table-alist 'fn2-views world))))
        (kids (fn2-arm-frame-children-of world))
        (observed (fn2-column-view-children (fn2-arm-get :select entry) kids))
        (table (fn2-column-view-table spec observed (len kids)))
        (columns (fn2-column-view-columns spec table)) (children (fn2-column-view-free spec table))
        (formals (formals fn world)) (before (nth (position-eq 'fn2-core formals) (cdr call)))
        (out (fn2-arm-frame-out-term fn call world)))
  `((:instance ,(fn2-column-contract-name fn) ,@(fn2-column-bindings formals (cdr call))
      (c0 ,before) (table ,table) (columns ',columns) (children ',children))
    (:instance fn2-column-frame-refl (a ,before) (table ,table) (columns ',columns) (children ',children))
    (:instance ,(fn2-columns-sym view "-COLUMN-FRAME-PROJECTION")
      (a ,before) (b ,out) (table ,table) (columns ',columns) (children ',children)))))

(mutual-recursion
 (defun fn2-column-calls (term world)
  (declare (xargs :verify-guards nil :measure (acl2-count term)))
  (cond ((atom term) nil) ((eq (car term) 'quote) nil)
        (t (append (and (symbolp (car term)) (assoc-eq (car term) (table-alist 'fn2-column-contracts world))
                         (list term))
                   (and (consp (car term)) (fn2-column-calls (caddr (car term)) world))
                   (fn2-column-calls-list (cdr term) world)))))
 (defun fn2-column-calls-list (terms world)
  (declare (xargs :verify-guards nil :measure (acl2-count terms)))
  (if (atom terms) nil
   (append (fn2-column-calls (car terms) world) (fn2-column-calls-list (cdr terms) world)))))

(defun fn2-column-call-view-uses (views call world)
 (declare (xargs :verify-guards nil))
 (if (atom views) nil
  (append (fn2-column-projection-uses (car views) call world)
          (fn2-column-call-view-uses (cdr views) call world))))

(defun fn2-column-calls-view-uses (calls views world)
 (declare (xargs :verify-guards nil))
 (if (atom calls) nil
  (append (fn2-column-call-view-uses views (car calls) world)
          (fn2-column-calls-view-uses (cdr calls) views world))))

(mutual-recursion
 (defun fn2-column-view-references (view term)
  (declare (xargs :verify-guards nil :measure (acl2-count term)))
  (cond ((atom term) nil) ((eq (car term) 'quote) nil)
   (t (append (and (eq (car term) view) (list (caddr term)))
              (fn2-column-view-references-list view (cdr term))))))
 (defun fn2-column-view-references-list (view terms)
  (declare (xargs :verify-guards nil :measure (acl2-count terms)))
  (if (atom terms) nil
   (append (fn2-column-view-references view (car terms))
           (fn2-column-view-references-list view (cdr terms))))))

(defun fn2-column-transitive-uses (view refs before out)
 (declare (xargs :verify-guards nil))
 (if (atom refs) nil
  (cons `(:instance ,(fn2-columns-sym view "-TRANSITIVE")
           (a ,(car refs)) (b ,before) (c ,out))
        (fn2-column-transitive-uses view (cdr refs) before out))))

(defun fn2-column-view-chain-uses (views call clause world)
 (declare (xargs :verify-guards nil))
 (if (atom views) nil
  (let* ((fn (car call)) (formals (formals fn world))
         (before (nth (position-eq 'fn2-core formals) (cdr call)))
         (out (fn2-arm-frame-out-term fn call world))
         (refs (remove-duplicates-equal (fn2-column-view-references-list (car views) clause))))
   (append (fn2-column-transitive-uses (car views) refs before out)
           (fn2-column-view-chain-uses (cdr views) call clause world)))))

(defun fn2-column-calls-chain-uses (calls views clause world)
 (declare (xargs :verify-guards nil))
 (if (atom calls) nil
  (append (fn2-column-view-chain-uses views (car calls) clause world)
          (fn2-column-calls-chain-uses (cdr calls) views clause world))))

(defun fn2-column-view-hint (views clause world)
 (declare (xargs :verify-guards nil))
 (let* ((calls (remove-duplicates-equal (fn2-column-calls-list clause world)))
        (uses (remove-duplicates-equal
               (append (fn2-column-calls-view-uses calls views world)
                       (fn2-column-calls-chain-uses calls views clause world)))))
  (and uses (list :use uses))))

; Consumer proofs keep producer definitions closed and instantiate only
; contracts for calls present in their clause. These rules normalize static
; footprint/view declarations; they never open a state representation reader.
(deftheory fn2-column-projection-base
 (union-theories '(fn2-column-footprint-allows fn2-view-columns-protected fn2-view-column-protected
    (:e natp) (:e binary-append) (:e member-equal) (:e subsetp-equal) (:e nfix))
    (theory 'minimal-theory)))

; Seed facts for calls visible in the statement before simplification splits
; reader equalities. The stable hint remains useful for calls exposed later.
(defun fn2-column-hint-without-use (options)
 (declare (xargs :verify-guards nil))
 (if (atom options) nil
  (if (eq (car options) :use) (cddr options)
   (list* (car options) (cadr options) (fn2-column-hint-without-use (cddr options))))))
(defun fn2-column-use-list (uses)
 (declare (xargs :verify-guards nil))
 (cond ((atom uses) (and uses (list uses)))
       ((member-eq (car uses) '(:instance :functional-instance)) (list uses))
       (t uses)))
(defun fn2-column-seed-hints (hints uses)
 (declare (xargs :verify-guards nil))
 (if (atom hints) nil
  (cons (if (and (consp (car hints)) (equal (caar hints) "Goal"))
            (append (list "Goal") (fn2-column-hint-without-use (cdar hints))
             (list :use (append (fn2-column-use-list (fn2-arm-get :use (cdar hints))) uses)))
          (car hints))
        (fn2-column-seed-hints (cdr hints) uses))))
(defun fn2-column-seed-options (options uses)
 (declare (xargs :verify-guards nil))
 (if (atom options) nil
  (list* (car options)
         (if (eq (car options) :hints) (fn2-column-seed-hints (cadr options) uses) (cadr options))
         (fn2-column-seed-options (cddr options) uses))))
(defun fn2-column-consumer-event (views event world)
 (declare (xargs :verify-guards nil))
 (let ((hint (fn2-column-view-hint views (list (caddr event)) world)))
  (if (not hint) event
   (list* (car event) (cadr event) (caddr event)
          (fn2-column-seed-options (cdddr event) (cadr hint))))))
(defmacro fn2-with-column-projections (views event)
 `(make-event (value (fn2-column-consumer-event ',views ',event (w state)))))
