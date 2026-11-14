; Typed product lowering of a linear core carrier. The product below exists
; only in the generator: emitted code passes concrete child stobjs directly.
(in-package "ACL2")
(include-book "core-lowering")
(include-book "core-lenses")
 ; Logical reconstruction domain; never tested on the executable path.
(defun fn2-product-spinep (n x) (and (true-listp x) (equal (len x) n)))
(defthm fn2-product-update-nth-true-listp
 (implies (true-listp xs) (true-listp (update-nth i value xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth))))
(defthm fn2-product-update-nth-spine
 (implies (and (fn2-product-spinep n xs) (natp i) (< i n))
          (fn2-product-spinep n (update-nth i value xs)))
 :hints (("Goal" :in-theory (e/d (fn2-product-spinep) (update-nth)))))
(defthm fn2-product-spine-consp
 (implies (and (fn2-product-spinep n x) (posp n)) (consp x))
 :hints (("Goal" :in-theory (enable fn2-product-spinep)))
 :rule-classes :forward-chaining)
(in-theory (disable fn2-product-spinep))
(defun fn2-product-value (x) (list :value x))
(defun fn2-product-child (x) (list :child x))
(defun fn2-product-name (n)
 (declare (xargs :verify-guards nil))
 (packn-pos (list 'fn2-product-value- n) 'fn2-core))
(defun fn2-product-writer (field)
 (declare (xargs :verify-guards nil)) (fn2-columns-pre "UPDATE-" field))
(defun fn2-product-writers (entries)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (cons (cons (fn2-product-writer (caar entries)) (fn2-core-child-property (car entries) :stobj))
        (fn2-product-writers (cdr entries)))))
(defun fn2-product-calls-childp (child calls property world)
 (declare (xargs :verify-guards nil))
 (if (atom calls) nil
  (or (member-eq child
        (fn2-decl-get property (cdr (assoc-eq (car calls) (table-alist 'fn2-core-lowered world)))))
      (fn2-product-calls-childp child (cdr calls) property world))))
(defun fn2-product-callee-properties (calls property world)
 (declare (xargs :verify-guards nil))
 (if (atom calls) nil
  (let ((row (cdr (assoc-eq (car calls) (table-alist 'fn2-core-lowered world)))))
   (append (and (fn2-decl-get :shape-reverse row) (fn2-decl-get property row)
                (list (fn2-decl-get property row)))
           (fn2-product-callee-properties (cdr calls) property world)))))
 ; Open only mutable boundaries without proved output invariant summaries.
; Guard verification reuses summaries at the other boundaries.
(defun fn2-product-mutable-children (rows)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (append (and (fn2-decl-get :shape-reverse (cdar rows))
               (not (fn2-decl-get :child-invariants (cdar rows)))
               (list (fn2-decl-get :child (cdar rows))))
          (fn2-product-mutable-children (cdr rows)))))
(defun fn2-product-guard-callees (calls world)
 (declare (xargs :verify-guards nil))
 (fn2-lower-guard-openings
  (fn2-product-callee-properties calls :child world)
  (fn2-product-mutable-children (table-alist 'fn2-core-lowered world)) nil world 10000))
(defun fn2-product-entries (entries calls world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (append (and (or (member-eq (caar entries) calls)
                   (member-eq (fn2-product-writer (caar entries)) calls)
                   (fn2-product-calls-childp (fn2-core-child-property (car entries) :stobj) calls :children world))
               (list (car entries)))
          (fn2-product-entries (cdr entries) calls world))))
; Reading a child must not make it an output. Writing an unchanged projection
; back into a malformed logical core can extend its shape, so reconstruction
; follows actual core update sites even though inputs include every read.
(defun fn2-product-written-entries (entries calls world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (append (and (or (member-eq (fn2-product-writer (caar entries)) calls)
                  (fn2-product-calls-childp (fn2-core-child-property (car entries) :stobj) calls :written world))
              (list (car entries)))
          (fn2-product-written-entries (cdr entries) calls world))))
(mutual-recursion
 (defun fn2-product-expr (ir)
  (declare (xargs :verify-guards nil))
  (case (car ir)
   ((:value :child) (mv nil (cadr ir)))
   (:tuple (mv-let (err xs) (fn2-product-exprs (cadr ir)) (mv err (cons 'list xs))))
   (otherwise (mv :core-in-value-context nil))))
 (defun fn2-product-exprs (irs)
  (declare (xargs :verify-guards nil))
  (if (atom irs) (mv nil nil)
   (mv-let (err x) (fn2-product-expr (car irs))
    (mv-let (err2 xs) (fn2-product-exprs (cdr irs)) (mv (or err err2) (cons x xs)))))))
(defun fn2-product-child-irs (children)
 (declare (xargs :verify-guards nil))
 (if (atom children) nil
  (cons (fn2-product-child (car children)) (fn2-product-child-irs (cdr children)))))
(mutual-recursion
 (defun fn2-product-flat (ir children)
  (declare (xargs :verify-guards nil))
  (case (car ir)
   (:core (fn2-product-child-irs children))
   (:tuple (fn2-product-flat-list (cadr ir) children))
   (otherwise (list ir))))
 (defun fn2-product-flat-list (irs children)
  (declare (xargs :verify-guards nil))
  (if (atom irs) nil
   (append (fn2-product-flat (car irs) children) (fn2-product-flat-list (cdr irs) children)))))
(defun fn2-product-shapes (irs)
 (declare (xargs :verify-guards nil))
 (if (atom irs) nil
  (cons (if (eq (caar irs) :child) (car irs) (list (caar irs))) (fn2-product-shapes (cdr irs)))))
(defun fn2-product-bindings (irs counter)
 (declare (xargs :verify-guards nil))
 (if (atom irs) (mv nil counter)
  (mv-let (vars next) (fn2-product-bindings (cdr irs) (1+ counter))
   (mv (cons (if (eq (caar irs) :child) (cadar irs) (fn2-product-name counter)) vars) next))))
(mutual-recursion
 (defun fn2-product-rebind (ir vars children)
  (declare (xargs :verify-guards nil))
  (case (car ir)
   (:core (mv ir (nthcdr (len children) vars)))
   (:tuple (mv-let (irs rest) (fn2-product-rebind-list (cadr ir) vars children) (mv (list :tuple irs) rest)))
   (otherwise (mv (list (car ir) (car vars)) (cdr vars)))))
 (defun fn2-product-rebind-list (irs vars children)
  (declare (xargs :verify-guards nil))
  (if (atom irs) (mv nil vars)
   (mv-let (ir rest) (fn2-product-rebind (car irs) vars children)
    (mv-let (others final) (fn2-product-rebind-list (cdr irs) rest children) (mv (cons ir others) final))))))
(defun fn2-product-block (stages tail)
 (declare (xargs :verify-guards nil))
 (if (atom stages) tail
  (let ((vars (caar stages)) (call (cadar stages)) (rest (fn2-product-block (cdr stages) tail)))
   (if (equal (len vars) 1) `(let ((,(car vars) ,call)) (declare (ignorable ,@vars)) ,rest)
    `(mv-let ,vars ,call (declare (ignorable ,@vars)) ,rest)))))
(defun fn2-product-return (ir children)
 (declare (xargs :verify-guards nil))
 (mv-let (err xs) (fn2-product-exprs (fn2-product-flat ir children)) (mv err (fn2-arms-mvx xs))))
(defun fn2-product-outs (outs counter)
 (declare (xargs :verify-guards nil))
 (if (atom outs) (mv nil nil counter)
  (mv-let (vars irs next) (fn2-product-outs (cdr outs) (1+ counter))
   (let ((v (or (car outs) (fn2-product-name counter))))
    (mv (cons v vars) (cons (if (car outs) (fn2-product-child v) (fn2-product-value v)) irs) next)))))

 ; A retained mutable boundary returns scalars plus only its declared written
; children. The core carrier stays in the compiler IR, never a runtime tuple.
(defun fn2-product-callee (fn irs world counter self)
 (declare (xargs :verify-guards nil))
 (let* ((selfp (and self (eq fn (fn2-decl-get :source self))
                         (equal (getpropc fn 'recursivep nil world) (list fn))))
        (row (if selfp self (cdr (assoc-eq fn (table-alist 'fn2-core-lowered world)))))
        (child (fn2-decl-get :child row))
        (inputs (fn2-decl-get :children row))
        (written (fn2-decl-get :written row))
        (ins (getpropc fn 'stobjs-in nil world))
        (outs (getpropc fn 'stobjs-out nil world))
        (child-outs (if selfp (append (remove-eq 'fn2-core outs) written)
                      (getpropc child 'stobjs-out nil world))))
  (if (not (and
                (if selfp
                    (and (symbolp child) child (not (function-symbolp child world)))
                  (and (fn2-decl-get :shape-reverse row)
                       (getpropc (fn2-decl-get :shape-reverse row) 'theorem nil world)
                       (getpropc (fn2-decl-get :shape-preserved row) 'theorem nil world)
                       (function-symbolp child world)
                       (eq (symbol-class child world) :common-lisp-compliant)))
                (equal (len irs) (len ins))
                (equal (car (last irs)) '(:core))
                (equal (remove-eq nil ins) '(fn2-core))
                (eq (car (last ins)) 'fn2-core)
                (equal (remove-eq nil outs) '(fn2-core))
                (eq (car (last outs)) 'fn2-core)
                (or selfp
                    (and (equal (getpropc child 'stobjs-in nil world)
                                (append (remove-eq 'fn2-core ins) inputs))
                         (equal child-outs (append (remove-eq 'fn2-core outs) written))))))
      (mv :mutable-callee-shape nil nil counter)
   (mv-let (bad args) (fn2-product-exprs (butlast irs 1))
    (mv-let (vars vals next) (fn2-product-outs child-outs counter)
     (mv bad (list (list vars (cons child (append args inputs))))
         (if (equal (len outs) 1) '(:core)
          (list :tuple (append (take (1- (len outs)) vals) '((:core))))) next))))))
; Returns error, ordered binding stages, typed result, fresh-name counter.
; IF compiles two bounded code blocks; its product is bound once. Lambda
; arguments are evaluated once and mapped to typed values, never substituted.
(mutual-recursion
 (defun fn2-product-compile (term env entries children world counter fuel self)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (mv :compilation-budget nil nil counter))
   ((atom term) (let ((binding (assoc-eq term env)))
                 (if binding (mv nil nil (cdr binding) counter)
                  (mv :unbound-variable nil nil counter))))
   ((eq (car term) 'quote) (mv nil nil (fn2-product-value term) counter))
   ((consp (car term))
    (mv-let (err stages irs next) (fn2-product-compile-list (cdr term) env entries children world counter (1- fuel) self)
     (if err (mv err nil nil next)
      (mv-let (err2 more ir final)
        (fn2-product-compile (caddar term) (append (pairlis$ (cadar term) irs) env)
                             entries children world next (1- fuel) self)
        (mv err2 (append stages more) ir final)))))
   ((eq (car term) 'if)
    (mv-let (err stages condition next) (fn2-product-compile (cadr term) env entries children world counter (1- fuel) self)
     (mv-let (err2 left lir next2) (fn2-product-compile (caddr term) env entries children world next (1- fuel) self)
      (mv-let (err3 right rir next3) (fn2-product-compile (cadddr term) env entries children world next2 (1- fuel) self)
       (mv-let (err4 test) (fn2-product-expr condition)
        (mv-let (err5 ltail) (fn2-product-return lir children)
         (mv-let (err6 rtail) (fn2-product-return rir children)
          (let* ((flat (fn2-product-flat lir children))
                 (mismatch (not (equal (fn2-product-shapes flat)
                                      (fn2-product-shapes (fn2-product-flat rir children))))))
           (mv-let (vars final) (fn2-product-bindings flat next3)
            (mv-let (ir rest) (fn2-product-rebind lir vars children)
             (declare (ignore rest))
             (mv (or err err2 err3 err4 err5 err6 (and mismatch :branch-shape))
                 (append stages (list (list vars `(if ,test ,(fn2-product-block left ltail)
                                                         ,(fn2-product-block right rtail))))) ir final)))))))))))
   (t
    (mv-let (err stages irs next) (fn2-product-compile-list (cdr term) env entries children world counter (1- fuel) self)
     (let* ((fn (car term)) (entry (assoc-eq fn entries))
            (writer (assoc-eq fn (fn2-product-writers entries))))
      (cond
       (err (mv err nil nil next))
       (entry
        (if (equal irs '((:core)))
            (mv nil stages (fn2-product-child (fn2-core-child-property entry :stobj)) next)
          (mv :accessor-shape nil nil next)))
       (writer
        (if (equal irs (list (fn2-product-child (cdr writer)) '(:core)))
            (mv nil stages '(:core) next)
          (mv :updater-shape nil nil next)))
       ((eq fn 'cons)
        (let ((a (car irs)) (d (cadr irs)))
         (cond ((equal d '(:value (quote nil))) (mv nil stages (list :tuple (list a)) next))
               ((eq (car d) :tuple) (mv nil stages (list :tuple (cons a (cadr d))) next))
               (t (mv-let (bad xs) (fn2-product-exprs irs)
                    (mv bad stages (fn2-product-value (cons 'cons xs)) next))))))
       ((and (eq fn 'mv-nth) (eq (caadr irs) :tuple)
             (eq (caar irs) :value) (quotep (cadar irs)) (natp (cadr (cadar irs))))
        (let ((i (cadr (cadar irs))) (parts (cadadr irs)))
         (if (< i (len parts)) (mv nil stages (nth i parts) next)
          (mv :tuple-index nil nil next))))
       ((member-eq 'fn2-core (getpropc fn 'stobjs-in nil world))
        (mv-let (bad more ir final) (fn2-product-callee fn irs world next self)
         (mv bad (append stages more) ir final)))
       (t
        (mv-let (bad args) (fn2-product-exprs irs)
         (let ((outs (getpropc fn 'stobjs-out nil world)))
          (if (or bad (atom outs)) (mv (or bad :unknown-results) nil nil next)
           (mv-let (vars vals final) (fn2-product-outs outs next)
            (mv nil (append stages (list (list vars (cons fn args))))
                (if (equal (len vals) 1) (car vals) (list :tuple vals)) final))))))))))))
 (defun fn2-product-compile-list (terms env entries children world counter fuel self)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((atom terms) (mv nil nil nil counter))
        ((zp fuel) (mv :compilation-budget nil nil counter))
        (t (mv-let (err stages ir next) (fn2-product-compile (car terms) env entries children world counter (1- fuel) self)
             (mv-let (err2 more rest final) (fn2-product-compile-list (cdr terms) env entries children world next (1- fuel) self)
              (mv (or err err2) (append stages more) (cons ir rest) final)))))))
(defun fn2-product-env (formals)
 (declare (xargs :verify-guards nil))
 (if (atom formals) nil
  (cons (cons (car formals) (if (eq (car formals) 'fn2-core) '(:core) (fn2-product-value (car formals))))
        (fn2-product-env (cdr formals)))))
(defun fn2-product-wrapper (fn child face entries written world)
 (declare (xargs :verify-guards nil))
 (let* ((formals (getpropc fn 'formals nil world))
        (values (fn2-arms-result-vars (1- (len (getpropc fn 'stobjs-out nil world)))))
        (children (fn2-core-child-types entries)))
  `(defun ,face ,formals
    (declare (xargs :stobjs fn2-core :guard ,(getpropc fn 'guard t world)
                    :verify-guards t :guard-hints (("Goal" :in-theory (enable ,child)))))
    (stobj-let ,(fn2-arms-core-stobj-lets children world)
      (,@values ,@written)
      (,child ,@(remove-eq 'fn2-core formals) ,@children)
      ,(fn2-arms-mvx (append values '(fn2-core)))))))
(defun fn2-product-reserved-formals (formals)
 (declare (xargs :verify-guards nil))
 (if (atom formals) nil
  (let* ((name (symbol-name (car formals))) (prefix "FN2-PRODUCT-VALUE-"))
   (or (and (<= (length prefix) (length name))
            (equal (subseq name 0 (length prefix)) prefix))
       (fn2-product-reserved-formals (cdr formals))))))
; An unchanged write is an identity only when the selected core cell exists.
; Keep this list argument separate from the substantive operation proof.
(defthm fn2-product-update-nth-current
 (implies (and (natp n) (< n (len xs)))
          (equal (update-nth n (nth n xs) xs) xs))
 :hints (("Goal" :induct (nth n xs) :in-theory (enable nth update-nth))))
(defun fn2-product-two-induct (n m xs)
 (if (and (posp n) (posp m) (consp xs))
     (fn2-product-two-induct (1- n) (1- m) (cdr xs)) (list n m xs)))
(defthm fn2-product-writeback-other
 (implies (and (natp n) (natp m) (< n (len xs)) (not (equal n m)))
  (equal (update-nth n (nth n xs) (update-nth m value xs))
         (update-nth m value xs)))
 :hints (("Goal" :induct (fn2-product-two-induct n m xs)
          :expand ((update-nth m value xs)) :in-theory (enable nth update-nth))))
(defun fn2-product-two-index-induct (n m xs)
 (if (and (posp n) (posp m))
     (fn2-product-two-index-induct (1- n) (1- m) (cdr xs)) (list n m xs)))
(defthm fn2-product-update-nth-commute
 (implies (and (natp n) (natp m) (not (equal n m)))
  (equal (update-nth n a (update-nth m b xs))
         (update-nth m b (update-nth n a xs))))
 :hints (("Goal" :induct (fn2-product-two-index-induct n m xs)
          :expand ((update-nth m b xs) (update-nth n a xs))
          :in-theory (enable update-nth))))
; Only one orientation per selected pair, in registry order, prevents loops.
(defun fn2-product-commute-facts (field entries world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((writer (fn2-product-writer field))
         (other (fn2-product-writer (caar entries)))
         (name (fn2-columns-sym writer
                 (concatenate 'string "-LOWERING-COMMUTES-" (symbol-name other)))))
   (append
    (and (not (getpropc name 'theorem nil world))
     `((defthm ,name
        (equal (,writer a (,other b fn2-core))
               (,other b (,writer a fn2-core)))
        :hints (("Goal" :in-theory (e/d (,writer ,other) (nth update-nth)))))))
    (fn2-product-commute-facts field (cdr entries) world)))))
(defthm fn2-product-update-nth-shadow
 (implies (natp n)
  (equal (update-nth n a (update-nth n b xs)) (update-nth n a xs)))
 :hints (("Goal" :induct (update-nth n a xs) :in-theory (enable update-nth))))
(defun fn2-product-shadow-facts (entries world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((writer (fn2-product-writer (caar entries)))
         (name (fn2-columns-sym writer "-LOWERING-SHADOW")))
   (append
    (and (not (getpropc name 'theorem nil world))
     `((defthm ,name
        (equal (,writer a (,writer b fn2-core)) (,writer a fn2-core))
        :hints (("Goal" :in-theory (e/d (,writer) (nth update-nth)))))))
    (fn2-product-shadow-facts (cdr entries) world)))))
(defun fn2-product-core-shape-events (world)
 (declare (xargs :verify-guards nil))
 (and (not (getpropc 'fn2-product-core-shape 'theorem nil world))
  `((defthm fn2-product-core-shape
     (implies (fn2-corep fn2-core)
      (and (fn2-product-spinep ,(len (fn2-core-child-registry world)) fn2-core)
           (true-listp fn2-core)
           (equal (len fn2-core) ,(len (fn2-core-child-registry world)))
           ,@(and (consp (fn2-core-child-registry world)) '((consp fn2-core)))))
     :hints (("Goal" :in-theory
       (e/d (fn2-corep fn2-product-spinep)
            (,@(strip-cars (fn2-lower-predicates
                 (fn2-core-child-types (fn2-core-child-registry world)) "P"))))))))))
(defun fn2-product-cross-writeback-facts (field entries world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((other (caar entries)) (writer (fn2-product-writer field))
         (other-writer (fn2-product-writer other))
         (name (fn2-columns-sym field
                 (concatenate 'string "-LOWERING-WRITEBACK-AFTER-" (symbol-name other)))))
   (append
    (and (not (eq field other)) (not (getpropc name 'theorem nil world))
     `((defthm ,name
        (implies (fn2-product-spinep ,(len (fn2-core-child-registry world)) fn2-core)
         (equal (,writer (,field fn2-core) (,other-writer value fn2-core))
                (,other-writer value fn2-core)))
        :hints (("Goal" :in-theory
          (e/d (fn2-product-spinep ,field ,writer ,other-writer)
               (fn2-corep nth update-nth
                ,@(strip-cars (fn2-lower-predicates
                    (fn2-core-child-types (fn2-core-child-registry world)) "P")))))))))
    (fn2-product-cross-writeback-facts field (cdr entries) world)))))
(defun fn2-product-writeback-facts (entries all world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((field (caar entries)) (writer (fn2-product-writer field))
         (name (fn2-columns-sym field "-LOWERING-WRITEBACK-IDENTITY")))
   (append
    (and (not (getpropc name 'theorem nil world))
     `((defthm ,name
        (implies (fn2-product-spinep ,(len (fn2-core-child-registry world)) fn2-core)
                 (equal (,writer (,field fn2-core) fn2-core) fn2-core))
        :hints (("Goal" :in-theory
          (e/d (fn2-product-spinep ,field ,writer)
               (fn2-corep nth update-nth
                ,@(strip-cars (fn2-lower-predicates
                    (fn2-core-child-types (fn2-core-child-registry world)) "P")))))))))
    (fn2-product-cross-writeback-facts field all world)
    (fn2-product-commute-facts field (cdr entries) world)
    (fn2-product-writeback-facts (cdr entries) all world)))))
(defun fn2-product-proof-leaves (calls opened fields world)
 (declare (xargs :verify-guards nil))
 (if (atom calls) nil
  (append
   (and (not (member-eq (car calls) opened))
        (not (member-eq (car calls) fields))
        (getpropc (car calls) 'unnormalized-body nil world)
        (list (car calls)))
   (fn2-product-proof-leaves (cdr calls) opened fields world))))
(defun fn2-product-spine-facts (entries world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((writer (fn2-product-writer (caar entries)))
         (name (fn2-columns-sym writer "-LOWERING-SPINE"))
         (count (len (fn2-core-child-registry world))))
   (append
    (and (not (getpropc name 'theorem nil world))
     `((defthm ,name
        (implies (fn2-product-spinep ,count fn2-core)
                 (fn2-product-spinep ,count (,writer value fn2-core)))
        :hints (("Goal" :in-theory
          (e/d (,writer) (fn2-product-spinep nth update-nth)))))))
    (fn2-product-spine-facts (cdr entries) world)))))
(defun fn2-product-read-events (entries written)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (append (fn2-core-lens-read-events (caar entries) written)
          (fn2-product-read-events (cdr entries) written))))
; Recognize the columns preservation contract by its complete live formula.
; Eligibility is not a proof: every child summary below is proved anew.
(defun fn2-product-source-invariantp (fn predicate suffix world)
 (declare (xargs :verify-guards nil))
 (let* ((outs (getpropc fn 'stobjs-out nil world))
        (call (cons fn (getpropc fn 'formals nil world)))
        (result (if (equal outs '(fn2-core)) call `(mv-nth ',(- (len outs) 1) ,call))))
  (equal (getpropc (fn2-columns-sym fn suffix) 'theorem nil world)
    `(implies (if (fn2-corep fn2-core) (fn2-core-wfp fn2-core) 'nil)
              (,predicate ,result)))))
; Normalize the finite result product once in a proof-only predicate. Separate
; projection proofs would otherwise repeat the complete operation body.
(defun fn2-product-output-conditions (outputs index single)
 (declare (xargs :verify-guards nil))
 (if (atom outputs) nil
  (append
   (and (car outputs)
     (let ((result (if single 'result `(mv-nth ,index result))) (obj (car outputs)))
      (list `(,(fn2-columns-sym obj "P") ,result)
            `(,(fn2-columns-sym obj "-WFP") ,result))))
   (fn2-product-output-conditions (cdr outputs) (+ 1 index) single))))
(defun fn2-product-output-corollaries (child outputs index guard args single predicate theorem)
 (declare (xargs :verify-guards nil))
 (if (atom outputs) nil
  (let* ((obj (car outputs))
         (result (if single `(,child ,@args) `(mv-nth ,index (,child ,@args)))))
   (append
    (and obj
      (list `(defthm ,(fn2-columns-sym child
                        (concatenate 'string "-OUTPUT-" (symbol-name obj) "-INVARIANTS"))
        (implies ,guard
          (and (,(fn2-columns-sym obj "P") ,result)
               (,(fn2-columns-sym obj "-WFP") ,result)))
        :hints (("Goal" :use ((:instance ,theorem))
                 :in-theory (e/d (,predicate) (,child)))))))
    (fn2-product-output-corollaries child (cdr outputs) (+ 1 index) guard args single predicate theorem)))))
(defun fn2-product-output-invariants (child outputs index guard args openings single opaque)
 (declare (xargs :verify-guards nil))
 (and (remove-eq nil outputs)
  (let ((predicate (fn2-columns-sym child "-OUTPUT-INVARIANTP"))
        (theorem (fn2-columns-sym child "-OUTPUTS-PRESERVED")))
   (append
    `((defun-nx ,predicate (result)
        (and ,@(fn2-product-output-conditions outputs index single)))
      (defthm ,theorem (implies ,guard (,predicate (,child ,@args)))
        :hints (("Goal" :in-theory (e/d (,predicate ,child ,@openings) ,opaque)))
        :rule-classes nil))
    (fn2-product-output-corollaries child outputs index guard args single predicate theorem)
    `((in-theory (disable ,predicate)))))))
(defun fn2-product-invariant-theorems (events)
 (declare (xargs :verify-guards nil))
 (if (atom events) nil
  (append (and (eq (caar events) 'defthm) (list (cadar events)))
          (fn2-product-invariant-theorems (cdr events)))))
(defun fn2-product-events-mode (fn child teeth world recursive)
 (declare (xargs :verify-guards nil))
 (mv-let (expansion-problem body opened)
  (fn2-lower-expand (getpropc fn 'unnormalized-body nil world)
    (append (strip-cars (fn2-core-child-registry world))
            (strip-cars (fn2-product-writers (fn2-core-child-registry world))))
    world (list fn) 10000 nil)
 (let* ((body body)
        (measure (and recursive (fn2-lower-scalar-measure fn world)))
        (formals (getpropc fn 'formals nil world))
        (ins (getpropc fn 'stobjs-in nil world))
        (outs (getpropc fn 'stobjs-out nil world))
        (entries (and (pseudo-termp body) (fn2-product-entries (fn2-core-child-registry world) (all-fnnames body) world)))
        (children (fn2-core-child-types entries))
        (written (fn2-core-child-types (fn2-product-written-entries entries (all-fnnames body) world)))
        (args (append (remove-eq 'fn2-core formals) children))
        (face (fn2-columns-sym child "-CORE-FACE"))
        (execution (fn2-columns-sym child "-EXEC-CORE-FACE"))
        (typed (fn2-columns-sym child "-TYPED-EXECUTION-REFINES-CORE"))
        (shaped (fn2-columns-sym child "-SPINE-EXECUTION-REFINES-CORE"))
        (reverse (fn2-columns-sym child "-CORE-TO-EXECUTION"))
        (preserves (fn2-columns-sym child "-CORE-SPINE-PRESERVED"))
        (count (len (fn2-core-child-registry world)))
        (guarded (fn2-columns-sym child "-GUARDED-EXECUTION-REFINES-CORE"))
        (bridge (fn2-columns-sym child "-EXECUTION-CORRESPONDENCE"))
        (refinement (fn2-columns-sym child "-REFINES-CORE"))
        (source-guard (getpropc fn 'guard t world))
        (execution-formula `(implies (and (fn2-corep fn2-core) ,source-guard)
                              (equal (,execution ,@formals) (,fn ,@formals))))
        (guard (fn2-lower-substitute (getpropc fn 'guard t world)
                (acons '(fn2-core-wfp fn2-core) (cons 'and (fn2-lower-predicates children "-WFP"))
                 (acons '(fn2-corep fn2-core) (cons 'and (fn2-lower-predicates children "P"))
                  (fn2-lower-projections entries))) world))
        (invariants
         (and (fn2-product-source-invariantp fn 'fn2-corep "-PRESERVES-TYPE" world)
              (fn2-product-source-invariantp fn 'fn2-core-wfp "-PRESERVES-WFP" world)
              (fn2-product-output-invariants child
                (append (make-list (- (len outs) 1) :initial-element nil) written)
                0 guard args (fn2-product-guard-callees (all-fnnames body) world)
                (equal (+ (- (len outs) 1) (len written)) 1)
                (fn2-product-proof-leaves (all-fnnames body) opened
                 (append (strip-cars entries) (strip-cars (fn2-product-writers entries))) world))))
        (problem
         (cond (expansion-problem expansion-problem)
               ((fn2-lower-teeth-problem teeth) :evidence-pair)
               ((fn2-product-reserved-formals formals) :reserved-formal)
               ((not (and (equal (remove-eq nil ins) '(fn2-core))
                          (eq (car (last formals)) 'fn2-core))) :input-shape)
               ((not (and (equal (remove-eq nil outs) '(fn2-core))
                          (eq (car (last outs)) 'fn2-core))) :output-shape)
               ((and (null written) (equal (len outs) 1)) :empty-result)
               ((and (getpropc fn 'recursivep nil world) (not measure)) :recursive)
               ((and recursive (not measure)) :unsupported-recursive-measure)
               ((or (function-symbolp child world) (function-symbolp face world)) :already-defined)
               ((member-eq 'fn2-core (fn2-lower-vars guard)) :unlowered-guard)
               (t nil))))
  (mv-let (err stages ir next) (fn2-product-compile body (fn2-product-env formals) entries written world 0 10000
      (and measure (list :source fn :child child :children children :written written)))
   (declare (ignore next))
   (mv-let (err2 tail) (fn2-product-return ir written)
    (if (or problem err err2)
        `(make-event (er soft 'defcore-product-child "Cannot lower ~x0: ~x1." ',fn ',(or problem err err2)))
     `(progn
       ,@(fn2-product-core-shape-events world)
       ,@(fn2-core-lens-missing-events
           (fn2-product-read-events entries (fn2-product-written-entries entries (all-fnnames body) world)) world)
       ,@(fn2-product-spine-facts (fn2-product-written-entries entries (all-fnnames body) world) world)
       ,@(fn2-product-shadow-facts (fn2-product-written-entries entries (all-fnnames body) world) world)
       ,@(fn2-product-writeback-facts (fn2-product-written-entries entries (all-fnnames body) world)
                                     (fn2-product-written-entries entries (all-fnnames body) world) world)
       (defun ,child ,args
        (declare (ignorable ,@args)
                 (xargs :stobjs ,children :guard ,guard :verify-guards ,(not measure)
                        ,@(and measure `(:measure ,measure :ruler-extenders :all))
                        :guard-hints (("Goal" :in-theory
                           (enable ,@(fn2-lower-guard-theory guard body world)
                             ,@(fn2-product-guard-callees (all-fnnames body) world))))))
        ,(fn2-product-block stages tail))
       ,@invariants
       ,@(and measure
           `((verify-guards ,child
              :hints (("Goal" :in-theory
                (enable ,@(fn2-lower-guard-theory guard body world)
                        ,@(fn2-product-guard-callees (all-fnnames body) world)))))))
       (assert-event
        (and (eq (symbol-class ',child (w state)) :common-lisp-compliant)
             (equal (getpropc ',child 'stobjs-in nil (w state)) ',(append (remove-eq 'fn2-core ins) children))
             (equal (getpropc ',child 'stobjs-out nil (w state)) ',(append (remove-eq 'fn2-core outs) written))))
       ,(fn2-product-wrapper fn child execution entries written world)
       (assert-event (and (equal (getpropc ',execution 'stobjs-in nil (w state)) ',ins)
                          (equal (getpropc ',execution 'stobjs-out nil (w state)) ',outs)))
       ;; This is the substantive extraction proof. The executable wrapper is
       ;; independent of the original operation and contains no type recheck.
       (defthm ,shaped
        (implies (fn2-product-spinep ,count fn2-core)
                 (equal (,execution ,@formals) (,fn ,@formals)))
        :hints (("Goal" ,@(and measure `(:induct (,fn ,@formals))) :in-theory
          (e/d (,execution ,child ,fn ,@opened
                ,@(strip-cadrs (fn2-product-read-events entries
                      (fn2-product-written-entries entries (all-fnnames body) world)))
                ,@(fn2-product-callee-properties (all-fnnames body) :shape-reverse world)
                ,@(fn2-product-callee-properties (all-fnnames body) :execution world)
                ,@(fn2-lower-leaf-properties (table-alist 'fn2-core-lowered world)
                                             (all-fnnames body) :reverse))
               (fn2-corep ,@(strip-cars entries) ,@(strip-cars (fn2-product-writers entries))
                ,@(fn2-product-callee-properties (all-fnnames body) :shape-refinement world)
                ,@(remove-eq fn (fn2-product-proof-leaves (all-fnnames body) opened
                     (append (strip-cars entries) (strip-cars (fn2-product-writers entries))) world))
                ,@(fn2-lower-leaf-properties (table-alist 'fn2-core-lowered world)
                                             (all-fnnames body) :source)
                ,@(fn2-lower-leaf-properties (table-alist 'fn2-core-lowered world)
                                             (all-fnnames body) :refinement)
                ,@(strip-cars (fn2-lower-predicates
                     (fn2-core-child-types (fn2-core-child-registry world)) "P")))))))
       (defthm ,typed
        (implies (fn2-corep fn2-core)
                 (equal (,execution ,@formals) (,fn ,@formals)))
        :hints (("Goal" :use ((:instance ,shaped))
                 :in-theory (disable ,execution ,child ,fn ,shaped fn2-corep))))
       (defthm ,reverse
        (implies (fn2-product-spinep ,count fn2-core)
                 (equal (,fn ,@formals) (,execution ,@formals)))
        :hints (("Goal" :use ((:instance ,shaped))
                 :in-theory (disable ,execution ,child ,fn ,shaped))))
       (in-theory (disable ,shaped ,reverse))
       (defthm ,preserves
        (implies (fn2-product-spinep ,count fn2-core)
          (fn2-product-spinep ,count
            ,(if (equal (len outs) 1) `(,fn ,@formals)
               `(mv-nth ,(1- (len outs)) (,fn ,@formals)))))
        :hints (("Goal" :in-theory
          (e/d (,reverse ,execution)
               (,fn ,child ,shaped ,@(strip-cars entries)
                ,@(strip-cars (fn2-product-writers entries)))))))
       (defthm ,guarded ,execution-formula
        :hints (("Goal" :use ((:instance ,typed))
                 :in-theory (disable ,execution ,child ,fn ,typed))))
       (in-theory (disable ,typed ,guarded))
       ;; Only the logical totalization handles malformed core values. MBE's
       ;; executable branch is the generated reconstruction, with no corep walk.
       (defun ,face ,formals
        (declare (xargs :stobjs fn2-core :guard ,source-guard :verify-guards t
                        :guard-hints (("Goal" :in-theory (disable ,execution ,fn fn2-corep)))))
        (mbe :logic (if (fn2-corep fn2-core) (,execution ,@formals) (,fn ,@formals))
             :exec (,execution ,@formals)))
       (assert-event (and (equal (getpropc ',face 'stobjs-in nil (w state)) ',ins)
                          (equal (getpropc ',face 'stobjs-out nil (w state)) ',outs)))
       (defthm ,bridge
        (implies (and (fn2-corep fn2-core) ,source-guard)
                 (equal (,face ,@formals) (,execution ,@formals)))
        :hints (("Goal" :in-theory (e/d (,face) (,execution ,fn))))
        :rule-classes nil)
       (defthm ,refinement
        (equal (,face ,@formals) (,fn ,@formals))
        :hints (("Goal" :use ((:instance ,typed))
                 :in-theory (e/d (,face) (,execution ,fn ,typed)))))
       ,@(fn2-lower-obligation-events fn child face formals
           `(equal (,face ,@formals) (,fn ,@formals)) refinement teeth)
       ,@(fn2-lower-obligation-events fn child execution formals execution-formula guarded
           (or teeth (list (fn2-columns-sym refinement "-POSITIVE")
                           (fn2-columns-sym refinement "-NEGATIVE"))))
       (in-theory (disable ,face ,execution ,child))
       (table fn2-core-lowered ',fn
        '(:child ,child :face ,face :execution ,execution
          :typed-refinement ,typed :guarded-refinement ,guarded
          :shape-refinement ,shaped :shape-reverse ,reverse :shape-preserved ,preserves
          :execution-correspondence ,bridge :refinement ,refinement
          :children ,children :written ,written :child-invariants ,(fn2-product-invariant-theorems invariants)
          :obligation ,refinement
          :execution-obligation ,guarded)))))))))
(defun fn2-product-events (fn child teeth world)
 (declare (xargs :verify-guards nil))
 (fn2-product-events-mode fn child teeth world nil))
; Staged entry point: not selected by production closure planning yet.
(defmacro defcore-recursive-product-child (fn child &key teeth)
 `(make-event (value (fn2-product-events-mode ',fn ',child ',teeth (w state) t))))
(defmacro defcore-product-child (fn child &key teeth)
 `(make-event (value (fn2-product-events ',fn ',child ',teeth (w state)))))

 ; Derive both reader and mutable boundaries bottom-up. A mutable callee is
; subsequently compiled as one child call using its proved spine contract.
(defun fn2-product-family-events (order root child teeth world)
 (declare (xargs :verify-guards nil))
 (if (atom order) nil
  (let* ((fn (car order))
         (name (if (eq fn root) child (fn2-columns-sym fn "-LOWERED-CHILD")))
         (macro (if (member-eq 'fn2-core (getpropc fn 'stobjs-out nil world))
                    'defcore-product-child 'defcore-readonly-child)))
   (cons `(,macro ,fn ,name ,@(and (eq fn root) teeth `(:teeth ,teeth)))
         (fn2-product-family-events (cdr order) root child teeth world)))))
(defmacro defcore-product-closure (fn child &key teeth)
 `(make-event
   (mv-let (problem order seen)
    (fn2-lower-reader-plan ',fn
     (append (strip-cars (fn2-core-child-registry (w state)))
             (strip-cars (fn2-product-writers (fn2-core-child-registry (w state)))))
     (w state) nil nil 10000 :all)
    (declare (ignore seen))
    (if (or problem (not (member-eq ',fn order)))
        (er soft 'defcore-product-closure "Cannot plan ~x0: ~x1." ',fn
            (or problem :root-already-lowered))
      (value (cons 'progn
        (fn2-product-family-events order ',fn ',child ',teeth (w state))))))))
