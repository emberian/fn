; fn: `def-keyset-check' --- a per-element membership test over two lists,
; quadratic in :logic (member-equal), linear in :exec (one local hash set,
; books/acceptance-alloc.lisp's fn-keyset), from one declaration.
;
; The pattern this replaces, hand-written in books/store-files.lisp
; (fn-sf-success-listp: every success is a pair bound among the records'
; pairs) and books/retention.lisp (fn-retain-ids-disjointp: no pin id is
; among the release ids), with books/acceptance-alloc.lisp's fn-ks-subsetp
; and fn-no-duplicatesp beside them: a fill of the set with one list's keys,
; a scan of the other list against it, a with-local-stobj wrapper, a bridge
; to the member-equal recursion under an empty table, and an `mbe' whose
; :exec takes the set only past a length threshold.
;
;   (def-keyset-check NAME (XS YS)
;     :sense :present | :absent        ; each XS key is bound / unbound in YS's keys
;     [:xs-key (lambda (x) TERM)]      ; the key an XS element asks for (default x)
;     [:ys-key (lambda (y) TERM)]      ; the key a YS element puts (default y)
;     [:each (lambda (x) TERM)]        ; a predicate on each XS element (default t)
;     [:base (null xs) | t]            ; the value at XS's end (default t)
;     [:logic-member (lambda (x ys) TERM) :member-is THM]
;                                      ; the :logic membership test as the
;                                      ; instance states it, and the named
;                                      ; correspondence (c04 6a): THM is
;                                      ; (equal TERM (if (member-equal XS-KEY[x]
;                                      ; (NAME-keys ys)) t nil)); default:
;                                      ; member-equal over NAME-keys itself
;     [:policy :long | :always | :nonempty])   ; when the :exec takes the set:
;                                      ; YS long (fn-ks-longp, the default),
;                                      ; always, or XS non-empty (a reopen has
;                                      ; no successes: no table is filled)
;
; Generated: NAME-keys (the YS keys, :logic), NAME-fill (the set of YS's
; keys), NAME-scan (XS against the set), NAME-ks (the with-local-stobj
; wrapper), NAME-walk (the direct walk, executable), NAME with
;   :logic (if (consp XS) (and EACH[x] SENSE(LOGIC-MEMBER[x, YS]) (NAME (cdr XS) YS)) BASE)
;   :exec  (if POLICY (NAME-ks XS YS) (NAME-walk XS YS))
; and the bridges NAME-scan-after-fill (under an empty table: the scan of the
; filled set is the :logic recursion), NAME-ks-is-logic and
; NAME-walk-is-logic, every executable guard-verified.  Each bridge is a
; functional instance of this book's library (fn-kc-*), proved once over
; constrained key, element and sense functions; the instance's obligations
; are its definitional equations and :member-is.
;
; (table fn-teeth-owed 'NAME-ks-is-logic ...) and (table fn-teeth-owed
; 'NAME-walk-is-logic ...) record the keystones the test book's defteeth
; must witness: 0, threshold-1, threshold and threshold+1 elements, success
; and failure in both arms, a dotted tail where the guard allows it (c04 6b).
;
; Refused at expansion, by name: a :sense other than :present/:absent; a
; lambda of the wrong arity; :logic-member without :member-is (or the
; converse); a :policy outside the three; NAME declared twice; :member-is
; not a theorem.

(in-package "ACL2")
(include-book "acceptance-alloc")

; ---------------------------------------------------------------------------
; The library: a keyed fill, a scan with a sense, and their bridge.

(encapsulate
  (((fn-kc-xkey *) => *)
   ((fn-kc-ykey *) => *)
   ((fn-kc-each *) => *)
   ((fn-kc-want *) => *)
   ((fn-kc-base *) => *))
  (local (defun fn-kc-xkey (x) x))
  (local (defun fn-kc-ykey (y) y))
  (local (defun fn-kc-each (x) (declare (ignore x)) t))
  (local (defun fn-kc-want (b) b))
  (local (defun fn-kc-base (xs) (declare (ignore xs)) t)))

(defun fn-kc-keys (ys)
  (if (consp ys) (cons (fn-kc-ykey (car ys)) (fn-kc-keys (cdr ys))) nil))

(defun fn-kc-logic (xs ys)
  (if (consp xs)
      (and (fn-kc-each (car xs))
           (fn-kc-want (if (member-equal (fn-kc-xkey (car xs)) (fn-kc-keys ys)) t nil))
           (fn-kc-logic (cdr xs) ys))
    (fn-kc-base xs)))

(defun fn-kc-fill (ys fn-keyset)
  (declare (xargs :stobjs fn-keyset :verify-guards nil))
  (if (consp ys)
      (let ((fn-keyset (fn-keyset-tab-put (fn-kc-ykey (car ys)) t fn-keyset)))
        (fn-kc-fill (cdr ys) fn-keyset))
    fn-keyset))

(defun fn-kc-scan (xs fn-keyset)
  (declare (xargs :stobjs fn-keyset :verify-guards nil))
  (if (consp xs)
      (and (fn-kc-each (car xs))
           (fn-kc-want (fn-keyset-tab-boundp (fn-kc-xkey (car xs)) fn-keyset))
           (fn-kc-scan (cdr xs) fn-keyset))
    (fn-kc-base xs)))

(defthm fn-kc-bound-after-fill
  (iff (consp (hons-assoc-equal k (nth 0 (fn-kc-fill ys fn-keyset))))
       (or (member-equal k (fn-kc-keys ys))
           (consp (hons-assoc-equal k (nth 0 fn-keyset)))))
  :hints (("Goal" :induct (fn-kc-fill ys fn-keyset)
           :in-theory (disable fn-keyset-tab-put nth))))

(defthm fn-kc-scan-after-fill
  (implies (not (consp (nth 0 fn-keyset)))
           (equal (fn-kc-scan xs (fn-kc-fill ys fn-keyset))
                  (fn-kc-logic xs ys)))
  :hints (("Goal" :induct (fn-kc-logic xs ys)
           :in-theory (disable fn-kc-fill nth))))

(in-theory (disable fn-kc-keys fn-kc-logic fn-kc-fill fn-kc-scan))

; ---------------------------------------------------------------------------
; The generator.

(defconst *fn-kc-keys*
  '(:sense :xs-key :ys-key :each :base :logic-member :member-is :policy))

(defun fn-kc-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-kc-unknown (kvs)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) *fn-kc-keys*) (fn-kc-unknown (cddr kvs)))
        (t (cons (car kvs) (fn-kc-unknown (cddr kvs))))))

(defun fn-kc-lambdap (x n)
  (declare (xargs :mode :program))
  (and (true-listp x) (equal (len x) 3) (eq (car x) 'lambda)
       (symbol-listp (cadr x)) (equal (len (cadr x)) n) (no-duplicatesp-eq (cadr x))))

(defun fn-kc-refusal (name formals kvs)
  (declare (xargs :mode :program))
  (cond
   ((not (and (symbolp name) name)) (list :bad-name name))
   ((not (and (symbol-listp formals) (equal (len formals) 2) (no-duplicatesp-eq formals)))
    (list :bad-formals formals))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-kc-unknown kvs) (cons :unknown-keyword (fn-kc-unknown kvs)))
   ((not (member-eq (fn-kc-get :sense kvs) '(:present :absent))) (list :bad-sense name))
   ((and (assoc-keyword :xs-key kvs) (not (fn-kc-lambdap (fn-kc-get :xs-key kvs) 1)))
    (list :bad-lambda :xs-key))
   ((and (assoc-keyword :ys-key kvs) (not (fn-kc-lambdap (fn-kc-get :ys-key kvs) 1)))
    (list :bad-lambda :ys-key))
   ((and (assoc-keyword :each kvs) (not (fn-kc-lambdap (fn-kc-get :each kvs) 1)))
    (list :bad-lambda :each))
   ((and (assoc-keyword :logic-member kvs) (not (fn-kc-lambdap (fn-kc-get :logic-member kvs) 2)))
    (list :bad-lambda :logic-member))
   ((not (eq (and (assoc-keyword :logic-member kvs) t) (and (assoc-keyword :member-is kvs) t)))
    (list :member-is-pairs-with-logic-member name))
   ((and (assoc-keyword :member-is kvs)
         (not (and (symbolp (fn-kc-get :member-is kvs)) (fn-kc-get :member-is kvs))))
    (list :bad-member-is name))
   ((and (assoc-keyword :policy kvs) (not (member-eq (fn-kc-get :policy kvs) '(:long :always :nonempty))))
    (list :bad-policy (fn-kc-get :policy kvs)))
   ((and (assoc-keyword :base kvs) (not (member-equal (fn-kc-get :base kvs) '(t (null xs)))))
    (list :bad-base (fn-kc-get :base kvs)))
   (t nil)))

(defun fn-kc-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:bad-sense (msg "~x0: :sense is :present or :absent." (cadr reason)))
    (:bad-lambda (msg "~x0 is not a lambda of the right arity." (cadr reason)))
    (:member-is-pairs-with-logic-member
     (msg "~x0: :logic-member and :member-is come together: the :logic test the ~
           instance states, and the named theorem that it is member-equal over ~
           NAME-keys." (cadr reason)))
    (:bad-policy (msg ":policy ~x0 is not :long, :always or :nonempty." (cadr reason)))
    (:bad-base (msg ":base ~x0 is t or (null xs)." (cadr reason)))
    (:declared-twice (msg "~x0 is already a keyset check of this world." (cadr reason)))
    (:not-a-theorem (msg "~x0: :member-is ~x1 is not a theorem in this world."
                         (cadr reason) (caddr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0." (cdr reason)))
    (otherwise (msg "malformed form: ~x0." reason))))

(mutual-recursion
 (defun fn-kc-subst (term alist)
   (declare (xargs :mode :program))
   (cond ((atom term) (let ((b (assoc-eq term alist))) (if b (cdr b) term)))
         ((eq (car term) 'quote) term)
         (t (cons (car term) (fn-kc-subst-lst (cdr term) alist)))))
 (defun fn-kc-subst-lst (terms alist)
   (declare (xargs :mode :program))
   (if (atom terms) nil
     (cons (fn-kc-subst (car terms) alist) (fn-kc-subst-lst (cdr terms) alist)))))

(defun fn-kc-sub (lam actuals)
  (declare (xargs :mode :program))
  (fn-kc-subst (caddr lam) (pairlis$ (cadr lam) actuals)))

(defun fn-kc-want-term (present b)
  (declare (xargs :mode :program))
  ; the sense applied to a boolean term
  (if present b `(not ,b)))

(defun fn-kc-name (name parts)
  (declare (xargs :mode :program))
  (packn-pos (cons name parts) name))

(defun fn-kc-events (name formals kvs)
  (declare (xargs :mode :program))
  (let* ((xs (car formals))
         (ys (cadr formals))
         (xkey (or (fn-kc-get :xs-key kvs) '(lambda (x) x)))
         (ykey (or (fn-kc-get :ys-key kvs) '(lambda (y) y)))
         (each (or (fn-kc-get :each kvs) '(lambda (x) t)))
         (present (eq (fn-kc-get :sense kvs) :present))
         (base (if (assoc-keyword :base kvs) (fn-kc-get :base kvs) t))
         (base-term (fn-kc-subst base (list (cons 'xs xs))))
         (policy (or (fn-kc-get :policy kvs) :long))
         (keys (fn-kc-name name '(-keys)))
         (fill (fn-kc-name name '(-fill)))
         (scan (fn-kc-name name '(-scan)))
         (ks (fn-kc-name name '(-ks)))
         (walk (fn-kc-name name '(-walk)))
         (member-term (if (assoc-keyword :logic-member kvs)
                          (fn-kc-sub (fn-kc-get :logic-member kvs) (list `(car ,xs) ys))
                        `(if (member-equal ,(fn-kc-sub xkey (list `(car ,xs))) (,keys ,ys)) t nil)))
         (subst `((fn-kc-xkey (lambda (x) ,(fn-kc-sub xkey '(x))))
                  (fn-kc-ykey (lambda (y) ,(fn-kc-sub ykey '(y))))
                  (fn-kc-each (lambda (x) ,(fn-kc-sub each '(x))))
                  (fn-kc-want (lambda (b) ,(fn-kc-want-term present 'b)))
                  (fn-kc-base (lambda (xs) ,(fn-kc-subst base (list (cons 'xs 'xs)))))
                  (fn-kc-keys ,keys) (fn-kc-logic ,walk) (fn-kc-fill ,fill) (fn-kc-scan ,scan)))
         (member-is (fn-kc-get :member-is kvs))
         (scan-after-fill (fn-kc-name name '(-scan-after-fill)))
         (ks-is-logic (fn-kc-name name '(-ks-is-logic)))
         (walk-is-logic (fn-kc-name name '(-walk-is-logic))))
    `(progn
       (table fn-keyset-check ',name '(:sense ,(if present :present :absent) :policy ,policy))
       (defun ,keys (,ys)
         (declare (xargs :guard t))
         (if (consp ,ys) (cons ,(fn-kc-sub ykey (list `(car ,ys))) (,keys (cdr ,ys))) nil))
       ; the direct walk: the :logic body, executable
       (defun ,walk (,xs ,ys)
         (declare (xargs :guard t))
         (if (consp ,xs)
             (and ,(fn-kc-sub each (list `(car ,xs)))
                  ,(fn-kc-want-term present member-term)
                  (,walk (cdr ,xs) ,ys))
           ,base-term))
       (defun ,fill (,ys fn-keyset)
         (declare (xargs :stobjs fn-keyset :guard t))
         (if (consp ,ys)
             (let ((fn-keyset (fn-keyset-tab-put ,(fn-kc-sub ykey (list `(car ,ys))) t fn-keyset)))
               (,fill (cdr ,ys) fn-keyset))
           fn-keyset))
       (defun ,scan (,xs fn-keyset)
         (declare (xargs :stobjs fn-keyset :guard t))
         (if (consp ,xs)
             (and ,(fn-kc-sub each (list `(car ,xs)))
                  ,(fn-kc-want-term present `(fn-keyset-tab-boundp ,(fn-kc-sub xkey (list `(car ,xs))) fn-keyset))
                  (,scan (cdr ,xs) fn-keyset))
           ,base-term))
       (defun ,ks (,xs ,ys)
         (declare (xargs :guard t))
         (with-local-stobj fn-keyset
           (mv-let (ok fn-keyset)
             (let ((fn-keyset (,fill ,ys fn-keyset)))
               (mv (,scan ,xs fn-keyset) fn-keyset))
             ok)))
       ; the bridges, from the library
       (defthm ,scan-after-fill
         (implies (not (consp (nth 0 fn-keyset)))
                  (equal (,scan ,xs (,fill ,ys fn-keyset)) (,walk ,xs ,ys)))
         :hints (("Goal" :use ((:instance (:functional-instance fn-kc-scan-after-fill ,@subst)
                                          (xs ,xs) (ys ,ys)))
                  :in-theory (union-theories '(,keys ,walk ,fill ,scan ,@(and member-is (list member-is)))
                                             (theory 'minimal-theory)))))
       (defthm ,ks-is-logic
         (equal (,ks ,xs ,ys) (,walk ,xs ,ys))
         :hints (("Goal" :in-theory (e/d (,ks ,scan-after-fill) (,scan ,fill ,walk nth)))))
       ; NAME: the :logic recursion, the :exec by policy
       (defun ,name (,xs ,ys)
         (declare (xargs :guard t :verify-guards nil))
         (mbe :logic (if (consp ,xs)
                         (and ,(fn-kc-sub each (list `(car ,xs)))
                              ,(fn-kc-want-term present member-term)
                              (,name (cdr ,xs) ,ys))
                       ,base-term)
              :exec ,(case policy
                       (:always `(,ks ,xs ,ys))
                       (:nonempty `(if (consp ,xs) (,ks ,xs ,ys) ,base-term))
                       (otherwise `(if (fn-ks-longp ,ys) (,ks ,xs ,ys) (,walk ,xs ,ys))))))
       (defthm ,walk-is-logic
         (equal (,walk ,xs ,ys) (,name ,xs ,ys))
         :hints (("Goal" :induct (,walk ,xs ,ys)
                  :in-theory (union-theories '(,walk ,name) (theory 'minimal-theory)))))
       (verify-guards ,name
         :hints (("Goal" :use (,ks-is-logic ,walk-is-logic)
                  :in-theory (union-theories '(,name fn-ks-longp)
                                             (theory 'minimal-theory)))))
       (table fn-teeth-owed ',ks-is-logic
              '(:by def-keyset-check :claim (nil (equal (,ks ,xs ,ys) (,walk ,xs ,ys)))))
       (table fn-teeth-owed ',walk-is-logic
              '(:by def-keyset-check :claim (nil (equal (,walk ,xs ,ys) (,name ,xs ,ys)))))
       (in-theory (disable ,keys ,walk ,fill ,scan ,ks ,ks-is-logic)))))

(defun fn-kc-world-problem (name kvs w)
  (declare (xargs :mode :program))
  (cond ((assoc-eq name (table-alist 'fn-keyset-check w)) (list :declared-twice name))
        ((and (fn-kc-get :member-is kvs) (null (getpropc (fn-kc-get :member-is kvs) 'theorem nil w)))
         (list :not-a-theorem name (fn-kc-get :member-is kvs)))
        (t nil)))

(defmacro def-keyset-check (name formals &rest kvs)
  (let ((reason (fn-kc-refusal name formals kvs)))
    (if reason
        `(make-event (er soft 'def-keyset-check "~x0: ~@1" ',name
                         ',(fn-kc-refusal-text reason)))
      `(make-event
        (let ((problem (fn-kc-world-problem ',name ',kvs (w state))))
          (if problem
              (er soft 'def-keyset-check "~x0: ~@1" ',name (fn-kc-refusal-text problem))
            (value (fn-kc-events ',name ',formals ',kvs))))))))
