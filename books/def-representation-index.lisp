; fn: `def-representation-index' --- an abstract stobj whose foundation is a
; LOG of objects with a salted eql-hash index, derived from the five
; functions the instance gives (lane s-hcf 2026-10-08; the store's history,
; books/history-columns-foundation.lisp, was written by hand before).
;
;   (def-representation-index NAME (FIELD :object)
;     :index (:key K :key-p KP :hash H :test T :project P :query-export Q)
;     :model (:recognizer R :creator C :count F :at F :append F :clear F :query F)
;     :lemmas (THM ...))
;
; The logical side is GIVEN, as `def-generic' takes it: R recognizes the
; value (a true list), C creates it, and each of count, at, append, clear and
; query is the :logic function of the export of that name.  The index is
; given as five functions: K the key of an object, KP whether a key is one (an
; object whose key is not one is not indexed), H the salted hash of a key,
; T the exact test (key object) applied to each candidate of a bucket, P what
; a matching object contributes; and the logical query (:query) is their
; filter over the history, oldest first.
;
; What is derived:
;   * the foundation NAME$C: the objects by position (an untyped array), the
;     count, the table from a hash to the positions under it (an eql
;     hash-table, newest first, keyed on the FULL hash: no reduction to a
;     table size), and the salt register; and its executables count, at,
;     append (a row write and a cons onto the bucket), the query (walk the
;     bucket of H(key, salt) and apply T to every candidate) and clear (which
;     takes the salt, stores it, and whose logical value ignores it);
;   * the instance of the generic theory (books/def-representation-index-lib
;     .lisp), proved ONCE over abstract key, hash and test functions:
;     NAME$CORR is equality with the fold of the history's appends from the
;     empty object with its salt (NAME-BUILD), and the facts about that fold
;     are the generic ones by functional instantiation, nothing re-proved;
;   * the obligations of every export and of the creator, as
;     `defabsstobj-missing-events' states them, and the `defabsstobj' (a
;     non-attachable one: the history's alternate concrete is attached by
;     books/history-paged-attach.lisp, which this keeps positional).
;
; Four things the instance proves about its own functions, named in :lemmas
; and used by the instantiation: H is a natural, T implies K (the object has
; the key and the key is one), and the logical query is the T-filter (the
; equations for an empty and a consed history).  No constraint is assumed.

(in-package "ACL2")
(include-book "def-representation")
(include-book "def-representation-index-lib")

(program)

(defun ixg-suffix (name export)
  (let* ((n (symbol-name name)) (e (symbol-name export)) (k (+ 1 (length n))))
    (and (> (length e) k)
         (equal (subseq e 0 k) (concatenate 'string n "-"))
         (subseq e k (length e)))))

(mutual-recursion
 (defun ixg-rename (term alist)
   (cond ((atom term) term)
         ((eq (car term) 'quote) term)
         ((consp (car term))
          (cons (list 'lambda (cadr (car term)) (ixg-rename (caddr (car term)) alist))
                (ixg-rename-lst (cdr term) alist)))
         (t (cons (let ((p (assoc-eq (car term) alist))) (if p (cdr p) (car term)))
                  (ixg-rename-lst (cdr term) alist)))))
 (defun ixg-rename-lst (terms alist)
   (if (endp terms) nil
     (cons (ixg-rename (car terms) alist) (ixg-rename-lst (cdr terms) alist)))))

(defun ixg-body (f wrld)
  (getprop f 'unnormalized-body nil 'current-acl2-world wrld))

(defun ixg-formula (thm wrld)
  (getpropc thm 'theorem nil wrld))

(defun ixg-fn-alist (key keyp hash test proj q app col cq build corr)
  `((ix-key . ,key) (ix-keyp . ,keyp) (ix-hash . ,hash) (ix-test . ,test)
    (ix-proj . ,proj) (ix-q . ,q) (ix-append . ,app) (ix-collect . ,col)
    (ix-cquery . ,cq) (ix-build . ,build) (ix-corr . ,corr)))

(defun ixg-fi-pairs (alist)
  (if (endp alist) nil
    (cons (list (car (car alist)) (cdr (car alist))) (ixg-fi-pairs (cdr alist)))))

; The generic theorems instantiated, each (IX-NAME SUFFIX).
(defconst *ixg-facts*
  '((ix-corr-facts "-CORR-FACTS")
    (ix-append-preserves-corr "-APPEND-PRESERVES-CORR")
    (ix-clear-preserves-corr "-CLEAR-PRESERVES-CORR")
    (ix-clear-is-empty "-CLEAR-IS-EMPTY")
    (ix-empty-establishes-correspondence "-EMPTY-ESTABLISHES-CORRESPONDENCE")
    (ix-build-of-append-one "-BUILD-OF-APPEND-ONE")
    (ix-fold-establishes-correspondence "-FOLD-ESTABLISHES-CORRESPONDENCE")
    (ix-fold-table-facts "-FOLD-TABLE-FACTS")
    (ix-fold-mids-of-append "-FOLD-MIDS-OF-APPEND")))

(defun ixg-fact-events1 (facts name alist lemmas build corr wrld)
  (if (endp facts) nil
    (let* ((ixn (car (car facts)))
           (thm (adt-sym name (cadr (car facts))))
           (formula (ixg-formula ixn wrld)))
      (cons `(defthm ,thm ,(untranslate (ixg-rename formula alist) t wrld)
               :rule-classes nil
               :hints (("Goal" :use ((:functional-instance ,ixn ,@(ixg-fi-pairs alist)))
                        :expand ((,build events c) (,corr c a))
                        :in-theory (e/d (,@lemmas) (,build ,corr)))))
            (ixg-fact-events1 (cdr facts) name alist lemmas build corr wrld)))))

(defun ixg-fact-events (facts name alist lemmas wrld)
  (if (endp facts) nil
    (let* ((build (cdr (assoc-eq 'ix-build alist)))
           (corr (cdr (assoc-eq 'ix-corr alist))))
      (ixg-fact-events1 facts name alist lemmas build corr wrld))))

; The model function F of the generic theory, renamed: a defun-nx NEW.
(defun ixg-model-defun (f new alist wrld)
  (let ((alist2 (cons (cons f new) alist)))
    `(defun-nx ,new ,(formals f wrld)
       ,(untranslate (ixg-rename (ixg-body f wrld) alist2) nil wrld))))

; The bridge EXEC = F, for a model function F that does not depend on the
; instance's functions.
(defun ixg-bridge (f exec hints wrld thm)
  `(defthm ,thm
     (equal (,exec ,@(formals f wrld)) (,f ,@(formals f wrld)))
     :hints ,hints))

; The equation EXEC = the model function's body, renamed (EXEC stands for F).
(defun ixg-equation (f exec alist hints wrld thm rule-classes)
  (let ((alist2 (cons (cons f exec) alist)))
    `(defthm ,thm
       (equal (,exec ,@(formals f wrld))
              ,(untranslate (ixg-rename (ixg-body f wrld) alist2) nil wrld))
       :rule-classes ,rule-classes
       :hints ,hints)))

(defun ixg-exports (name p lcount lat lappend lclear lquery qexport)
  `((,(adt-sym name "-COUNT") :logic ,lcount :exec ,(adt-sym p "-COUNT"))
    (,(adt-sym name "-AT") :logic ,lat :exec ,(adt-sym p "-AT"))
    (,qexport :logic ,lquery :exec ,(adt-sym p (concatenate 'string "-" (ixg-suffix name qexport))))
    (,(adt-sym name "-APPEND") :logic ,lappend :exec ,(adt-sym p "-APPEND") :protect t)
    (,(adt-sym name "-CLEAR") :logic ,lclear :exec ,(adt-sym p "-CLEAR") :protect t)))

(defun ixg-ob-hints (ob name p open corr facts logic dis)
  ; OB is NAME{KIND} for the export or creator OB prefix.
  (let* ((s (symbol-name ob))
         (i (position #\{ s))
         (pre (subseq s 0 i))
         (kind (subseq s (+ i 1) (- (length s) 1)))
         (use-facts `(:instance ,(adt-sym name "-CORR-FACTS") (c ,p) (a ,name)))
         (base `(e/d (,open ,@logic) (nth ,corr ,@dis))))
    (cond
     ((equal pre (concatenate 'string "CREATE-" (symbol-name name)))
      (if (equal kind "CORRESPONDENCE")
          `(("Goal" :in-theory (enable ,corr ,(adt-sym name "-BUILD") ,@(cdr facts)))) ; CDR: the empty fn
        nil))
     ((equal kind "PRESERVED") `(("Goal" :in-theory (enable ,@logic))))
     ((equal pre (concatenate 'string (symbol-name name) "-APPEND"))
      `(("Goal" :in-theory ,base
         :use ((:instance ,(adt-sym name "-APPEND-PRESERVES-CORR") (c ,p) (a ,name))))))
     ((equal pre (concatenate 'string (symbol-name name) "-CLEAR"))
      `(("Goal" :in-theory ,base
         :use (,use-facts (:instance ,(adt-sym name "-CLEAR-PRESERVES-CORR") (c ,p))
               (:instance ,(adt-sym (adt-sym p "-CLEAR") "-IS-IX-CLEAR") (c ,p))))))
     (t `(("Goal" :in-theory ,base :use (,use-facts)))))))

(defun ixg-ob-thms (missing name p open corr facts logic dis)
  (if (endp missing) nil
    (cons `(defthm ,(car (car missing)) ,(cadr (car missing))
             :rule-classes nil
             :hints ,(ixg-ob-hints (car (car missing)) name p open corr facts logic dis))
          (ixg-ob-thms (cdr missing) name p open corr facts logic dis))))

(defun ixg-events (name field key keyp hash test proj qexport r cr lcount lat lappend lclear
                        lquery lemmas wrld)
  (declare (ignorable field))
  (let* ((p (adt-sym name "$C"))
         (rows (adt-sym p "-ROWS")) (cnt (adt-sym p "-COUNT"))
         (mids (adt-sym p "-MIDS")) (salt (adt-sym p "-SALT"))
         (rowsi (adt-sym p "-ROWSI"))
         (upd-rowsi (adt-sym-pre "UPDATE-" rowsi))
         (upd-cnt (adt-sym-pre "UPDATE-" cnt))
         (upd-salt (adt-sym-pre "UPDATE-" salt))
         (resize (adt-sym-pre "RESIZE-" rows))
         (rows-len (adt-sym rows "-LENGTH"))
         (mget (adt-sym mids "-GET")) (mput (adt-sym mids "-PUT")) (mclear (adt-sym mids "-CLEAR"))
         (open (adt-sym name "-OPEN"))
         (at (adt-sym p "-AT")) (grow (adt-sym p "-GROW")) (app (adt-sym p "-APPEND"))
         (col (adt-sym p "-COLLECT"))
         (cq (adt-sym p (concatenate 'string "-" (ixg-suffix name qexport))))
         (clr (adt-sym p "-CLEAR"))
         (cp (adt-sym p "P"))
         (build (adt-sym name "-BUILD")) (corr (adt-sym name "$CORR"))
         (alist (ixg-fn-alist key keyp hash test proj lquery app col cq build corr))
         (logic (list lcount lat lappend lclear lquery r cr))
         (exports (ixg-exports name p lcount lat lappend lclear lquery qexport))
         (facts (list nil 'ix-empty))
         (dis (list hash key test proj cq col clr app grow
                    (adt-sym grow "-IS-IX-GROW") (adt-sym clr "-IS-IX-CLEAR")
                    (adt-sym app "-IS-IX-APPEND") (adt-sym cq "-IS-IX-CQUERY")
                    'ix-clear 'ix-clear-is-empty)))
    `((defstobj ,p
        (,rows :type (array t (0)) :resizable t)
        (,cnt :type (integer 0 *) :initially 0)
        (,mids :type (hash-table eql))
        (,salt :type (unsigned-byte 32) :initially 0)
        :inline t)
      (local
       (deftheory ,open
         '(,cnt ,upd-cnt ,rowsi ,upd-rowsi ,resize ,rows-len ,salt ,upd-salt
           ,mget ,mput ,mclear update-nth-array)))
      (defun ,at (seq ,p)
        (declare (xargs :stobjs ,p :guard (and (natp seq) (< seq (,rows-len ,p)))))
        (,rowsi seq ,p))
      (defun ,grow (,p)
        (declare (xargs :stobjs ,p))
        (let ((n (,cnt ,p)) (cap (,rows-len ,p)))
          (if (< n cap) ,p (,resize (max 16 (* 2 (max n cap))) ,p))))
      (local
       (defthm ,(adt-sym p "-LEN-OF-RESIZE-LIST")
         (equal (len (resize-list l n d)) (nfix n))
         :hints (("Goal" :in-theory (enable resize-list)))))
      (local
       (defthm ,(adt-sym grow "-ROWS-LENGTH")
         (implies (natp (nth 1 ,p))
                  (< (nth 1 ,p) (len (nth 0 (,grow ,p)))))
         :rule-classes :linear))
      (local
       (defthm ,(adt-sym grow "-FIELDS")
         (and (equal (nth 1 (,grow ,p)) (nth 1 ,p))
              (equal (nth 2 (,grow ,p)) (nth 2 ,p))
              (equal (nth 3 (,grow ,p)) (nth 3 ,p)))))
      (local
       (defthm ,(adt-sym rows "P-OF-ANYTHING")
         (equal (,(adt-sym rows "P") x) (true-listp x))
         :hints (("Goal" :in-theory (enable ,(adt-sym rows "P"))))))
      (local
       (defthm ,(adt-sym grow "-CP")
         (implies (,cp ,p) (,cp (,grow ,p)))))
      (defun ,app (ev ,p)
        (declare (xargs :stobjs ,p))
        (let* ((n (,cnt ,p))
               (,p (,grow ,p))
               (,p (,upd-rowsi n ev ,p))
               (k (,key ev))
               (,p (if (,keyp k)
                       (let ((h (,hash k (,salt ,p))))
                         (,mput h (cons n (,mget h ,p)) ,p))
                     ,p)))
          (,upd-cnt (1+ n) ,p)))
      (defun ,col (k seqs acc ,p)
        (declare (xargs :stobjs ,p :guard (,keyp k)))
        (if (consp seqs)
            (let ((i (car seqs)))
              (if (and (natp i) (< i (,rows-len ,p)))
                  (let ((ev (,rowsi i ,p)))
                    (,col k (cdr seqs) (if (,test k ev) (cons (,proj ev) acc) acc) ,p))
                (,col k (cdr seqs) acc ,p)))
          acc))
      (defun ,cq (m ,p)
        (declare (xargs :stobjs ,p :guard (,keyp m)))
        (,col m (,mget (,hash m (,salt ,p)) ,p) nil ,p))
      (defun ,clr (salt ,p)
        (declare (xargs :stobjs ,p :guard (unsigned-byte-p 32 salt)))
        (let* ((,p (,resize 0 ,p))
               (,p (,upd-cnt 0 ,p))
               (,p (,mclear ,p)))
          (,upd-salt salt ,p)))
      ,(ixg-model-defun 'ix-build build alist wrld)
      ,(ixg-model-defun 'ix-corr corr alist wrld)
      (defthm ,(adt-sym p "P-IS-IX-CP")
        (equal (,cp c) (ix-cp c))
        :hints (("Goal" :in-theory (enable ,cp ix-cp))))
      ,(ixg-bridge 'ix-grow grow `(("Goal" :in-theory (e/d (,grow ,open ix-grow) (nth update-nth resize-list ,hash ,key ,test ,proj)))) wrld
                   (adt-sym grow "-IS-IX-GROW"))
      ,(ixg-bridge 'ix-clear clr `(("Goal" :in-theory (e/d (,clr ,open ix-clear) (nth update-nth resize-list ,hash ,key ,test ,proj)))) wrld
                   (adt-sym clr "-IS-IX-CLEAR"))
      ,(ixg-equation 'ix-append app alist `(("Goal" :in-theory (e/d (,app ,open) (nth update-nth resize-list ,hash ,key ,test ,proj)))) wrld
                     (adt-sym app "-IS-IX-APPEND") :rewrite)
      ,(ixg-equation 'ix-collect col alist `(("Goal" :in-theory (e/d (,open) (nth update-nth resize-list ,hash ,key ,test ,proj)))) wrld
                     (adt-sym col "-IS-IX-COLLECT") nil)
      ,(ixg-equation 'ix-cquery cq alist `(("Goal" :in-theory (e/d (,cq ,open) (nth update-nth resize-list ,hash ,key ,test ,proj)))) wrld
                     (adt-sym cq "-IS-IX-CQUERY") :rewrite)
      ,@(ixg-fact-events *ixg-facts* name alist lemmas wrld)
      (local (in-theory (disable ,corr ,build)))
      (make-event
       (er-let* ((missing
                  (defabsstobj-missing-events
                    ,name
                    :attachable t
                    :foundation ,p
                    :recognizer (,(adt-sym name "-P") :logic ,r :exec ,cp)
                    :creator (,(adt-sym-pre "CREATE-" name) :logic ,cr
                              :exec ,(adt-sym-pre "CREATE-" p))
                    :corr-fn ,corr
                    :exports ,exports
                    :corr-fn-exists t)))
         (value (cons 'progn (ixg-ob-thms missing ',name ',p ',open ',corr ',facts ',logic ',dis))))))))

(defun ixg-check (name fields index model wrld)
  (declare (ignorable wrld))
  (cond
   ((not (and (symbolp name) name (not (keywordp name))))
    "the name must be a non-nil symbol")
   ((not (and (true-listp fields) (equal (len fields) 1)
              (true-listp (car fields)) (equal (len (car fields)) 2)
              (symbolp (car (car fields))) (eq (cadr (car fields)) :object)))
    "the schema must be one (FIELD :object) column")
   ((not (and (keyword-value-listp index)
              (subsetp-eq (rep-plist-keys index) '(:key :key-p :hash :test :project :query-export))
              (equal (len index) 12)))
    ":index must be (:key K :key-p KP :hash H :test T :project P :query-export Q)")
   ((not (and (keyword-value-listp model)
              (subsetp-eq (rep-plist-keys model)
                          '(:recognizer :creator :count :at :append :clear :query))
              (equal (len model) 14)))
    ":model must give :recognizer :creator :count :at :append :clear :query")
   (t nil)))

(defun ixg-fns-ok (fns wrld)
  (cond ((endp fns) t)
        (t (and (symbolp (car fns)) (car fns) (function-symbolp (car fns) wrld)
                (ixg-fns-ok (cdr fns) wrld)))))

(defun def-representation-index-fn (name fields index model lemmas state)
  (declare (xargs :stobjs state))
  (let* ((wrld (w state)) (ctx 'def-representation-index)
         (bad (ixg-check name fields index model wrld)))
    (cond
     (bad (er soft ctx "~x0: ~@1." name bad))
     (t
      (let* ((key (cadr (assoc-keyword :key index)))
             (keyp (cadr (assoc-keyword :key-p index)))
             (hash (cadr (assoc-keyword :hash index)))
             (test (cadr (assoc-keyword :test index)))
             (proj (cadr (assoc-keyword :project index)))
             (qexport (cadr (assoc-keyword :query-export index)))
             (r (cadr (assoc-keyword :recognizer model)))
             (cr (cadr (assoc-keyword :creator model)))
             (lcount (cadr (assoc-keyword :count model)))
             (lat (cadr (assoc-keyword :at model)))
             (lappend (cadr (assoc-keyword :append model)))
             (lclear (cadr (assoc-keyword :clear model)))
             (lquery (cadr (assoc-keyword :query model))))
        (cond
         ((not (ixg-fns-ok (list key keyp hash test proj r cr lcount lat lappend lclear lquery) wrld))
          (er soft ctx "~x0: every function named in :index and :model must be in the world." name))
         ((not (and (symbolp qexport) (ixg-suffix name qexport)))
          (er soft ctx "~x0: :query-export must be NAME-SUFFIX." name))
         ((not (and (symbol-listp lemmas) (rep-theorem-names-p lemmas wrld)))
          (er soft ctx "~x0: :lemmas must name theorems already proved." name))
         (t
          (value `(progn ,@(ixg-events name (car (car fields)) key keyp hash test proj qexport
                                       r cr lcount lat lappend lclear lquery lemmas wrld))))))))))

(defmacro def-representation-index (name fields &key index model lemmas)
  `(make-event (def-representation-index-fn ',name '(,fields) ',index ',model ',lemmas state)))

(logic)
