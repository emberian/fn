; fn: `def-carried-view' --- a reader's answer carried by an index over a
; list, from one declaration; `def-carried-reader', the reader that takes
; the index's answer only when the list in hand IS the carried one.
;
; The shape this replaces, hand-written in books/withdrawal-index-carried
; (fn-wix), books/newnews-cursor (fn-nnw), books/msgid-index (fn-midx),
; books/owner (fn-gidx) and books/group-access-cache (fn-gacc): a CARRY
; (KEY IDX1 ... IDXn) where KEY is the list the indexes were built from; a
; recognizer "every index agrees with KEY"; a REFRESH that walks the new
; list to the tail EQUAL to KEY, folds the walked prefix (oldest first) onto
; the carried indexes, else rebuilds; and READERS that take an index's
; answer only when the list in hand is EQUAL to KEY, else the reference
; walk.  Each instance wrote the same five theorems (150-300 lines).
;
;   (def-carried-view NAME
;     :key WS                                  ; the list's name: accessor NAME-WS
;     :indexes ((IDX :kind :set :key-fn (lambda (e) ...)  ; a key or nil
;                    :put (lambda (e idx) ...) :hasp (lambda (k idx) ...)
;                    :empty TERM [:lemmas (L ...)])
;               (IDX :kind :exact :put (lambda (e idx) ...) :empty TERM) ...)
;     [:build NAME-build])                     ; the name of the build (default)
;
; A :set index is COMPLETE: every element's key (when it has one) is in it;
; a reader trusts only a negative answer.  An :exact index IS the fold of
; the list: `(put (car ws) (build (cdr ws)))' from `empty'.  Generated:
;
;   NAME-WS, NAME-IDX           accessors (guard t)
;   NAME-put, NAME-empty        the tuple put and the empty tuple
;   NAME-build-onto YS IDXS     the :logic fold, (car YS) put last
;   NAME-build WS               = (NAME-build-onto WS (NAME-empty)), executed
;                               by the tail-recursive NAME-fold over
;                               (revappend WS nil)
;   NAME-IDX-okp WS IDX         per index: complete (:set) or exact
;   NAME-okp WS IDXS            every index agrees with WS
;   NAME-carryp CARRY           = (NAME-okp (NAME-WS CARRY) (cdr CARRY))
;   NAME-walk TAIL OLD RACC     (mv FOUND RACC): the walk to the tail EQUAL
;                               to OLD, the walked prefix reversed
;   NAME-refresh CARRY WS       the same list: CARRY; a tail found: the
;                               prefix folded onto the carried indexes; else
;                               (cons WS (NAME-build WS))
;   NAME-carryp-of-nil          (NAME-carryp nil)
;   NAME-carryp-of-refresh      (implies (NAME-carryp c) (NAME-carryp (NAME-refresh c ws)))
;   NAME-WS-of-refresh          (equal (NAME-WS (NAME-refresh c ws)) ws)
;   NAME-walk-steps-of-append   the VISIT bound: (equal ws (append new old))
;                               implies the walk steps exactly (len new)
;                               elements (fn-cv-walk-steps): the refresh
;                               visits the delta, not the list
;   (table fn-carried-view NAME ROW), and (table fn-teeth-owed K '(:by
;   def-carried-view)) for each keystone above
;
; Every theorem is obtained by `:functional-instance' of this book's library
; (fn-cv-*), proved once over constrained put/empty/hasp/key: the instance's
; obligations are its definitional equations, and for a :set index the two
; facts its :lemmas prove (hasp survives a put; a put has its key).
;
;   (def-carried-reader R (FORMALS)
;     :of NAME :carry C :list WS            ; C and WS among FORMALS
;     :when PRE                             ; the fast arm's precondition
;     :probe (IDX KEY-TERM)                 ; the :set index asked, and the key
;     :fast TERM                            ; the answer when the probe is negative
;     :reference TERM                       ; the walk, over FORMALS less C
;     :by THM                               ; (implies (and (NAME-IDX-okp ws idx)
;                                           ;   PRE (not (HASP KEY-TERM idx)))
;                                           ;   (equal REFERENCE FAST)), the one
;                                           ; hand proof, stated over WS and IDX
;     [:name R-is-REF] [:guard G] [:stobjs (ST ...)] [:theory (RUNE ...)])
;
; generates R = (if (and PRE (equal WS (NAME-WS C)) (not (HASP KEY (NAME-IDX C))))
; FAST REFERENCE), the keystone (implies (NAME-carryp C) (equal (R ...)
; REFERENCE)) proved by :use THM, (in-theory (disable R)), the owed-teeth
; row, and REFUSES a :fast term that mentions WS: the fast arm cannot visit
; the list it does not hold.  That, with NAME-walk-steps-of-append, is the
; reader's visit bound, structural; the `equal' of the two lists is one
; pointer comparison when they are the same object (the host's refresh
; stores the list it indexed), a host fact a cost claim names (:rests-on).
;
; Refused at expansion, each by name: a malformed form; an index kind other
; than :set or :exact; a :set index without :key-fn, :put, :hasp; a lambda
; of the wrong arity; a repeated index name; a reader whose :carry or
; :list is not a formal, whose :probe names no :set index of NAME, or whose
; :fast mentions its list; a NAME not declared; a :by that is not a theorem.

(in-package "ACL2")

(defun fn-cv-car (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn-cv-cdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

; ---------------------------------------------------------------------------
; The library.  PUT and EMPTY build an index; HASP and KEY are the :set
; kind's question and an element's key (nil: no key).  The two constraints
; are what a :set instance proves; an :exact instance substitutes a HASP
; that is always true and a KEY that is always nil.

(encapsulate
  (((fn-cv-put * *) => *)
   ((fn-cv-empty) => *)
   ((fn-cv-hasp * *) => *)
   ((fn-cv-key *) => *))
  (local (defun fn-cv-put (e idx) (cons e idx)))
  (local (defun fn-cv-empty () nil))
  (local (defun fn-cv-hasp (k idx) (member-equal k idx)))
  (local (defun fn-cv-key (e) e))
  (defthm fn-cv-hasp-of-put
    (implies (and (fn-cv-key e2) (fn-cv-hasp (fn-cv-key e2) idx))
             (fn-cv-hasp (fn-cv-key e2) (fn-cv-put e idx))))
  (defthm fn-cv-put-has-key
    (implies (fn-cv-key e)
             (fn-cv-hasp (fn-cv-key e) (fn-cv-put e idx)))))

; The :logic fold: (car ys) is put last, so the index of (cons e ws) is
; (put e (index of ws)).
(defun fn-cv-build-onto (ys idx)
  (if (consp ys)
      (fn-cv-put (car ys) (fn-cv-build-onto (cdr ys) idx))
    idx))

; The executed fold: puts (car racc) first.
(defun fn-cv-fold (racc idx)
  (if (consp racc)
      (fn-cv-fold (cdr racc) (fn-cv-put (car racc) idx))
    idx))

(defthm fn-cv-fold-of-revappend
  (equal (fn-cv-fold (revappend ys racc) idx)
         (fn-cv-fold racc (fn-cv-build-onto ys idx)))
  :hints (("Goal" :induct (revappend ys racc))))

(defthm fn-cv-build-onto-of-append
  (equal (fn-cv-build-onto (append a b) idx)
         (fn-cv-build-onto a (fn-cv-build-onto b idx))))

; The walk to the tail EQUAL to OLD: (mv FOUND RACC), the walked prefix
; reversed onto RACC.
(defun fn-cv-walk (tail old racc)
  (cond ((equal tail old) (mv t racc))
        ((atom tail) (mv nil racc))
        (t (fn-cv-walk (cdr tail) old (cons (car tail) racc)))))

(defun fn-cv-walk-steps (tail old)
  (cond ((equal tail old) 0)
        ((atom tail) 0)
        (t (+ 1 (fn-cv-walk-steps (cdr tail) old)))))

(defthm fn-cv-walk-found
  (implies (mv-nth 0 (fn-cv-walk tail old racc))
           (equal (revappend (mv-nth 1 (fn-cv-walk tail old racc)) old)
                  (revappend racc tail)))
  :hints (("Goal" :induct (fn-cv-walk tail old racc))))

(local
 (defthm fn-cv-len-of-append
   (equal (len (append x y)) (+ (len x) (len y)))))

; NEW ++ OLD is not a list of OLD's length (so never OLD) while NEW has an
; element; its first element and its rest, with `append' kept closed.
(local
 (defthm fn-cv-append-longer
   (implies (and (consp new) (equal (len z) (len old)))
            (not (equal (append new old) z)))
   :hints (("Goal" :expand ((len new)) :in-theory (disable append)))))

(local
 (defthm fn-cv-consp-of-append
   (implies (consp new) (consp (append new old)))))

(local
 (defthm fn-cv-cdr-of-append
   (implies (consp new) (equal (cdr (append new old)) (append (cdr new) old)))))

(local
 (defthm fn-cv-append-of-atom
   (implies (atom new) (equal (append new old) old))))

; THE VISIT BOUND: the walk over NEW ++ OLD steps exactly (len NEW)
; elements, since no earlier tail has OLD's length.
(defthm fn-cv-walk-steps-of-append
  (equal (fn-cv-walk-steps (append new old) old) (len new))
  :hints (("Goal" :induct (len new)
           :in-theory (e/d (fn-cv-walk-steps) (append)))))

; ---------------------------------------------------------------------------
; The two invariant kinds, and the refresh over an abstract one.

; :set, complete: every element's key (when it has one) is in IDX.
(defun fn-cv-set-okp (ws idx)
  (if (consp ws)
      (and (or (not (fn-cv-key (car ws)))
               (fn-cv-hasp (fn-cv-key (car ws)) idx))
           (fn-cv-set-okp (cdr ws) idx))
    t))

(defthm fn-cv-set-okp-of-put
  (implies (fn-cv-set-okp ws idx)
           (fn-cv-set-okp ws (fn-cv-put e idx))))

(defthm fn-cv-set-okp-of-build-onto-kept
  (implies (fn-cv-set-okp ws idx)
           (fn-cv-set-okp ws (fn-cv-build-onto ys idx)))
  :hints (("Goal" :induct (fn-cv-build-onto ys idx))))

(defthm fn-cv-set-okp-of-build-onto
  (fn-cv-set-okp ys (fn-cv-build-onto ys idx))
  :hints (("Goal" :induct (fn-cv-build-onto ys idx))))

(defthm fn-cv-set-okp-of-append
  (equal (fn-cv-set-okp (append a b) idx)
         (and (fn-cv-set-okp a idx) (fn-cv-set-okp b idx))))

(defthm fn-cv-set-okp-of-build
  (fn-cv-set-okp ws (fn-cv-build-onto ws (fn-cv-empty))))

(defthm fn-cv-set-okp-of-extend
  (implies (fn-cv-set-okp old idx)
           (fn-cv-set-okp (append new old) (fn-cv-build-onto new idx))))

; :exact: IDX is the fold of WS.
(defun fn-cv-exact-okp (ws idx)
  (equal idx (fn-cv-build-onto ws (fn-cv-empty))))

(defthm fn-cv-exact-okp-of-build
  (fn-cv-exact-okp ws (fn-cv-build-onto ws (fn-cv-empty))))

(defthm fn-cv-exact-okp-of-extend
  (implies (fn-cv-exact-okp old idx)
           (fn-cv-exact-okp (append new old) (fn-cv-build-onto new idx))))

; The refresh, over an abstract OKP with the two facts both kinds have.
(encapsulate
  (((fn-cv-okp * *) => *))
  (local (defun fn-cv-okp (ws idx) (fn-cv-exact-okp ws idx)))
  (defthm fn-cv-okp-of-build
    (fn-cv-okp ws (fn-cv-build-onto ws (fn-cv-empty))))
  (defthm fn-cv-okp-of-extend
    (implies (fn-cv-okp old idx)
             (fn-cv-okp (append new old) (fn-cv-build-onto new idx)))))

(defun fn-cv-carryp (carry)
  (fn-cv-okp (fn-cv-car carry) (fn-cv-cdr carry)))

; On an equal list the outer cell is rebuilt on the CURRENT object (c04 4c):
; a later comparison then meets the same object, never an obsolete equal one.
(defun fn-cv-refresh (carry ws)
  (if (equal ws (fn-cv-car carry))
      (cons ws (fn-cv-cdr carry))
    (mv-let (found racc)
      (fn-cv-walk ws (fn-cv-car carry) nil)
      (if found
          (cons ws (fn-cv-fold racc (fn-cv-cdr carry)))
        (cons ws (fn-cv-fold (revappend ws nil) (fn-cv-empty)))))))

(local
 (defthm fn-cv-revappend-append
   (equal (revappend a (append b c)) (append (revappend a b) c))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm fn-cv-revappend-is-append
   (equal (revappend a c) (append (revappend a nil) c))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-cv-revappend-append (b nil)))
            :in-theory (disable fn-cv-revappend-append)))))

(local
 (defthm fn-cv-build-onto-of-revappend-cons
   (equal (fn-cv-build-onto (revappend a (cons e nil)) idx)
          (fn-cv-build-onto (revappend a nil) (fn-cv-put e idx)))
   :hints (("Goal" :use ((:instance fn-cv-revappend-is-append (c (cons e nil))))))))

; The executed fold of the reversed prefix is the :logic fold of the prefix.
(local
 (defthm fn-cv-fold-is-build-onto-of-reverse
   (equal (fn-cv-fold racc idx) (fn-cv-build-onto (revappend racc nil) idx))
   :hints (("Goal" :induct (fn-cv-fold racc idx)))))

(local (in-theory (disable fn-cv-fold-is-build-onto-of-reverse)))

; A found walk splits the list: WS = (the walked prefix) ++ OLD.
(local
 (defthm fn-cv-found-splits
   (implies (mv-nth 0 (fn-cv-walk ws old nil))
            (equal ws (append (revappend (mv-nth 1 (fn-cv-walk ws old nil)) nil) old)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-cv-walk-found (tail ws) (racc nil))
                         (:instance fn-cv-revappend-is-append
                                    (a (mv-nth 1 (fn-cv-walk ws old nil))) (c old)))
            :in-theory (disable fn-cv-walk-found)))))

(local
 (defthm fn-cv-fold-of-nil
   (equal (fn-cv-fold nil idx) idx)
   :hints (("Goal" :in-theory (enable fn-cv-fold)))))

(local
 (defthm fn-cv-okp-of-extend-at
   (implies (and (fn-cv-okp old idx) (equal ws (append new old)))
            (fn-cv-okp ws (fn-cv-build-onto new idx)))))

(defthm fn-cv-carryp-of-refresh
  (implies (fn-cv-carryp carry)
           (fn-cv-carryp (fn-cv-refresh carry ws)))
  :hints (("Goal" :in-theory (disable fn-cv-walk fn-cv-build-onto fn-cv-fold)
           :use ((:instance fn-cv-found-splits (old (fn-cv-car carry)))
                 (:instance fn-cv-fold-is-build-onto-of-reverse
                            (racc (mv-nth 1 (fn-cv-walk ws (fn-cv-car carry) nil)))
                            (idx (fn-cv-cdr carry)))
                 (:instance fn-cv-okp-of-extend-at
                            (old (fn-cv-car carry)) (idx (fn-cv-cdr carry))
                            (new (revappend (mv-nth 1 (fn-cv-walk ws (fn-cv-car carry) nil))
                                            nil)))))))

(defthm fn-cv-car-of-refresh
  (equal (fn-cv-car (fn-cv-refresh carry ws)) ws))

(in-theory (disable fn-cv-build-onto fn-cv-fold fn-cv-walk fn-cv-walk-steps
                    fn-cv-set-okp fn-cv-exact-okp fn-cv-carryp fn-cv-refresh))

; ===========================================================================
; The generator.
;
; Two forms a view may take, both narrow (c04 3b): ALL-SET (every index a
; complete negative filter over its own key) and ALL-EXACT (the tuple of
; indexes IS the fold of the list).  The carry is (WS . IDX) for one index
; and (WS IDX1 ... IDXn) for several.  Every theorem is a functional
; instance of the library above; a :set index owes the two facts its
; :lemmas prove (a put keeps what the index has; a put has its key), stated
; here as NAME-IDX-hasp-of-put and NAME-IDX-put-has-key before the instance.

(defconst *fn-cv-keys* '(:key :indexes :build))
(defconst *fn-cv-index-keys* '(:kind :key-fn :put :hasp :empty :lemmas))

(defun fn-cv-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-cv-unknown-keys (kvs keys)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) keys) (fn-cv-unknown-keys (cddr kvs) keys))
        (t (cons (car kvs) (fn-cv-unknown-keys (cddr kvs) keys)))))

(defun fn-cv-lambdap (x n)
  (declare (xargs :mode :program))
  ; (lambda (V1 .. Vn) BODY)
  (and (true-listp x) (equal (len x) 3) (eq (car x) 'lambda)
       (symbol-listp (cadr x)) (equal (len (cadr x)) n)
       (no-duplicatesp-eq (cadr x))))

(defun fn-cv-index-refusal (entry)
  (declare (xargs :mode :program))
  ; nil, or (REASON . DETAILS) for one (IDX . OPTS)
  (let* ((opts (cdr entry))
         (kind (fn-cv-get :kind opts)))
    (cond
     ((not (and (consp entry) (symbolp (car entry)) (car entry) (keyword-value-listp opts)))
      (list :bad-index entry))
     ((fn-cv-unknown-keys opts *fn-cv-index-keys*)
      (cons :unknown-keyword (fn-cv-unknown-keys opts *fn-cv-index-keys*)))
     ((not (member-eq kind '(:set :exact))) (list :bad-kind (car entry) kind))
     ((not (fn-cv-lambdap (fn-cv-get :put opts) 2)) (list :bad-put (car entry)))
     ((not (assoc-keyword :empty opts)) (list :no-empty (car entry)))
     ((and (eq kind :set) (not (fn-cv-lambdap (fn-cv-get :key-fn opts) 1)))
      (list :bad-key-fn (car entry)))
     ((and (eq kind :set) (not (fn-cv-lambdap (fn-cv-get :hasp opts) 2)))
      (list :bad-hasp (car entry)))
     ((and (eq kind :exact) (or (assoc-keyword :key-fn opts) (assoc-keyword :hasp opts)))
      (list :exact-has-no-probe (car entry)))
     ((not (symbol-listp (fn-cv-get :lemmas opts))) (list :bad-lemmas (car entry)))
     (t nil))))

(defun fn-cv-indexes-refusal (entries)
  (declare (xargs :mode :program))
  (cond ((atom entries) nil)
        ((fn-cv-index-refusal (car entries)))
        (t (fn-cv-indexes-refusal (cdr entries)))))

(defun fn-cv-kinds (entries)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (cons (fn-cv-get :kind (cdr (car entries))) (fn-cv-kinds (cdr entries)))))

(defun fn-cv-refusal (name kvs)
  (declare (xargs :mode :program))
  ; nil when (def-carried-view NAME . KVS) is well-formed (world-free)
  (let ((indexes (fn-cv-get :indexes kvs)))
    (cond
     ((not (and (symbolp name) name)) (list :bad-name name))
     ((not (keyword-value-listp kvs)) (list :bad-options kvs))
     ((fn-cv-unknown-keys kvs *fn-cv-keys*)
      (cons :unknown-keyword (fn-cv-unknown-keys kvs *fn-cv-keys*)))
     ((not (and (symbolp (fn-cv-get :key kvs)) (fn-cv-get :key kvs))) (list :no-key name))
     ((not (and (consp indexes) (true-listp indexes))) (list :no-indexes name))
     ((fn-cv-indexes-refusal indexes))
     ((not (no-duplicatesp-eq (strip-cars indexes)))
      (list :duplicate-index (strip-cars indexes)))
     ((and (member-eq :set (fn-cv-kinds indexes)) (member-eq :exact (fn-cv-kinds indexes)))
      (list :mixed-kinds name))
     ((and (assoc-keyword :build kvs)
           (not (and (symbolp (fn-cv-get :build kvs)) (fn-cv-get :build kvs))))
      (list :bad-build (fn-cv-get :build kvs)))
     (t nil))))

(defun fn-cv-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:no-key (msg "~x0 has no :key WS: name the list the indexes are built from."
                  (cadr reason)))
    (:no-indexes (msg "~x0 has no :indexes ((IDX :kind :set|:exact ...) ...)."
                      (cadr reason)))
    (:bad-kind (msg "index ~x0: :kind ~x1 is not :set or :exact." (cadr reason) (caddr reason)))
    (:bad-put (msg "index ~x0: :put is not (lambda (e idx) ...)." (cadr reason)))
    (:no-empty (msg "index ~x0 has no :empty TERM." (cadr reason)))
    (:bad-key-fn (msg "index ~x0 (:set): :key-fn is not (lambda (e) ...), the element's ~
                       key or nil." (cadr reason)))
    (:bad-hasp (msg "index ~x0 (:set): :hasp is not (lambda (k idx) ...)." (cadr reason)))
    (:exact-has-no-probe (msg "index ~x0 (:exact) takes no :key-fn or :hasp: it is the ~
                               fold of the list, not a filter." (cadr reason)))
    (:mixed-kinds (msg "~x0 mixes :set and :exact indexes; a view is one kind (c04 3b)."
                       (cadr reason)))
    (:duplicate-index (msg "index names repeat: ~x0." (cadr reason)))
    (:declared-twice (msg "~x0 is already a carried view of this world." (cadr reason)))
    (:not-a-theorem (msg "~x0 names ~x1 in :lemmas, which is not a theorem in this world."
                         (cadr reason) (caddr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0." (cdr reason)))
    (otherwise (msg "malformed form: ~x0." reason))))

; --- names

(defun fn-cv-name-fn (name parts)
  (declare (xargs :mode :program))
  (packn-pos (cons name parts) name))

(defmacro fn-cv-name (name &rest parts)
  `(fn-cv-name-fn ,name (list ,@parts)))

(mutual-recursion
 (defun fn-dt-subst-cv (term alist)
   (declare (xargs :mode :program))
   (cond ((atom term) (let ((b (assoc-eq term alist))) (if b (cdr b) term)))
         ((eq (car term) 'quote) term)
         (t (cons (car term) (fn-dt-subst-cv-lst (cdr term) alist)))))
 (defun fn-dt-subst-cv-lst (terms alist)
   (declare (xargs :mode :program))
   (if (atom terms) nil
     (cons (fn-dt-subst-cv (car terms) alist) (fn-dt-subst-cv-lst (cdr terms) alist)))))

(defun fn-cv-sub (lam actuals)
  (declare (xargs :mode :program))
  ; the body of (lambda (v...) body) with ACTUALS for its variables
  (fn-dt-subst-cv (caddr lam) (pairlis$ (cadr lam) actuals)))

(defun fn-cv-nth-term (k x)
  (declare (xargs :mode :program))
  ; the K-th component of the tuple X, guard t
  (if (zp k) `(fn-cv-car ,x) (fn-cv-nth-term (1- k) `(fn-cv-cdr ,x))))

(defun fn-cv-component (k n x)
  (declare (xargs :mode :program))
  ; the K-th index of the tuple X of N indexes: the tuple itself when N = 1
  (if (equal n 1) x (fn-cv-nth-term k x)))

(defun fn-cv-put-terms (entries e idxs k n)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (cons (fn-cv-sub (fn-cv-get :put (cdr (car entries))) (list e (fn-cv-component k n idxs)))
          (fn-cv-put-terms (cdr entries) e idxs (1+ k) n))))

(defun fn-cv-empty-terms (entries)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (cons (fn-cv-get :empty (cdr (car entries))) (fn-cv-empty-terms (cdr entries)))))

(defun fn-cv-tuple (terms n)
  (declare (xargs :mode :program))
  (if (equal n 1) (car terms) `(list ,@terms)))

; --- per-index events (:set)

(defun fn-cv-set-index-events (name ws entries k n)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (let* ((idx (car (car entries)))
           (opts (cdr (car entries)))
           (key-fn (fn-cv-get :key-fn opts))
           (hasp (fn-cv-get :hasp opts))
           (lemmas (fn-cv-get :lemmas opts))
           (of (fn-cv-name name '- idx '-of))
           (okp (fn-cv-name name '- idx '-okp))
           (put (fn-cv-name name '-put))
           (empty (fn-cv-name name '-empty))
           (build-onto (fn-cv-name name '-build-onto))
           (key-e2 (fn-cv-sub key-fn '(e2)))
           (key-e (fn-cv-sub key-fn '(e)))
           (hasp-of-put (fn-cv-name name '- idx '-hasp-of-put))
           (put-has-key (fn-cv-name name '- idx '-put-has-key))
           (subst `((fn-cv-put ,put) (fn-cv-empty ,empty)
                    (fn-cv-hasp (lambda (k idxs) ,(fn-cv-sub hasp (list 'k (list of 'idxs)))))
                    (fn-cv-key (lambda (e) ,key-e))
                    (fn-cv-set-okp ,okp)
                    (fn-cv-build-onto ,build-onto))))
      (append
       `((defun ,of (idxs)
           (declare (xargs :guard t))
           ,(fn-cv-component k n 'idxs))
         (defun ,(fn-cv-name name '- idx) (carry)
           (declare (xargs :guard t))
           (,of (fn-cv-cdr carry)))
         ; complete: every element's key (when it has one) is in the index
         (defun ,okp (,ws idxs)
           (declare (xargs :guard t))
           (if (consp ,ws)
               (and (or (not ,(fn-cv-sub key-fn (list `(car ,ws))))
                        ,(fn-cv-sub hasp (list (fn-cv-sub key-fn (list `(car ,ws))) (list of 'idxs))))
                    (,okp (cdr ,ws) idxs))
             t))
         ; the two facts the index owes (c04 3b), from its :lemmas
         (defthm ,hasp-of-put
           (implies (and ,key-e2 ,(fn-cv-sub hasp (list key-e2 (list of 'idxs))))
                    ,(fn-cv-sub hasp (list key-e2 (list of (list put 'e 'idxs)))))
           :hints (("Goal" :in-theory (enable ,put ,of fn-cv-car fn-cv-cdr ,@lemmas))))
         (defthm ,put-has-key
           (implies ,key-e ,(fn-cv-sub hasp (list key-e (list of (list put 'e 'idxs)))))
           :hints (("Goal" :in-theory (enable ,put ,of fn-cv-car fn-cv-cdr ,@lemmas))))
         (defthm ,(fn-cv-name name '- idx '-okp-of-build)
           (,okp ,ws (,build-onto ,ws (,empty)))
           :hints (("Goal" :use ((:instance (:functional-instance fn-cv-set-okp-of-build ,@subst)
                                            (ws ,ws)))
                    :in-theory (union-theories '(,okp ,build-onto ,put ,empty ,of
                                                 ,hasp-of-put ,put-has-key
                                                 fn-cv-car fn-cv-cdr)
                                               (theory 'minimal-theory)))))
         (defthm ,(fn-cv-name name '- idx '-okp-of-extend)
           (implies (,okp old idxs) (,okp (append new old) (,build-onto new idxs)))
           :hints (("Goal" :use ((:instance (:functional-instance fn-cv-set-okp-of-extend ,@subst)
                                            (old old) (new new) (idx idxs)))
                    :in-theory (union-theories '(,okp ,build-onto ,put ,empty ,of
                                                 ,hasp-of-put ,put-has-key
                                                 fn-cv-car fn-cv-cdr)
                                               (theory 'minimal-theory))))))
       (fn-cv-set-index-events name ws (cdr entries) (1+ k) n)))))

(defun fn-cv-exact-index-events (name entries k n)
  (declare (xargs :mode :program))
  ; accessors only: exactness is the tuple's
  (if (atom entries)
      nil
    (let* ((idx (car (car entries)))
           (of (fn-cv-name name '- idx '-of)))
      (append
       `((defun ,of (idxs) (declare (xargs :guard t)) ,(fn-cv-component k n 'idxs))
         (defun ,(fn-cv-name name '- idx) (carry)
           (declare (xargs :guard t))
           (,of (fn-cv-cdr carry))))
       (fn-cv-exact-index-events name (cdr entries) (1+ k) n)))))

(defun fn-cv-okp-conjuncts (name ws entries)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (cons `(,(fn-cv-name name '- (car (car entries)) '-okp) ,ws idxs)
          (fn-cv-okp-conjuncts name ws (cdr entries)))))

(defun fn-cv-okp-instances (name entries thm-suffix extra)
  (declare (xargs :mode :program))
  ; (:instance NAME-IDX-okp-THM-SUFFIX . EXTRA) per index
  (if (atom entries)
      nil
    (cons `(:instance ,(fn-cv-name name '- (car (car entries)) thm-suffix) ,@extra)
          (fn-cv-okp-instances name (cdr entries) thm-suffix extra))))

(defun fn-cv-okp-pairs (name entries)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (cons (list (fn-cv-name name '- (car (car entries)) '-okp))
          (fn-cv-okp-pairs name (cdr entries)))))

(defun fn-cv-index-accessors (name entries)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (list* (fn-cv-name name '- (car (car entries)))
           (fn-cv-name name '- (car (car entries)) '-of)
           (fn-cv-index-accessors name (cdr entries)))))

(defun fn-cv-events (name kvs)
  (declare (xargs :mode :program))
  (let* ((ws (fn-cv-get :key kvs))
         (entries (fn-cv-get :indexes kvs))
         (n (len entries))
         (setp (eq (fn-cv-get :kind (cdr (car entries))) :set))
         (ws-of (fn-cv-name name '- ws))
         (put (fn-cv-name name '-put))
         (empty (fn-cv-name name '-empty))
         (build-onto (fn-cv-name name '-build-onto))
         (fold (fn-cv-name name '-fold))
         (build (or (fn-cv-get :build kvs) (fn-cv-name name '-build)))
         (okp (fn-cv-name name '-okp))
         (carryp (fn-cv-name name '-carryp))
         (refresh (fn-cv-name name '-refresh))
         (okp-of-build (fn-cv-name name '-okp-of-build))
         (okp-of-extend (fn-cv-name name '-okp-of-extend))
         (empty-term (fn-cv-tuple (fn-cv-empty-terms entries) n))
         (index-names (strip-cars entries))
         (claim-refresh `(((carried (,carryp carry))) (,carryp (,refresh carry ,ws)))))
    `(progn
       (table fn-carried-view ',name
              '(:key ,ws :indexes ,index-names :kind ,(if setp :set :exact)
                :carryp ,carryp :refresh ,refresh :build ,build
                :declared ,entries))
       ; the carry: (WS . IDX) or (WS IDX1 ... IDXn)
       (defun ,ws-of (carry) (declare (xargs :guard t)) (fn-cv-car carry))
       (defun ,put (e idxs)
         (declare (xargs :guard t))
         ,(fn-cv-tuple (fn-cv-put-terms entries 'e 'idxs 0 n) n))
       (defun ,empty () (declare (xargs :guard t)) ,empty-term)
       (defun ,build-onto (ys idxs)
         (declare (xargs :guard t))
         (if (consp ys) (,put (car ys) (,build-onto (cdr ys) idxs)) idxs))
       (defun ,fold (racc idxs)
         (declare (xargs :guard t))
         (if (consp racc) (,fold (cdr racc) (,put (car racc) idxs)) idxs))
       (defun ,build (,ws)
         (declare (xargs :guard t))
         (,fold (revappend ,ws nil) (,empty)))
       (defthm ,(fn-cv-name build '-is-build-onto)
         (equal (,build ,ws) (,build-onto ,ws (,empty)))
         :hints (("Goal" :use ((:instance (:functional-instance fn-cv-fold-of-revappend
                                                                (fn-cv-put ,put) (fn-cv-empty ,empty)
                                                                (fn-cv-hasp (lambda (k idx) t))
                                                                (fn-cv-key (lambda (e) nil))
                                                                (fn-cv-build-onto ,build-onto)
                                                                (fn-cv-fold ,fold))
                                          (ys ,ws) (racc nil) (idx (,empty))))
                  :in-theory (union-theories '(,build ,build-onto ,fold ,put ,empty)
                                             (theory 'minimal-theory)))))
       ,@(if setp
             (fn-cv-set-index-events name ws entries 0 n)
           (fn-cv-exact-index-events name entries 0 n))
       ,(if setp
            `(defun ,okp (,ws idxs)
               (declare (xargs :guard t))
               (and ,@(fn-cv-okp-conjuncts name ws entries)))
          `(defun ,okp (,ws idxs)
             (declare (xargs :guard t))
             (equal idxs (,build-onto ,ws (,empty)))))
       (defun ,carryp (carry)
         (declare (xargs :guard t))
         (,okp (fn-cv-car carry) (fn-cv-cdr carry)))
       ,@(if setp
             `((defthm ,okp-of-build
                 (,okp ,ws (,build-onto ,ws (,empty)))
                 :hints (("Goal" :use ,(fn-cv-okp-instances name entries '-okp-of-build nil)
                          :in-theory (union-theories '(,okp) (theory 'minimal-theory)))))
               (defthm ,okp-of-extend
                 (implies (,okp old idxs) (,okp (append new old) (,build-onto new idxs)))
                 :hints (("Goal" :use ,(fn-cv-okp-instances name entries '-okp-of-extend nil)
                          :in-theory (union-theories '(,okp) (theory 'minimal-theory))))))
           `((defthm ,okp-of-build
               (,okp ,ws (,build-onto ,ws (,empty)))
               :hints (("Goal" :in-theory (union-theories '(,okp) (theory 'minimal-theory)))))
             (defthm ,okp-of-extend
               (implies (,okp old idxs) (,okp (append new old) (,build-onto new idxs)))
               :hints (("Goal" :use ((:instance (:functional-instance fn-cv-exact-okp-of-extend
                                                                      (fn-cv-put ,put) (fn-cv-empty ,empty)
                                                                      (fn-cv-hasp (lambda (k idx) t))
                                                                      (fn-cv-key (lambda (e) nil))
                                                                      (fn-cv-build-onto ,build-onto)
                                                                      (fn-cv-exact-okp ,okp))
                                                (old old) (new new) (idx idxs)))
                        :in-theory (union-theories '(,okp ,build-onto ,put ,empty)
                                                   (theory 'minimal-theory)))))))
       (defun ,refresh (carry ,ws)
         (declare (xargs :guard t))
         (if (equal ,ws (fn-cv-car carry))
             (cons ,ws (fn-cv-cdr carry))
           (mv-let (found racc)
             (fn-cv-walk ,ws (fn-cv-car carry) nil)
             (if found
                 (cons ,ws (,fold racc (fn-cv-cdr carry)))
               (cons ,ws (,fold (revappend ,ws nil) (,empty)))))))
       ; KEYSTONES
       (defthm ,(fn-cv-name carryp '-of-refresh)
         (implies (,carryp carry) (,carryp (,refresh carry ,ws)))
         :hints (("Goal" :use ((:instance (:functional-instance fn-cv-carryp-of-refresh
                                                                (fn-cv-put ,put) (fn-cv-empty ,empty)
                                                                (fn-cv-hasp (lambda (k idx) t))
                                                                (fn-cv-key (lambda (e) nil))
                                                                (fn-cv-build-onto ,build-onto)
                                                                (fn-cv-fold ,fold)
                                                                (fn-cv-okp ,okp)
                                                                (fn-cv-carryp ,carryp)
                                                                (fn-cv-refresh ,refresh))
                                          (carry carry) (ws ,ws)))
                  :in-theory (union-theories '(,carryp ,refresh ,build-onto ,fold ,put ,empty
                                               ,okp-of-build ,okp-of-extend)
                                             (theory 'minimal-theory)))))
       (defthm ,(fn-cv-name ws-of '-of-refresh)
         (equal (,ws-of (,refresh carry ,ws)) ,ws)
         :hints (("Goal" :in-theory (union-theories '(,ws-of ,refresh fn-cv-car)
                                                    (theory 'minimal-theory)))))
       ; the walk steps exactly the delta (fn-cv-walk-steps counts the
       ; elements the refresh's walk consumes; the equal at each step is
       ; the host's, c04 4a)
       (defthm ,(fn-cv-name refresh '-walks-the-delta)
         (equal (fn-cv-walk-steps (append new (,ws-of carry)) (,ws-of carry)) (len new))
         :hints (("Goal" :use ((:instance fn-cv-walk-steps-of-append (old (,ws-of carry))))
                  :in-theory (theory 'minimal-theory))))
       ,@(and (or setp (and (equal n 1) (null (car (fn-cv-empty-terms entries)))))
              `((defthm ,(fn-cv-name carryp '-of-nil)
                  (,carryp nil)
                  :hints (("Goal" :in-theory (enable ,carryp ,okp ,build-onto ,put ,empty
                                                     fn-cv-car fn-cv-cdr
                                                     ,@(and setp (strip-cars (fn-cv-okp-pairs name entries)))))))))
       (table fn-teeth-owed ',(fn-cv-name carryp '-of-refresh)
              '(:by def-carried-view :claim ,claim-refresh))
       (in-theory (disable ,ws-of ,put ,empty ,build-onto ,fold ,build ,okp ,carryp ,refresh
                           ,@(fn-cv-index-accessors name entries))))))

(defun fn-cv-first-non-theorem (names w)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((getpropc (car names) 'theorem nil w) (fn-cv-first-non-theorem (cdr names) w))
        (t (car names))))

(defun fn-cv-all-lemmas (entries)
  (declare (xargs :mode :program))
  (if (atom entries)
      nil
    (append (fn-cv-get :lemmas (cdr (car entries))) (fn-cv-all-lemmas (cdr entries)))))

(defun fn-cv-world-problem (name kvs w)
  (declare (xargs :mode :program))
  (cond ((assoc-eq name (table-alist 'fn-carried-view w)) (list :declared-twice name))
        ((fn-cv-first-non-theorem (fn-cv-all-lemmas (fn-cv-get :indexes kvs)) w)
         (list :not-a-theorem name
               (fn-cv-first-non-theorem (fn-cv-all-lemmas (fn-cv-get :indexes kvs)) w)))
        (t nil)))

(defmacro def-carried-view (name &rest kvs)
  (let ((reason (fn-cv-refusal name kvs)))
    (if reason
        `(make-event (er soft 'def-carried-view "~x0: ~@1" ',name
                         ',(fn-cv-refusal-text reason)))
      `(make-event
        (let ((problem (fn-cv-world-problem ',name ',kvs (w state))))
          (if problem
              (er soft 'def-carried-view "~x0: ~@1" ',name (fn-cv-refusal-text problem))
            (value (fn-cv-events ',name ',kvs))))))))

; ---------------------------------------------------------------------------
; def-carried-reader: a NEGATIVE FILTER over a :set view (c04 3a).  The
; reader takes the index's answer only when its list IS the carried one and
; the probe is negative; a positive probe, a stale carry or a failed
; precondition runs the reference.  The equality to the reference is proved
; from the instance's one lemma THM, stated over the variables `ws' and
; `idxs': (implies (and (NAME-IDX-okp ws idxs) PRE (not PROBE[idxs])) (equal
; REFERENCE FAST)).  No visit claim is made for the reader (c04 3c): its
; cost is the condition's, the probe's and, on the fallback, the reference's.
;
;   (def-carried-reader R (FORMALS) :of NAME :carry C :list WS :when PRE
;     :probe (IDX KEY-TERM) :fast TERM :reference TERM :by THM
;     [:name R-is-REF] [:guard G] [:stobjs (ST ...)])

(defconst *fn-cv-reader-keys*
  '(:of :carry :list :when :probe :fast :reference :by :name :guard :stobjs))

(defun fn-cv-reader-refusal (r formals kvs)
  (declare (xargs :mode :program))
  (cond
   ((not (and (symbolp r) r)) (list :bad-name r))
   ((not (and (symbol-listp formals) (no-duplicatesp-eq formals))) (list :bad-formals formals))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-cv-unknown-keys kvs *fn-cv-reader-keys*)
    (cons :unknown-keyword (fn-cv-unknown-keys kvs *fn-cv-reader-keys*)))
   ((not (and (symbolp (fn-cv-get :of kvs)) (fn-cv-get :of kvs))) (list :no-view r))
   ((not (member-eq (fn-cv-get :carry kvs) formals)) (list :carry-not-a-formal r))
   ((not (member-eq (fn-cv-get :list kvs) formals)) (list :list-not-a-formal r))
   ((not (and (true-listp (fn-cv-get :probe kvs)) (equal (len (fn-cv-get :probe kvs)) 2)
              (symbolp (car (fn-cv-get :probe kvs)))))
    (list :bad-probe r))
   ((not (assoc-keyword :fast kvs)) (list :no-fast r))
   ((not (assoc-keyword :reference kvs)) (list :no-reference r))
   ((not (and (symbolp (fn-cv-get :by kvs)) (fn-cv-get :by kvs))) (list :no-by r))
   (t nil)))

(defun fn-cv-reader-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:no-view (msg "~x0: :of names no carried view." (cadr reason)))
    (:carry-not-a-formal (msg "~x0: :carry is not one of its formals." (cadr reason)))
    (:list-not-a-formal (msg "~x0: :list is not one of its formals." (cadr reason)))
    (:bad-probe (msg "~x0: :probe is not (IDX KEY-TERM)." (cadr reason)))
    (:no-fast (msg "~x0 has no :fast answer." (cadr reason)))
    (:no-reference (msg "~x0 has no :reference walk." (cadr reason)))
    (:no-by (msg "~x0 has no :by THM, the lemma that the index's negative answer is the ~
                  reference's." (cadr reason)))
    (:no-such-view (msg "~x0: ~x1 is not a carried view of this world." (cadr reason) (caddr reason)))
    (:not-a-set-view (msg "~x0: ~x1 is an :exact view; a reader filters a :set view."
                          (cadr reason) (caddr reason)))
    (:no-such-index (msg "~x0: ~x1 has no index ~x2." (cadr reason) (caddr reason) (cadddr reason)))
    (:not-a-theorem (msg "~x0: :by ~x1 is not a theorem in this world." (cadr reason) (caddr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0." (cdr reason)))
    (otherwise (msg "malformed form: ~x0." reason))))

(defun fn-cv-reader-world-problem (r kvs w)
  (declare (xargs :mode :program))
  (let* ((view (fn-cv-get :of kvs))
         (row (cdr (assoc-eq view (table-alist 'fn-carried-view w)))))
    (cond ((null row) (list :no-such-view r view))
          ((not (eq (fn-cv-get :kind row) :set)) (list :not-a-set-view r view))
          ((not (member-eq (car (fn-cv-get :probe kvs)) (fn-cv-get :indexes row)))
           (list :no-such-index r view (car (fn-cv-get :probe kvs))))
          ((null (getpropc (fn-cv-get :by kvs) 'theorem nil w))
           (list :not-a-theorem r (fn-cv-get :by kvs)))
          (t nil))))

(defun fn-cv-hasp-of-index (view idx w)
  (declare (xargs :mode :program))
  ; the :hasp lambda the view declared for IDX, from the recorded declaration
  (fn-cv-get :hasp (cdr (assoc-eq idx (fn-cv-get :declared
                                                (cdr (assoc-eq view (table-alist 'fn-carried-view w))))))))

(defun fn-cv-reader-events (r formals kvs w)
  (declare (xargs :mode :program))
  (let* ((view (fn-cv-get :of kvs))
         (row (cdr (assoc-eq view (table-alist 'fn-carried-view w))))
         (c (fn-cv-get :carry kvs))
         (ws (fn-cv-get :list kvs))
         (idx (car (fn-cv-get :probe kvs)))
         (key (cadr (fn-cv-get :probe kvs)))
         (ws-of (fn-cv-name view '- (fn-cv-get :key row)))
         (idx-of (fn-cv-name view '- idx '-of))
         (idx-okp (fn-cv-name view '- idx '-okp))
         (carryp (fn-cv-get :carryp row))
         (okp (fn-cv-name view '-okp))
         (pre (if (assoc-keyword :when kvs) (fn-cv-get :when kvs) t))
         (hasp (fn-cv-hasp-of-index view idx w))
         (probe (fn-cv-sub hasp (list key `(,idx-of (fn-cv-cdr ,c)))))
         (fast (fn-cv-get :fast kvs))
         (reference (fn-cv-get :reference kvs))
         (thm (or (fn-cv-get :name kvs) (fn-cv-name r '-is- (car reference))))
         (claim `(((carried (,carryp ,c))) (equal (,r ,@formals) ,reference))))
    `(progn
       (defun ,r ,formals
         (declare (xargs :guard ,(if (assoc-keyword :guard kvs) (fn-cv-get :guard kvs) t)
                         ,@(and (fn-cv-get :stobjs kvs) `(:stobjs ,(fn-cv-get :stobjs kvs)))))
         (if (and ,pre (equal ,ws (,ws-of ,c)) (not ,probe))
             ,fast
           ,reference))
       (defthm ,thm
         (implies (,carryp ,c) (equal (,r ,@formals) ,reference))
         :hints (("Goal" :use ((:instance ,(fn-cv-get :by kvs) (ws (,ws-of ,c)) (idxs (fn-cv-cdr ,c))))
                  :in-theory (e/d (,r ,carryp ,okp ,ws-of fn-cv-car) (,idx-okp)))))
       (table fn-teeth-owed ',thm '(:by def-carried-reader :claim ,claim))
       (in-theory (disable ,r)))))

(defmacro def-carried-reader (r formals &rest kvs)
  (let ((reason (fn-cv-reader-refusal r formals kvs)))
    (if reason
        `(make-event (er soft 'def-carried-reader "~x0: ~@1" ',r
                         ',(fn-cv-reader-text reason)))
      `(make-event
        (let ((problem (fn-cv-reader-world-problem ',r ',kvs (w state))))
          (if problem
              (er soft 'def-carried-reader "~x0: ~@1" ',r (fn-cv-reader-text problem))
            (value (fn-cv-reader-events ',r ',formals ',kvs (w state)))))))))
