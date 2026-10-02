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

(defun fn-cv-refresh (carry ws)
  (if (equal ws (fn-cv-car carry))
      carry
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
   :hints (("Goal" :use ((:instance fn-cv-revappend-append (b nil)))))))

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
