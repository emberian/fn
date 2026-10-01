; fn: `def-loop' --- the loop twin of docs/proof-style.md and PKT-877,
; generated instead of written (stage 1 of
; planning/design-store-representation-2026-10-01.md, section 3).
;
; The pattern this replaces (books/hybrid-store.lisp, 2026-09-25 and 493
; more): a structural recursion is the `:logic' body the rewriter sees; an
; accumulator loop `NAME-loop' is the `:exec' body that runs in constant
; stack; a local bridge `NAME-loop-is-revappend' states that the loop is
; `revappend' of the accumulator onto the recursion; and two `verify-guards'
; close the `mbe'.  Written by hand that is twenty-six lines, one induction
; under `minimal-theory' and two guard proofs per loop, 850 inductions
; tree-wide, and every one of them the same induction.
;
; Here each SHAPE's bridge is proved ONCE, over constrained functions that
; have no axioms (`fn-dl-f', `fn-dl-while', ...), and every instance obtains
; its bridge by `:functional-instance' of that one theorem.  The obligation
; ACL2 generates for the instance is the definitional equation of `NAME' and
; of `NAME-loop' under the substitution, which one unfold of each discharges
; in `minimal-theory': no instance induction, no instance hint.  The
; mechanism is the one books/proto/adt.lisp uses for its pool loops and
; books/history-image-fold.lisp for `fn-hif-def-fold'.
;
; Shapes, each one library theorem:
;
;   :map   (NAME XS ...) = (if (and (consp XS) WHILE)
;                              [let* LET]
;                              (if STOP STOP-VALUE
;                                (if KEEP (cons BODY (NAME (cdr XS) ...))
;                                  (NAME (cdr XS) ...)))
;                            TAIL)
;          with WHILE, KEEP default t, STOP absent, TAIL default nil, so a
;          plain map, a filter, a map that stops early (header-block), a
;          map onto a tail (append1) and a map with extra formals are the
;          same shape.  Bridge: `fn-dl-map-loop-is-revappend'.
;   :take  (NAME N XS ...) = (if (and (not (zp N)) WHILE)
;                                (cons BODY (NAME (- N 1) (cdr XS) ...))
;                              TAIL)
;          the indexed loop (`fn-rof-first', `fn-tcl-take').  Bridge:
;          `fn-dl-take-loop-is-revappend'.
;   :sum   (NAME XS ...) = (if (consp XS) (+ BODY (NAME (cdr XS) ...)) 0)
;          a count or a total; the loop adds onto a number.  Bridge:
;          `fn-dl-sum-loop-is-plus'.
;   :into  (NAME XS ... ST) = (if (consp XS) (NAME (cdr XS) ... (WRITE BODY ST)) ST)
;          the D27 form: each element's value is written into a buffer
;          stobj whose logical value is a list (`fn-octets'), and the
;          exported meaning `NAME-is-append' says the result is the buffer
;          followed by the list-level map `:map MAP' (a function with the
;          `:map' logic body over the same BODY).  Nothing is consed.
;          Bridge: `fn-dl-into-loop-is-append'.
;
; BODY, WHILE, STOP, STOP-VALUE, KEEP and TAIL are terms over the instance's
; formals; `:elt X' names a variable that stands for `(car XS)' in them and
; is substituted at expansion, so the emitted definition reads as the hand
; one did.  `:let' binds a `let*' around STOP/KEEP/BODY, for a loop whose
; test and element share a computation.
;
; What is emitted, in order: `NAME-loop' (`:verify-guards nil'); `NAME' with
; the `mbe'; the local bridge; `(verify-guards NAME-loop)'; `(verify-guards
; NAME)' by the bridge at the empty accumulator; `(in-theory (disable
; NAME-loop))'; and a row in the world table `fn-generated' naming what was
; generated, so a tool reads the world rather than a mirror of this macro.
; The bridge is local, as the hand one was: nothing above a book reasons
; about the loop.  Nothing else is enabled or exported; the library's own
; definitions are disabled at the end of this book.
;
; :keep-order :skip-first emits (if KEEP RECUR (cons BODY RECUR));
; the default :cons-first preserves the original expansion.
;
; Guards.  `:guard G' is the wrapper's guard (default t); the loop's is
; `(and G (true-listp ACC))' (`(acl2-numberp ACC)' for `:sum').  The
; wrapper's `verify-guards' runs in `minimal-theory' plus `revappend', the
; wrapper and `:guard-theory' (runes the BODY's own guard obligations need,
; when G is not t); `:guard-hints' replaces the loop's hints.
;
; Refused at expansion, with the check named: an unknown shape; `:over' (or
; `:count') not a formal; the accumulator's name among the formals; a
; `:stop' without `:stop-value'; `:stop', `:keep', `:let' or `:tail' on a
; shape that has none; a `:into' without `:map'.
;
; Not generated: a loop that steps by other than `(cdr XS)' (nov-scrub skips
; two), a loop that threads a stobj AND accumulates (a fold; see
; `fn-hif-def-fold'), `defexec'.  Those stay by hand with a `; GEN: def-loop'
; marker until a shape is added here.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; The library: one constrained shape and one bridge per form.  The
; constrained functions have no axioms (the local witnesses are trivial),
; so a functional instance owes only the definitional equations of the two
; defined functions it substitutes.  The variables are `dl-xs', `dl-acc',
; `dl-n', `dl-st' so that an instance's own formals never clash with them.

; --- :map

(encapsulate
  (((fn-dl-while *) => *) ((fn-dl-stop *) => *) ((fn-dl-stop-value *) => *)
   ((fn-dl-keep *) => *) ((fn-dl-f *) => *) ((fn-dl-tail *) => *))
  (local (defun fn-dl-while (xs) (declare (ignore xs)) t))
  (local (defun fn-dl-stop (xs) (declare (ignore xs)) nil))
  (local (defun fn-dl-stop-value (xs) (declare (ignore xs)) nil))
  (local (defun fn-dl-keep (xs) (declare (ignore xs)) t))
  (local (defun fn-dl-f (xs) (car xs)))
  (local (defun fn-dl-tail (xs) (declare (ignore xs)) nil)))

(defun fn-dl-map (dl-xs)
  (if (and (consp dl-xs) (fn-dl-while dl-xs))
      (if (fn-dl-stop dl-xs)
          (fn-dl-stop-value dl-xs)
        (if (fn-dl-keep dl-xs)
            (cons (fn-dl-f dl-xs) (fn-dl-map (cdr dl-xs)))
          (fn-dl-map (cdr dl-xs))))
    (fn-dl-tail dl-xs)))

(defun fn-dl-map-loop (dl-xs dl-acc)
  (if (and (consp dl-xs) (fn-dl-while dl-xs))
      (if (fn-dl-stop dl-xs)
          (revappend dl-acc (fn-dl-stop-value dl-xs))
        (if (fn-dl-keep dl-xs)
            (fn-dl-map-loop (cdr dl-xs) (cons (fn-dl-f dl-xs) dl-acc))
          (fn-dl-map-loop (cdr dl-xs) dl-acc)))
    (revappend dl-acc (fn-dl-tail dl-xs))))

(defthm fn-dl-map-loop-is-revappend
  (equal (fn-dl-map-loop dl-xs dl-acc) (revappend dl-acc (fn-dl-map dl-xs)))
  :hints (("Goal" :induct (fn-dl-map-loop dl-xs dl-acc))))

; Skip-first uses the same unconstrained predicates, with the keep test
; interpreted as the skip test. Its single bridge supplies every instance.
(defun fn-dl-map-skip (dl-xs)
  (if (and (consp dl-xs) (fn-dl-while dl-xs))
      (if (fn-dl-stop dl-xs) (fn-dl-stop-value dl-xs)
        (if (fn-dl-keep dl-xs)
            (fn-dl-map-skip (cdr dl-xs))
          (cons (fn-dl-f dl-xs) (fn-dl-map-skip (cdr dl-xs)))))
    (fn-dl-tail dl-xs)))

(defun fn-dl-map-skip-loop (dl-xs dl-acc)
  (if (and (consp dl-xs) (fn-dl-while dl-xs))
      (if (fn-dl-stop dl-xs) (revappend dl-acc (fn-dl-stop-value dl-xs))
        (if (fn-dl-keep dl-xs)
            (fn-dl-map-skip-loop (cdr dl-xs) dl-acc)
          (fn-dl-map-skip-loop (cdr dl-xs) (cons (fn-dl-f dl-xs) dl-acc))))
    (revappend dl-acc (fn-dl-tail dl-xs))))

(defthm fn-dl-map-skip-loop-is-revappend
  (equal (fn-dl-map-skip-loop dl-xs dl-acc)
         (revappend dl-acc (fn-dl-map-skip dl-xs)))
  :hints (("Goal" :induct (fn-dl-map-skip-loop dl-xs dl-acc))))

; --- :take

(encapsulate
  (((fn-dl-tk-while * *) => *) ((fn-dl-tk-f * *) => *) ((fn-dl-tk-tail * *) => *))
  (local (defun fn-dl-tk-while (n xs) (declare (ignore n xs)) t))
  (local (defun fn-dl-tk-f (n xs) (declare (ignore n)) (car xs)))
  (local (defun fn-dl-tk-tail (n xs) (declare (ignore n xs)) nil)))

(defun fn-dl-take (dl-n dl-xs)
  (if (and (not (zp dl-n)) (fn-dl-tk-while dl-n dl-xs))
      (cons (fn-dl-tk-f dl-n dl-xs) (fn-dl-take (- dl-n 1) (cdr dl-xs)))
    (fn-dl-tk-tail dl-n dl-xs)))

(defun fn-dl-take-loop (dl-n dl-xs dl-acc)
  (if (and (not (zp dl-n)) (fn-dl-tk-while dl-n dl-xs))
      (fn-dl-take-loop (- dl-n 1) (cdr dl-xs) (cons (fn-dl-tk-f dl-n dl-xs) dl-acc))
    (revappend dl-acc (fn-dl-tk-tail dl-n dl-xs))))

(defthm fn-dl-take-loop-is-revappend
  (equal (fn-dl-take-loop dl-n dl-xs dl-acc) (revappend dl-acc (fn-dl-take dl-n dl-xs)))
  :hints (("Goal" :induct (fn-dl-take-loop dl-n dl-xs dl-acc))))

; --- :sum

(encapsulate
  (((fn-dl-sm-f *) => *))
  (local (defun fn-dl-sm-f (xs) (declare (ignore xs)) 1)))

(defun fn-dl-sum (dl-xs)
  (if (consp dl-xs) (+ (fn-dl-sm-f dl-xs) (fn-dl-sum (cdr dl-xs))) 0))

(defun fn-dl-sum-loop (dl-xs dl-acc)
  (if (consp dl-xs) (fn-dl-sum-loop (cdr dl-xs) (+ (fn-dl-sm-f dl-xs) dl-acc)) dl-acc))

(defthm fn-dl-sum-loop-is-plus
  (implies (acl2-numberp dl-acc)
           (equal (fn-dl-sum-loop dl-xs dl-acc) (+ dl-acc (fn-dl-sum dl-xs))))
  :hints (("Goal" :induct (fn-dl-sum-loop dl-xs dl-acc))))

; --- :into

; The write is constrained, not fixed: a buffer's append export is its own
; executable (`fn-octets-append-octet' is `fn-oct-snoc'), equal to `append'
; on the buffer's logical list.  That one equation is the constraint an
; instance owes, and the buffer book has already proved it.

(encapsulate
  (((fn-dl-in-f *) => *) ((fn-dl-in-write * *) => *))
  (local (defun fn-dl-in-f (xs) (car xs)))
  (local (defun fn-dl-in-write (v st) (append st (list v))))
  (defthm fn-dl-in-write-is-append
    (implies (true-listp st)
             (equal (fn-dl-in-write v st) (append st (list v))))))

(defun fn-dl-into-map (dl-xs)
  (if (consp dl-xs) (cons (fn-dl-in-f dl-xs) (fn-dl-into-map (cdr dl-xs))) nil))

(defun fn-dl-into-loop (dl-xs dl-st)
  (if (consp dl-xs)
      (fn-dl-into-loop (cdr dl-xs) (fn-dl-in-write (fn-dl-in-f dl-xs) dl-st))
    dl-st))

(defthm fn-dl-into-loop-is-append
  (implies (true-listp dl-st)
           (equal (fn-dl-into-loop dl-xs dl-st) (append dl-st (fn-dl-into-map dl-xs))))
  :hints (("Goal" :induct (fn-dl-into-loop dl-xs dl-st))))

(in-theory (disable fn-dl-map fn-dl-map-loop fn-dl-map-loop-is-revappend
                    fn-dl-map-skip fn-dl-map-skip-loop fn-dl-map-skip-loop-is-revappend
                    fn-dl-take fn-dl-take-loop fn-dl-take-loop-is-revappend
                    fn-dl-sum fn-dl-sum-loop fn-dl-sum-loop-is-plus
                    fn-dl-into-map fn-dl-into-loop fn-dl-into-loop-is-append))

; -----------------------------------------------------------------------------
; Term and symbol plumbing, `:program' mode: these run at macroexpansion time
; and contribute no rune to any includer (as books/defrecord.lisp).

(defun fn-dl-name (parts witness)
  (declare (xargs :mode :program))
  (packn-pos parts witness))

; BODY with unquoted occurrences of the symbol VAR replaced by TERM.  A
; syntactic substitution over the untranslated body: `:elt' must not be
; rebound inside BODY.
(defun fn-dl-subst (var term body)
  (declare (xargs :mode :program))
  (cond ((eq body var) term)
        ((atom body) body)
        ((eq (car body) 'quote) body)
        (t (cons (fn-dl-subst var term (car body))
                 (fn-dl-subst var term (cdr body))))))

; The formals with XS replaced by NEW (and, for :take, N by NEW-N).
(defun fn-dl-replace (formals old new)
  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        ((eq (car formals) old) (cons new (fn-dl-replace (cdr formals) old new)))
        (t (cons (car formals) (fn-dl-replace (cdr formals) old new)))))

(defun fn-dl-and (a b)
  (declare (xargs :mode :program))
  (cond ((eq b t) a) ((eq a t) b) (t `(and ,a ,b))))

(defun fn-dl-let (bindings body)
  (declare (xargs :mode :program))
  (if bindings `(let* ,bindings ,body) body))

; TERM with the element variable ELT (if any) standing for `(car XS)'.
(defun fn-dl-elt (elt xs term)
  (declare (xargs :mode :program))
  (if elt (fn-dl-subst elt `(car ,xs) term) term))

; -----------------------------------------------------------------------------
; The generated events.

(defun fn-dl-map-events (name formals xs elt body while stop stop-value keep tail
                              let guard guard-hints guard-theory acc loop measure keep-order)
  (declare (xargs :mode :program))
  (let* ((body (fn-dl-elt elt xs body))
         (while (fn-dl-elt elt xs while))
         (stop (fn-dl-elt elt xs stop))
         (stop-value (fn-dl-elt elt xs stop-value))
         (keep (fn-dl-elt elt xs keep))
         (tail (fn-dl-elt elt xs tail))
         (let (fn-dl-elt elt xs let))
         (test (fn-dl-and `(consp ,xs) while))
         (next (fn-dl-replace formals xs `(cdr ,xs)))
         (rec `(,name ,@next))
         (loop-cons `(,loop ,@next (cons ,body ,acc)))
         (loop-skip `(,loop ,@next ,acc))
         (bridge (fn-dl-name (list loop "-IS-REVAPPEND") name))
         (logic-inner (if (eq keep-order :skip-first)
                          `(if ,keep ,rec (cons ,body ,rec))
                        (if (eq keep t)
                          `(cons ,body ,rec)
                        `(if ,keep (cons ,body ,rec) ,rec))))
         (logic-body
          `(if ,test
               ,(fn-dl-let let (if stop `(if ,stop ,stop-value ,logic-inner) logic-inner))
             ,tail))
         (loop-inner (if (eq keep-order :skip-first)
                         `(if ,keep ,loop-skip ,loop-cons)
                       (if (eq keep t)
                         loop-cons
                       `(if ,keep ,loop-cons ,loop-skip))))
         (loop-body
          `(if ,test
               ,(fn-dl-let let (if stop
                                   `(if ,stop (revappend ,acc ,stop-value) ,loop-inner)
                                 loop-inner))
             (revappend ,acc ,tail))))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(fn-dl-and guard `(true-listp ,acc))
                        :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        ,loop-body)
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (mbe :logic ,logic-body
             :exec (,loop ,@formals nil)))
      (local
       (defthm ,bridge
         (equal (,loop ,@formals ,acc) (revappend ,acc (,name ,@formals)))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          ,(if (eq keep-order :skip-first)
                               'fn-dl-map-skip-loop-is-revappend
                             'fn-dl-map-loop-is-revappend)
                          (fn-dl-while (lambda (,xs) ,while))
                          (fn-dl-stop (lambda (,xs) ,(if stop (fn-dl-let let stop) nil)))
                          (fn-dl-stop-value (lambda (,xs) ,(if stop (fn-dl-let let stop-value) nil)))
                          (fn-dl-keep (lambda (,xs) ,(fn-dl-let let keep)))
                          (fn-dl-f (lambda (,xs) ,(fn-dl-let let body)))
                          (fn-dl-tail (lambda (,xs) ,tail))
                          (,(if (eq keep-order :skip-first) 'fn-dl-map-skip 'fn-dl-map) (lambda (,xs) (,name ,@formals)))
                          (,(if (eq keep-order :skip-first) 'fn-dl-map-skip-loop 'fn-dl-map-loop) (lambda (,xs ,acc) (,loop ,@formals ,acc))))
                         (dl-xs ,xs) (dl-acc ,acc)))
                  :in-theory (union-theories '(,name ,loop) (theory 'minimal-theory))))))
      (verify-guards ,loop ,@(and guard-hints `(:hints ,guard-hints)))
      (verify-guards ,name
        :hints (("Goal"
                 :use ((:instance ,bridge (,acc nil)))
                 :in-theory (union-theories '(revappend ,name ,@guard-theory)
                                            (union-theories (theory 'minimal-theory)
                                                            (executable-counterpart-theory :here))))))
      (in-theory (disable ,loop))
      (table fn-generated ',name '(:def-loop :shape :map :loop ,loop :bridge ,bridge)))))

(defun fn-dl-take-events (name formals n xs elt body while tail
                               guard guard-hints guard-theory acc loop measure)
  (declare (xargs :mode :program))
  (let* ((body (fn-dl-elt elt xs body))
         (while (fn-dl-elt elt xs while))
         (tail (fn-dl-elt elt xs tail))
         (test (fn-dl-and `(not (zp ,n)) while))
         (next (fn-dl-replace (fn-dl-replace formals xs `(cdr ,xs)) n `(- ,n 1)))
         (bridge (fn-dl-name (list loop "-IS-REVAPPEND") name)))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(fn-dl-and guard `(true-listp ,acc))
                        :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (if ,test
            (,loop ,@next (cons ,body ,acc))
          (revappend ,acc ,tail)))
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (mbe :logic (if ,test (cons ,body (,name ,@next)) ,tail)
             :exec (,loop ,@formals nil)))
      (local
       (defthm ,bridge
         (equal (,loop ,@formals ,acc) (revappend ,acc (,name ,@formals)))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          fn-dl-take-loop-is-revappend
                          (fn-dl-tk-while (lambda (,n ,xs) ,while))
                          (fn-dl-tk-f (lambda (,n ,xs) ,body))
                          (fn-dl-tk-tail (lambda (,n ,xs) ,tail))
                          (fn-dl-take (lambda (,n ,xs) (,name ,@formals)))
                          (fn-dl-take-loop (lambda (,n ,xs ,acc) (,loop ,@formals ,acc))))
                         (dl-n ,n) (dl-xs ,xs) (dl-acc ,acc)))
                  :in-theory (union-theories '(,name ,loop) (theory 'minimal-theory))))))
      (verify-guards ,loop ,@(and guard-hints `(:hints ,guard-hints)))
      (verify-guards ,name
        :hints (("Goal"
                 :use ((:instance ,bridge (,acc nil)))
                 :in-theory (union-theories '(revappend ,name ,@guard-theory)
                                            (union-theories (theory 'minimal-theory)
                                                            (executable-counterpart-theory :here))))))
      (in-theory (disable ,loop))
      (table fn-generated ',name '(:def-loop :shape :take :loop ,loop :bridge ,bridge)))))

(defun fn-dl-sum-events (name formals xs elt body guard guard-hints guard-theory acc loop measure)
  (declare (xargs :mode :program))
  (let* ((body (if elt (fn-dl-subst elt `(car ,xs) body) body))
         (next (fn-dl-replace formals xs `(cdr ,xs)))
         (bridge (fn-dl-name (list loop "-IS-PLUS") name)))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(fn-dl-and guard `(acl2-numberp ,acc))
                        :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (if (consp ,xs)
            (,loop ,@next (+ ,body ,acc))
          ,acc))
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (mbe :logic (if (consp ,xs) (+ ,body (,name ,@next)) 0)
             :exec (,loop ,@formals 0)))
      (local
       (defthm ,bridge
         (implies (acl2-numberp ,acc)
                  (equal (,loop ,@formals ,acc) (+ ,acc (,name ,@formals))))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          fn-dl-sum-loop-is-plus
                          (fn-dl-sm-f (lambda (,xs) ,body))
                          (fn-dl-sum (lambda (,xs) (,name ,@formals)))
                          (fn-dl-sum-loop (lambda (,xs ,acc) (,loop ,@formals ,acc))))
                         (dl-xs ,xs) (dl-acc ,acc)))
                  :in-theory (union-theories '(,name ,loop) (theory 'minimal-theory))))))
      (verify-guards ,loop ,@(and guard-hints `(:hints ,guard-hints)))
      (verify-guards ,name
        :hints (("Goal"
                 :use ((:instance ,bridge (,acc 0)))
                 :in-theory (union-theories '(,name ,@guard-theory)
                                            (union-theories (theory 'minimal-theory)
                                                            (executable-counterpart-theory :here))))))
      (in-theory (disable ,loop))
      (table fn-generated ',name '(:def-loop :shape :sum :loop ,loop :bridge ,bridge)))))

(defun fn-dl-into-events (name formals xs elt body st write write-theory map
                               guard guard-hints measure)
  (declare (xargs :mode :program))
  (let* ((body (if elt (fn-dl-subst elt `(car ,xs) body) body))
         (next (fn-dl-replace formals xs `(cdr ,xs)))
         (map-formals (remove1-eq st formals))
         (bridge (fn-dl-name (list name "-IS-APPEND") name)))
    `((defun ,name ,formals
        (declare (xargs :stobjs ,st :guard ,guard
                        ,@(and guard-hints `(:guard-hints ,guard-hints))
                        ,@(and measure `(:measure ,measure))))
        (if (consp ,xs)
            (let ((,st (,write ,body ,st)))
              (,name ,@next))
          ,st))
      (defthm ,bridge
        (implies (true-listp ,st)
                 (equal (,name ,@formals) (append ,st (,map ,@map-formals))))
        :hints (("Goal"
                 :use ((:instance
                        (:functional-instance
                         fn-dl-into-loop-is-append
                         (fn-dl-in-f (lambda (,xs) ,body))
                         (fn-dl-in-write (lambda (dl-v ,st) (,write dl-v ,st)))
                         (fn-dl-into-map (lambda (,xs) (,map ,@map-formals)))
                         (fn-dl-into-loop (lambda (,xs ,st) (,name ,@formals))))
                        (dl-xs ,xs) (dl-st ,st)))
                 :in-theory (union-theories '(,name ,map ,@write-theory) (theory 'minimal-theory)))))
      (in-theory (disable ,name))
      (table fn-generated ',name '(:def-loop :shape :into :bridge ,bridge)))))

; -----------------------------------------------------------------------------
; def-loop
;
;   (def-loop fn-hsig-octet-fields-to-strings (fields)
;     :shape :map :elt field
;     :body (fn-record-octets-string field))
;
;   (def-loop fn-sl-append1 (x r) :shape :map :elt e :body e :tail (list r))
;
;   (def-loop fn-rof-first (n xs) :shape :take :count n :over xs
;     :while (consp xs) :elt e :body e :guard (natp n))
;
;   (def-loop fn-render-octets (items fn-octets) :shape :into
;     :into fn-octets :write fn-octets-append-octet
;     :write-theory (fn-octets-append-octet fn-octets$a-append-octet)
;     :map fn-render-list :elt item :body (fn-item-octet item)
;     :guard (fn-item-listp items))
;
; `:over' is the list formal (default: the first formal; for `:into', the
; first formal that is not the stobj); `:count' the index formal of `:take'
; (default: the first formal).  `:acc' renames the accumulator (default
; `acc'); `:loop' renames the loop (default `NAME-loop').

; The checks are soft errors from a `make-event' (as `definterface' and
; `defkeystone' refuse), so a test book can state them with `must-fail'.
; The expansion is stored in the certificate; an include replays it.

(defun fn-dl-fn (name formals shape over count elt body while stop stop-value keep tail let
                      guard guard-hints guard-theory measure into write write-theory map
                      acc loop keep-order state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((loop (or loop (fn-dl-name (list name "-LOOP") name)))
         (xs (or over (if (eq shape :into) (car (remove1-eq into formals)) (car formals))))
         (n (or count (car formals)))
         (ctx 'def-loop))
    (cond
     ((not (member-eq shape '(:map :take :sum :into)))
      (er soft ctx "~x0: :shape ~x1 is not one of :map, :take, :sum, :into." name shape))
     ((not (and (symbol-listp formals) formals))
      (er soft ctx "~x0: the formals must be a non-empty list of symbols." name))
     ((not (member-eq xs formals))
      (er soft ctx "~x0: :over ~x1 is not a formal." name xs))
     ((and (eq shape :take) (or (not (member-eq n formals)) (eq n xs)))
      (er soft ctx "~x0: :count ~x1 must be a formal other than :over ~x2." name n xs))
     ((member-eq acc formals)
      (er soft ctx "~x0: the accumulator ~x1 is among the formals; rename it with :acc." name acc))
     ((not (member-eq keep-order '(:cons-first :skip-first)))
      (er soft ctx "~x0: :keep-order must be :cons-first or :skip-first." name))
     ((and (not (eq keep-order :cons-first)) (not (eq shape :map)))
      (er soft ctx "~x0: :keep-order is a :map option." name))
     ((null body)
      (er soft ctx "~x0: :body is required." name))
     ((and stop (not (eq shape :map)))
      (er soft ctx "~x0: :stop is a :map option; shape ~x1 has none." name shape))
     ((and stop (null stop-value))
      (er soft ctx "~x0: :stop needs :stop-value (the value returned when it holds)." name))
     ((and (not (eq keep t)) (not (eq shape :map)))
      (er soft ctx "~x0: :keep is a :map option; shape ~x1 has none." name shape))
     ((and let (not (eq shape :map)))
      (er soft ctx "~x0: :let is a :map option; shape ~x1 has none." name shape))
     ((and (not (eq tail nil)) (not (member-eq shape '(:map :take))))
      (er soft ctx "~x0: :tail is a :map or :take option; shape ~x1 has none." name shape))
     ((and (not (eq while t)) (not (member-eq shape '(:map :take))))
      (er soft ctx "~x0: :while is a :map or :take option; shape ~x1 has none." name shape))
     ((and (eq shape :into) (not (and into write map (member-eq into formals))))
      (er soft ctx "~x0: :into needs :into (a stobj formal), :write (its append export) and :map (the list-level map)." name))
     (t
      (value
       `(encapsulate
          ()
          ,@(case shape
              (:map (fn-dl-map-events name formals xs elt body while stop stop-value keep tail
                                      let guard guard-hints guard-theory acc loop measure keep-order))
              (:take (fn-dl-take-events name formals n xs elt body while tail
                                        guard guard-hints guard-theory acc loop measure))
              (:sum (fn-dl-sum-events name formals xs elt body guard guard-hints guard-theory
                                      acc loop measure))
              (otherwise (fn-dl-into-events name formals xs elt body into write write-theory map
                                            guard guard-hints measure)))))))))

(defmacro def-loop (name formals &key
                         (shape ':map)
                         over count elt body
                         (while 't) stop stop-value (keep 't) (tail 'nil) let
                         (guard 't) guard-hints guard-theory measure
                         into write write-theory map
                         (acc 'acc) loop (keep-order ':cons-first))
  `(make-event
    (fn-dl-fn ',name ',formals ',shape ',over ',count ',elt ',body ',while ',stop ',stop-value
              ',keep ',tail ',let ',guard ',guard-hints ',guard-theory ',measure
              ',into ',write ',write-theory ',map ',acc ',loop ',keep-order state)))
