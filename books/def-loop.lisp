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
;   :concat (NAME XS ...) appends BODY for each element; the loop
;           revappends each BODY into ACC, then reverses ACC at the end.
;           Bridge: `fn-dl-concat-loop-is-revappend'.
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
; :map :base TERM emits (if TERM TAIL INNER), preserving every inner
; option. Its only constraint is (implies (not TERM) (consp XS)); the
; instance discharges it with the defining equations in minimal-theory.
; :base excludes :while, including an explicitly supplied :while t.
;
; :take :base TERM emits a base-first IF. The shape requires that
; (not TERM) imply (posp COUNT); each instance discharges that progress
; condition along with the two defining equations. :base excludes :while.
;
; :map :loop-guard G overrides only the loop declaration. It uses the
; same unconditional library bridge; both guard-verification events still
; discharge the caller-supplied guard. :default preserves the old form.
;
; :map :acc-fix t reverses (true-list-fix ACC), permitting the loop
; guard to omit true-listp ACC. Its bridge states that same fixed value.
;
; :map :stobjs ST (or a list of stobj formals) declares immutable
; context. It uses the same map library bridge, with those formals fixed.
; Updaters, including macro-expanded calls, are refused before expansion.
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
; element/selector functions have no constraints (their local witnesses
; are trivial). Base-first shapes additionally require progress, and :into
; requires the append equation below. An instance owes these constraints
; plus the defining equations of the two functions it substitutes.  The variables are `dl-xs', `dl-acc',
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

; The guard-T accumulator variant fixes only the accumulator at reversal.
; The model's map is unchanged; a skip-first instance negates its selector
; in the functional substitution, not in the emitted logic body.
(defun fn-dl-map-fixed-loop (dl-xs dl-acc)
  (if (and (consp dl-xs) (fn-dl-while dl-xs))
      (if (fn-dl-stop dl-xs)
          (revappend (true-list-fix dl-acc) (fn-dl-stop-value dl-xs))
        (if (fn-dl-keep dl-xs)
            (fn-dl-map-fixed-loop (cdr dl-xs) (cons (fn-dl-f dl-xs) dl-acc))
          (fn-dl-map-fixed-loop (cdr dl-xs) dl-acc)))
    (revappend (true-list-fix dl-acc) (fn-dl-tail dl-xs))))

(defthm fn-dl-map-fixed-loop-is-revappend
  (equal (fn-dl-map-fixed-loop dl-xs dl-acc)
         (revappend (true-list-fix dl-acc) (fn-dl-map dl-xs)))
  :hints (("Goal" :induct (fn-dl-map-fixed-loop dl-xs dl-acc))))

; --- :map with a base-first predicate. The only base constraint is progress.
; FIXP selects the existing accumulator convention; it has no constraints.
; Skip-first instances negate KEEP in the substitution, leaving the emitted
; branch order intact. All combinations use this one bridge.
(encapsulate
  (((fn-dl-mb-base *) => *) ((fn-dl-mb-fixp) => *))
  (local (defun fn-dl-mb-base (xs) (atom xs)))
  (local (defun fn-dl-mb-fixp () nil))
  (defthm fn-dl-mb-base-progress
    (implies (not (fn-dl-mb-base xs)) (consp xs))))

(defun fn-dl-map-base (dl-xs)
  (if (fn-dl-mb-base dl-xs)
      (fn-dl-tail dl-xs)
    (if (fn-dl-stop dl-xs)
        (fn-dl-stop-value dl-xs)
      (if (fn-dl-keep dl-xs)
          (cons (fn-dl-f dl-xs) (fn-dl-map-base (cdr dl-xs)))
        (fn-dl-map-base (cdr dl-xs))))))

(defun fn-dl-map-base-loop (dl-xs dl-acc)
  (if (fn-dl-mb-base dl-xs)
      (revappend (if (fn-dl-mb-fixp) (true-list-fix dl-acc) dl-acc)
                 (fn-dl-tail dl-xs))
    (if (fn-dl-stop dl-xs)
        (revappend (if (fn-dl-mb-fixp) (true-list-fix dl-acc) dl-acc)
                   (fn-dl-stop-value dl-xs))
      (if (fn-dl-keep dl-xs)
          (fn-dl-map-base-loop (cdr dl-xs) (cons (fn-dl-f dl-xs) dl-acc))
        (fn-dl-map-base-loop (cdr dl-xs) dl-acc)))))

(defthm fn-dl-map-base-loop-is-revappend
  (equal (fn-dl-map-base-loop dl-xs dl-acc)
         (revappend (if (fn-dl-mb-fixp) (true-list-fix dl-acc) dl-acc)
                    (fn-dl-map-base dl-xs)))
  :hints (("Goal" :induct (fn-dl-map-base-loop dl-xs dl-acc))))

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

; --- :take with a caller's base predicate. Progress is the shape's
; termination condition, not an assumption about any stored data.
(encapsulate
  (((fn-dl-tb-base * *) => *))
  (local (defun fn-dl-tb-base (n xs) (declare (ignore xs)) (not (posp n))))
  (defthm fn-dl-tb-base-progress
    (implies (not (fn-dl-tb-base n xs)) (posp n))))

(defun fn-dl-take-base (dl-n dl-xs)
  (declare (xargs :measure (nfix dl-n)
                  :hints (("Goal" :use ((:instance fn-dl-tb-base-progress
                                                   (n dl-n) (xs dl-xs)))
                                  :in-theory (enable posp)))))
  (if (fn-dl-tb-base dl-n dl-xs)
      (fn-dl-tk-tail dl-n dl-xs)
    (cons (fn-dl-tk-f dl-n dl-xs)
          (fn-dl-take-base (- dl-n 1) (cdr dl-xs)))))

(defun fn-dl-take-base-loop (dl-n dl-xs dl-acc)
  (declare (xargs :measure (nfix dl-n)
                  :hints (("Goal" :use ((:instance fn-dl-tb-base-progress
                                                   (n dl-n) (xs dl-xs)))
                                  :in-theory (enable posp)))))
  (if (fn-dl-tb-base dl-n dl-xs)
      (revappend dl-acc (fn-dl-tk-tail dl-n dl-xs))
    (fn-dl-take-base-loop (- dl-n 1) (cdr dl-xs)
                         (cons (fn-dl-tk-f dl-n dl-xs) dl-acc))))

(defthm fn-dl-take-base-loop-is-revappend
  (equal (fn-dl-take-base-loop dl-n dl-xs dl-acc)
         (revappend dl-acc (fn-dl-take-base dl-n dl-xs)))
  :hints (("Goal" :induct (fn-dl-take-base-loop dl-n dl-xs dl-acc))))

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

; --- :concat: each element contributes a list, collected in reverse.
(encapsulate
  (((fn-dl-cc-f *) => *))
  (local (defun fn-dl-cc-f (xs) (list (car xs)))))

(defun fn-dl-concat (dl-xs)
  (if (consp dl-xs)
      (append (fn-dl-cc-f dl-xs) (fn-dl-concat (cdr dl-xs)))
    nil))

(defun fn-dl-concat-loop (dl-xs dl-acc)
  (if (consp dl-xs)
      (fn-dl-concat-loop (cdr dl-xs) (revappend (fn-dl-cc-f dl-xs) dl-acc))
    (revappend dl-acc nil)))

(local (defthm fn-dl-revappend-revappend
         (equal (revappend (revappend a b) c)
                (revappend b (append a c)))))

(defthm fn-dl-concat-loop-is-revappend
  (equal (fn-dl-concat-loop dl-xs dl-acc)
         (revappend dl-acc (fn-dl-concat dl-xs)))
  :hints (("Goal" :induct (fn-dl-concat-loop dl-xs dl-acc))))

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

; --- :step: one state, arbitrary advance.  The state S is the list of the
; formals the recursion changes (one formal is the state itself; several are
; a tuple, and an instance's lambdas destructure it with CAR/CDR).  A step
; is DONE (the TAIL), an EMIT (the element F of S consed, then the recursion
; on NE), or a skip (the recursion on NS).  The measure M is constrained to
; be a natural number that falls on both advances: the instance owes those
; facts, the same ones its own termination proof owes, and `def-loop' states
; them as local lemmas and hands them to the bridge's proof.
(encapsulate
  (((fn-dl-sp-done *) => *) ((fn-dl-sp-emit *) => *) ((fn-dl-sp-f *) => *)
   ((fn-dl-sp-tail *) => *) ((fn-dl-sp-ne *) => *) ((fn-dl-sp-ns *) => *)
   ((fn-dl-sp-m *) => *))
  (local (defun fn-dl-sp-done (s) (atom s)))
  (local (defun fn-dl-sp-emit (s) (declare (ignore s)) t))
  (local (defun fn-dl-sp-f (s) (car s)))
  (local (defun fn-dl-sp-tail (s) (declare (ignore s)) nil))
  (local (defun fn-dl-sp-ne (s) (cdr s)))
  (local (defun fn-dl-sp-ns (s) (cdr s)))
  (local (defun fn-dl-sp-m (s) (acl2-count s)))
  (defthm fn-dl-sp-m-natp (natp (fn-dl-sp-m dl-ps)))
  (defthm fn-dl-sp-emit-progress
    (implies (and (not (fn-dl-sp-done dl-ps)) (fn-dl-sp-emit dl-ps))
             (< (fn-dl-sp-m (fn-dl-sp-ne dl-ps)) (fn-dl-sp-m dl-ps))))
  (defthm fn-dl-sp-skip-progress
    (implies (and (not (fn-dl-sp-done dl-ps)) (not (fn-dl-sp-emit dl-ps)))
             (< (fn-dl-sp-m (fn-dl-sp-ns dl-ps)) (fn-dl-sp-m dl-ps)))))

(defun fn-dl-step (dl-s)
  (declare (xargs :measure (nfix (fn-dl-sp-m dl-s))))
  (if (fn-dl-sp-done dl-s)
      (fn-dl-sp-tail dl-s)
    (if (fn-dl-sp-emit dl-s)
        (cons (fn-dl-sp-f dl-s) (fn-dl-step (fn-dl-sp-ne dl-s)))
      (fn-dl-step (fn-dl-sp-ns dl-s)))))

(defun fn-dl-step-loop (dl-s dl-acc)
  (declare (xargs :measure (nfix (fn-dl-sp-m dl-s))))
  (if (fn-dl-sp-done dl-s)
      (revappend dl-acc (fn-dl-sp-tail dl-s))
    (if (fn-dl-sp-emit dl-s)
        (fn-dl-step-loop (fn-dl-sp-ne dl-s) (cons (fn-dl-sp-f dl-s) dl-acc))
      (fn-dl-step-loop (fn-dl-sp-ns dl-s) dl-acc))))

(defthm fn-dl-step-loop-is-revappend
  (equal (fn-dl-step-loop dl-s dl-acc) (revappend dl-acc (fn-dl-step dl-s)))
  :hints (("Goal" :induct (fn-dl-step-loop dl-s dl-acc))))

; --- :fold: a stobj (or any value) threaded through each element; the
; result is the list of the elements' rows, or FAIL when a step fails.
; STEP is an (mv ROW ST); the recursion and the loop agree on the rows and the
; final ST.  Same state and measure discipline as :step.
(encapsulate
  (((fn-dl-fo-done *) => *) ((fn-dl-fo-step * *) => (mv * *))
   ((fn-dl-fo-next *) => *) ((fn-dl-fo-m *) => *) ((fn-dl-fo-fail) => *))
  (local (defun fn-dl-fo-done (s) (atom s)))
  (local (defun fn-dl-fo-step (s st) (mv (car s) st)))
  (local (defun fn-dl-fo-next (s) (cdr s)))
  (local (defun fn-dl-fo-m (s) (acl2-count s)))
  (local (defun fn-dl-fo-fail () :bad))
  (defthm fn-dl-fo-fail-not-a-list (not (listp (fn-dl-fo-fail))))
  (defthm fn-dl-fo-m-natp (natp (fn-dl-fo-m dl-ps)))
  (defthm fn-dl-fo-progress
    (implies (not (fn-dl-fo-done dl-ps))
             (< (fn-dl-fo-m (fn-dl-fo-next dl-ps)) (fn-dl-fo-m dl-ps)))))

(defun fn-dl-fold (dl-s dl-st)
  (declare (xargs :measure (nfix (fn-dl-fo-m dl-s))))
  (if (fn-dl-fo-done dl-s)
      (mv nil dl-st)
    (mv-let (row st1) (fn-dl-fo-step dl-s dl-st)
      (if (equal row (fn-dl-fo-fail))
          (mv (fn-dl-fo-fail) st1)
        (mv-let (rest st2) (fn-dl-fold (fn-dl-fo-next dl-s) st1)
          (if (equal rest (fn-dl-fo-fail))
              (mv (fn-dl-fo-fail) st2)
            (mv (cons row rest) st2)))))))

(defun fn-dl-fold-loop (dl-s dl-acc dl-st)
  (declare (xargs :measure (nfix (fn-dl-fo-m dl-s))))
  (if (fn-dl-fo-done dl-s)
      (mv (revappend dl-acc nil) dl-st)
    (mv-let (row st1) (fn-dl-fo-step dl-s dl-st)
      (if (equal row (fn-dl-fo-fail))
          (mv (fn-dl-fo-fail) st1)
        (fn-dl-fold-loop (fn-dl-fo-next dl-s) (cons row dl-acc) st1)))))

(local
 (defthm fn-dl-fo-cons-not-fail
   (not (equal (cons a b) (fn-dl-fo-fail)))
   :hints (("Goal" :use fn-dl-fo-fail-not-a-list
                   :in-theory (disable fn-dl-fo-fail-not-a-list)))))

(defthm fn-dl-fold-loop-is-revappend
  (equal (fn-dl-fold-loop dl-s dl-acc dl-st)
         (mv-let (r a) (fn-dl-fold dl-s dl-st)
           (mv (if (equal r (fn-dl-fo-fail)) (fn-dl-fo-fail) (revappend dl-acc r)) a)))
  :hints (("Goal" :induct (fn-dl-fold-loop dl-s dl-acc dl-st))))

; --- :foldr: a right fold with a non-list accumulator, executed as a left
; fold over the reversed list.  F combines an element with the fold of the
; rest, Z is the fold of the empty list; the loop runs `fn-dl-fr-f' left to
; right over the reversal.  No hypothesis: both stop at the first atom.
(encapsulate
  (((fn-dl-fr-f * *) => *) ((fn-dl-fr-z) => *))
  (local (defun fn-dl-fr-f (x acc) (cons x acc)))
  (local (defun fn-dl-fr-z () nil)))

(defun fn-dl-foldr (dl-xs)
  (if (consp dl-xs)
      (fn-dl-fr-f (car dl-xs) (fn-dl-foldr (cdr dl-xs)))
    (fn-dl-fr-z)))

(defun fn-dl-foldr-loop (dl-xs dl-acc)
  (if (consp dl-xs)
      (fn-dl-foldr-loop (cdr dl-xs) (fn-dl-fr-f (car dl-xs) dl-acc))
    dl-acc))

(local
 (defthm fn-dl-foldr-loop-of-snoc
   (equal (fn-dl-foldr-loop (append dl-l (list dl-x)) dl-acc)
          (fn-dl-fr-f dl-x (fn-dl-foldr-loop dl-l dl-acc)))
   :hints (("Goal" :induct (fn-dl-foldr-loop dl-l dl-acc)))))

(local
 (defthm fn-dl-foldr-revappend-append-gen
   (equal (revappend dl-l (append dl-a dl-b)) (append (revappend dl-l dl-a) dl-b))
   :rule-classes nil
   :hints (("Goal" :induct (revappend dl-l dl-a)))))

(local
 (defthm fn-dl-foldr-revappend-cons
   (equal (revappend (cons dl-x dl-xs) nil)
          (append (revappend dl-xs nil) (list dl-x)))
   :hints (("Goal" :use ((:instance fn-dl-foldr-revappend-append-gen
                                    (dl-l dl-xs) (dl-a nil) (dl-b (list dl-x))))))))

(defthm fn-dl-foldr-loop-is-foldr
  (equal (fn-dl-foldr-loop (revappend dl-xs nil) (fn-dl-fr-z)) (fn-dl-foldr dl-xs))
  :hints (("Goal" :induct (fn-dl-foldr dl-xs))))

(in-theory (disable fn-dl-mb-base-progress fn-dl-map-base
                    fn-dl-map-base-loop fn-dl-map-base-loop-is-revappend
                    fn-dl-map fn-dl-map-loop fn-dl-map-loop-is-revappend
                    fn-dl-map-fixed-loop fn-dl-map-fixed-loop-is-revappend
                    fn-dl-map-skip fn-dl-map-skip-loop fn-dl-map-skip-loop-is-revappend
                    fn-dl-take fn-dl-take-loop fn-dl-take-loop-is-revappend
                    fn-dl-tb-base-progress fn-dl-take-base fn-dl-take-base-loop
                    fn-dl-take-base-loop-is-revappend
                    fn-dl-sum fn-dl-sum-loop fn-dl-sum-loop-is-plus
                    fn-dl-concat fn-dl-concat-loop fn-dl-concat-loop-is-revappend
                    fn-dl-into-map fn-dl-into-loop fn-dl-into-loop-is-append
                    fn-dl-sp-m-natp fn-dl-sp-emit-progress fn-dl-sp-skip-progress
                    fn-dl-step fn-dl-step-loop fn-dl-step-loop-is-revappend
                    fn-dl-fo-fail-not-a-list fn-dl-fo-m-natp fn-dl-fo-progress
                    fn-dl-fold fn-dl-fold-loop fn-dl-fold-loop-is-revappend
                    fn-dl-foldr fn-dl-foldr-loop fn-dl-foldr-loop-is-foldr))

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

; Base-first map proof substitutions may use only some LET bindings (for
; example KEEP defaults to T). Declarations affect translation checks only;
; they do not alter the instance's emitted logic or loop bodies.
(defun fn-dl-map-proof-let (base bindings body)
  (declare (xargs :mode :program))
  (if (and base bindings)
      `(let* ,bindings (declare (ignorable ,@(strip-cars bindings))) ,body)
    (fn-dl-let bindings body)))

; TERM with the element variable ELT (if any) standing for `(car XS)'.
(defun fn-dl-elt (elt xs term)
  (declare (xargs :mode :program))
  (if elt (fn-dl-subst elt `(car ,xs) term) term))

; Check read-only stobj options against the world and the translated terms,
; so an updater hidden behind a macro is checked too. ACL2 also checks the
; generated functions' stobj signatures and guard obligations at admission.
(defun fn-dl-stobjs-knownp (stobjs formals wrld)
  (declare (xargs :mode :program))
  (if (endp stobjs) t
    (and (member-eq (car stobjs) formals)
         (getpropc (car stobjs) 'stobj nil wrld)
         (fn-dl-stobjs-knownp (cdr stobjs) formals wrld))))

(defun fn-dl-updaterp (term stobjs wrld)
  (declare (xargs :mode :program))
  (cond ((atom term) nil)
        ((eq (car term) 'quote) nil)
        (t (or (and (symbolp (car term))
                    (intersection-eq stobjs (getpropc (car term) 'stobjs-out nil wrld)))
               (fn-dl-updaterp (car term) stobjs wrld)
               (fn-dl-updaterp (cdr term) stobjs wrld)))))

(defun fn-dl-readonly-check (name stobjs term state)
  (declare (xargs :mode :program :stobjs state))
  (if (null stobjs) (value nil)
    (er-let* ((translated (translate term t t t 'def-loop (w state) state)))
      (if (fn-dl-updaterp translated stobjs (w state))
          (er soft 'def-loop "~x0: :stobjs is read-only; a term returns a declared stobj." name)
        (value nil)))))

; -----------------------------------------------------------------------------
; :step and :fold plumbing.  The recursion's state is the list SVARS of the
; formals it changes.  One formal is the library's state itself; several are
; a tuple `(list v1 v2 ..)' that an instance's lambdas take apart with
; CAR/CDR.  PSUBST is simultaneous, so a tuple's advance may mention every
; old component.

(defun fn-dl-psubst (alist body)
  (declare (xargs :mode :program))
  (cond ((symbolp body) (let ((hit (assoc-eq body alist))) (if hit (cdr hit) body)))
        ((atom body) body)
        ((eq (car body) 'quote) body)
        (t (cons (fn-dl-psubst alist (car body)) (fn-dl-psubst alist (cdr body))))))

(defun fn-dl-sp-binds (parts)
  (declare (xargs :mode :program))
  (if (endp parts) nil (cons (list (car (car parts)) (cdr (car parts)))
                             (fn-dl-sp-binds (cdr parts)))))

(defun fn-dl-sp-rest (i)
  (declare (xargs :mode :program))
  (if (zp i) 'dl-s `(cdr ,(fn-dl-sp-rest (- i 1)))))

; ((v1 . (car dl-s)) (v2 . (car (cdr dl-s))) ..) for the tuple variable dl-s.
(defun fn-dl-sp-parts (svars i)
  (declare (xargs :mode :program))
  (if (endp svars) nil
    (cons (cons (car svars) `(car ,(fn-dl-sp-rest i)))
          (fn-dl-sp-parts (cdr svars) (+ i 1)))))

; The library's state variable in place of the instance's SVARS, in a call's
; argument list (FORMALS with each state formal replaced).
(defun fn-dl-sp-formals-at (formals svars)
  (declare (xargs :mode :program))
  (if (null (cdr svars))
      (fn-dl-psubst (list (cons (car svars) 'dl-s)) formals)
    (fn-dl-psubst (fn-dl-sp-parts svars 0) formals)))

; (lambda (STATE) TERM) over the state: the lone state formal, or the tuple.
(defun fn-dl-sp-lam (svars term)
  (declare (xargs :mode :program))
  (if (null (cdr svars))
      `(lambda (,(car svars)) ,term)
    `(lambda (dl-s)
       ((lambda ,svars (declare (ignorable ,@svars)) ,term)
        ,@(strip-cdrs (fn-dl-sp-parts svars 0))))))

; TERM under LET's sequential bindings, written out (the lemma statements
; use this so that a stored rewrite rule has no lambda in it).
(defun fn-dl-let-out (bindings term)
  (declare (xargs :mode :program))
  (if (endp bindings) term
    (let ((b (car (last bindings))))
      (fn-dl-let-out (butlast bindings 1)
                     (fn-dl-psubst (list (cons (car b) (cadr b))) term)))))

(defun fn-dl-proof-let (bindings body)
  (declare (xargs :mode :program))
  (if bindings
      `(let* ,bindings (declare (ignorable ,@(strip-cars bindings))) ,body)
    body))

; the terms of a list-valued option, one per state formal
(defun fn-dl-sp-terms (svars x)
  (declare (xargs :mode :program))
  (if (null (cdr svars)) (list x) x))

(defun fn-dl-sp-tuple (svars terms)
  (declare (xargs :mode :program))
  (if (null (cdr svars)) (car terms) `(list ,@terms)))

; FORMALS with each state formal replaced by the matching term of TERMS.
(defun fn-dl-sp-call-args (formals svars terms)
  (declare (xargs :mode :program))
  (fn-dl-psubst (pairlis$ svars terms) formals))

;  The lemma instances that put the progress facts at the library's state.
(defun fn-dl-sp-uses (lemmas svars)
  (declare (xargs :mode :program))
  (if (endp lemmas) nil
    (cons `(:instance ,(car lemmas) :extra-bindings-ok
                      ,@(if (null (cdr svars))
                            (list (list (car svars) 'dl-ps))
                          (fn-dl-sp-binds (fn-dl-psubst '((dl-s . dl-ps)) (fn-dl-sp-parts svars 0)))))
          (fn-dl-sp-uses (cdr lemmas) svars))))

; (lambda (STATE dl-acc) (LOOP formals dl-acc)): the loop over the state.
(defun fn-dl-sp-loop-lam (svars loop formals)
  (declare (xargs :mode :program))
  (if (null (cdr svars))
      `(lambda (,(car svars) dl-acc) (,loop ,@formals dl-acc))
    `(lambda (dl-s dl-acc)
       ((lambda ,svars (declare (ignorable ,@svars)) (,loop ,@formals dl-acc))
        ,@(strip-cdrs (fn-dl-sp-parts svars 0))))))

; -----------------------------------------------------------------------------
; The :step events.

(defun fn-dl-step-events (name formals svars done emit skip body elt next skip-next tail let
                               guard guard-hints guard-theory acc loop measure progress-hints)
  (declare (xargs :mode :program))
  (let* ((s1 (car svars))
         (done (fn-dl-elt elt s1 done))
         (emit (fn-dl-elt elt s1 emit))
         (skip (fn-dl-elt elt s1 skip))
         (body (fn-dl-elt elt s1 body))
         (tail (fn-dl-elt elt s1 tail))
         (let (fn-dl-elt elt s1 let))
         (next (fn-dl-elt elt s1 (fn-dl-sp-terms svars next)))
         (skip-next (fn-dl-elt elt s1 (fn-dl-sp-terms svars skip-next)))
         (emit-test (if skip `(not ,skip) emit))
         (m (or measure `(acl2-count ,s1)))
         (rec-e `(,name ,@(fn-dl-sp-call-args formals svars next)))
         (rec-s `(,name ,@(fn-dl-sp-call-args formals svars skip-next)))
         (loop-e `(,loop ,@(fn-dl-sp-call-args formals svars next) (cons ,body ,acc)))
         (loop-s `(,loop ,@(fn-dl-sp-call-args formals svars skip-next) ,acc))
         (always (and (eq emit t) (not skip)))
         (logic-body `(if ,done ,tail
                          ,(fn-dl-let let (cond (always `(cons ,body ,rec-e))
                                                (skip `(if ,skip ,rec-s (cons ,body ,rec-e)))
                                                (t `(if ,emit (cons ,body ,rec-e) ,rec-s))))))
         (loop-body `(if ,done (revappend ,acc ,tail)
                         ,(fn-dl-let let (cond (always loop-e)
                                               (skip `(if ,skip ,loop-s ,loop-e))
                                               (t `(if ,emit ,loop-e ,loop-s))))))
         (bridge (fn-dl-name (list loop "-IS-REVAPPEND") name))
         (mop (fn-dl-name (list name "-MEASURE-NATP") name))
         (pe (fn-dl-name (list name "-EMIT-PROGRESS") name))
         (ps (fn-dl-name (list name "-SKIP-PROGRESS") name))
         (calls (list `(,loop ,@(fn-dl-sp-formals-at formals svars) dl-acc)
                      `(,name ,@(fn-dl-sp-formals-at formals svars)))))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(fn-dl-and guard `(true-listp ,acc))
                        :verify-guards nil
                        :measure ,m))
        ,loop-body)
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil
                        :measure ,m))
        (mbe :logic ,logic-body
             :exec (,loop ,@formals nil)))
      (local (defthm ,mop (natp ,m) :rule-classes nil
               ,@(and progress-hints `(:hints ,progress-hints))))
      (local
       (defthm ,pe
         (implies (and (not ,(fn-dl-let-out let done)) ,(fn-dl-let-out let emit-test))
                  (< ,(fn-dl-let-out let (fn-dl-psubst (pairlis$ svars next) m))
                     ,(fn-dl-let-out let m)))
         :rule-classes nil
         ,@(and progress-hints `(:hints ,progress-hints))))
      (local
       (defthm ,ps
         (implies (and (not ,(fn-dl-let-out let done)) (not ,(fn-dl-let-out let emit-test)))
                  (< ,(fn-dl-let-out let (fn-dl-psubst (pairlis$ svars skip-next) m))
                     ,(fn-dl-let-out let m)))
         :rule-classes nil
         ,@(and progress-hints `(:hints ,progress-hints))))
      (local
       (defthm ,bridge
         (equal (,loop ,@formals ,acc) (revappend ,acc (,name ,@formals)))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          fn-dl-step-loop-is-revappend
                          (fn-dl-sp-done ,(fn-dl-sp-lam svars done))
                          (fn-dl-sp-emit ,(fn-dl-sp-lam svars (fn-dl-proof-let let emit-test)))
                          (fn-dl-sp-f ,(fn-dl-sp-lam svars (fn-dl-proof-let let body)))
                          (fn-dl-sp-tail ,(fn-dl-sp-lam svars tail))
                          (fn-dl-sp-ne ,(fn-dl-sp-lam svars (fn-dl-proof-let let (fn-dl-sp-tuple svars next))))
                          (fn-dl-sp-ns ,(fn-dl-sp-lam svars (fn-dl-proof-let let (fn-dl-sp-tuple svars skip-next))))
                          (fn-dl-sp-m ,(fn-dl-sp-lam svars m))
                          (fn-dl-step ,(fn-dl-sp-lam svars `(,name ,@formals)))
                          (fn-dl-step-loop ,(fn-dl-sp-loop-lam svars loop formals)))
                         (dl-s ,(fn-dl-sp-tuple svars svars)) (dl-acc ,acc)))
                  :expand ,calls
                  :in-theory (union-theories '(,name ,loop car-cons cdr-cons)
                                             (theory 'minimal-theory)))
                 (if stable-under-simplificationp
                     '(:computed-hint-replacement nil
                       :use ,(fn-dl-sp-uses (list mop pe ps) svars))
                   nil))))
      (verify-guards ,loop ,@(and guard-hints `(:hints ,guard-hints)))
      (verify-guards ,name
        :hints (("Goal"
                 :use ((:instance ,bridge (,acc nil)))
                 :in-theory (union-theories '(revappend ,name ,@guard-theory)
                                            (union-theories (theory 'minimal-theory)
                                                            (executable-counterpart-theory :here))))))
      (in-theory (disable ,loop))
      (table fn-generated ',name '(:def-loop :shape :step :loop ,loop :bridge ,bridge)))))

; -----------------------------------------------------------------------------
; The :fold events.  ST is the formal threaded through every step (a stobj or
; any value); ROW is a term returning (mv ROW-VALUE ST).  Like :step, the
; recursion's state is the list SVARS of the other formals it changes.

; (lambda (STATE ST) (LOOP formals dl-acc)), for the library's three-argument loop.
(defun fn-dl-fo-loop-lam (svars st loop formals)
  (declare (xargs :mode :program))
  (if (null (cdr svars))
      `(lambda (,(car svars) dl-acc ,st) (,loop ,@formals dl-acc))
    `(lambda (dl-s dl-acc ,st)
       ((lambda ,svars (declare (ignorable ,@svars)) (,loop ,@formals dl-acc))
        ,@(strip-cdrs (fn-dl-sp-parts svars 0))))))

; (lambda (STATE ST) TERM): the library's two-argument form of a lambda.
(defun fn-dl-fo-lam (svars st term)
  (declare (xargs :mode :program))
  (if (null (cdr svars))
      `(lambda (,(car svars) ,st) ,term)
    `(lambda (dl-s ,st)
       ((lambda ,svars (declare (ignorable ,@svars)) ,term)
        ,@(strip-cdrs (fn-dl-sp-parts svars 0))))))

(defun fn-dl-fold-events (name formals svars st stobjp done row elt next fail let
                               guard guard-hints guard-theory acc loop measure progress-hints)
  (declare (xargs :mode :program))
  (let* ((s1 (car svars))
         (done (fn-dl-elt elt s1 done))
         (row (fn-dl-elt elt s1 row))
         (let (fn-dl-elt elt s1 let))
         (next (fn-dl-elt elt s1 (fn-dl-sp-terms svars next)))
         (m (or measure `(acl2-count ,s1)))
         (rec-call `(,name ,@(fn-dl-sp-call-args formals svars next)))
         (loop-call `(,loop ,@(fn-dl-sp-call-args formals svars next) (cons dl-row ,acc)))
         (bridge (fn-dl-name (list loop "-IS-REVAPPEND") name))
         (mop (fn-dl-name (list name "-MEASURE-NATP") name))
         (pe (fn-dl-name (list name "-PROGRESS") name))
         (at (fn-dl-psubst (list (cons st 'dl-st)) (fn-dl-sp-formals-at formals svars)))
         (calls (list `(,loop ,@at dl-acc) `(,name ,@at))))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(fn-dl-and guard `(true-listp ,acc))
                        :verify-guards nil :measure ,m
                        ,@(and stobjp `(:stobjs ,st))))
        (if ,done
            (mv (revappend ,acc nil) ,st)
          ,(fn-dl-let let
             `(mv-let (dl-row ,st) ,row
                (if (eq dl-row ,fail)
                    (mv ,fail ,st)
                  ,loop-call)))))
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil :measure ,m
                        ,@(and stobjp `(:stobjs ,st))))
        (mbe :logic (if ,done
                        (mv nil ,st)
                      ,(fn-dl-let let
                         `(mv-let (dl-row ,st) ,row
                            (if (eq dl-row ,fail)
                                (mv ,fail ,st)
                              (mv-let (dl-rest ,st) ,rec-call
                                (if (eq dl-rest ,fail)
                                    (mv ,fail ,st)
                                  (mv (cons dl-row dl-rest) ,st)))))))
             :exec (,loop ,@formals nil)))
      (local (defthm ,mop (natp ,m) :rule-classes nil
               ,@(and progress-hints `(:hints ,progress-hints))))
      (local
       (defthm ,pe
         (implies (not ,done)
                  (< ,(fn-dl-psubst (pairlis$ svars next) m) ,m))
         :rule-classes nil
         ,@(and progress-hints `(:hints ,progress-hints))))
      (local
       (defthm ,bridge
         (equal (,loop ,@formals ,acc)
                (mv-let (r a) (,name ,@formals)
                  (mv (if (eq r ,fail) ,fail (revappend ,acc r)) a)))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          fn-dl-fold-loop-is-revappend
                          (fn-dl-fo-done ,(fn-dl-sp-lam svars done))
                          (fn-dl-fo-step ,(fn-dl-fo-lam svars st (fn-dl-proof-let let row)))
                          (fn-dl-fo-next ,(fn-dl-sp-lam svars (fn-dl-proof-let let (fn-dl-sp-tuple svars next))))
                          (fn-dl-fo-m ,(fn-dl-sp-lam svars m))
                          (fn-dl-fo-fail (lambda () ,fail))
                          (fn-dl-fold ,(fn-dl-fo-lam svars st `(,name ,@formals)))
                          (fn-dl-fold-loop ,(fn-dl-fo-loop-lam svars st loop formals)))
                         (dl-s ,(fn-dl-sp-tuple svars svars)) (dl-acc ,acc) (dl-st ,st)))
                  :expand ,calls
                  :in-theory (union-theories '(,name ,loop car-cons cdr-cons)
                                             (theory 'minimal-theory)))
                 (if stable-under-simplificationp
                     '(:computed-hint-replacement nil
                       :use ,(fn-dl-sp-uses (list mop pe) svars))
                   nil))))
      (verify-guards ,loop ,@(and guard-hints `(:hints ,guard-hints)))
      (verify-guards ,name
        :hints (("Goal"
                 :use ((:instance ,bridge (,acc nil)))
                 :expand ((,name ,@formals))
                 :in-theory (union-theories '(revappend mv-nth car-cons cdr-cons ,@guard-theory)
                                            (union-theories (theory 'minimal-theory)
                                                            (executable-counterpart-theory :here))))))
      (in-theory (disable ,loop))
      (table fn-generated ',name '(:def-loop :shape :fold :loop ,loop :bridge ,bridge)))))


; -----------------------------------------------------------------------------
; The :foldr events.  COMBINE is a term over ELT (the element) and ACC (the
; fold of the rest in the recursion, the running value in the loop); INIT is
; the value at the empty list.  REV reverses the list (default `revappend';
; another function must agree with it, which the expansion proves).

(defun fn-dl-foldr-events (name formals xs elt combine init rev guard guard-hints guard-theory
                                acc loop loop-guard measure)
  (declare (xargs :mode :program))
  (let* ((e elt)
         (next (fn-dl-replace formals xs `(cdr ,xs)))
         (rev-call `(,rev ,xs nil))
         (rev-xs (fn-dl-replace formals xs rev-call))
         (m (or measure `(acl2-count ,xs)))
         (bridge (fn-dl-name (list loop "-IS-" name) name))
         (rev-lemma (fn-dl-name (list name "-REV-IS-REVAPPEND") name))
         (rev-ok (eq rev 'revappend)))
    `(,@(and (not rev-ok)
             `((local (defthm ,rev-lemma (equal (,rev dl-a dl-b) (revappend dl-a dl-b))
                        :hints (("Goal" :induct (,rev dl-a dl-b)
                                 :in-theory (union-theories '(,rev revappend)
                                                            (theory 'minimal-theory))))))))
      (defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,loop-guard :verify-guards nil :measure ,m)
                 (ignorable ,@(remove1-eq xs formals)))
        (if (consp ,xs)
            (,loop ,@next ,(fn-dl-psubst (list (cons e `(car ,xs))) combine))
          ,acc))
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil :measure ,m))
        (mbe :logic (if (consp ,xs)
                        ,(fn-dl-psubst (list (cons e `(car ,xs)) (cons acc `(,name ,@next))) combine)
                      ,init)
             :exec (,loop ,@rev-xs ,init)))
      (local
       (defthm ,bridge
         (equal (,loop ,@rev-xs ,init) (,name ,@formals))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          fn-dl-foldr-loop-is-foldr
                          (fn-dl-fr-f (lambda (,e ,acc) ,combine))
                          (fn-dl-fr-z (lambda () ,init))
                          (fn-dl-foldr (lambda (,xs) (,name ,@formals)))
                          (fn-dl-foldr-loop (lambda (,xs ,acc) (,loop ,@formals ,acc))))
                         (dl-xs ,xs)))
                  :expand ((,name ,@formals))
                  :in-theory (union-theories '(,name ,loop ,@(and (not rev-ok) (list rev-lemma)))
                                             (theory 'minimal-theory))))))
      (verify-guards ,loop ,@(and guard-hints `(:hints ,guard-hints)))
      (verify-guards ,name
        :hints (("Goal"
                 :use (,bridge)
                 :in-theory (union-theories '(,name revappend ,@(and (not rev-ok) (list rev-lemma))
                                                    ,@guard-theory)
                                            (union-theories (theory 'minimal-theory)
                                                            (executable-counterpart-theory :here))))))
      (in-theory (disable ,loop))
      (table fn-generated ',name '(:def-loop :shape :foldr :loop ,loop :bridge ,bridge)))))

; -----------------------------------------------------------------------------
; The generated events.

(defun fn-dl-map-events (name formals xs elt body while stop stop-value keep tail
                              let guard guard-hints guard-theory acc loop measure keep-order loop-guard acc-fix stobjs base)
  (declare (xargs :mode :program))
  (let* ((fixed (if acc-fix `(true-list-fix ,acc) acc))
         (body (fn-dl-elt elt xs body))
         (while (fn-dl-elt elt xs while))
         (base (fn-dl-elt elt xs base))
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
          (if base
              `(if ,base ,tail
                 ,(fn-dl-let let (if stop `(if ,stop ,stop-value ,logic-inner) logic-inner)))
            `(if ,test
                 ,(fn-dl-let let (if stop `(if ,stop ,stop-value ,logic-inner) logic-inner))
               ,tail)))
         (loop-inner (if (eq keep-order :skip-first)
                         `(if ,keep ,loop-skip ,loop-cons)
                       (if (eq keep t)
                         loop-cons
                       `(if ,keep ,loop-cons ,loop-skip))))
         (loop-body
          (if base
              `(if ,base (revappend ,fixed ,tail)
                 ,(fn-dl-let let (if stop
                                     `(if ,stop (revappend ,fixed ,stop-value) ,loop-inner)
                                   loop-inner)))
            `(if ,test
                 ,(fn-dl-let let (if stop
                                     `(if ,stop (revappend ,fixed ,stop-value) ,loop-inner)
                                   loop-inner))
               (revappend ,fixed ,tail)))))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(if (eq loop-guard :default)
                                    (if acc-fix guard (fn-dl-and guard `(true-listp ,acc)))
                                  loop-guard)
                        :verify-guards nil
                        ,@(and stobjs `(:stobjs ,stobjs))
                        ,@(and measure `(:measure ,measure))))
        ,loop-body)
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil
                        ,@(and stobjs `(:stobjs ,stobjs))
                        ,@(and measure `(:measure ,measure))))
        (mbe :logic ,logic-body
             :exec (,loop ,@formals nil)))
      (local
       (defthm ,bridge
         (equal (,loop ,@formals ,acc) (revappend ,fixed (,name ,@formals)))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          ,(cond (base 'fn-dl-map-base-loop-is-revappend)
                                 (acc-fix 'fn-dl-map-fixed-loop-is-revappend)
                                 ((eq keep-order :skip-first) 'fn-dl-map-skip-loop-is-revappend)
                                 (t 'fn-dl-map-loop-is-revappend))
                          ,@(if base
                                `((fn-dl-mb-base (lambda (,xs) ,base))
                                  (fn-dl-mb-fixp (lambda () ,acc-fix)))
                              `((fn-dl-while (lambda (,xs) ,while))))
                          (fn-dl-stop (lambda (,xs) ,(if stop (fn-dl-map-proof-let base let stop) nil)))
                          (fn-dl-stop-value (lambda (,xs) ,(if stop (fn-dl-map-proof-let base let stop-value) nil)))
                          (fn-dl-keep (lambda (,xs)
                                       ,(fn-dl-map-proof-let base let
                                          (if (and (or base acc-fix) (eq keep-order :skip-first))
                                              `(not ,keep) keep))))
                          (fn-dl-f (lambda (,xs) ,(fn-dl-map-proof-let base let body)))
                          (fn-dl-tail (lambda (,xs) ,tail))
                          (,(cond (base 'fn-dl-map-base)
                                  ((and (not acc-fix) (eq keep-order :skip-first)) 'fn-dl-map-skip)
                                  (t 'fn-dl-map)) (lambda (,xs) (,name ,@formals)))
                          (,(cond (base 'fn-dl-map-base-loop)
                                  (acc-fix 'fn-dl-map-fixed-loop)
                                  ((eq keep-order :skip-first) 'fn-dl-map-skip-loop)
                                  (t 'fn-dl-map-loop)) (lambda (,xs ,acc) (,loop ,@formals ,acc))))
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

(defun fn-dl-take-base-events (name formals n xs elt body base tail
                               guard guard-hints guard-theory acc loop measure)
  (declare (xargs :mode :program))
  (let* ((body (fn-dl-elt elt xs body))
         (base (fn-dl-elt elt xs base))
         (tail (fn-dl-elt elt xs tail))
         (next (fn-dl-replace (fn-dl-replace formals xs `(cdr ,xs)) n `(- ,n 1)))
         (bridge (fn-dl-name (list loop "-IS-REVAPPEND") name)))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(fn-dl-and guard `(true-listp ,acc))
                        :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (if ,base
            (revappend ,acc ,tail)
          (,loop ,@next (cons ,body ,acc))))
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (mbe :logic (if ,base ,tail (cons ,body (,name ,@next)))
             :exec (,loop ,@formals nil)))
      (local
       (defthm ,bridge
         (equal (,loop ,@formals ,acc) (revappend ,acc (,name ,@formals)))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          fn-dl-take-base-loop-is-revappend
                          (fn-dl-tb-base (lambda (,n ,xs) ,base))
                          (fn-dl-tk-f (lambda (,n ,xs) ,body))
                          (fn-dl-tk-tail (lambda (,n ,xs) ,tail))
                          (fn-dl-take-base (lambda (,n ,xs) (,name ,@formals)))
                          (fn-dl-take-base-loop (lambda (,n ,xs ,acc) (,loop ,@formals ,acc))))
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

(defun fn-dl-concat-events (name formals xs elt body guard guard-hints guard-theory acc loop measure)
  (declare (xargs :mode :program))
  (let* ((body (if elt (fn-dl-subst elt `(car ,xs) body) body))
         (next (fn-dl-replace formals xs `(cdr ,xs)))
         (bridge (fn-dl-name (list loop "-IS-REVAPPEND") name)))
    `((defun ,loop (,@formals ,acc)
        (declare (xargs :guard ,(fn-dl-and guard `(true-listp ,acc))
                        :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (if (consp ,xs)
            (,loop ,@next (revappend ,body ,acc))
          (revappend ,acc nil)))
      (defun ,name ,formals
        (declare (xargs :guard ,guard :verify-guards nil
                        ,@(and measure `(:measure ,measure))))
        (mbe :logic (if (consp ,xs) (append ,body (,name ,@next)) nil)
             :exec (,loop ,@formals nil)))
      (local
       (defthm ,bridge
         (equal (,loop ,@formals ,acc) (revappend ,acc (,name ,@formals)))
         :hints (("Goal"
                  :use ((:instance
                         (:functional-instance
                          fn-dl-concat-loop-is-revappend
                          (fn-dl-cc-f (lambda (,xs) ,body))
                          (fn-dl-concat (lambda (,xs) (,name ,@formals)))
                          (fn-dl-concat-loop (lambda (,xs ,acc) (,loop ,@formals ,acc))))
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
      (table fn-generated ',name '(:def-loop :shape :concat :loop ,loop :bridge ,bridge)))))

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
                      acc loop keep-order base loop-guard acc-fix stobjs
                      done emit skip next skip-next progress-hints st row fail
                      combine init rev state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((loop (or loop (fn-dl-name (list name "-LOOP") name)))
         (svars (and (member-eq shape '(:step :fold))
                     (cond ((null over) (list (car formals)))
                           ((symbolp over) (list over))
                           (t over))))
         (xs (cond (svars (car svars))
                   (t (or over (if (eq shape :into) (car (remove1-eq into formals)) (car formals))))))
         (n (or count (car formals)))
         (ctx 'def-loop)
         (stobjs (if (and stobjs (symbolp stobjs)) (list stobjs) stobjs)))
    (cond
     ((not (member-eq shape '(:map :take :sum :into :concat :step :fold :foldr)))
      (er soft ctx "~x0: :shape ~x1 is not one of :map, :take, :sum, :into, :concat, :step, :fold, :foldr." name shape))
     ((and (not (member-eq shape '(:step :fold)))
           (or done skip next skip-next progress-hints (not (eq emit t))))
      (er soft ctx "~x0: :done, :emit, :skip, :next, :skip-next and :progress-hints are :step or :fold options." name))
     ((and (not (eq shape :foldr)) (or combine init (not (eq rev 'revappend))))
      (er soft ctx "~x0: :combine, :init and :rev are :foldr options." name))
     ((and (eq shape :foldr) (not (and combine elt)))
      (er soft ctx "~x0: :foldr needs :elt (the element variable) and :combine (a term over it and ~x1, the fold of the rest)." name acc))
     ((and (eq shape :foldr) (or body (not (eq while t)) stop (not (eq keep t)) let (not (eq tail nil))))
      (er soft ctx "~x0: :foldr takes :combine and :init, not :body, :while, :stop, :keep, :let or :tail." name))
     ((and (not (eq shape :fold)) (or st row (not (eq fail :bad))))
      (er soft ctx "~x0: :st, :row and :fail are :fold options." name))
     ((and (eq shape :fold)
           (not (and st (member-eq st formals) (not (member-eq st svars)) row done next)))
      (er soft ctx "~x0: :fold needs :st (a formal not in :over), :row (a term returning (mv value st)), :done and :next." name))
     ((and (eq shape :fold) (or skip skip-next (not (eq emit t)) (not (eq body nil))))
      (er soft ctx "~x0: :fold takes :row, not :body, :emit, :skip or :skip-next." name))
     ((and (eq shape :step)
           (not (and (symbol-listp svars) svars (no-duplicatesp-eq svars)
                     (subsetp-eq svars formals))))
      (er soft ctx "~x0: :over must name distinct formals (the state the recursion changes)." name))
     ((and (eq shape :step) (not (and done next)))
      (er soft ctx "~x0: :step needs :done (the base test) and :next (the advance)." name))
     ((and (eq shape :step) skip (not (eq emit t)))
      (er soft ctx "~x0: :step takes :emit or :skip, not both." name))
     ((and (member-eq shape '(:step :fold)) (cdr svars)
           (not (and (true-listp next) (equal (length next) (length svars))
                     (or (null skip-next)
                         (and (true-listp skip-next) (equal (length skip-next) (length svars)))))))
      (er soft ctx "~x0: with several :over formals, :next and :skip-next are lists of one term each." name))
     ((and (eq shape :step) (and while (not (eq while t))))
      (er soft ctx "~x0: :while is not a :step option; the base test is :done." name))
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
     ((and base (not (member-eq shape '(:map :take))))
      (er soft ctx "~x0: :base is a :map or :take option." name))
     ((and base (not (eq while t)))
      (er soft ctx "~x0: :base and :while are mutually exclusive." name))
     ((and (not (eq loop-guard :default)) (not (member-eq shape '(:map :foldr))))
      (er soft ctx "~x0: :loop-guard is a :map or :foldr option." name))
     ((not (member-eq acc-fix '(nil t)))
      (er soft ctx "~x0: :acc-fix must be t or nil." name))
     ((and acc-fix (not (eq shape :map)))
      (er soft ctx "~x0: :acc-fix is a :map option." name))
     ((and stobjs (not (eq shape :map)))
      (er soft ctx "~x0: :stobjs is a read-only :map option." name))
     ((not (and (symbol-listp stobjs) (no-duplicatesp-eq stobjs)
                (fn-dl-stobjs-knownp stobjs formals (w state))
                (not (member-eq xs stobjs))))
      (er soft ctx "~x0: :stobjs must name distinct stobj formals other than :over." name))
     ((and (null body) (not (member-eq shape '(:fold :foldr))))
      (er soft ctx "~x0: :body is required." name))
     ((and stop (not (eq shape :map)))
      (er soft ctx "~x0: :stop is a :map option; shape ~x1 has none." name shape))
     ((and stop (null stop-value))
      (er soft ctx "~x0: :stop needs :stop-value (the value returned when it holds)." name))
     ((and (not (eq keep t)) (not (eq shape :map)))
      (er soft ctx "~x0: :keep is a :map option; shape ~x1 has none." name shape))
     ((and let (not (member-eq shape '(:map :step :fold))))
      (er soft ctx "~x0: :let is a :map, :step or :fold option; shape ~x1 has none." name shape))
     ((and (not (eq tail nil)) (not (member-eq shape '(:map :take :step))))
      (er soft ctx "~x0: :tail is a :map, :take or :step option; shape ~x1 has none." name shape))
     ((and (not (eq while t)) (not (member-eq shape '(:map :take))))
      (er soft ctx "~x0: :while is a :map or :take option; shape ~x1 has none." name shape))
     ((and (eq shape :into) (not (and into write map (member-eq into formals))))
      (er soft ctx "~x0: :into needs :into (a stobj formal), :write (its append export) and :map (the list-level map)." name))
     (t
      (er-progn
       (fn-dl-readonly-check
        name stobjs
        (fn-dl-elt elt xs
          (fn-dl-let let `(list ,body ,while ,stop ,stop-value ,keep ,tail ,base))) state)
       (value
       `(encapsulate
          ()
          ,@(case shape
              (:map (fn-dl-map-events name formals xs elt body while stop stop-value keep tail
                                      let guard guard-hints guard-theory acc loop measure keep-order loop-guard acc-fix stobjs base))
              (:take (if base
                         (fn-dl-take-base-events name formals n xs elt body base tail
                                                guard guard-hints guard-theory acc loop measure)
                       (fn-dl-take-events name formals n xs elt body while tail
                                          guard guard-hints guard-theory acc loop measure)))
              (:step (fn-dl-step-events name formals svars done emit skip body elt next skip-next
                                        tail let guard guard-hints guard-theory acc loop measure
                                        progress-hints))
              (:foldr (fn-dl-foldr-events name formals xs elt combine init rev guard guard-hints
                                          guard-theory acc loop
                                          (if (eq loop-guard :default) t loop-guard) measure))
              (:fold (fn-dl-fold-events name formals svars st
                                        (and (getpropc st 'stobj nil (w state)) t)
                                        done row elt next fail let guard guard-hints guard-theory
                                        acc loop measure progress-hints))
              (:sum (fn-dl-sum-events name formals xs elt body guard guard-hints guard-theory
                                      acc loop measure))
              (:concat (fn-dl-concat-events name formals xs elt body guard guard-hints
                                           guard-theory acc loop measure))
              (otherwise (fn-dl-into-events name formals xs elt body into write write-theory map
                                            guard guard-hints measure))))))))))

(defmacro def-loop (name formals &key
                         (shape ':map)
                         over count elt body
                         (while 't while-p) stop stop-value (keep 't) (tail 'nil) let
                         (guard 't) guard-hints guard-theory measure
                         into write write-theory map
                         (acc 'acc) loop (keep-order ':cons-first) (base 'nil base-p) (loop-guard ':default) acc-fix stobjs
                         done (emit 't) skip next skip-next progress-hints st row (fail ':bad)
                         combine init (rev 'revappend))
  `(make-event
    (fn-dl-fn ',name ',formals ',shape ',over ',count ',elt ',body
              ',(if (and (eq shape :map) base-p while-p) :explicit-while while) ',stop ',stop-value
              ',keep ',tail ',let ',guard ',guard-hints ',guard-theory ',measure
              ',into ',write ',write-theory ',map ',acc ',loop ',keep-order
              ',(if (and (not (eq shape :take)) base-p (null base)) '(quote nil) base)
              ',loop-guard ',acc-fix ',stobjs
              ',done ',emit ',skip ',next ',skip-next ',progress-hints ',st ',row ',fail
              ',combine ',init ',rev state)))
