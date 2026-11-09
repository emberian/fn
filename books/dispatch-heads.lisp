; THE RUN STUBS' HEADS. FN2-DFR-HEADS-ADVANCE A B: every incarnation of an op
; slot that has begun and been issued in A (FN2-ENV-INCARNATION-OK) still
; has in B. Every run stub keeps it (machines.lisp fn2-dispatch-heads-claim),
; and each run attachment is proved to by its chain (FN2-DFR-WALK-FORMS,
; assembly-dispatch.lisp): every core-level function under the run that
; writes the ops child advances the op heads (FN2-ENV-OPS-ADVANCED,
; ops-heads.lisp) from any start they advanced from, from its callees' --
; the ops children it calls (the issues, down to the op primitives) and the
; core functions, each other one leaving the ops child (its KIDS contract).
; FRESHNESS and LENT-OK read the op heads only through incarnations
; (books/dispatch-fresh.lisp).
(in-package "ACL2")
(include-book "assembly-core")
(include-book "ops-heads")
(include-book "core-walk")

(defun fn2-env-op (s fn2-core)
  ; (VALID GEN PHASE KIND OKIND OSLOT OGEN RSLOT RGEN ROFF RLEN OFFSET FUA C0P C0H C0E C0O C0C MAYREL C1P)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (r)
    (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
        (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops) (fn2-ops-kind s fn2-ops)
              (fn2-ops-owner-kind s fn2-ops) (fn2-ops-owner-slot s fn2-ops) (fn2-ops-owner-gen s fn2-ops)
              (fn2-ops-range-slot s fn2-ops) (fn2-ops-range-gen s fn2-ops)
              (fn2-ops-range-off s fn2-ops) (fn2-ops-range-len s fn2-ops)
              (fn2-ops-storage-offset s fn2-ops) (fn2-ops-fua s fn2-ops)
              (fn2-ops-c0-posted s fn2-ops) (fn2-ops-c0-harvested s fn2-ops) (fn2-ops-c0-event s fn2-ops)
              (fn2-ops-c0-outcome s fn2-ops) (fn2-ops-c0-count s fn2-ops)
              (fn2-ops-may-release s fn2-ops) (fn2-ops-c1-posted s fn2-ops))
      (list nil))
    r))
(defun fn2-env-incarnation-ok (s g fn2-core)
  ; (S G) names an incarnation of op slot S that has begun and been issued
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((op (fn2-env-op s fn2-core)))
    (and (nth 0 op) (natp g) (<= g (nfix (nth 1 op)))
         (implies (equal g (nth 1 op))
                  (not (member-equal (nth 2 op) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))))
(in-theory (disable fn2-env-incarnation-ok))

(defun-sk fn2-dfr-heads-advance (a b)
  (forall (s g) (implies (fn2-env-incarnation-ok s g a) (fn2-env-incarnation-ok s g b))))
(in-theory (disable fn2-dfr-heads-advance))
(defthm fn2-dfr-heads-advance-trans
  (implies (and (fn2-dfr-heads-advance a b) (fn2-dfr-heads-advance b c)) (fn2-dfr-heads-advance a c))
  :hints (("Goal" :in-theory '(fn2-dfr-heads-advance)
           :use ((:instance fn2-dfr-heads-advance-necc (s (mv-nth 0 (fn2-dfr-heads-advance-witness a c)))
                            (g (mv-nth 1 (fn2-dfr-heads-advance-witness a c))))
                 (:instance fn2-dfr-heads-advance-necc (a b) (b c) (s (mv-nth 0 (fn2-dfr-heads-advance-witness a c)))
                            (g (mv-nth 1 (fn2-dfr-heads-advance-witness a c))))))))
(defthm fn2-dfr-incarnation-ok-of-advance
  (implies (and (fn2-env-incarnation-ok s g a) (fn2-dfr-heads-advance a b)) (fn2-env-incarnation-ok s g b))
  :hints (("Goal" :in-theory nil :use ((:instance fn2-dfr-heads-advance-necc)))))

;; The op heads advancing advance the incarnations: an incarnation reads op
;; S's validity, generation and phase, its head.
(defthm fn2-dfr-op-head
  (and (equal (nth 0 (fn2-env-op s c)) (nth 0 (fn2-env-ops-head s (fn2-core-ops c))))
       (equal (nth 1 (fn2-env-op s c)) (nth 1 (fn2-env-ops-head s (fn2-core-ops c))))
       (equal (nth 2 (fn2-env-op s c)) (nth 2 (fn2-env-ops-head s (fn2-core-ops c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-op fn2-env-ops-head) (fn2-ops-gen fn2-ops-phase fn2-ops-rows)))))
(defthm fn2-dfr-incarnation-ok-of-ops-advanced
  (implies (and (fn2-env-incarnation-ok s g a) (fn2-env-ops-advanced (fn2-core-ops a) (fn2-core-ops b)))
           (fn2-env-incarnation-ok s g b))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-incarnation-ok fn2-env-head-advanced)
                                  (fn2-env-op fn2-env-ops-head fn2-env-ops-advanced))
           :use ((:instance fn2-env-ops-advanced-necc (a (fn2-core-ops a)) (b (fn2-core-ops b)))
                 (:instance fn2-dfr-op-head (c a)) (:instance fn2-dfr-op-head (c b))))))
(defthm fn2-dfr-heads-advance-of-ops-advanced
  (implies (fn2-env-ops-advanced (fn2-core-ops a) (fn2-core-ops b)) (fn2-dfr-heads-advance a b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-dfr-heads-advance)
           :use ((:instance fn2-dfr-incarnation-ok-of-ops-advanced
                            (s (mv-nth 0 (fn2-dfr-heads-advance-witness a b)))
                            (g (mv-nth 1 (fn2-dfr-heads-advance-witness a b))))))))
(defthm fn2-dfr-heads-advance-of-ops-equal
  (implies (equal (fn2-core-ops b) (fn2-core-ops a)) (fn2-dfr-heads-advance a b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-ops-advanced-refl)
           :use ((:instance fn2-dfr-heads-advance-of-ops-advanced)))))

;; THE LOANS. FN2-DFR-LOANS-KEPT A B (commit-io tables): every unit's
;; validity, operation and loan flag stay -- all LENT-OK reads of a unit. The
;; batch kinds' runs (txn, cns, auth) write commit-io's extents, epochs,
;; counters, readiness and pool rows, never those: each run stub of a kind
;; whose frame holds the commit-io child keeps them (-KEEPS-LOANS). Every
;; commit-io setter of another column keeps them (-LOANS-KEPT, the walk's
;; leaves).
(defun fn2-dfr-io-loan (u fn2-commit-io)
  (declare (xargs :stobjs fn2-commit-io :verify-guards nil))
  (if (and (natp u) (< u (fn2-commit-io-rows fn2-commit-io)))
      (list t (fn2-commit-io-op-slot u fn2-commit-io) (fn2-commit-io-op-gen u fn2-commit-io)
            (fn2-commit-io-lent u fn2-commit-io))
    (list nil)))
(defun-sk fn2-dfr-loans-kept (a b)
  (forall u (equal (fn2-dfr-io-loan u b) (fn2-dfr-io-loan u a))))
(in-theory (disable fn2-dfr-loans-kept))
(defthm fn2-dfr-loans-kept-refl (fn2-dfr-loans-kept a a)
  :hints (("Goal" :in-theory '(fn2-dfr-loans-kept))))
(defthm fn2-dfr-loans-kept-trans
  (implies (and (fn2-dfr-loans-kept a b) (fn2-dfr-loans-kept b c)) (fn2-dfr-loans-kept a c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-dfr-loans-kept)
           :use ((:instance fn2-dfr-loans-kept-necc (u (fn2-dfr-loans-kept-witness a c)))
                 (:instance fn2-dfr-loans-kept-necc (a b) (b c) (u (fn2-dfr-loans-kept-witness a c)))))))
(defun fn2-dfr-setter-loan-events (cols)
  (declare (xargs :mode :program))
  (if (atom cols) nil
    (let* ((set (fn2-columns-sym 'fn2-commit-io-set (concatenate 'string "-" (symbol-name (car cols)))))
           (raw (fn2-columns-pre "UPDATE-" (fn2-columns-sym (fn2-columns-sym 'fn2-commit-io (concatenate 'string "-" (symbol-name (car cols)))) "$AI")))
           (call `(,set i v fn2-commit-io)))
      (list* `(defthm ,(fn2-columns-sym set "-LOAN")
                (equal (fn2-dfr-io-loan u ,call) (fn2-dfr-io-loan u fn2-commit-io))
                :hints (("Goal" :in-theory '(,set ,raw fn2-dfr-io-loan fn2-commit-io-rows fn2-commit-io-op-slot
                                             fn2-commit-io-op-gen fn2-commit-io-lent fn2-commit-io-op-slot$ai
                                             fn2-commit-io-op-gen$ai fn2-commit-io-lent$ai update-nth-array
                                             nth-update-nth (:e nfix) (:e equal) (:e natp) (:e <) (:e not)))))
             `(defthm ,(fn2-columns-sym set "-LOANS-KEPT")
                (implies (fn2-dfr-loans-kept fn2-dfr-o0 fn2-commit-io) (fn2-dfr-loans-kept fn2-dfr-o0 ,call))
                :hints (("Goal" :in-theory '(,(fn2-columns-sym set "-LOAN"))
                         :use ((:instance fn2-dfr-loans-kept-trans (a fn2-dfr-o0) (b fn2-commit-io) (c ,call))
                               (:instance fn2-dfr-loans-kept (a fn2-commit-io) (b ,call))))))
             (fn2-dfr-setter-loan-events (cdr cols))))))
(make-event (value (cons 'progn (fn2-dfr-setter-loan-events '(extent epoch counter pool-slot pool-gen ready)))))

;; ---------------------------------------------------------------------------
;; THE WALK, for a relation on a core child: the ops child's FN2-ENV-OPS-ADVANCED
;; (lemmas -HEADS-ADVANCED, frames -KEEPS-OPS) and commit-io's
;; FN2-DFR-LOANS-KEPT (-LOANS-KEPT, -KEEPS-IO), each a relation R with
;; (R a a) and (R a b), (R b c) give (R a c). Below a run attachment RUN of
;; kind KIND: the core-level functions writing the child, callees first; each
;; gets <fn><SUFFIX>,
;;   (implies (R fn2-dfr-o0 (ACC fn2-core)) (R fn2-dfr-o0 (ACC OUT))),
;; with its body opened once over its callees' lemmas: the child writers it
;; calls (the same statement of the child, walked down to the leaves proved
;; before: the op primitives, ops-heads.lisp; the commit-io setters, above)
;; and every other core function it calls, <fn><KEEP> (its child is the
;; input's, from its KIDS contract).
;; (REL STOBJ ACC UPDATER SUFFIX KEEP)
(defconst *fn2-dfr-ops-walk*
  '(fn2-env-ops-advanced fn2-ops fn2-core-ops update-fn2-core-ops "-HEADS-ADVANCED" "-KEEPS-OPS"))
(defconst *fn2-dfr-loans-walk*
  '(fn2-dfr-loans-kept fn2-commit-io fn2-core-commit-io update-fn2-core-commit-io "-LOANS-KEPT" "-KEEPS-IO"))
(deftheory fn2-dfr-walk-base (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))
(defun fn2-dfr-closure (todo wrld acc fuel)
  ; every function TODO reaches
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((zp fuel) acc)
        ((atom todo) acc)
        ((member-eq (car todo) acc) (fn2-dfr-closure (cdr todo) wrld acc (- fuel 1)))
        (t (let ((body (getpropc (car todo) 'unnormalized-body nil wrld)))
             (fn2-dfr-closure (append (and (pseudo-termp body) (remove-eq (car todo) (all-fnnames body))) (cdr todo))
                              wrld (cons (car todo) acc) (- fuel 1))))))
(defun fn2-dfr-stobj-formal (f stobj wrld)
  (declare (xargs :verify-guards nil))
  (nth (position-eq stobj (getpropc f 'stobjs-in nil wrld)) (formals f wrld)))
(defun fn2-dfr-writers (fs stobj wrld)
  ; FS's functions returning STOBJ, not its own accessors
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((and (true-listp (getpropc (car fs) 'stobjs-out nil wrld))
              (member-eq stobj (getpropc (car fs) 'stobjs-out nil wrld))
              (not (getpropc (car fs) 'stobj-function nil wrld))
              (getpropc (car fs) 'unnormalized-body nil wrld))
         (cons (car fs) (fn2-dfr-writers (cdr fs) stobj wrld)))
        (t (fn2-dfr-writers (cdr fs) stobj wrld))))
(defun fn2-dfr-callees-of (fs wrld)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (union-eq (let ((body (getpropc (car fs) 'unnormalized-body nil wrld)))
                (and (pseudo-termp body) (remove-eq (car fs) (all-fnnames body))))
              (fn2-dfr-callees-of (cdr fs) wrld))))
(defun fn2-dfr-child-faces (fs upd suffix wrld acc)
  ; the functions of FS (callees first) calling UPD, or one before them, or
  ; whose lemma (a writer's, SUFFIX) is proved
  (declare (xargs :verify-guards nil))
  (if (atom fs) acc
    (fn2-dfr-child-faces
     (cdr fs) upd suffix wrld
     (let ((body (getpropc (car fs) 'unnormalized-body nil wrld)))
       (if (or (getpropc (fn2-bf-name (car fs) suffix) 'theorem nil wrld)
               (and (pseudo-termp body) (intersectp-eq (cons upd acc) (all-fnnames body))))
           (cons (car fs) acc)
         acc)))))
(defun fn2-dfr-named (fs suffix wrld)
  ; the proved lemmas <f>SUFFIX of FS
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((getpropc (fn2-bf-name (car fs) suffix) 'theorem nil wrld)
         (cons (fn2-bf-name (car fs) suffix) (fn2-dfr-named (cdr fs) suffix wrld)))
        (t (fn2-dfr-named (cdr fs) suffix wrld))))
(defun fn2-dfr-update-runes (lemmas wrld)
  ; the core's accessor-of-updater rules for a child (the updater one of the core's own)
  (declare (xargs :mode :program))
  (cond ((atom lemmas) nil)
        ((let ((lhs (access rewrite-rule (car lemmas) :lhs)))
           (and (consp (fargn lhs 1)) (symbolp (ffn-symb (fargn lhs 1)))
                (eq (getpropc (ffn-symb (fargn lhs 1)) 'stobj-function nil wrld) 'fn2-core)))
         (cons (access rewrite-rule (car lemmas) :rune) (fn2-dfr-update-runes (cdr lemmas) wrld)))
        (t (fn2-dfr-update-runes (cdr lemmas) wrld))))
(defun fn2-dfr-relation-form (f walk core-level wrld)
  ; F's lemma: its child output (read by ACC when CORE-LEVEL) keeps the relation
  (declare (xargs :mode :program))
  (let* ((rel (nth 0 walk)) (stobj (if core-level 'fn2-core (nth 1 walk))) (acc (and core-level (nth 2 walk)))
         (suffix (nth 4 walk)) (keep (nth 5 walk))
         (call (cons f (formals f wrld))) (outs (getpropc f 'stobjs-out nil wrld))
         (in (fn2-dfr-stobj-formal f stobj wrld)) (out (fn2-bf-out call outs stobj))
         (callees (fn2-dfr-callees-of (list f) wrld))
         (induct (getpropc f 'recursivep nil wrld)))
    `(defthm ,(fn2-bf-name f suffix)
       (implies (,rel fn2-dfr-o0 ,(if acc `(,acc ,in) in))
                (,rel fn2-dfr-o0 ,(if acc `(,acc ,out) out)))
       :hints (("Goal" ,@(if induct `(:induct ,call) `(:expand (,call)))
                :in-theory (union-theories '(mv-nth car-cons cdr-cons ,@(and induct (list f))
                                             ,@(fn2-dfr-named callees suffix wrld)
                                             ,@(fn2-dfr-named callees keep wrld)
                                             ,@(fn2-dfr-update-runes (getpropc (nth 2 walk) 'lemmas nil wrld) wrld))
                                           (theory 'fn2-dfr-walk-base)))))))
(defun fn2-dfr-keeps-form (g kind walk wrld)
  ; G (a core function not writing the child) leaves it: its KIDS contract
  (declare (xargs :mode :program))
  (let* ((acc (nth 2 walk)) (d (fn2-dc-entry g kind wrld)) (k (fn2-arm-frame-child-index acc wrld))
         (call (cons g (formals g wrld))) (out (fn2-bf-out call (getpropc g 'stobjs-out nil wrld) 'fn2-core))
         (in (fn2-dfr-stobj-formal g 'fn2-core wrld)))
    (if (or (null d) (member-equal k (car d)))
        `(make-event (er soft 'fn2-dfr-walk "~x0 (under ~x1) has no KIDS contract leaving the ~x2 child." ',g ',kind ',acc))
      `(defthm ,(fn2-bf-name g (nth 5 walk))
         (equal (,acc ,out) (,acc ,in))
         :hints (("Goal" :in-theory (union-theories '(,acc) (theory 'fn2-arm-frame-base))
                  :do-not-induct t
                  :use ((:instance ,(cdr d) (fn2-arm-free ',(car d)) (fn2-arm-c0 ,in))
                        (:instance fn2-arm-kids-refl (i 0) (free ',(car d)) (a ,in))
                        (:instance fn2-arm-kids-nth (i 0) (k ,k) (free ',(car d)) (a ,in) (b ,out)))))))))
(defun fn2-dfr-unproved (fs suffix wrld)
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((getpropc (fn2-bf-name (car fs) suffix) 'theorem nil wrld) (fn2-dfr-unproved (cdr fs) suffix wrld))
        (t (cons (car fs) (fn2-dfr-unproved (cdr fs) suffix wrld)))))
(defun fn2-dfr-forms-each (fs walk core-level)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (cons `(make-event (fn2-dfr-relation-form ',(car fs) ',walk ',core-level (w state)))
          (fn2-dfr-forms-each (cdr fs) walk core-level))))
(defun fn2-dfr-keeps-each (fs kind walk)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (cons `(make-event (fn2-dfr-keeps-form ',(car fs) ',kind ',walk (w state)))
          (fn2-dfr-keeps-each (cdr fs) kind walk))))
(defun fn2-dfr-walk-of (run kind walk wrld)
  ; RUN's walk of WALK under KIND: the child writers, the other core callees'
  ; frames, the child-writing core functions, callees first; proved ones are leaves
  (declare (xargs :mode :program))
  (let* ((stobj (nth 1 walk)) (suffix (nth 4 walk))
         (core-fns (fn2-bf-core-closure (list run) wrld nil 100000))
         (core-fns (fn2-walk-topo core-fns core-fns suffix nil nil wrld 100000))
         (wfns (intersection-eq core-fns (fn2-dfr-child-faces core-fns (nth 3 walk) suffix wrld nil)))
         (todo (fn2-dfr-unproved wfns suffix wrld))
         (ow (fn2-dfr-writers (fn2-dfr-callees-of todo wrld) stobj wrld))
         (ow-all (fn2-dfr-writers (fn2-dfr-closure ow wrld nil 100000) stobj wrld))
         (ow-order (fn2-walk-topo ow ow-all suffix nil nil wrld 100000))
         (keeps (set-difference-eq (intersection-eq (fn2-dfr-callees-of todo wrld) core-fns) wfns)))
    (append (fn2-dfr-forms-each (fn2-dfr-unproved ow-order suffix wrld) walk nil)
            (fn2-dfr-keeps-each (fn2-dfr-unproved keeps (nth 5 walk) wrld) kind walk)
            (fn2-dfr-forms-each todo walk t))))
(defun fn2-dfr-walk-forms (run kind wrld)
  ; the ops walk; and the loans walk where the kind's frame holds commit-io
  (declare (xargs :mode :program))
  (append (fn2-dfr-walk-of run kind *fn2-dfr-ops-walk* wrld)
          (and (not (fn2-dispatch-run-units-p kind wrld))
               (fn2-dfr-walk-of run kind *fn2-dfr-loans-walk* wrld))))
;; A run attachment's claims: the op heads advance (by its chain when it
;; writes ops, else by its KIDS contract); where its kind's frame leaves
;; commit-io, the IO units are kept, else their loans (by its chain).
(defun fn2-dfr-chain-claim (name run walk wrld)
  ; NAME: (REL (ACC fn2-core) (ACC out)) from RUN's walk lemma, else from its KIDS contract
  (declare (xargs :mode :program))
  (let* ((rel (nth 0 walk)) (acc (nth 2 walk)) (out `(mv-nth 4 (,run id budget fn2-core)))
         (lemma (fn2-bf-name run (nth 4 walk))) (keep (fn2-bf-name run (nth 5 walk))))
    `(defthm ,name (,rel (,acc fn2-core) (,acc ,out))
       :hints (("Goal" :in-theory '(,(fn2-columns-sym rel "-REFL"))
                :use ,(if (getpropc lemma 'theorem nil wrld)
                          `((:instance ,lemma (fn2-dfr-o0 (,acc fn2-core))))
                        `((:instance ,keep))))))))
(defun fn2-dfr-run-claims (run kind wrld)
  (declare (xargs :mode :program))
  (let* ((call (list run 'id 'budget 'fn2-core)) (out `(mv-nth 4 ,call))
         (d (fn2-dc-entry run kind wrld))
         (heads (if (getpropc (fn2-bf-name run "-HEADS-ADVANCED") 'theorem nil wrld)
                    `(defthm ,(fn2-bf-name run "-DISPATCH-HEADS") (fn2-dfr-heads-advance fn2-core ,out)
                       :hints (("Goal" :in-theory nil
                                :use ((:instance fn2-dfr-heads-advance-of-ops-advanced (a fn2-core) (b ,out))
                                      (:instance ,(fn2-bf-name run "-HEADS-ADVANCED") (fn2-dfr-o0 (fn2-core-ops fn2-core)))
                                      (:instance fn2-env-ops-advanced-refl (a (fn2-core-ops fn2-core)))))))
                  (if (null d) `(make-event (er soft 'fn2-dfr-walk "~x0 has no KIDS contract." ',run))
                    (fn2-dispatch-heads-claim (fn2-bf-name run "-DISPATCH-HEADS") out out (cdr d) (car d) nil wrld)))))
    `(progn ,heads
            ,(cond ((not (fn2-dispatch-run-units-p kind wrld))
                    (if (or (getpropc (fn2-bf-name run "-LOANS-KEPT") 'theorem nil wrld)
                            (getpropc (fn2-bf-name run "-KEEPS-IO") 'theorem nil wrld))
                        (fn2-dfr-chain-claim (fn2-bf-name run "-KEEPS-LOANS") run *fn2-dfr-loans-walk* wrld)
                      `(make-event (er soft 'fn2-dfr-walk "~x0: no loans chain." ',run))))
                   ((null d) `(make-event (er soft 'fn2-dfr-walk "~x0 has no KIDS contract." ',run)))
                   (t (fn2-dispatch-units-claim (fn2-bf-name run "-KEEPS-UNITS") out out (cdr d) (car d) nil wrld))))))
