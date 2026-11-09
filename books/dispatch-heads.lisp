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

;; ---------------------------------------------------------------------------
;; THE WALK. Below a run attachment RUN of kind KIND: the core-level
;; functions writing the ops child (fn2-bf-ops-faces), callees first; each
;; gets <fn>-HEADS-ADVANCED,
;;   (implies (fn2-env-ops-advanced fn2-dfr-o0 (fn2-core-ops fn2-core))
;;            (fn2-env-ops-advanced fn2-dfr-o0 (fn2-core-ops OUT))),
;; with its body opened once over its callees' lemmas: the ops writers it
;; calls (the same statement of their ops, walked down to the op primitives'
;; lemmas, ops-heads.lisp) and every other core function it calls,
;; <fn>-KEEPS-OPS (its ops child is the input's, from its KIDS contract).
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
(defun fn2-dfr-named (fs suffix wrld)
  ; the proved lemmas <f>SUFFIX of FS
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((getpropc (fn2-bf-name (car fs) suffix) 'theorem nil wrld)
         (cons (fn2-bf-name (car fs) suffix) (fn2-dfr-named (cdr fs) suffix wrld)))
        (t (fn2-dfr-named (cdr fs) suffix wrld))))
(defun fn2-dfr-update-runes (lemmas)
  ; the core's accessor-of-updater rules for the ops child
  (declare (xargs :mode :program))
  (cond ((atom lemmas) nil)
        ((let ((lhs (access rewrite-rule (car lemmas) :lhs)))
           (and (consp (fargn lhs 1)) (symbolp (ffn-symb (fargn lhs 1)))
                (let ((n (symbol-name (ffn-symb (fargn lhs 1)))))
                  (and (< 16 (length n)) (equal (subseq n 0 16) "UPDATE-FN2-CORE-")))))
         (cons (access rewrite-rule (car lemmas) :rune) (fn2-dfr-update-runes (cdr lemmas))))
        (t (fn2-dfr-update-runes (cdr lemmas)))))
(defun fn2-dfr-advanced-form (f stobj acc wrld)
  ; F's lemma: its STOBJ output (the ops child, read by ACC) advances the heads
  (declare (xargs :mode :program))
  (let* ((call (cons f (formals f wrld))) (outs (getpropc f 'stobjs-out nil wrld))
         (in (fn2-dfr-stobj-formal f stobj wrld)) (out (fn2-bf-out call outs stobj))
         (callees (fn2-dfr-callees-of (list f) wrld))
         (induct (getpropc f 'recursivep nil wrld)))
    `(defthm ,(fn2-bf-name f "-HEADS-ADVANCED")
       (implies (fn2-env-ops-advanced fn2-dfr-o0 ,(if acc `(,acc ,in) in))
                (fn2-env-ops-advanced fn2-dfr-o0 ,(if acc `(,acc ,out) out)))
       :hints (("Goal" ,@(if induct `(:induct ,call) `(:expand (,call)))
                :in-theory (union-theories '(mv-nth car-cons cdr-cons ,@(and induct (list f))
                                             ,@(fn2-dfr-named callees "-HEADS-ADVANCED" wrld)
                                             ,@(fn2-dfr-named callees "-KEEPS-OPS" wrld)
                                             ,@(fn2-dfr-update-runes (getpropc 'fn2-core-ops 'lemmas nil wrld)))
                                           (theory 'fn2-dfr-walk-base)))))))
(defun fn2-dfr-keeps-ops-form (g kind wrld)
  ; G (a core function writing no ops) leaves the ops child: its KIDS contract
  (declare (xargs :mode :program))
  (let* ((d (fn2-dc-entry g kind wrld)) (k (fn2-arm-frame-child-index 'fn2-core-ops wrld))
         (call (cons g (formals g wrld))) (out (fn2-bf-out call (getpropc g 'stobjs-out nil wrld) 'fn2-core))
         (in (fn2-dfr-stobj-formal g 'fn2-core wrld)))
    (if (or (null d) (member-equal k (car d)))
        `(make-event (er soft 'fn2-dfr-walk "~x0 (under ~x1) has no KIDS contract leaving the ops child." ',g ',kind))
      `(defthm ,(fn2-bf-name g "-KEEPS-OPS")
         (equal (fn2-core-ops ,out) (fn2-core-ops ,in))
         :hints (("Goal" :in-theory (union-theories '(fn2-core-ops) (theory 'fn2-arm-frame-base))
                  :do-not-induct t
                  :use ((:instance ,(cdr d) (fn2-arm-free ',(car d)) (fn2-arm-c0 ,in))
                        (:instance fn2-arm-kids-refl (i 0) (free ',(car d)) (a ,in))
                        (:instance fn2-arm-kids-nth (i 0) (k ,k) (free ',(car d)) (a ,in) (b ,out)))))))))
(defun fn2-dfr-unproved (fs suffix wrld)
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((getpropc (fn2-bf-name (car fs) suffix) 'theorem nil wrld) (fn2-dfr-unproved (cdr fs) suffix wrld))
        (t (cons (car fs) (fn2-dfr-unproved (cdr fs) suffix wrld)))))
(defun fn2-dfr-forms-each (fs stobj acc)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (cons `(make-event (fn2-dfr-advanced-form ',(car fs) ',stobj ',acc (w state)))
          (fn2-dfr-forms-each (cdr fs) stobj acc))))
(defun fn2-dfr-keeps-each (fs kind)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (cons `(make-event (fn2-dfr-keeps-ops-form ',(car fs) ',kind (w state)))
          (fn2-dfr-keeps-each (cdr fs) kind))))
(defun fn2-dfr-walk-forms (run kind wrld)
  ; RUN's walk under KIND: the ops children, the non-ops core callees' frames,
  ; the ops-writing core functions, callees first; the proved ones are leaves
  (declare (xargs :mode :program))
  (let* ((core-fns (fn2-bf-core-closure (list run) wrld nil 100000))
         (core-fns (fn2-walk-topo core-fns core-fns "-HEADS-ADVANCED" nil nil wrld 100000))
         (ops-set (fn2-bf-ops-faces core-fns wrld nil))
         (ops-fns (intersection-eq core-fns ops-set))
         (ow (fn2-dfr-writers (fn2-dfr-callees-of ops-fns wrld) 'fn2-ops wrld))
         (ow-all (fn2-dfr-writers (fn2-dfr-closure ow wrld nil 100000) 'fn2-ops wrld))
         (ow-order (fn2-walk-topo ow ow-all "-HEADS-ADVANCED" nil nil wrld 100000))
         (keeps (set-difference-eq (intersection-eq (fn2-dfr-callees-of ops-fns wrld) core-fns) ops-fns)))
    (append (fn2-dfr-forms-each (fn2-dfr-unproved ow-order "-HEADS-ADVANCED" wrld) 'fn2-ops nil)
            (fn2-dfr-keeps-each (fn2-dfr-unproved keeps "-KEEPS-OPS" wrld) kind)
            (fn2-dfr-forms-each (fn2-dfr-unproved ops-fns "-HEADS-ADVANCED" wrld) 'fn2-core 'fn2-core-ops))))
;; A run attachment's claims: the op heads advance (by its chain when it
;; writes ops, else by its KIDS contract) and, where its kind's frame leaves
;; commit-io, the IO units are kept.
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
            ,@(and (fn2-dispatch-run-units-p kind wrld)
                   (list (if (null d) `(make-event (er soft 'fn2-dfr-walk "~x0 has no KIDS contract." ',run))
                           (fn2-dispatch-units-claim (fn2-bf-name run "-KEEPS-UNITS") out out (cdr d) (car d) nil wrld)))))))
