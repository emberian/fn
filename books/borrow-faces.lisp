; A2 across every machine-arm face: each core-level function that writes the
; pool child, beyond borrow-conservation.lisp's steps, keeps the borrow count.
; Nothing here is listed by hand: the faces are every fn2-core-returning
; caller of a pool writer in this world, and their children's pool writers
; are walked to the primitives, whose A2 lemmas (borrow-accounting.lisp) are
; rewrite rules. Each writer gets one lemma, callees first; each face gets one
; lemma from its children's.
(in-package "ACL2")
(include-book "borrow-conservation")
(include-book "core-walk")
;; The books defining every face (tests/borrow-conservation-unit.lisp checks
;; that host-boundary's world has no face beyond them).
(include-book "assembly-callbacks")
(include-book "assembly-callbacks-d-conn")
(include-book "assembly-callbacks-d-upload")
(include-book "assembly-callbacks-d-txn")
(include-book "assembly-callbacks-d-cursor")
(include-book "assembly-callbacks-e-auth")
;; The layout recognizer's list fact would open on every true-listp goal.
(local (in-theory (disable fn2-layoutp-list fn2-layoutp-cdr)))

;; ---------------------------------------------------------------------------
;; The world walk.
(defun fn2-bf-writers (stobj wrld acc)
  (declare (xargs :guard (and (symbolp stobj) (plist-worldp wrld) (true-listp acc))))
  (if (endp wrld) acc
    (let ((trip (car wrld)))
      (fn2-bf-writers stobj (cdr wrld)
                      (if (and (eq (cadr trip) 'stobjs-out) (true-listp (cddr trip))
                               (member-eq stobj (cddr trip)) (not (member-eq (car trip) acc)))
                          (cons (car trip) acc)
                        acc)))))
(defthm fn2-bf-all-fnnames-true-listp
  (implies (true-listp acc) (true-listp (all-fnnames1 flg x acc)))
  :hints (("Goal" :in-theory (enable all-fnnames1))))
(defun fn2-bf-core-callers (ws wrld wrld0 acc)
  ;; every fn2-core-returning function whose body calls one of WS
  (declare (xargs :guard (and (symbol-listp ws) (plist-worldp wrld) (plist-worldp wrld0) (true-listp acc))
                  :guard-hints (("Goal" :in-theory (disable all-fnnames1 pseudo-termp)))))
  (if (endp wrld) acc
    (let ((trip (car wrld)))
      (fn2-bf-core-callers
       ws (cdr wrld) wrld0
       (if (and (eq (cadr trip) 'unnormalized-body)
                (not (member-eq (car trip) acc))
                (let ((outs (getpropc (car trip) 'stobjs-out nil wrld0)))
                  (and (true-listp outs) (member-eq 'fn2-core outs)))
                (pseudo-termp (cddr trip))
                (intersectp-eq ws (all-fnnames (cddr trip))))
           (cons (car trip) acc)
         acc)))))
(defun fn2-bf-lemma-name (f) (declare (xargs :verify-guards nil)) (fn2-bf-name f "-BORROWS-ACCOUNTED"))
(defun fn2-bf-provedp (f wrld)
  (declare (xargs :verify-guards nil))
  (getpropc (fn2-bf-lemma-name f) 'theorem nil wrld))
(defun fn2-bf-topo (todo pw done stack wrld fuel)
  ;; post-order over pool-writer callees; a writer with its lemma already
  ;; proved is a leaf (its callees are not walked)
  (declare (xargs :verify-guards nil))
  (fn2-walk-topo todo pw "-BORROWS-ACCOUNTED" done stack wrld fuel))
(defun fn2-bf-children (faces pw wrld)
  (declare (xargs :verify-guards nil))
  (if (atom faces) nil
    (union-eq (fn2-bf-callees (car faces) pw wrld) (fn2-bf-children (cdr faces) pw wrld))))

;; The faces A2 already states (borrow-conservation.lisp), and core init.
(defconst *fn2-bf-stated*
  '(fn2-harvest-one fn2-issue-receive fn2-issue-send fn2-issue-read fn2-issue-write fn2-issue-fence
    fn2-issue-accept fn2-issue-close fn2-issue-cancel fn2-issue-entropy fn2-core-reserve fn2-core-release
    fn2-core-reset fn2-core-write fn2-core-copy-range fn2-core-hand fn2-core-accept-hand
    fn2-core-drop-prefix fn2-core-truncate init-fn2-core-pool fn2-core-borrow-step))
(defun fn2-bf-pool-writers (wrld)
  (declare (xargs :verify-guards nil))
  ;; create-fn2-pool is a local stobj's creation: no writer's input pool flows into it
  (set-difference-eq (fn2-bf-writers 'fn2-pool wrld nil) '(fn2-core-pool create-fn2-pool)))
(defun fn2-bf-faces (wrld)
  (declare (xargs :verify-guards nil))
  (set-difference-eq
   (fn2-bf-core-callers (cons 'update-fn2-core-pool (fn2-bf-pool-writers wrld)) wrld wrld nil)
   *fn2-bf-stated*))

;; Below the faces: every core-level function a face reaches (a face applies
;; them to intermediate cores; fn2-bf-core-closure, core-walk.lisp), callees
;; first. The stobj's own field updaters are not walked; the core's
;; accessor-of-updater rules state them.

;; The issue children's lemma under the walk's name, so the walk stops there
;; (below it, the lease's key writes are argued in borrow-accounting.lisp).
(defthm fn2-issue-children-borrows-accounted
  (implies (and (fn2-opsp ops) (fn2-ops-wfp ops) (fn2-borrows-accountedp pool ops))
           (fn2-borrows-accountedp
            (mv-nth 3 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                                          target-slot target-gen okind oslot ogen principal pool ops control))
            (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                                          target-slot target-gen okind oslot ogen principal pool ops control))))
  :hints (("Goal" :by fn2-issue-children-borrows)))

;; The fill column is outside every borrow key (the pool's row frames).
(defthm fn2-pool-set-fill-borrows-accounted
  (implies (and (fn2-borrows-accountedp fn2-pool fn2-ops) (natp (fn2-ops-rows fn2-ops)))
           (fn2-borrows-accountedp (fn2-pool-set-fill i v fn2-pool) fn2-ops))
  :hints (("Goal" :in-theory (e/d (fn2-pool-keys-except fn2-pool-free-row-writep fn2-pool-row-key-same
                                   fn2-pool-writers fn2-borrow-readers fn2-pool-out-count$ai fn2-pool-state$ai
                                   fn2-pool-gen$ai)
                                  (fn2-borrows-accountedp fn2-borrows-accountedp-free-row-transfer update-nth-array))
           :use ((:instance fn2-borrows-accountedp-free-row-transfer
                            (s 0) (pool fn2-pool) (ops fn2-ops) (p2 (fn2-pool-set-fill i v fn2-pool)))))))

;; ---------------------------------------------------------------------------
;; One lemma per writer. Its pool output keeps the count against the ops it
;; was given; a writer that also returns ops keeps it against its own ops.
(defun fn2-bf-lemma-names (fs wrld)
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((fn2-bf-provedp (car fs) wrld) (cons (fn2-bf-lemma-name (car fs)) (fn2-bf-lemma-names (cdr fs) wrld)))
        (t (fn2-bf-lemma-names (cdr fs) wrld))))
(defun fn2-bf-leaf-names (fs pw wrld)
  ;; the lemmas proved before the walk that the writers FS call
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (union-eq (fn2-bf-lemma-names (fn2-bf-callees (car fs) pw wrld) wrld) (fn2-bf-leaf-names (cdr fs) pw wrld))))
(defun fn2-bf-writer-lemma (f pw wrld)
  ;; First the writer's body opened once in the ground theory with the
  ;; lemmas before it (no arithmetic, no case analysis of conditions the pool
  ;; does not depend on); else the whole theory with the body open.
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals f wrld)) (outs (getpropc f 'stobjs-out nil wrld))
         (call (cons f formals)) (pool (fn2-bf-out call outs 'fn2-pool))
         (opsp (member-eq 'fn2-ops outs))
         (ops (if opsp (fn2-bf-out call outs 'fn2-ops) 'fn2-ops))
         (induct (and (getpropc f 'recursivep nil wrld) `(:induct ,call)))
         (stmt `(implies (and ,@(and opsp '((fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)))
                              (fn2-borrows-accountedp fn2-pool fn2-ops) (natp (fn2-ops-rows fn2-ops)))
                         (fn2-borrows-accountedp ,pool ,ops))))
    `(:or (defthm ,(fn2-bf-lemma-name f) ,stmt
            :hints (("Goal" ,@(if induct `(,@induct :in-theory (enable ,f)) `(:expand (,call))))))
          (defthm ,(fn2-bf-lemma-name f) ,stmt
            :hints (("Goal" ,@induct
                     :in-theory (union-theories '(,f ,@(fn2-bf-lemma-names (fn2-bf-callees f pw wrld) wrld))
                                                (theory 'fn2-bf-full))))))))
(defun fn2-bf-writer-lemmas (fs pw wrld)
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((fn2-bf-provedp (car fs) wrld) (fn2-bf-writer-lemmas (cdr fs) pw wrld))
        (t (cons `(make-event (fn2-bf-writer-lemma ',(car fs) ',pw (w state)))
                 (fn2-bf-writer-lemmas (cdr fs) pw wrld)))))

;; The ops writers below the faces that write ops keep the ops child's type
;; and well-formedness (the premise their borrow lemmas carry), one lemma per
;; writer, callees first; a writer whose type and wfp lemmas the ops vocabulary
;; already proves is a leaf.
(defun fn2-bf-wf-name (f) (declare (xargs :verify-guards nil)) (fn2-bf-name f "-OPS-WF"))
(defun fn2-bf-wf-leaf-names (f wrld)
  (declare (xargs :verify-guards nil))
  (cond ((getpropc (fn2-bf-wf-name f) 'theorem nil wrld) (list (fn2-bf-wf-name f)))
        ((and (getpropc (fn2-bf-name f "-PRESERVES-TYPE") 'theorem nil wrld)
              (getpropc (fn2-bf-name f "-PRESERVES-WFP") 'theorem nil wrld))
         (list (fn2-bf-name f "-PRESERVES-TYPE") (fn2-bf-name f "-PRESERVES-WFP")))
        (t nil)))
(defun fn2-bf-wf-topo (todo ow done stack wrld fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((zp fuel) done)
        ((atom todo) done)
        ((or (member-eq (car todo) done) (member-eq (car todo) stack))
         (fn2-bf-wf-topo (cdr todo) ow done stack wrld (- fuel 1)))
        ((fn2-bf-wf-leaf-names (car todo) wrld) (fn2-bf-wf-topo (cdr todo) ow done stack wrld (- fuel 1)))
        (t (let ((done (fn2-bf-wf-topo (fn2-bf-callees (car todo) ow wrld) ow done
                                       (cons (car todo) stack) wrld (- fuel 1))))
             (fn2-bf-wf-topo (cdr todo) ow (append done (list (car todo))) stack wrld (- fuel 1))))))
(defun fn2-bf-wf-callee-names (fs wrld)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil (append (fn2-bf-wf-leaf-names (car fs) wrld) (fn2-bf-wf-callee-names (cdr fs) wrld))))
(defun fn2-bf-wf-leaf-names-of (fs ow wrld)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (union-eq (fn2-bf-wf-callee-names (fn2-bf-callees (car fs) ow wrld) wrld) (fn2-bf-wf-leaf-names-of (cdr fs) ow wrld))))
(defun fn2-bf-wf-lemma (f ow wrld)
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals f wrld)) (outs (getpropc f 'stobjs-out nil wrld))
         (call (cons f formals)) (ops (fn2-bf-out call outs 'fn2-ops))
         (induct (and (getpropc f 'recursivep nil wrld) `(:induct ,call)))
         (stmt `(implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)) (and (fn2-opsp ,ops) (fn2-ops-wfp ,ops)))))
    `(:or (defthm ,(fn2-bf-wf-name f) ,stmt
            :hints (("Goal" ,@(if induct `(,@induct :in-theory (enable ,f)) `(:expand (,call))))))
          (defthm ,(fn2-bf-wf-name f) ,stmt
            :hints (("Goal" ,@induct
                     :in-theory (union-theories '(,f ,@(fn2-bf-wf-callee-names (fn2-bf-callees f ow wrld) wrld))
                                                (theory 'fn2-bf-full))))))))
(defun fn2-bf-wf-lemmas (fs ow)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (cons `(make-event (fn2-bf-wf-lemma ',(car fs) ',ow (w state))) (fn2-bf-wf-lemmas (cdr fs) ow))))
(defun fn2-bf-new-names (order wrld)
  ;; the writer lemmas the walk proves for ORDER
  (declare (xargs :verify-guards nil))
  (cond ((atom order) nil)
        ((fn2-bf-provedp (car order) wrld) (fn2-bf-new-names (cdr order) wrld))
        (t (cons (fn2-bf-lemma-name (car order)) (fn2-bf-new-names (cdr order) wrld)))))
(defun fn2-bf-wf-names (wf)
  (declare (xargs :verify-guards nil))
  (if (atom wf) nil (cons (fn2-bf-wf-name (car wf)) (fn2-bf-wf-names (cdr wf)))))
;; The core-level functions the faces reach that the borrow-conservation
;; steps state, and that leave the ops child as it was.
(defun fn2-bf-ops-frame (f wrld)
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals f wrld)) (outs (getpropc f 'stobjs-out nil wrld))
         (core (fn2-bf-out (cons f formals) outs 'fn2-core)))
    `(defthm ,(fn2-bf-name f "-OPS-FRAME")
       (equal (fn2-core-ops ,core) (fn2-core-ops fn2-core))
       :hints (("Goal" :in-theory (enable ,f))))))
(defun fn2-bf-pool-form (f wrld)
  ;; its lemma's count, read as its children (its ops child is the input's)
  (declare (xargs :verify-guards nil))
  (let* ((formals (subst 'core 'fn2-core (formals f wrld))) (outs (getpropc f 'stobjs-out nil wrld))
         (core (fn2-bf-out (cons f formals) outs 'fn2-core)))
    `(defthm ,(fn2-bf-name f "-POOL-BORROWS-ACCOUNTED")
       (implies (and (fn2-core-borrows-accountedp core) (natp (fn2-ops-rows (fn2-core-ops core))))
                (fn2-borrows-accountedp (fn2-core-pool ,core) (fn2-core-ops core)))
       :hints (("Goal" :in-theory '(fn2-core-borrows-accountedp ,(fn2-bf-name f "-OPS-FRAME"))
                :use ,(fn2-bf-lemma-name f))))))
(defun fn2-bf-ops-frames (fs)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (list* `(make-event (fn2-bf-ops-frame ',(car fs) (w state)))
           `(make-event (fn2-bf-pool-form ',(car fs) (w state)))
           (fn2-bf-ops-frames (cdr fs)))))

;; One lemma per face and per core function below it, from its children's,
;; over the least the pool argument needs: the count holds and the ops rows
;; are a natural (and, for a function writing ops, the ops child is
;; well-formed); the result keeps the same, so the lemmas chain through the
;; intermediate cores a face threads.
(defun fn2-bf-core-facts (core opsp)
  (declare (xargs :verify-guards nil))
  `((fn2-core-borrows-accountedp ,core) (natp (fn2-ops-rows (fn2-core-ops ,core)))
    ,@(and opsp `((fn2-opsp (fn2-core-ops ,core)) (fn2-ops-wfp (fn2-core-ops ,core))))))
(defun fn2-bf-face-lemma (f opsp wrld)
  ;; the count is concluded both of the core and of its children, the form a
  ;; caller's pool writer reads after its stobj-let
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals f wrld)) (outs (getpropc f 'stobjs-out nil wrld))
         (call (cons f formals)) (core (fn2-bf-out call outs 'fn2-core))
         (induct (and (getpropc f 'recursivep nil wrld) `(:induct ,call))))
    `(defthm ,(fn2-bf-lemma-name f)
       (implies (and ,@(fn2-bf-core-facts 'fn2-core opsp))
                (and ,@(fn2-bf-core-facts core opsp)
                     (fn2-borrows-accountedp (fn2-core-pool ,core) (fn2-core-ops ,core))))
       :hints (("Goal" ,@(if induct `(,@induct :in-theory (enable ,f)) `(:expand (,call))))))))
(defun fn2-bf-face-lemmas (fs opsfs)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (cons `(make-event (fn2-bf-face-lemma ',(car fs) ',(and (member-eq (car fs) opsfs) t) (w state)))
          (fn2-bf-face-lemmas (cdr fs) opsfs))))

(local (deftheory fn2-bf-ground (executable-counterpart-theory :here)))
(make-event
 (let* ((wrld (w state)) (pw (fn2-bf-pool-writers wrld))
        (faces (fn2-bf-faces wrld))
        ;; the faces and every core function below them, callees first
        (core-fns (set-difference-eq (fn2-bf-core-closure faces wrld nil 100000) *fn2-bf-stated*))
        (core-fns (intersection-eq (fn2-bf-topo core-fns core-fns nil nil wrld 100000) core-fns))
        (order (fn2-bf-topo (fn2-bf-children core-fns pw wrld) pw nil nil wrld 100000))
        (ops-fns (fn2-bf-ops-faces core-fns wrld nil))
        (ow (set-difference-eq (fn2-bf-writers 'fn2-ops wrld nil) '(fn2-core-ops create-fn2-ops)))
        (wf (fn2-bf-wf-topo (fn2-bf-children ops-fns ow wrld) ow nil nil wrld 100000))
        (frames (intersection-eq *fn2-bf-stated* (fn2-bf-core-closure faces wrld nil 100000))))
   `(progn
      (defconst *fn2-bf-faces* ',faces)
      (defconst *fn2-bf-core-fns* ',core-fns)
      (defconst *fn2-bf-writers* ',order)
      (defconst *fn2-bf-ops-wf* ',wf)
      (local (in-theory (disable fn2-borrows-accountedp fn2-core-borrows-accountedp ,@order ,@wf ,@core-fns)))
      (local (deftheory fn2-bf-full (current-theory :here)))
      ;; The writers' and ops lemmas in one theory, set once: the ground
      ;; theory, the lemmas proved before the walk that they call, and each
      ;; lemma as it is proved; each opens only its own body.
      (local (in-theory (union-theories '(mv-nth car-cons cdr-cons fn2-bc-mv-nth-cons-const
                                          ,@(fn2-bf-leaf-names order pw wrld)
                                          ,@(fn2-bf-wf-leaf-names-of wf ow wrld))
                                        (union-theories (theory 'fn2-bf-ground) (theory 'minimal-theory)))))
      ,@(fn2-bf-writer-lemmas order pw wrld)
      ,@(fn2-bf-wf-lemmas wf ow)
      ;; The faces and core functions in the whole theory, the count opened to
      ;; the core's children.
      (local (in-theory (union-theories ',(append (fn2-bf-new-names order wrld) (fn2-bf-wf-names wf)) (theory 'fn2-bf-full))))
      (local (in-theory (enable fn2-core-borrows-accountedp)))
      ,@(fn2-bf-ops-frames frames)
      ,@(fn2-bf-face-lemmas core-fns ops-fns))))

;; ---------------------------------------------------------------------------
;; FN2-CORE-BORROW-CONSERVATION (A2) over every step: borrow-conservation's
;; steps (issues, harvest, core pool writers, the loan write, the host's ops
;; entries, the mailbox) and every face above, each face keyed by its own
;; name with its arguments A's elements.
(defun fn2-bf-nths (formals i)
  (declare (xargs :verify-guards nil))
  (cond ((atom formals) nil)
        ((eq (car formals) 'fn2-core) (cons 'fn2-core (fn2-bf-nths (cdr formals) i)))
        (t (cons `(nth ,i a) (fn2-bf-nths (cdr formals) (+ 1 (nfix i)))))))
(defun fn2-bf-out-vars (outs i)
  (declare (xargs :verify-guards nil))
  (cond ((atom outs) nil)
        ((eq (car outs) 'fn2-core) (cons 'fn2-core (fn2-bf-out-vars (cdr outs) (+ 1 (nfix i)))))
        (t (cons (fn2-bf-name 'fn2-bf-v (coerce (explode-nonnegative-integer (nfix i) 10 nil) 'string))
                 (fn2-bf-out-vars (cdr outs) (+ 1 (nfix i)))))))
(defun fn2-bf-step-clauses (faces wrld)
  (declare (xargs :verify-guards nil))
  (if (atom faces) nil
    (let* ((f (car faces)) (call (cons f (fn2-bf-nths (formals f wrld) 0)))
           (outs (getpropc f 'stobjs-out nil wrld)))
      (cons (list f (if (and (consp outs) (consp (cdr outs)))
                        (let ((vars (fn2-bf-out-vars outs 0)))
                          `(mv-let ,vars ,call (declare (ignore ,@(remove-eq 'fn2-core vars))) fn2-core))
                      call))
            (fn2-bf-step-clauses (cdr faces) wrld)))))
(make-event
 `(defun fn2-core-borrow-face-step (op a fn2-core)
    (declare (xargs :stobjs fn2-core :verify-guards nil))
    (case op ,@(fn2-bf-step-clauses *fn2-bf-faces* (w state)) (otherwise fn2-core))))
(defun fn2-core-borrow-all-step (op a fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (member-eq op *fn2-core-borrow-steps*)
      (fn2-core-borrow-step op a fn2-core)
    (fn2-core-borrow-face-step op a fn2-core)))
(defun fn2-core-borrow-all-hyps (op fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (or (member-eq op *fn2-core-borrow-steps*) (member-eq op *fn2-bf-faces*))
       (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (ok) (fn2-ops-semanticp fn2-ops) ok)
       (fn2-core-borrows-accounted-check fn2-core)))
;; The steps borrow-conservation names keep its executable check; a face keeps
;; the invariant itself (the check equals it once the result's row counts are
;; naturals, which no face lemma here establishes).
(defun-nx fn2-core-borrow-all-conclusion (op a core)
  (if (member-eq op *fn2-core-borrow-steps*)
      (fn2-core-borrows-accounted-check (fn2-core-borrow-step op a core))
    (fn2-core-borrows-accountedp (fn2-core-borrow-face-step op a core))))
(make-event
 `(defthm fn2-core-borrow-face-steps-proved
    (implies (and (member-eq op *fn2-bf-faces*) (fn2-core-wfp core) (fn2-ops-semanticp (fn2-core-ops core))
                  (fn2-core-borrows-accounted-check core))
             (fn2-core-borrows-accountedp (fn2-core-borrow-face-step op a core)))
    :hints (("Goal" :in-theory (e/d (fn2-core-borrow-face-step)
                                    (fn2-core-wfp fn2-core-borrows-accountedp fn2-core-borrows-accounted-check
                                     fn2-ops-semanticp ,@*fn2-bf-faces*))
             :use ((:instance fn2-core-borrows-accounted-check-equiv)
                   (:instance fn2-core-rows-natp)
                   (:instance fn2-ops-semanticp-row-facts (ops (fn2-core-ops core))))))))
(defthm-owed fn2-core-borrow-conservation (op a core)
  (implies (fn2-core-borrow-all-hyps op core)
           (fn2-core-borrow-all-conclusion op a core))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-core-borrow-teeth)
  :doc "A2: every core-level step that writes the pool or the ops child keeps each pool row's out-count equal to the number of live send/write operations on that row that have not released their borrow, with every live borrow naming its row's current generation and may-release only on a send; so the release a harvested operation triggers spends that operation's own counted borrow. The steps: every issue (each action kind and arm-wake), every harvest, every core pool writer and the host's loan write, the host boundary's ops entries, the executor's mailbox, and every machine-arm face and core function that writes the pool (*fn2-bf-faces*, computed from the world: every fn2-core-returning caller of a pool writer).")
(defthm fn2-core-borrow-conservation-all-proved
  (implies (fn2-core-borrow-all-hyps op core)
           (fn2-core-borrow-all-conclusion op a core))
  :hints (("Goal" :in-theory (e/d (fn2-core-borrow-all-hyps fn2-core-borrow-all-conclusion fn2-core-borrow-all-step)
                                  (fn2-core-borrow-step fn2-core-borrow-face-step fn2-core-borrow-hyps
                                   fn2-core-borrow-conclusion fn2-core-wfp fn2-ops-semanticp
                                   fn2-core-borrows-accounted-check))
           :use ((:instance fn2-core-borrow-conservation-proved)
                 (:instance fn2-core-borrow-face-steps-proved)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn2-core-borrow-all-hyps fn2-core-borrow-all-conclusion fn2-core-borrow-all-step
                                  fn2-core-borrow-hyps fn2-core-borrow-conclusion)
                                 (fn2-core-borrow-step fn2-core-borrow-face-step fn2-core-wfp fn2-ops-semanticp
                                  fn2-core-borrows-accounted-check))))))
(defthm fn2-core-borrow-conservation-statement
  (fn2-core-borrow-conservation$owed op a core)
  :hints (("Goal" :in-theory '(fn2-core-borrow-conservation$owed) :use fn2-core-borrow-conservation-all-proved)))
(fn2-owed-discharge fn2-core-borrow-conservation fn2-core-borrow-conservation-statement)
