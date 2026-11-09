; A2 across every machine-arm face: each core-level function that writes the
; pool child, beyond borrow-conservation.lisp's steps, keeps the borrow count.
; Nothing here is listed by hand: the faces are every fn2-core-returning
; caller of a pool writer in this world, and their children's pool writers
; are walked to the primitives, whose A2 lemmas (borrow-accounting.lisp) are
; rewrite rules. Each writer gets one lemma, callees first; each face gets one
; lemma from its children's.
(in-package "ACL2")
(include-book "borrow-conservation")
(include-book "host-boundary")

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
(defun fn2-bf-name (f suffix)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name f) suffix) 'fn2-bf-name))
(defun fn2-bf-lemma-name (f) (declare (xargs :verify-guards nil)) (fn2-bf-name f "-BORROWS-ACCOUNTED"))
(defun fn2-bf-provedp (f wrld)
  (declare (xargs :verify-guards nil))
  (getpropc (fn2-bf-lemma-name f) 'theorem nil wrld))
(defun fn2-bf-callees (f pw wrld)
  (declare (xargs :verify-guards nil))
  (let ((body (getpropc f 'unnormalized-body nil wrld)))
    (and (pseudo-termp body) (intersection-eq (remove-eq f (all-fnnames body)) pw))))
(defun fn2-bf-topo (todo pw done stack wrld fuel)
  ;; post-order over pool-writer callees; a writer with its lemma already
  ;; proved is a leaf (its callees are not walked)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((zp fuel) done)
        ((atom todo) done)
        ((or (member-eq (car todo) done) (member-eq (car todo) stack))
         (fn2-bf-topo (cdr todo) pw done stack wrld (- fuel 1)))
        ((fn2-bf-provedp (car todo) wrld)
         (fn2-bf-topo (cdr todo) pw (append done (list (car todo))) stack wrld (- fuel 1)))
        (t (let ((done (fn2-bf-topo (fn2-bf-callees (car todo) pw wrld) pw done
                                    (cons (car todo) stack) wrld (- fuel 1))))
             (fn2-bf-topo (cdr todo) pw (append done (list (car todo))) stack wrld (- fuel 1))))))
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
;; Faces whose lemma is owed, each with why; A2 below is stated over the rest.
;; The class: a face that reaches the pool through a core-level helper that is
;; not itself a face (or through a face applied to an intermediate core) needs
;; that helper's pool/ops frame or its own face lemma first.
(defconst *fn2-bf-owed*
  '(fn2-principals-genesis      ; via core helper fn2-principals-bind-genesis
    fn2-upload-block-entry      ; via core helpers fn2-upload-page-zero-to, fn2-am-entry-at
    fn2-txn-add-group           ; via core helper fn2-group-counts-put-accept
    fn2-auth-put-create         ; via core helpers fn2-successor-release, fn2-principals-put-row
    fn2-txn-xref                ; via face fn2-txn-xref-pairs on an intermediate core (its corep/wfp)
    fn2-cns-post-reply          ; pool, fields, digests and b3 written by one reply-pool call: not isolated
    fn2-auth-post-reply))       ; the same shape through fn2-auth-seal-reply-pool: not isolated
(defun fn2-bf-pool-writers (wrld)
  (declare (xargs :verify-guards nil))
  ;; create-fn2-pool is a local stobj's creation: no writer's input pool flows into it
  (set-difference-eq (fn2-bf-writers 'fn2-pool wrld nil) '(fn2-core-pool create-fn2-pool)))
(defun fn2-bf-faces (wrld)
  (declare (xargs :verify-guards nil))
  (set-difference-eq
   (fn2-bf-core-callers (cons 'update-fn2-core-pool (fn2-bf-pool-writers wrld)) wrld wrld nil)
   *fn2-bf-stated*))

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
(defun fn2-bf-out (call outs stobj)
  (declare (xargs :verify-guards nil))
  (if (and (consp outs) (consp (cdr outs)))
      `(mv-nth ,(position-eq stobj outs) ,call)
    call))
(defun fn2-bf-lemma-names (fs wrld)
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((fn2-bf-provedp (car fs) wrld) (cons (fn2-bf-lemma-name (car fs)) (fn2-bf-lemma-names (cdr fs) wrld)))
        (t (fn2-bf-lemma-names (cdr fs) wrld))))
(defun fn2-bf-writer-lemma (f pw wrld)
  ;; First the writer's body against only its callees' lemmas (no arithmetic,
  ;; no case analysis of conditions the pool does not depend on); else the
  ;; current theory with the body open.
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
            :hints (("Goal" ,@induct
                     :in-theory (union-theories '(,f mv-nth car-cons cdr-cons fn2-bc-mv-nth-cons-const
                                                  ,@(fn2-bf-lemma-names (fn2-bf-callees f pw wrld) wrld))
                                                (union-theories (theory 'fn2-bf-ground)
                                                                (theory 'minimal-theory))))))
          (defthm ,(fn2-bf-lemma-name f) ,stmt
            :hints (("Goal" ,@induct :in-theory (enable ,f)))))))
(defun fn2-bf-writer-lemmas (fs pw wrld)
  (declare (xargs :verify-guards nil))
  (cond ((atom fs) nil)
        ((fn2-bf-provedp (car fs) wrld) (fn2-bf-writer-lemmas (cdr fs) pw wrld))
        (t (cons `(make-event (fn2-bf-writer-lemma ',(car fs) ',pw (w state)))
                 (fn2-bf-writer-lemmas (cdr fs) pw wrld)))))

;; One lemma per face, from its children's.
(defun fn2-bf-face-lemma (f wrld)
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals f wrld)) (outs (getpropc f 'stobjs-out nil wrld))
         (core (fn2-bf-out (cons f formals) outs 'fn2-core)))
    `(defthm ,(fn2-bf-lemma-name f)
       (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-core-borrows-accountedp fn2-core))
                (fn2-core-borrows-accountedp ,core))
       :hints (("Goal" :in-theory (e/d (,f fn2-core-borrows-accountedp) (fn2-borrows-accountedp fn2-core-wfp))
                :use ((:instance fn2-core-rows-natp (core fn2-core))
                      (:instance fn2-ops-wfp-of-fn2-core-ops)))))))
(defun fn2-bf-face-lemmas (fs)
  (declare (xargs :verify-guards nil))
  (if (atom fs) nil
    (cons `(make-event (fn2-bf-face-lemma ',(car fs) (w state))) (fn2-bf-face-lemmas (cdr fs)))))

(local (deftheory fn2-bf-ground (executable-counterpart-theory :here)))
(make-event
 (let* ((wrld (w state)) (pw (fn2-bf-pool-writers wrld))
        (all (fn2-bf-faces wrld))
        (faces (set-difference-eq all *fn2-bf-owed*))
        ;; a face may call another face (a core helper that writes the pool): callees first
        (faces (intersection-eq (fn2-bf-topo faces faces nil nil wrld 100000) faces))
        (order (fn2-bf-topo (fn2-bf-children faces pw wrld) pw nil nil wrld 100000)))
   `(progn
      (defconst *fn2-bf-all-faces* ',all)
      (assert-event (subsetp-eq *fn2-bf-owed* *fn2-bf-all-faces*))
      (defconst *fn2-bf-faces* ',faces)
      (defconst *fn2-bf-writers* ',order)
      (local (in-theory (disable fn2-borrows-accountedp fn2-core-borrows-accountedp ,@order ,@faces)))
      ,@(fn2-bf-writer-lemmas order pw wrld)
      ,@(fn2-bf-face-lemmas faces))))

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
    (implies (and (member-eq op *fn2-bf-faces*) (fn2-corep core) (fn2-core-wfp core)
                  (fn2-core-borrows-accounted-check core))
             (fn2-core-borrows-accountedp (fn2-core-borrow-face-step op a core)))
    :hints (("Goal" :in-theory (e/d (fn2-core-borrow-face-step)
                                    (fn2-core-wfp fn2-core-borrows-accountedp fn2-core-borrows-accounted-check
                                     ,@*fn2-bf-faces*))
             :use ((:instance fn2-core-borrows-accounted-check-equiv))))))
(defthm-owed fn2-core-borrow-conservation (op a core)
  (implies (fn2-core-borrow-all-hyps op core)
           (fn2-core-borrow-all-conclusion op a core))
  :schema :invariant :from (:columns fn2-pool)
  :teeth (fn2-core-borrow-teeth)
  :doc "A2: every core-level step that writes the pool or the ops child keeps each pool row's out-count equal to the number of live send/write operations on that row that have not released their borrow, with every live borrow naming its row's current generation and may-release only on a send; so the release a harvested operation triggers spends that operation's own counted borrow. The steps: every issue (each action kind and arm-wake), every harvest, every core pool writer and the host's loan write, the host boundary's ops entries, the executor's mailbox, and every machine-arm face and core function that writes the pool (*fn2-bf-faces*, computed from the world: every fn2-core-returning caller of a pool writer, less the faces in *fn2-bf-owed*, whose lemmas are owed).")
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
