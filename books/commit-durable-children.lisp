; The child-level half of commit durability (commit-durable-all.lisp): the
; device log's list lemmas (takes, answers, results), the ops table's and the
; pool's per-primitive lemmas, and the loan and unit views that read no core.
; They need only the core's children and ops-conservation, and prove here in
; a seventh of the time they took in the executor's world (whose 58 stobjs'
; column facts every NTH term tries); commit-durable-all includes this book.
(in-package "ACL2")
(include-book "arm-children")
(include-book "core-children")
(include-book "assumptions-device")
(include-book "pointwise-contracts")
(local (deflabel fn2-env-children-before-ops-conservation))
(include-book "ops-conservation")
; FN2-OPS-CREDIT-CONSERVATION's per-operation exports are used by name only.
(local (in-theory (set-difference-theories
                   (current-theory :here)
                   (set-difference-theories (universal-theory :here)
                                            (universal-theory 'fn2-env-children-before-ops-conservation)))))
(defun fn2-env-arg (i x)
  (declare (xargs :guard (natp i)))
  (if (true-listp x) (nth i x) nil))
(defun fn2-env-tag (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn2-env-pool-octets (n addr fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (natp n) (natp addr)) :measure (nfix n)))
  (if (or (zp n) (not (natp addr)) (>= addr (fn2-pool-data-length fn2-pool))) nil
    (cons (fn2-pool-datai addr fn2-pool) (fn2-env-pool-octets (- n 1) (+ 1 addr) fn2-pool))))

; The take entry of (SLOT GEN) in the newest-first LOG.
(defun fn2-env-taken (slot gen rlog)
  (declare (xargs :guard t))
  (cond ((atom rlog) nil)
        ((and (fn2-dev-takep (car rlog))
              (equal (nth 1 (car rlog)) slot) (equal (nth 2 (car rlog)) gen))
         (car rlog))
        (t (fn2-env-taken slot gen (cdr rlog)))))
(defthm fn2-env-taken-true-listp
  (true-listp (fn2-env-taken slot gen rlog))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn2-env-taken slot gen rlog)
           :in-theory '(fn2-env-taken fn2-dev-takep atom (:type-prescription true-listp)))))

; The fresh core a wrapper's with-local-stobj makes satisfies fn2-corep:
; each child's creator meets its recognizer (a column table's CREATE-<T>-TYPE,
; else the creator and recognizer opened).
(defun fn2-env-create-runes (children world)
  (declare (xargs :mode :program))
  (if (atom children) nil
    (let* ((type (cadar children)) (create (fn2-columns-pre "CREATE-" type))
           (lemma (fn2-columns-sym create "-TYPE")))
      (if (getpropc lemma 'theorem nil world)
          (cons lemma (fn2-env-create-runes (cdr children) world))
        (list* create (fn2-columns-sym type "P") (fn2-env-create-runes (cdr children) world))))))
(defun fn2-env-device-log (run)
  (declare (xargs :guard t))
  (fn2-env-arg 0 run))
(defun fn2-env-acknowledged-batches (run)
  (declare (xargs :guard t))
  (fn2-env-arg 1 run))
(defconst *fn2-env-recovery-assume* 3)
(defun fn2-env-recovery-done-p (rec)
  (declare (xargs :guard t))
  (and (fn2-env-arg 0 rec) t))
(defun fn2-env-iota (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (append (fn2-env-iota (- n 1)) (list n))))
(defun fn2-env-recovered-batches (rec)
  (declare (xargs :guard t))
  (fn2-env-iota (nfix (fn2-env-arg 1 rec))))
(defun fn2-env-observe-rows (rows acked)
  (declare (xargs :verify-guards nil))
  (if (atom rows) acked
    (fn2-env-observe-rows
     (cdr rows)
     (let ((r (car rows)))
       (if (and (eq (nth 0 r) :ok) (eq (nth 1 r) :ok) (posp (nth 2 r)))
           (add-to-set-equal (nth 3 r) acked)
         acked)))))
(defun fn2-env-observed-p (rows acked)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (let ((r (car rows)))
      (and (or (not (and (eq (nth 0 r) :ok) (eq (nth 1 r) :ok) (posp (nth 2 r))))
               (member-equal (nth 3 r) acked))
           (fn2-env-observed-p (cdr rows) acked)))))
(defthm fn2-env-observe-rows-observed
  (implies (fn2-env-observed-p rows acked)
           (equal (fn2-env-observe-rows rows acked) acked)))
; Entry W of LOG is a write the device answered done in full.
(defun fn2-env-done-write-p (w log)
  (declare (xargs :verify-guards nil))
  (and (natp w) (true-listp log) (< w (len log))
       (let ((e (nth w log)))
         (and (fn2-dev-take-writep e)
              (fn2-dev-done-answer-p (fn2-dev-answer (nth 1 e) (nth 2 e) (nthcdr (+ 1 w) log))
                                     *fn2-dev-write-result* (len (nth 6 e)))))))
; The index of the first take of (SLOT GEN) in the oldest-first LOG.
(defun fn2-env-take-index (slot gen log)
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (fn2-dev-takep (car log)) (equal (nth 1 (car log)) slot) (equal (nth 2 (car log)) gen)) 0)
        (t (let ((w (fn2-env-take-index slot gen (cdr log)))) (and w (+ 1 w))))))
; The op's take is in LOG iff it left the outbox; its first answer is the
; posted terminal cell iff one is posted.
(defun fn2-env-j5-taken (op slot log)
  (declare (xargs :verify-guards nil))
  (let ((gen (nth 1 op)) (phase (nth 2 op)))
    (if (equal phase *fn2-op-phase-queued*)
        (and (not (fn2-env-take-index slot gen log)) (equal (nth 13 op) 0))
      (let ((w (fn2-env-take-index slot gen log)))
        (and (equal phase *fn2-op-phase-submitted*) (natp w)
             (let ((ans (fn2-dev-answer slot gen (nthcdr (+ 1 w) log))))
               (if (equal (nth 13 op) 1)
                   (and (equal (nth 14 op) 0) (consp ans)
                        (equal (nth 3 (car ans)) (nth 15 op)) (equal (nth 4 (car ans)) (nth 16 op))
                        (equal (nth 5 (car ans)) (nth 17 op)))
                 (not ans))))))))
;; A role write's posted terminal cell is a write result whose count is at
;; most the write's range length (the post's payload check), so the
;; harvest's complete-in branch accepts it and the handler's byte count
;; stays in range. Its own disabled function of the op: every frame that
;; keeps the op keeps it.
(defun fn2-env-j5-event-ok (op)
  (declare (xargs :verify-guards nil))
  (implies (equal (nth 13 op) 1)
           (and (equal (nth 15 op) *fn2-event-write-result*) (<= (nth 17 op) (nth 10 op)))))
(defthm fn2-env-j5-event-ok-of-update-phase
  (equal (fn2-env-j5-event-ok (update-nth 2 x op)) (fn2-env-j5-event-ok op)))
(in-theory (disable fn2-env-j5-event-ok))
(defun fn2-env-b2n (x) (declare (xargs :guard t)) (if x 1 0))

; Durability only grows with the log.
(local (defthm fn2-env-nth-append-low
  (implies (< (nfix n) (len x)) (equal (nth n (append x y)) (nth n x)))))
(local (defthm fn2-env-len-append (equal (len (append x y)) (+ (len x) (len y)))))
(defun fn2-env-acks-bounded-p (rows n)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (let ((r (car rows)))
      (and (implies (and (eq (nth 0 r) :ok) (eq (nth 1 r) :ok) (posp (nth 2 r)))
                    (and (natp (nth 3 r)) (<= (nth 3 r) (nfix n))))
           (fn2-env-acks-bounded-p (cdr rows) n)))))
(defthm fn2-env-observed-p-mono
  (implies (and (fn2-env-observed-p rows a) (subsetp-equal a b))
           (fn2-env-observed-p rows b)))
(defthm fn2-env-subsetp-add-to-set-x
  (implies (subsetp-equal x acked) (subsetp-equal x (add-to-set-equal a acked))))
(defthm fn2-env-observe-rows-superset-gen
  (implies (subsetp-equal x acked) (subsetp-equal x (fn2-env-observe-rows rows acked)))
  :hints (("Goal" :induct (fn2-env-observe-rows rows acked) :in-theory (disable add-to-set-equal))))
(defthm fn2-env-member-observe-rows
  (implies (member-equal a acked) (member-equal a (fn2-env-observe-rows rows acked)))
  :hints (("Goal" :induct (fn2-env-observe-rows rows acked))))
(defthm fn2-env-member-add-to-set
  (member-equal a (add-to-set-equal a x)))
(defthm fn2-env-observe-rows-covers
  (fn2-env-observed-p rows (fn2-env-observe-rows rows acked))
  :hints (("Goal" :induct (fn2-env-observe-rows rows acked) :in-theory (disable add-to-set-equal))))

;; J ONLY GROWS WITH THE LOG, and the host steps leave every child J reads.
(local (defthm fn2-env-nthcdr-append
  (implies (<= (nfix n) (len x))
           (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))))
(local (defthm fn2-env-consp-append (implies (consp x) (consp (append x y)))))
(local (defthm fn2-env-done-answer-append
  (implies (consp tail)
           (equal (fn2-dev-done-answer-p (append tail y) evkind count)
                  (fn2-dev-done-answer-p tail evkind count)))
  :hints (("Goal" :in-theory '(fn2-dev-done-answer-p car-cons fn2-env-consp-append) :expand ((append tail y))))))
(local (defthm fn2-env-done-answer-nil (not (fn2-dev-done-answer-p nil evkind count))))
(defthm fn2-env-done-write-extends
  (implies (and (fn2-env-done-write-p w log) (true-listp more))
           (fn2-env-done-write-p w (append log more)))
  :hints (("Goal" :in-theory '(fn2-env-done-write-p fn2-env-nth-append-low fn2-env-nthcdr-append
                                fn2-env-done-answer-append fn2-dev-answer-append fn2-env-len-append
                                fn2-env-done-answer-nil natp nfix fix (:type-prescription true-listp-append) true-listp-append
                                (:type-prescription len) (:type-prescription fn2-dev-answer)
                                (:type-prescription binary-append))
           :cases ((consp (fn2-dev-answer (nth 1 (nth w log)) (nth 2 (nth w log)) (nthcdr (+ 1 w) log)))))))
(defun-nx fn2-env-log-step (delta g a h b)
  (and (equal b a) (true-listp delta) (equal h (append g delta))))
;; the readers J uses, past the host steps' children (ops, pool, extents)
(defun fn2-env-j-reader-frame-1 (fn args updates)
  (declare (xargs :mode :program))
  (if (atom updates) nil
    (cons `(defthm ,(fn2-columns-sym fn (concatenate 'string "-OF-" (symbol-name (car updates))))
             (equal (,fn ,@args (,(car updates) x fn2-core)) (,fn ,@args fn2-core))
             :hints (("Goal" :in-theory (enable ,fn))))
          (fn2-env-j-reader-frame-1 fn args (cdr updates)))))
(defun fn2-env-j-reader-frame-events (readers updates)
  (declare (xargs :mode :program))
  (if (atom readers) nil
    (append (fn2-env-j-reader-frame-1 (caar readers) (cdar readers) updates)
            (fn2-env-j-reader-frame-events (cdr readers) updates))))

;; :ADMIT. The admission adds no reply a commit row did not show before:
;; fn2-env-no-new-acks-p of the rows after against the rows before, so
;; OBSERVED carries over and DURABLE is untouched (the admission logs
;; nothing). Each sub-operation's arm-frames contract (books/machines.lisp,
;; derived under the commit kind) bounds what it changes; one bridge lemma
;; turns a contract that leaves the directory, the commit table's rows and
;; its cb-acks and batch-no columns alone into the relation, and the row
;; write of fn2-commit-start, which writes both columns, leaves cb-acks 0
;; by its write contract's read-back.
(defun fn2-env-no-new-acks-p (post pre)
  (declare (xargs :verify-guards nil))
  (if (atom post) t
    (and (or (equal (car post) (car pre)) (not (posp (nth 2 (car post)))))
         (fn2-env-no-new-acks-p (cdr post) (cdr pre)))))
(defthm fn2-env-observed-no-new-acks
  (implies (and (fn2-env-observed-p pre acked) (fn2-env-no-new-acks-p post pre))
           (fn2-env-observed-p post acked)))
(defthm fn2-env-no-new-acks-refl (fn2-env-no-new-acks-p x x))
(defthm fn2-env-no-new-acks-trans
  (implies (and (fn2-env-no-new-acks-p c b) (fn2-env-no-new-acks-p b a) (equal (len c) (len b)))
           (fn2-env-no-new-acks-p c a)))
(defthm fn2-env-nth-off-update-nth
  (implies (and (equal (update-nth r nil x) (update-nth r nil y)) (not (equal (nfix s) (nfix r))))
           (equal (nth s x) (nth s y)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance nth-update-nth (m s) (n r) (val nil) (l x))
                        (:instance nth-update-nth (m s) (n r) (val nil) (l y)))
           :in-theory (disable nth-update-nth))))

; The row write of fn2-commit-start writes cb-acks and batch-no at its row.
; Accepted, its contract's read-back leaves cb-acks 0 there; refused, it
; changes neither the directory nor the commit table.
(defthm fn2-env-cols-nth-in
  (implies (and (fn2-arm-cols k row columns a b) (natp k) (natp j) (member-equal (+ k j) columns))
           (equal (update-nth row nil (nth j a)) (update-nth row nil (nth j b))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-arm-kids-nth-induct k j a b) :in-theory (enable nth fn2-arm-cols))))
(defun fn2-env-row-read-events (fields)
  (declare (xargs :mode :program))
  (if (atom fields) nil
    (let* ((f (caar fields)) (j (cdar fields))
           (r (fn2-columns-col-name 'fn2-machine f))
           (tr (fn2-columns-col-name 'fn2-commit f)) (ai (fn2-columns-sym tr "$AI")))
      (cons
       `(defthm ,(fn2-columns-sym r "-OF-ROW-FRAME")
          (implies (and (fn2-arm-row-frame 9 row cs ch a b) (not (member-equal 9 ch)) (natp row)
                        (not (member-equal 33 cs)) (fn2-ctf-dir b a)
                        (equal (fn2-machine-kind id a) *fn2-commit-kind*)
                        (or (not (member-equal ,j cs)) (not (equal (fn2-machine-slot id a) row))))
                   (equal (,r id b) (,r id a)))
          :rule-classes nil
          :hints (("Goal" :in-theory (e/d (,r fn2-commit-table fn2-commit-rows ,tr ,ai)
                                          (fn2-machine-kind fn2-machine-slot fn2-machine-idp nth update-nth
                                           fn2-arm-row-frame fn2-ctf-dir))
                   :cases ((member-equal ,j cs))
                   :do-not-induct t
                   :use ((:instance fn2-ctf-dir-readers)
                         (:instance fn2-arm-row-frame-cols (table 9) (columns cs) (children ch))
                         (:instance fn2-arm-cols-nth (k 0) (j 33) (columns cs) (a (nth 9 a)) (b (nth 9 b)))
                         (:instance fn2-arm-cols-nth (k 0) (j ,j) (columns cs) (a (nth 9 a)) (b (nth 9 b)))
                         (:instance fn2-env-cols-nth-in (k 0) (j ,j) (row row) (columns cs) (a (nth 9 a)) (b (nth 9 b)))
                         (:instance fn2-env-nth-off-update-nth (r row) (s (fn2-machine-slot id a))
                                    (x (nth ,j (nth 9 a))) (y (nth ,j (nth 9 b))))))))
       (fn2-env-row-read-events (cdr fields))))))
(defthm fn2-env-row-frame-child
  (implies (and (fn2-arm-row-frame tb row cs ch a b) (natp k) (not (equal k tb)) (not (member-equal k ch)))
           (equal (nth k b) (nth k a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-arm-row-frame) (nth))
           :use ((:instance fn2-arm-kids-nth (i 0) (free (cons tb ch)))))))
(defun fn2-env-ek-col-events (cols)
  (declare (xargs :mode :program))
  (if (atom cols) nil
    (let ((upd (fn2-columns-pre "UPDATE-" (fn2-columns-sym (fn2-columns-col-name 'fn2-commit-io (car cols)) "$AI"))))
      (cons `(defthm ,(fn2-columns-sym (fn2-columns-pre "FN2-ENV-EK-OF-" upd) "")
               (equal (fn2-env-ek (update-fn2-core-commit-io (,upd i v io) y) a)
                      (fn2-env-ek (update-fn2-core-commit-io io y) a))
               :hints (("Goal" :in-theory (enable fn2-env-ek update-fn2-core-commit-io ,upd update-nth-array))))
            (fn2-env-ek-col-events (cdr cols))))))
(defconst *fn2-env-ek-runes*
  '(fn2-env-ek-of-update-same fn2-env-ek-refl
    fn2-env-ek-of-update-fn2-commit-io-epoch$ai fn2-env-ek-of-update-fn2-commit-io-counter$ai
    fn2-env-ek-of-update-fn2-commit-io-pool-slot$ai fn2-env-ek-of-update-fn2-commit-io-pool-gen$ai
    fn2-env-ek-of-update-fn2-commit-io-op-slot$ai fn2-env-ek-of-update-fn2-commit-io-op-gen$ai
    fn2-env-ek-of-update-fn2-commit-io-ready$ai fn2-env-ek-of-update-fn2-commit-io-lent$ai
    fn2-commit-io-set-counter fn2-commit-io-set-epoch fn2-commit-io-set-lent fn2-commit-io-set-op-gen
    fn2-commit-io-set-op-slot fn2-commit-io-set-pool-gen fn2-commit-io-set-pool-slot fn2-commit-io-set-ready))
(defun fn2-env-rk-col-events (cols)
  (declare (xargs :mode :program))
  (if (atom cols) nil
    (let ((upd (fn2-columns-pre "UPDATE-" (fn2-columns-sym (fn2-columns-col-name 'fn2-commit-root (car cols)) "$AI"))))
      (cons `(defthm ,(fn2-columns-sym (fn2-columns-pre "FN2-ENV-RK-OF-" upd) "")
               (equal (fn2-env-rk (update-fn2-core-commit-root (,upd i v r) y) a)
                      (fn2-env-rk (update-fn2-core-commit-root r y) a))
               :hints (("Goal" :in-theory (enable fn2-env-rk fn2-env-root update-fn2-core-commit-root fn2-core-commit-root
                                                  ,upd update-nth-array fn2-commit-root-rows fn2-commit-root-installed
                                                  fn2-commit-root-published fn2-commit-root-installed$ai fn2-commit-root-published$ai))))
            (fn2-env-rk-col-events (cdr cols))))))
(defconst *fn2-env-rk-runes*
  '(fn2-env-rk-of-update-same fn2-env-rk-refl
    fn2-env-rk-of-update-fn2-commit-root-parent$ai fn2-env-rk-of-update-fn2-commit-root-extent$ai
    fn2-env-rk-of-update-fn2-commit-root-first-key$ai fn2-env-rk-of-update-fn2-commit-root-members$ai
    fn2-env-rk-of-update-fn2-commit-root-proposed$ai fn2-env-rk-of-update-fn2-commit-root-abort-event$ai
    fn2-env-rk-of-update-fn2-commit-root-aborting$ai fn2-env-rk-of-update-fn2-commit-root-barrier-mode$ai
    fn2-env-rk-of-update-fn2-commit-root-seal-ready$ai
    fn2-commit-root-set-abort-event fn2-commit-root-set-aborting fn2-commit-root-set-barrier-mode
    fn2-commit-root-set-extent fn2-commit-root-set-first-key fn2-commit-root-set-members fn2-commit-root-set-parent
    fn2-commit-root-set-proposed fn2-commit-root-set-seal-ready))
(defun fn2-env-rel-name (fn rel) (declare (xargs :mode :program)) (fn2-columns-sym fn (concatenate 'string "-" (symbol-name rel))))
;; The frame of the visit at PHASE, from the arm's declaration; the
;; commit-io (30) and root (31) children are kept when the arm does not
;; declare them, and then the frontier and the installed root stay.
(defun fn2-env-arm-state-const (state-name)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string "*FN2-COMMIT-STATE-" (symbol-name state-name) "*") 'fn2-core))
;; Each semantic row contract instantiates the shared pointwise transport.
(defun fn2-env-pw-arm-hints (point all one hyps point-open facts)
  (declare (xargs :verify-guards nil))
  (let* ((step `(lambda (delta g a h b)
                 (and (equal h g)
                      (equal b (mv-nth 4 (fn2-commit-run (car delta) (cadr delta) a)))
                      ,@(sublis '((id . (car delta)) (budget . (cadr delta))
                                  (log . g) (fn2-core . a)) hyps))))
         (instance `(:functional-instance fn2-pw-transport
                      (fn2-pw-point ,point) (fn2-pw-all ,all) (fn2-pw-step ,step)
                      (fn2-pw-affected (lambda (key delta g a h b) nil))
                      (fn2-pw-repaired (lambda (keys delta g a h b) t)))))
    `(("Goal" :use ((:instance ,instance (keys ids) (g log) (h log)
                     (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                     (delta (list id budget))) ,@facts)
       :in-theory '(,all ,@point-open car-cons cdr-cons) :do-not-induct t)
      ; ACL2 caches already discharged functional constraints; locality is
      ; subgoal 2 on the first lift and subgoal 1 on later lifts.
      ("Subgoal 2" :use ((:instance ,one (i key) (id (car delta)) (budget (cadr delta))
                          (log g) (fn2-core a))))
      ("Subgoal 1" :use ((:instance ,one (i key) (id (car delta)) (budget (cadr delta))
                          (log g) (fn2-core a)))))))

;; Each per-id lift FN2-ENV-J-ROW-<PHASE>-ARM, lifted over the id list.
(defun fn2-env-arm-rows-events (state-name extra)
  (declare (xargs :mode :program))
  (let* ((const (fn2-env-arm-state-const state-name))
         (row (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-row state-name) "-ARM"))
         (rw (fn2-columns-sym row "-REWRITE"))
         (hyps `(,@extra (fn2-env-j-frontier log fn2-core) (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (equal (fn2-commit-row-phase id fn2-core) ,const))))
    `((defthm ,rw
        (implies (and (fn2-env-j-row i log fn2-core) ,@hyps)
                 (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
        :hints (("Goal" :in-theory nil :use ((:instance ,row)))))
      (defthm ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-rows state-name) "-ARM")
        (implies (and (fn2-env-j-rows ids log fn2-core) ,@hyps)
                 (fn2-env-j-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
        :hints ,(fn2-env-pw-arm-hints 'fn2-env-j-row 'fn2-env-j-rows row hyps nil nil))
      (in-theory (disable ,rw)))))
(defthm fn2-env-root-fields
  (implies (equal r (list t x y)) (and (nth 0 r) (equal (nth 1 r) x) (equal (nth 2 r) y)))
  :rule-classes nil)
(defun fn2-env-arm-fn (state-name)
  (declare (xargs :mode :program))
  (fn2-columns-sym (fn2-columns-col-name 'fn2-commit-run state-name) ""))
(defun fn2-env-arm-phase-events (state-name extra world)
  ; FN2-ENV-COMMIT-RUN-<STATE>-NEXT: the visit at STATE leaves the row's
  ; phase among the arm's declared successors (any stop reason)
  (declare (xargs :mode :program))
  (let* ((arm (fn2-env-arm-fn state-name))
         (next (cadddr (cdr (assoc-eq arm (table-alist 'fn2-arm-frame-fns world)))))
         ; the theory the generator proved the arm's own -ARM-PHASE contract in
         (ev (get-event (fn2-columns-sym arm "-ARM-PHASE") world))
         (th (cadr (member :in-theory (cdr (car (cadr (member :hints ev)))))))
         (runes (if (and (consp th) (eq (car th) 'union-theories)) (unquote (cadr th))
                  (er hard 'fn2-env-arm-phase-events "No -ARM-PHASE theory for ~x0." arm)))
         (arm-phase (fn2-columns-sym (fn2-columns-col-name 'fn2-env-arm-phase state-name) "")))
    `((defthm ,arm-phase
        (implies (and (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
                      (equal (fn2-machine-phase id fn2-core) ,(fn2-env-arm-state-const state-name))
                      (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (subsetp-equal ',next fn2-arm-pset))
                 (member-equal (fn2-machine-phase id (mv-nth 4 (,arm id budget fn2-core))) fn2-arm-pset))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(,@runes) (theory 'fn2-arm-frame-base))
                 :do-not-induct t)))
      (defthm ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-NEXT")
        (implies (and ,@extra (equal (fn2-commit-row-phase id fn2-core) ,(fn2-env-arm-state-const state-name)))
                 (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run id budget fn2-core))) ',next))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase
                                                     fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase fn2-core-stop-arm-phase fn2-commit-idp)
                                                   (theory 'fn2-arm-frame-base))
                 :do-not-induct t
                 :use ((:instance ,arm-phase (fn2-arm-pset ',next))
                       (:instance fn2-env-row-phase-snapshot))))))))
(defthm fn2-env-not-intersectp-member
  (implies (and (not (intersectp-equal x y)) (member-equal j y)) (not (member-equal j x)))
  :rule-classes nil)
(defun fn2-env-tk-read-events (fields)
  (declare (xargs :mode :program))
  (if (atom fields) nil
    (let* ((f (car fields))
           (r (fn2-columns-col-name 'fn2-machine f))
           (tr (fn2-columns-col-name 'fn2-commit f)) (ai (fn2-columns-sym tr "$AI")))
      (cons
       `(defthm ,(fn2-columns-sym r "-OF-TK")
          (implies (and (fn2-env-tk b a) (equal (fn2-machine-kind id a) *fn2-commit-kind*))
                   (equal (,r id b) (,r id a)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(fn2-env-tk fn2-ctf-dir fn2-machines-directory-keeps
                                          ,r ,(fn2-columns-sym r "-READ-CODE") fn2-commit-table fn2-commit-rows ,tr ,ai)
                                         (theory 'minimal-theory))
                   :do-not-induct t
                   :use ((:instance fn2-ctf-dir-readers)))))
       (fn2-env-tk-read-events (cdr fields))))))
(defthm fn2-env-row-units-disjoint
  (implies (and (natp a) (natp b) (not (equal a b)) (natp role) (< role 3) (natp k) (< k 3))
           (not (equal (+ (* 3 a) role) (+ k (* 3 b)))))
  :rule-classes nil
  :hints (("Goal" :cases ((< a b)))))
(defun fn2-env-jr-shape-runes (fn world)
  (declare (xargs :mode :program))
  (cond ((getpropc (fn2-columns-sym fn "-PRESERVES-TYPE") 'theorem nil world)
         (list (fn2-columns-sym fn "-PRESERVES-TYPE") (fn2-columns-sym fn "-PRESERVES-WFP")))
        ((getpropc (fn2-columns-sym fn "-TYPE") 'theorem nil world)
         (list (fn2-columns-sym fn "-TYPE") (fn2-columns-sym fn "-WFP")))
        (t (list (fn2-columns-sym fn "-SHAPE")))))
(defun fn2-env-jr-events (fns world)
  ; FN-FN2-ENV-JR from FN's TK, EK and RK steps; an entry (FN . HYPS)
  ; adds its shape theorem's hypotheses
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (let* ((fn (if (consp (car fns)) (caar fns) (car fns))) (hyps (and (consp (car fns)) (cdar fns))) (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
      (cons `(fn2-with-column-projections (fn2-env-ek fn2-env-rk fn2-env-tk)
(defthm ,(fn2-env-rel-name fn 'fn2-env-jr)
               (implies (and (fn2-env-jr ids log fn2-core) ,@hyps) (fn2-env-jr ids log ,out))
               :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-jr fn2-env-tk-refl fn2-env-ek-refl fn2-env-rk-refl

                                                             ,@(fn2-env-jr-shape-runes fn world))
                                                          (theory 'minimal-theory))))
                        :do-not-induct t
                        :use ((:instance fn2-env-jr-of-tk (a fn2-core) (b ,out))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ek fn2-env-rk fn2-env-tk) clause world)))))
            (fn2-env-jr-events (cdr fns) world)))))
;; every commit visit: the arm's frame keeps the directory and the rows field
(defthm fn2-env-subsetp-cons
  (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
(defthm fn2-env-machines-setters-dir
  (and (equal (fn2-machines-kind j (fn2-machines-set-kind i v m)) (if (equal (nfix i) (nfix j)) v (fn2-machines-kind j m)))
       (equal (fn2-machines-slot j (fn2-machines-set-kind i v m)) (fn2-machines-slot j m))
       (equal (fn2-machines-rows (fn2-machines-set-kind i v m)) (fn2-machines-rows m))
       (equal (fn2-machines-kind j (fn2-machines-set-slot i v m)) (fn2-machines-kind j m))
       (equal (fn2-machines-slot j (fn2-machines-set-slot i v m)) (if (equal (nfix i) (nfix j)) v (fn2-machines-slot j m)))
       (equal (fn2-machines-rows (fn2-machines-set-slot i v m)) (fn2-machines-rows m))
       (equal (fn2-machines-kind j (fn2-machines-set-ready-prev i v m)) (fn2-machines-kind j m))
       (equal (fn2-machines-slot j (fn2-machines-set-ready-prev i v m)) (fn2-machines-slot j m))
       (equal (fn2-machines-rows (fn2-machines-set-ready-prev i v m)) (fn2-machines-rows m))
       (equal (fn2-machines-kind j (fn2-machines-set-ready-next i v m)) (fn2-machines-kind j m))
       (equal (fn2-machines-slot j (fn2-machines-set-ready-next i v m)) (fn2-machines-slot j m))
       (equal (fn2-machines-rows (fn2-machines-set-ready-next i v m)) (fn2-machines-rows m))
       (equal (fn2-machines-kind j (fn2-machines-set-wait-reason i v m)) (fn2-machines-kind j m))
       (equal (fn2-machines-slot j (fn2-machines-set-wait-reason i v m)) (fn2-machines-slot j m))
       (equal (fn2-machines-rows (fn2-machines-set-wait-reason i v m)) (fn2-machines-rows m)))
  :hints (("Goal" :in-theory (enable fn2-machines-set-kind fn2-machines-set-slot fn2-machines-set-ready-prev
                                     fn2-machines-set-ready-next fn2-machines-set-wait-reason fn2-machines-kind fn2-machines-slot
                                     fn2-machines-rows fn2-machines-kind$ai fn2-machines-slot$ai update-fn2-machines-kind$ai
                                     update-fn2-machines-slot$ai update-fn2-machines-ready-prev$ai update-fn2-machines-ready-next$ai
                                     update-fn2-machines-wait-reason$ai))))
(defun fn2-env-write-keeps-ids-event (w world)
  ; W-KEEPS-IDS: a commit-table row write keeps every id's readability and slot
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit) (formals (formals w world)) (call (cons w formals))
         (e (fn2-arm-frame-known w kind world)) (cs (fn2-arm-frame-entry-j e)) (ch (fn2-arm-frame-entry-s e))
         (row '(fn2-machine-slot id fn2-core)))
    `(defthm ,(fn2-columns-sym w "-KEEPS-IDS")
       (and (equal (fn2-commit-idp x ,call) (fn2-commit-idp x fn2-core))
            (equal (fn2-machine-slot x ,call) (fn2-machine-slot x fn2-core)))
       :rule-classes nil
       :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir-refl (:type-prescription fn2-machine-slot-natp))
                                                  (theory 'fn2-arm-frame-base))
                :do-not-induct t
                :use ((:instance ,(fn2-columns-sym w "-ARM-ROW-FRAME") (fn2-arm-tb 9) (fn2-arm-row ,row)
                                 (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                      (:instance fn2-arm-row-frame-refl (table 9) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                      (:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                      (:instance fn2-arm-kids-nth (i 0) (k 3) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                      (:instance fn2-ctf-dir-of-nth (b ,call) (x fn2-core) (a fn2-core))
                      (:instance fn2-ctf-dir-readers (id x) (b ,call) (a fn2-core))
                      (:instance fn2-env-read-codes-of-row-frame (id x) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))))))))
(defun fn2-env-j3-move-ok (p q mode d d2)
  ; the phase moves a commit visit may make that keep J3 at the row: out of
  ; the write span, a stay, :collect -> :seal -> :dependencies, :fence ->
  ; :log-write in barrier mode 1, each with the count kept; or a write phase
  ; advancing with its count reset
  (declare (xargs :guard t))
  (or (not (member-equal q '(1 2 3 4 5)))
      (and (equal d2 d)
           (or (equal q p) (and (equal p 1) (equal q 2)) (and (equal p 2) (equal q 3))
               (and (equal p 5) (equal q 4) (equal mode 1))))
      (and (equal d2 0) (member-equal p '(3 4)) (member-equal q '(3 4 5)) (or (equal p 3) (not (equal q 3))))))
(defun fn2-env-row-frame-uses (rs row cs ch b)
  (declare (xargs :mode :program))
  (if (atom rs) nil
    (cons `(:instance ,(car rs) (id id) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))
          (fn2-env-row-frame-uses (cdr rs) row cs ch b))))
(defun fn2-env-arm-phase-runes (state-name world)
  ; the theory the generator proved the arm's own -ARM-PHASE contract in
  (declare (xargs :mode :program))
  (let* ((arm (fn2-env-arm-fn state-name))
         (ev (get-event (fn2-columns-sym arm "-ARM-PHASE") world))
         (th (cadr (member :in-theory (cdr (car (cadr (member :hints ev))))))))
    (if (and (consp th) (eq (car th) 'union-theories)) (unquote (cadr th))
      (er hard 'fn2-env-arm-phase-runes "No -ARM-PHASE theory for ~x0." arm))))
(defmacro fn2-env-turn-instance ()
  '(defthm fn2-env-turn-preserves
     (implies (and (fn2-env-turn-inv g fn2-core)
                   (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
              (fn2-env-turn-inv g (mv-nth 4 (fn2-turn fn2-core))))
     :hints (("Goal"
              :use ((:functional-instance fn2-executor-inv-turn
                      (fn2-executor-inv fn2-env-turn-inv)
                      (fn2-executor-rel fn2-env-turn-rel)))
              :in-theory (disable fn2-corep fn2-core-wfp fn2-turn
                           fn2-env-inv fn2-env-observe fn2-env-observe-is-rows fn2-env-rows
                           fn2-env-observed-p fn2-env-acked-durable-p)
              :do-not-induct t))))
(defun fn2-env-image-holds-write-p (e image)
  (declare (xargs :verify-guards nil))
  (equal (fn2-dev-image-octets image (nfix (nth 4 e)) (len (nth 6 e))) (true-list-fix (nth 6 e))))
; Some fenced write at OFFSET in LOG from W whose octets IMAGE holds.
(defun fn2-env-held-offset-from (w offset log image)
  (declare (xargs :verify-guards nil :measure (nfix (- (len log) (nfix w)))
                  :hints (("Goal" :in-theory (disable fn2-dev-fenced-write-p fn2-env-image-holds-write-p)))))
  (cond ((not (and (natp w) (true-listp log) (< w (len log)))) nil)
        ((and (fn2-dev-fenced-write-p w log) (equal (nth 4 (nth w log)) offset)
              (fn2-env-image-holds-write-p (nth w log) image))
         t)
        (t (fn2-env-held-offset-from (+ 1 w) offset log image))))

(local (defthm fn2-env-nth-0 (equal (nth 0 l) (car l))))
(local (defthm fn2-env-nth-1+ (implies (natp n) (equal (nth (+ 1 n) l) (nth n (cdr l))))))
(local (defthm fn2-env-len-cdr (implies (consp l) (equal (len l) (+ 1 (len (cdr l)))))))
(defthm fn2-env-take-index-bound
  (let ((w (fn2-env-take-index slot gen log)))
    (implies w (and (natp w) (< w (len log)) (fn2-dev-takep (nth w log))
                    (equal (nth 1 (nth w log)) slot) (equal (nth 2 (nth w log)) gen))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-env-take-index slot gen log)
           :in-theory '(fn2-env-take-index natp fn2-env-nth-0 fn2-env-nth-1+ fn2-env-len-cdr
                        (:type-prescription fn2-env-take-index) (:t len) atom (:e <)))))
(local (in-theory (disable fn2-env-nth-0 fn2-env-nth-1+ fn2-env-len-cdr)))
(defthm fn2-env-answer-resultp
  (implies (fn2-dev-answer slot gen l)
           (and (consp (fn2-dev-answer slot gen l)) (fn2-dev-resultp (car (fn2-dev-answer slot gen l)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-dev-answer slot gen l) :in-theory '(fn2-dev-answer atom))))

;; THE FENCE'S RISE. A write answered done in full before a fence is taken
;; whose first answer is a successful fence result is fenced.
(defthm fn2-env-fence-after-of-later
  (implies (fn2-dev-fence-after-p y) (fn2-dev-fence-after-p (append x y)))
  :hints (("Goal" :induct (len x) :in-theory (disable fn2-dev-answer fn2-dev-done-answer-p))))
(local (defthm fn2-env-cdr-append
  (implies (consp x) (equal (cdr (append x y)) (append (cdr x) y)))))
(defthm fn2-env-fenced-by-later-fence
  (implies (and (fn2-env-done-write-p w x) (fn2-dev-fence-after-p y) (true-listp y))
           (fn2-dev-fenced-write-p w (append x y)))
  :hints (("Goal" :in-theory '(fn2-env-done-write-p fn2-dev-fenced-write-p fn2-env-nth-append-low fn2-env-nthcdr-append
                                fn2-env-done-answer-append fn2-dev-answer-append fn2-env-len-append fn2-env-cdr-append
                                fn2-env-fence-after-of-later fn2-env-done-answer-nil natp nfix fix
                                true-listp-append (:type-prescription true-listp-append)
                                (:type-prescription len) (:type-prescription fn2-dev-answer) (:type-prescription binary-append))
           :cases ((consp (fn2-dev-answer (nth 1 (nth w x)) (nth 2 (nth w x)) (nthcdr (+ 1 w) x)))))))
(local (defthm fn2-env-nthcdr-at
  (implies (and (natp n) (< n (len l)))
           (and (consp (nthcdr n l)) (equal (car (nthcdr n l)) (nth n l))
                (equal (cdr (nthcdr n l)) (nthcdr (+ 1 n) l))))
  :rule-classes nil))
(local (defthm fn2-env-append-take-nthcdr
  (implies (<= (nfix n) (len l)) (equal (append (take n l) (nthcdr n l)) l))))
(defthm fn2-env-pool-octets-len
  (implies (and (natp n) (natp addr) (<= (+ addr n) (fn2-pool-data-length fn2-pool)))
           (equal (len (fn2-env-pool-octets n addr fn2-pool)) n))
  :hints (("Goal" :induct (fn2-env-pool-octets n addr fn2-pool) :in-theory (enable fn2-env-pool-octets))))
(defun fn2-env-ops-op (s fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
      (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops) (fn2-ops-kind s fn2-ops)
            (fn2-ops-owner-kind s fn2-ops) (fn2-ops-owner-slot s fn2-ops) (fn2-ops-owner-gen s fn2-ops)
            (fn2-ops-range-slot s fn2-ops) (fn2-ops-range-gen s fn2-ops)
            (fn2-ops-range-off s fn2-ops) (fn2-ops-range-len s fn2-ops)
            (fn2-ops-storage-offset s fn2-ops) (fn2-ops-fua s fn2-ops)
            (fn2-ops-c0-posted s fn2-ops) (fn2-ops-c0-harvested s fn2-ops) (fn2-ops-c0-event s fn2-ops)
            (fn2-ops-c0-outcome s fn2-ops) (fn2-ops-c0-count s fn2-ops)
            (fn2-ops-may-release s fn2-ops) (fn2-ops-c1-posted s fn2-ops))
    (list nil)))
(defun fn2-env-post-accepted-p (cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (let ((tail (fn2-ops-post-tail fn2-ops)) (n (fn2-ops-post-count fn2-ops))
        (capacity (fn2-ops-posted-fifo-length fn2-ops)))
    (and (fn2-post-eligiblep cell slot gen fn2-ops)
         (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
         (< tail capacity) (< n capacity) (< n *fn2-u60-max*)
         (< capacity 1152921504606846976))))
(defun fn2-env-op-posted (op evkind outcome count)
  ; OP with its terminal cell posted (EVKIND OUTCOME COUNT), unharvested
  (declare (xargs :verify-guards nil))
  (update-nth 13 1 (update-nth 14 0 (update-nth 15 evkind (update-nth 16 outcome (update-nth 17 count op))))))
(defun fn2-env-op-c1-posted (op)
  ; OP with its release cell posted
  (declare (xargs :verify-guards nil))
  (update-nth 19 1 op))
(defthm fn2-env-nth-op-c1-posted
  (implies (and (natp i) (< i 19)) (equal (nth i (fn2-env-op-c1-posted op)) (nth i op))))
(defthm fn2-env-j5-taken-op-c1-posted
  ; the take and its first answer read no release field
  (equal (fn2-env-j5-taken (fn2-env-op-c1-posted op) slot log) (fn2-env-j5-taken op slot log))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-taken fn2-env-nth-op-c1-posted (:e natp) (:e <))
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-event-ok-of-c1-posted
  (equal (fn2-env-j5-event-ok (fn2-env-op-c1-posted op)) (fn2-env-j5-event-ok op))
  :hints (("Goal" :in-theory (enable fn2-env-j5-event-ok))))
(defthm fn2-env-j5-event-ok-of-posted
  (implies (and (equal evkind *fn2-event-write-result*) (<= count (nth 10 op)))
           (fn2-env-j5-event-ok (fn2-env-op-posted op evkind outcome count)))
  :hints (("Goal" :in-theory (enable fn2-env-j5-event-ok))))
(in-theory (disable fn2-env-op-c1-posted))
(defthm fn2-env-take-index-append-result
  (implies (not (fn2-dev-takep r))
           (equal (fn2-env-take-index s g (append log (list r)))
                  (fn2-env-take-index s g log)))
  :hints (("Goal" :induct (fn2-env-take-index s g log)
           :in-theory '(fn2-env-take-index binary-append car-cons cdr-cons atom (:e fn2-dev-takep) (:e fn2-env-take-index))
           :expand ((append log (list r)) (fn2-env-take-index s g (append log (list r)))
                    (fn2-env-take-index s g (list r))))))
(defthm fn2-env-answer-append-result
  (equal (fn2-dev-answer s g (append l (list r)))
         (if (fn2-dev-answer s g l)
             (append (fn2-dev-answer s g l) (list r))
           (and (fn2-dev-resultp r) (equal (nth 1 r) s) (equal (nth 2 r) g) (list r))))
  :hints (("Goal" :in-theory '(fn2-dev-answer-append fn2-dev-answer atom (:e fn2-dev-answer) car-cons cdr-cons))))
(local (defthm fn2-env-nthcdr-append-list
  (implies (and (natp n) (<= n (len x)))
           (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))))
(local (defthm fn2-env-car-append (implies (consp x) (equal (car (append x y)) (car x)))))
(defthm fn2-env-j5-taken-other-result
  (let ((r (list :result slot gen evkind outcome count)))
    (implies (and (fn2-env-j5-taken op s log) (true-listp log)
                  (not (and (equal s slot) (equal (nth 1 op) gen))))
             (fn2-env-j5-taken op s (append log (list r)))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append-result fn2-env-answer-append-result
                            fn2-env-nthcdr-append-list fn2-env-car-append fn2-env-consp-append)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take))
           :use ((:instance fn2-env-take-index-bound (slot s) (gen (nth 1 op)))))))
(defthm fn2-env-j5-taken-posted-result
  (let ((r (list :result slot gen evkind outcome count)))
    (implies (and (fn2-env-j5-taken op slot log) (true-listp log)
                  (equal (nth 1 op) gen) (equal (nth 2 op) *fn2-op-phase-submitted*) (equal (nth 13 op) 0))
             (fn2-env-j5-taken (fn2-env-op-posted op evkind outcome count) slot (append log (list r)))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append-result fn2-env-answer-append-result
                            fn2-env-nthcdr-append-list fn2-env-car-append fn2-env-consp-append fn2-env-op-posted)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take))
           :use ((:instance fn2-env-take-index-bound (gen (nth 1 op)))))))
; D26: one lemma per cell (refused, terminal, release), each opening
; fn2-post-result with its cell known (4.2 s -> 2.6 s together)
(defthm fn2-env-ops-op-of-post-refused
  (implies (not (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
           (equal (fn2-env-ops-op s (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
                  (fn2-env-ops-op s fn2-ops)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize) :do-not-induct t
           :in-theory (e/d (fn2-post-result fn2-count-stray fn2-env-ops-op fn2-env-post-accepted-p)
                           (fn2-post-eligiblep fn2-post-payloadp nth)))))
(defthm fn2-env-ops-op-of-post-cell0
  (implies (and (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops) (equal cell 0))
           (equal (fn2-env-ops-op s (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
                  (if (equal s slot) (fn2-env-op-posted (fn2-env-ops-op s fn2-ops) evkind outcome count)
                    (fn2-env-ops-op s fn2-ops))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize) :do-not-induct t
           :in-theory (e/d (fn2-post-result fn2-env-ops-op fn2-env-post-accepted-p fn2-env-op-posted update-nth)
                           (fn2-post-eligiblep fn2-post-payloadp nth)))))
(defthm fn2-env-ops-op-of-post-cell1
  (implies (and (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops) (not (equal cell 0)))
           (equal (fn2-env-ops-op s (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
                  (if (equal s slot) (fn2-env-op-c1-posted (fn2-env-ops-op s fn2-ops)) (fn2-env-ops-op s fn2-ops))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize) :do-not-induct t
           :in-theory (e/d (fn2-post-result fn2-env-ops-op fn2-env-post-accepted-p fn2-env-op-c1-posted update-nth)
                           (fn2-post-eligiblep fn2-post-payloadp nth)))))
(defthm fn2-env-ops-op-of-post-result
  ; an accepted post sets the op's terminal cell (cell 0) or its release cell
  (equal (fn2-env-ops-op s (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
         (if (and (equal s slot)
                  (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
             (if (equal cell 0)
                 (fn2-env-op-posted (fn2-env-ops-op s fn2-ops) evkind outcome count)
               (fn2-env-op-c1-posted (fn2-env-ops-op s fn2-ops)))
           (fn2-env-ops-op s fn2-ops)))
  :hints (("Goal" :in-theory '(fn2-env-ops-op-of-post-refused fn2-env-ops-op-of-post-cell0 fn2-env-ops-op-of-post-cell1)
           :do-not-induct t
           :cases ((not (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
                   (and (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops) (equal cell 0))
                   (and (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)
                        (not (equal cell 0)))))))
(in-theory (disable fn2-env-ops-op-of-post-refused fn2-env-ops-op-of-post-cell0 fn2-env-ops-op-of-post-cell1))
(defthm fn2-env-post-count-of-post-result
  (equal (fn2-ops-post-count (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
         (if (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)
             (+ 1 (fn2-ops-post-count fn2-ops))
           (fn2-ops-post-count fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-post-result fn2-count-stray fn2-env-post-accepted-p fn2-ops-post-count
                            update-fn2-ops-stray update-fn2-ops-posted-fifoi update-fn2-ops-post-tail
                            update-fn2-ops-post-count update-nth-array)
                           (fn2-post-eligiblep fn2-post-payloadp nth update-nth)))))
(defthm fn2-env-take-append-low
  (implies (and (natp n) (<= n (len x))) (equal (take n (append x y)) (take n x))))
(defthm fn2-env-nth-op-posted
  (implies (and (natp i) (or (< i 13) (< 17 i))) (equal (nth i (fn2-env-op-posted op evkind outcome count)) (nth i op)))
  :hints (("Goal" :in-theory (enable fn2-env-op-posted))))
(in-theory (disable fn2-env-op-posted))
(defun fn2-env-post-log (p log r)
  ; the device log after a post: R appended iff the post was accepted on cell 0
  (declare (xargs :verify-guards nil))
  (if p (append log (list r)) log))
(defmacro fn2-env-pr-ops () '(fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c)))
(defun fn2-env-post-ok (cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)
  ; the post was accepted on cell 0: the device log gains its result
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (and (equal cell 0) (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)))
(defmacro fn2-env-pr-p () '(fn2-env-post-ok cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c)))
(defmacro fn2-env-pr-log () '(fn2-env-post-log (fn2-env-pr-p) log (list :result slot gen evkind outcome count)))
(in-theory (disable fn2-env-post-ok fn2-env-post-log))
(defthm fn2-env-not-takep-result
  (not (fn2-dev-takep (list :result slot gen evkind outcome count)))
  :hints (("Goal" :in-theory (enable fn2-dev-takep))))

;; J5 ACROSS :TAKE. The device takes the outbox head: the ack moves that op
;; from queued to its ack phase (submitted for a completion kind), and a
;; non-completion kind is finished at once (FN2-ENV-TAKE-OP); every other
;; op and every other child's reader is unchanged (FN2-ENV-TAKE-FRAMES). The
;; log gains the take, so the taken op's first take is the new last entry
;; (FN2-ENV-J5-TAKEN-TAKE) and every other op's take and answer stay
;; (FN2-ENV-J5-TAKEN-OTHER-TAKE). A taken fence follows the writes its rise
;; fences by J2 (FN2-ENV-FENCE-PREFIX-OF-J2).
(defthm fn2-env-outbox-ack-1-head
  (implies (equal (mv-nth 0 (fn2-outbox-ack 1 fn2-ops)) :ok)
           (let ((h (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops))
                 (g (fn2-ops-out-geni (fn2-ops-out-head fn2-ops) fn2-ops)))
             (and (natp h) (< h (fn2-ops-rows fn2-ops))
                  (equal (fn2-ops-gen h fn2-ops) g)
                  (equal (fn2-ops-phase h fn2-ops) *fn2-op-phase-queued*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-outbox-ack fn2-outbox-prefixp fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
           :expand ((fn2-outbox-prefixp 1 (fn2-ops-out-head fn2-ops) fn2-ops)))))
(defthm fn2-env-ops-op-of-outbox-ack-1
  (implies (and (fn2-opsp fn2-ops) (equal (mv-nth 0 (fn2-outbox-ack 1 fn2-ops)) :ok))
           (equal (fn2-env-ops-op s (mv-nth 1 (fn2-outbox-ack 1 fn2-ops)))
                  (let ((h (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops)))
                    (if (equal s h)
                        (update-nth 2 (fn2-op-ack-phase (nth 3 (fn2-env-ops-op h fn2-ops))) (fn2-env-ops-op s fn2-ops))
                      (fn2-env-ops-op s fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-outbox-ack fn2-outbox-prefixp fn2-op-phase-code fn2-op-handle-code fn2-op-slotp
                            fn2-outbox-submit-prefix fn2-env-ops-op)
                           (fn2-op-ack-phase fn2-opsp))
           :expand ((fn2-outbox-prefixp 1 (fn2-ops-out-head fn2-ops) fn2-ops)
                    (fn2-outbox-submit-prefix 1 fn2-ops)))))
(defthm fn2-env-outbox-peek-0
  (implies (and (fn2-opsp fn2-ops) (equal (mv-nth 0 (fn2-outbox-peek 0 fn2-ops)) :ok))
           (and (equal (mv-nth 1 (fn2-outbox-peek 0 fn2-ops)) (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops))
                (equal (mv-nth 2 (fn2-outbox-peek 0 fn2-ops)) (fn2-ops-out-geni (fn2-ops-out-head fn2-ops) fn2-ops))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-outbox-peek) (fn2-opsp)))))
(defthm fn2-env-ops-op-of-op-finish-other
  (implies (and (fn2-opsp fn2-ops) (not (equal s h)))
           (equal (fn2-env-ops-op s (mv-nth 1 (fn2-op-finish h g fn2-ops))) (fn2-env-ops-op s fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-finish fn2-op-recycle fn2-ops-clear-row fn2-op-phase-code fn2-op-handle-code
                            fn2-op-slotp fn2-env-ops-op)
                           (fn2-opsp)))))
(defthm fn2-env-ops-op-of-op-finish-self
  (implies (fn2-opsp fn2-ops)
           (let ((o (fn2-env-ops-op h (mv-nth 1 (fn2-op-finish h g fn2-ops)))))
             (or (equal o (fn2-env-ops-op h fn2-ops))
                 (member-equal (nth 2 o) (list *fn2-op-phase-free* *fn2-op-phase-retired*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-finish fn2-op-recycle fn2-ops-clear-row fn2-op-phase-code fn2-op-handle-code
                            fn2-op-slotp fn2-env-ops-op)
                           (fn2-opsp)))))
;; THE HARVEST'S OPS STEP (fn2-harvest-next, then fn2-op-finish): the
;; harvested slot is the posted head's, every other op is kept, and a
;; terminal cell harvested from an op with no release cell leaves it done,
;; which fn2-op-finish recycles while the free and retired counts have room.
(defun fn2-env-op-harvested (cell phase op)
  ; OP with cell CELL harvested and its phase PHASE
  (declare (xargs :verify-guards nil))
  (update-nth 2 phase (if (equal cell 0) (update-nth 14 1 op) op)))
(defthm fn2-env-peek-posted-cell
  (let ((pk (fn2-ops-peek-posted fn2-ops)))
    (implies (eq (mv-nth 0 pk) t)
             (and (fn2-op-slotp (mv-nth 1 pk) fn2-ops) (unsigned-byte-p 1 (mv-nth 2 pk))
                  (if (equal (mv-nth 2 pk) 0)
                      (and (equal (fn2-ops-c0-posted (mv-nth 1 pk) fn2-ops) 1)
                           (equal (fn2-ops-c0-harvested (mv-nth 1 pk) fn2-ops) 0))
                    (equal (fn2-ops-c1-posted (mv-nth 1 pk) fn2-ops) 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-ops-peek-posted))))
(defthm fn2-env-ops-op-of-harvest-next
  (let ((hn (fn2-harvest-next fn2-ops)))
    (equal (fn2-env-ops-op s (mv-nth 4 hn))
           (if (and (eq (mv-nth 0 hn) t) (equal s (mv-nth 1 hn)))
               (fn2-env-op-harvested (mv-nth 3 hn) (fn2-ops-phase s (mv-nth 4 hn)) (fn2-env-ops-op s fn2-ops))
             (fn2-env-ops-op s fn2-ops))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-harvest-next fn2-ops-latch-peer fn2-env-ops-op fn2-env-op-harvested update-nth)
                           (fn2-op-harvest-phase fn2-ops-peek-posted nth))
           :use ((:instance fn2-env-peek-posted-cell)))))
(defthm fn2-env-harvest-next-head
  ; the harvested slot, generation and cell are the posted head's
  (let ((hn (fn2-harvest-next fn2-ops)) (pk (fn2-ops-peek-posted fn2-ops)))
    (and (equal (mv-nth 0 hn) (mv-nth 0 pk))
         (implies (eq (mv-nth 0 pk) t)
                  (and (equal (mv-nth 1 hn) (mv-nth 1 pk)) (equal (mv-nth 3 hn) (mv-nth 2 pk))
                       (equal (mv-nth 2 hn) (fn2-ops-gen (mv-nth 1 pk) fn2-ops))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-harvest-next) (fn2-ops-peek-posted fn2-op-harvest-phase fn2-ops-latch-peer)))))
(defthm fn2-env-harvest-phase-done
  ; a terminal cell harvested from an op with no release cell finishes it
  (let* ((hn (fn2-harvest-next fn2-ops)) (s (mv-nth 1 hn)))
    (implies (and (eq (mv-nth 0 hn) t) (equal (mv-nth 3 hn) 0)
                  (equal (fn2-ops-c1-posted s fn2-ops) 0)
                  (not (equal (fn2-ops-kind s fn2-ops) *fn2-action-send*)))
             (equal (fn2-ops-phase s (mv-nth 4 hn)) *fn2-op-phase-done*)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-harvest-next fn2-ops-latch-peer fn2-op-harvest-phase) (fn2-ops-peek-posted)))))
(defthm fn2-env-op-finish-done
  ; finishing a done op at its generation recycles it
  (implies (and (fn2-opsp fn2-ops) (fn2-op-slotp h fn2-ops) (equal g (fn2-ops-gen h fn2-ops))
                (equal (fn2-ops-phase h fn2-ops) *fn2-op-phase-done*)
                ;; the free and retired counts have room (FN2-OPS-SEMANTICP bounds them by the rows)
                (not (equal (fn2-ops-free-count fn2-ops) *fn2-none*))
                (not (equal (fn2-ops-retired-count fn2-ops) *fn2-none*)))
           (and (member-equal (mv-nth 0 (fn2-op-finish h g fn2-ops)) '(:ok :retired))
                (member-equal (nth 2 (fn2-env-ops-op h (mv-nth 1 (fn2-op-finish h g fn2-ops))))
                              (list *fn2-op-phase-free* *fn2-op-phase-retired*))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-finish fn2-op-recycle fn2-ops-clear-row fn2-op-phase-code fn2-op-handle-code
                            fn2-op-slotp fn2-env-ops-op)
                           (fn2-opsp)))))
(defthm fn2-env-outbox-ack-refused
  (implies (not (equal (mv-nth 0 (fn2-outbox-ack n fn2-ops)) :ok))
           (equal (mv-nth 1 (fn2-outbox-ack n fn2-ops)) fn2-ops))
  :hints (("Goal" :in-theory (enable fn2-outbox-ack))))
(defthm fn2-env-outbox-ack-1-head-op
  (implies (equal (mv-nth 0 (fn2-outbox-ack 1 fn2-ops)) :ok)
           (let ((o (fn2-env-ops-op (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops) fn2-ops)))
             (and (nth 0 o) (equal (nth 1 o) (fn2-ops-out-geni (fn2-ops-out-head fn2-ops) fn2-ops))
                  (equal (nth 2 o) *fn2-op-phase-queued*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-ops-op nth-0-cons nth-add1 (:e zp) (:e nth) car-cons cdr-cons
                                               (:e binary-+) (:e equal) zp nth)
                                             (theory 'minimal-theory))
           :use fn2-env-outbox-ack-1-head)))
(defthm fn2-env-take-index-append
  (equal (fn2-env-take-index s g (append log (list e)))
         (or (fn2-env-take-index s g log)
             (and (fn2-dev-takep e) (equal (nth 1 e) s) (equal (nth 2 e) g) (len log))))
  :hints (("Goal" :induct (fn2-env-take-index s g log)
           :in-theory '(fn2-env-take-index binary-append car-cons cdr-cons atom len (:e fn2-env-take-index) fix
                        (:type-prescription fn2-env-take-index) (:e len) (:e binary-append))
           :expand ((append log (list e)) (fn2-env-take-index s g (append log (list e)))
                    (fn2-env-take-index s g (list e))))))
(defthm fn2-env-j5-taken-other-take
  (implies (and (fn2-env-j5-taken op s log) (true-listp log) (fn2-dev-takep e) (not (equal s (nth 1 e))))
           (fn2-env-j5-taken op s (append log (list e))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append fn2-env-answer-append-result
                            fn2-env-nthcdr-append-list fn2-env-car-append fn2-env-consp-append)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take fn2-dev-takep))
           :use ((:instance fn2-env-take-index-bound (slot s) (gen (nth 1 op)))))))
(defthm fn2-env-nthcdr-len-append
  (implies (true-listp log) (equal (nthcdr (+ 1 (len log)) (append log (list e))) nil)))
(defthm fn2-env-answer-of-nil (equal (fn2-dev-answer s g nil) nil))
(defthm fn2-env-j5-taken-take
  (implies (and (fn2-env-j5-taken o slot log) (true-listp log) (equal (nth 2 o) *fn2-op-phase-queued*)
                (fn2-dev-takep e) (equal (nth 1 e) slot) (equal (nth 2 e) (nth 1 o)))
           (and (fn2-env-j5-taken (update-nth 2 *fn2-op-phase-submitted* o) slot (append log (list e)))
                (equal (fn2-env-take-index slot (nth 1 o) (append log (list e))) (len log))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append fn2-env-nthcdr-len-append fn2-env-answer-of-nil)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take fn2-dev-takep)))))
(defthm fn2-env-nth-len-append (equal (nth (len x) (append x (list e))) e))
(defthm fn2-env-take-len-true-list (implies (true-listp x) (equal (take (len x) x) x)))
(defun fn2-env-log+ (log e)
  ; the device log after a step whose entry is E (nil: none)
  (declare (xargs :verify-guards nil))
  (append log (if e (list e) nil)))
(defmacro fn2-env-tk-e () '(mv-nth 0 (fn2-env-take nil image c)))
(defmacro fn2-env-tk-c () '(mv-nth 1 (fn2-env-take nil image c)))
(in-theory (disable fn2-env-log+))
(defthm fn2-env-pool-octets-addr-natp
  (implies (consp (fn2-env-pool-octets n addr fn2-pool)) (natp addr))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((fn2-env-pool-octets n addr fn2-pool)))))
(defthm fn2-env-j5-taken-queued-untaken
  (implies (and (fn2-env-j5-taken op slot log) (equal (nth 2 op) *fn2-op-phase-queued*) (equal (nth 1 op) g))
           (not (fn2-env-take-index slot g log)))
  :hints (("Goal" :in-theory '(fn2-env-j5-taken (:e equal)))))
;; J5 ACROSS THE FRAME STEPS. :accept-result, :clock and :signal update the
;; ops table keeping every op (FN2-ENV-OPS-KEPT: an op is unchanged, or an
;; accept keeps its head fields), and an op the row could account for is
;; never an accept, so J5 and J6 hold over the kept table
;; (FN2-ENV-J5-ROWS-KEPT). :epoch writes the extents child and :loan-write
;; the pool, which J5 does not read; J6 reads the pool, so J6 across
;; :loan-write is FN2-POOL-CONSERVATION's (the loan's range is disjoint from
;; the roles').
(defun fn2-env-op-kept (o2 o)
  ; O2 is O, or O is an accept whose head fields (validity .. owner-gen) and
  ; release fields O2 keeps
  (declare (xargs :verify-guards nil))
  (or (equal o2 o)
      (and (equal (nth 3 o) *fn2-action-accept*)
           (equal (nth 0 o2) (nth 0 o)) (equal (nth 1 o2) (nth 1 o)) (equal (nth 2 o2) (nth 2 o))
           (equal (nth 3 o2) (nth 3 o)) (equal (nth 4 o2) (nth 4 o)) (equal (nth 5 o2) (nth 5 o))
           (equal (nth 6 o2) (nth 6 o)) (equal (nth 18 o2) (nth 18 o)) (equal (nth 19 o2) (nth 19 o)))))(in-theory (disable fn2-env-op-kept))
(defthm fn2-env-ops-op-accept-kind
  (implies (and (fn2-op-slotp slot fn2-ops) (equal (fn2-ops-kind slot fn2-ops) *fn2-action-accept*))
           (equal (nth 3 (fn2-env-ops-op slot fn2-ops)) *fn2-action-accept*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-ops-op fn2-op-slotp))))
(defthm fn2-env-ops-op-of-peer-sets
  (and (equal (fn2-env-ops-op s (fn2-ops-set-peer-family i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-port i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w0 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w1 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w2 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w3 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-count-stray y)) (fn2-env-ops-op s y)))
  :hints (("Goal" :in-theory (enable fn2-env-ops-op fn2-ops-set-peer-family fn2-ops-set-peer-port fn2-ops-set-peer-w0
                                     fn2-ops-set-peer-w1 fn2-ops-set-peer-w2 fn2-ops-set-peer-w3 fn2-count-stray
                                     update-fn2-ops-peer-family$ai update-fn2-ops-peer-port$ai update-fn2-ops-peer-w0$ai
                                     update-fn2-ops-peer-w1$ai update-fn2-ops-peer-w2$ai update-fn2-ops-peer-w3$ai
                                     update-fn2-ops-stray update-nth-array))))
(defthm fn2-env-car-update-nth
  (equal (car (update-nth n v l)) (if (zp n) v (car l)))
  :rule-classes nil
  :hints (("Goal" :expand ((update-nth n v l)))))
(defthm fn2-env-car-op-posted
  (equal (car (fn2-env-op-posted op evkind outcome count)) (car op))
  :hints (("Goal" :in-theory (enable fn2-env-op-posted)
           :use ((:instance fn2-env-car-update-nth (n 13) (v 1)
                            (l (update-nth 14 0 (update-nth 15 evkind (update-nth 16 outcome (update-nth 17 count op))))))
                 (:instance fn2-env-car-update-nth (n 14) (v 0)
                            (l (update-nth 15 evkind (update-nth 16 outcome (update-nth 17 count op)))))
                 (:instance fn2-env-car-update-nth (n 15) (v evkind) (l (update-nth 16 outcome (update-nth 17 count op))))
                 (:instance fn2-env-car-update-nth (n 16) (v outcome) (l (update-nth 17 count op)))
                 (:instance fn2-env-car-update-nth (n 17) (v count) (l op))))))
(defthm fn2-env-ops-op-of-post-accept-result
  (fn2-env-op-kept (fn2-env-ops-op s (fn2-post-accept-result slot gen outcome reason cap-index cap-nonce family port
                                                             w0 w1 w2 w3 fn2-ops))
                   (fn2-env-ops-op s fn2-ops))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-post-accept-result fn2-env-op-kept fn2-env-ops-op-of-peer-sets
                            fn2-env-ops-op-of-post-result fn2-env-nth-op-posted fn2-env-car-op-posted)
                           (fn2-post-result fn2-peer-recordp fn2-env-ops-op fn2-env-op-posted fn2-count-stray
                            fn2-ops-set-peer-family fn2-ops-set-peer-port fn2-ops-set-peer-w0
                            fn2-ops-set-peer-w1 fn2-ops-set-peer-w2 fn2-ops-set-peer-w3))
           :use ((:instance fn2-env-ops-op-accept-kind)))))
(defthm fn2-env-ops-op-of-post-clock-signal
  (and (equal (fn2-env-ops-op s (fn2-post-clock mono real flags fn2-ops)) (fn2-env-ops-op s fn2-ops))
       (equal (fn2-env-ops-op s (fn2-post-signal bits fn2-ops)) (fn2-env-ops-op s fn2-ops)))
  :hints (("Goal" :in-theory (e/d (fn2-env-ops-op fn2-post-clock fn2-post-signal)
                                  (binary-logior binary-logand fn2-saturating-inc60 unsigned-byte-p)))))
(defthm fn2-env-op-kept-refl (fn2-env-op-kept o o) :hints (("Goal" :in-theory (enable fn2-env-op-kept))))
; An ops update X(fn2-ops) that keeps every op: the core's ops become X's.
(defmacro fn2-env-ops-kept-events (name call)
  ; CALL: the update applied to (fn2-core-ops c), e.g. (fn2-post-signal bits (fn2-core-ops c))
  (let ((from (fn2-columns-sym name "-KEPT-FROM")) (all (fn2-columns-sym name "-KEPT")))
    `(progn
       (defthm ,from
         (fn2-env-ops-kept-from s k ,call c)
         :hints (("Goal" :induct (fn2-env-ops-kept-from s k ,call c)
                  :in-theory '(fn2-env-ops-kept-from fn2-env-op-is-ops-op fn2-env-op-kept-refl
                               fn2-env-ops-op-of-post-accept-result fn2-env-ops-op-of-post-clock-signal))))
       (defthm ,all
         (implies (fn2-corep c) (fn2-env-ops-kept ,call c))
         :hints (("Goal" :in-theory (e/d (fn2-env-ops-kept fn2-env-ops-rows ,from) (fn2-env-ops-kept-from fn2-ops-rows))
                  :use ((:instance fn2-core-ops-type (fn2-core c)))))))))
; J5 reads no child but the machine table, commit-io, ops and (J6) pool: the
; extents and the pool frames.
(defmacro fn2-env-j5-child-frame-events (upd)
  (progn$
    `(progn
       (defthm ,(fn2-columns-sym 'fn2-env-j5-readers (concatenate 'string "-OF-" (symbol-name upd)))
         (and (equal (fn2-env-io u (,upd x c)) (fn2-env-io u c))
              (equal (fn2-env-op s (,upd x c)) (fn2-env-op s c))
              (equal (fn2-env-ops-rows (,upd x c)) (fn2-env-ops-rows c))
              (equal (fn2-env-role-io id role (,upd x c)) (fn2-env-role-io id role c))
              (equal (fn2-env-role-offset id role (,upd x c)) (fn2-env-role-offset id role c))
              (equal (fn2-env-role-written id role f log (,upd x c)) (fn2-env-role-written id role f log c)))
         :hints (("Goal" :in-theory (e/d (fn2-env-io fn2-env-op fn2-env-ops-rows fn2-env-role-io fn2-env-role-offset
                                          fn2-env-role-written)
                                         (fn2-env-written-from)))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-fence (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-fence id op s log (,upd x c)) (fn2-env-j5-fence id op s log c))
         :hints (("Goal" :in-theory (e/d (fn2-env-j5-fence) (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take)))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-op (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-op s id log (,upd x c)) (fn2-env-j5-op s id log c))
         :hints (("Goal" :in-theory (e/d (fn2-env-j5-op) (fn2-env-op fn2-env-io fn2-env-j5-fence)))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-ops (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-ops s k id log (,upd x c)) (fn2-env-j5-ops s k id log c))
         :hints (("Goal" :induct (fn2-env-j5-ops s k id log c) :in-theory (disable fn2-env-j5-op))))
       (defthm ,(fn2-columns-sym 'fn2-env-owned-fences (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-owned-fences s k id (,upd x c)) (fn2-env-owned-fences s k id c))
         :hints (("Goal" :induct (fn2-env-owned-fences s k id c) :in-theory (disable fn2-env-op))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-row (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-row id log (,upd x c)) (fn2-env-j5-row id log c))
         :hints (("Goal" :in-theory (e/d (fn2-env-j5-row fn2-env-j5-roles fn2-env-j5-role fn2-env-role-live)
                                         (fn2-env-j5-ops fn2-env-owned-fences fn2-env-op fn2-env-role-io
                                          fn2-env-role-offset fn2-env-role-written fn2-env-j5-taken fn2-env-take-index
                                          fn2-env-j5-take-ok))))))))
;; J6 ACROSS POOL WRITES. J6 reads a role's 4096 octets at its pool row's
;; base (fn2-env-pool-octets); inside a carved extent of a semantic pool that
;; is the prefix of the extent's logical octets (FN2-ENV-POOL-OCTETS-IN-EXTENT),
;; the octets FN2-CORE-POOL-WRITE-FRAME and FN2-POOL-CONSERVATION speak of.
;; J6P: through the write phases each role's pool row is a workspace or
;; lent row owned by the commit row and at least a unit long. A loan's fill
;; writes only a leased-in row (fn2-pool-adapter-write's input check), so it
;; keeps every role's row and octets (FN2-ENV-FILL-KEEPS-ROLE) and the pool
;; semantic, and :loan-write keeps J5, J6 and J6P (FN2-ENV-J5-ROWS-LOAN-WRITE-STEP).
(defthm fn2-env-pool-octets-is-logical
  (implies (and (natp addr) (<= (+ addr (nfix n)) (fn2-pool-data-length fn2-pool)))
           (equal (fn2-env-pool-octets n addr fn2-pool) (fn2-pool-logical-octets n addr fn2-pool)))
  :hints (("Goal" :induct (fn2-env-pool-octets n addr fn2-pool))))
(defun fn2-env-two-down (k n b)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) (list n b) (fn2-env-two-down (- k 1) (- n 1) (+ 1 b))))
(defthm fn2-env-logical-octets-prefix
  (implies (and (natp k) (natp n) (<= k n))
           (equal (fn2-pool-logical-octets k b fn2-pool) (take k (fn2-pool-logical-octets n b fn2-pool))))
  :hints (("Goal" :induct (fn2-env-two-down k n b))))
(defthm fn2-env-pool-octets-in-extent
  ; inside a carved extent, J6's reader is a prefix of the extent's logical octets
  (implies (and (fn2-pool-semanticp fn2-pool) (natp s) (< s (fn2-pool-rows fn2-pool))
                (natp k) (<= k (fn2-pool-cap s fn2-pool)))
           (equal (fn2-env-pool-octets k (fn2-pool-base s fn2-pool) fn2-pool)
                  (take k (fn2-pool-logical-octets (fn2-pool-cap s fn2-pool) (fn2-pool-base s fn2-pool) fn2-pool))))
  :hints (("Goal" :in-theory '(natp nfix (:type-prescription fn2-pool-base))
           :do-not-induct t
           :use ((:instance fn2-pool-semanticp-row-bounds (i s))
                 (:instance fn2-env-pool-octets-is-logical (n k) (addr (fn2-pool-base s fn2-pool)))
                 (:instance fn2-env-logical-octets-prefix (n (fn2-pool-cap s fn2-pool)) (b (fn2-pool-base s fn2-pool)))))))
(defthm fn2-env-adapter-write-row-extent
  (implies (and (fn2-pool-semanticp p) (natp r) (< r (fn2-pool-rows p))
                (not (equal (fn2-pool-state r p) *fn2-pool-state-leased-in*)))
           (equal (fn2-pool-logical-octets (fn2-pool-cap r p) (fn2-pool-base r p)
                                           (mv-nth 1 (fn2-pool-adapter-write slot gen opslot opgen idx byte p)))
                  (fn2-pool-logical-octets (fn2-pool-cap r p) (fn2-pool-base r p) p)))
  :hints (("Goal" :cases ((equal slot r)) :in-theory (disable fn2-pool-semanticp fn2-pool-logical-octets fn2-pool-adapter-write))
          ("Subgoal 2" :use ((:instance fn2-pool-adapter-write-other-extent (other r) (fn2-pool p))))
          ("Subgoal 1" :in-theory (e/d (fn2-pool-adapter-write fn2-pool-input-code) (fn2-pool-semanticp fn2-pool-logical-octets)))))
(defthm fn2-env-adapter-write-row-meta
  (let ((q (mv-nth 1 (fn2-pool-adapter-write slot gen opslot opgen idx byte p))))
    (and (equal (fn2-pool-state i q) (fn2-pool-state i p))
         (equal (fn2-pool-gen i q) (fn2-pool-gen i p))
         (equal (fn2-pool-owner-slot i q) (fn2-pool-owner-slot i p))))
  :hints (("Goal" :in-theory (enable fn2-pool-adapter-write))))
(defthm fn2-env-row-invariant-leased-out-count
  (implies (and (fn2-pool-row-invariantp n p) (natp i) (< i (nfix n))
                (equal (fn2-pool-state i p) *fn2-pool-state-leased-out*))
           (< 0 (fn2-pool-out-count i p)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-pool-row-invariantp n p)
           :in-theory (union-theories '((:induction fn2-pool-row-invariantp) iff zp nfix natp (:e zp) (:e nfix) (:e equal)
                                        commutativity-of-+ associativity-of-+ unicity-of-0 inverse-of-+ fold-consts-in-+ (:e binary-+) fix)
                                      (theory 'minimal-theory))
           :expand ((fn2-pool-row-invariantp n p)))))
(defthm fn2-env-pool-leased-out-count
  ; a semantic pool's leased-out row has a lease out
  (implies (and (fn2-pool-semanticp p) (natp i) (< i (fn2-pool-rows p))
                (equal (fn2-pool-state i p) *fn2-pool-state-leased-out*))
           (< 0 (fn2-pool-out-count i p)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-pool-semanticp) (fn2-pool-row-invariantp fn2-pool-class-accountsp fn2-pool-retired-slots))
           :use ((:instance fn2-env-row-invariant-leased-out-count (n (fn2-pool-rows p)))))))
(defthm fn2-env-release-out-accepted
  ; the release of a leased-out row at its generation is accepted
  (implies (and (fn2-pool-semanticp p) (natp i) (< i (fn2-pool-rows p))
                (equal (fn2-pool-state i p) *fn2-pool-state-leased-out*) (equal g (fn2-pool-gen i p)))
           (equal (mv-nth 0 (fn2-pool-release-out i g p)) :ok))
  :hints (("Goal" :in-theory (union-theories '(fn2-pool-release-out fn2-pool-handle-code mv-nth car-cons (:e zp) zp
                                               natp (:e equal) (:e natp))
                                             (theory 'minimal-theory))
           :use fn2-env-pool-leased-out-count)))
(defthm fn2-env-pool-octets-of-data
  ; J6's reader reads the pool's octet array alone
  (implies (equal (nth *fn2-pool-datai* q) (nth *fn2-pool-datai* p))
           (equal (fn2-env-pool-octets n addr q) (fn2-env-pool-octets n addr p)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-env-pool-octets n addr p) :in-theory (enable fn2-pool-datai))))
(defthm fn2-env-pool-reserve-keeps
  ; a reservation writes no octet, moves no row, and leaves every row that is
  ; not free as it was
  (let ((q (mv-nth 3 (fn2-pool-reserve class okind oslot ogen p))))
    (and (equal (nth *fn2-pool-datai* q) (nth *fn2-pool-datai* p))
         (equal (fn2-pool-rows q) (fn2-pool-rows p))
         (equal (fn2-pool-base r q) (fn2-pool-base r p))
         (implies (not (equal (fn2-pool-state r p) *fn2-pool-state-free*))
                  (and (equal (fn2-pool-state r q) (fn2-pool-state r p))
                       (equal (fn2-pool-owner-slot r q) (fn2-pool-owner-slot r p))
                       (equal (fn2-pool-cap r q) (fn2-pool-cap r p))
                       (equal (fn2-pool-gen r q) (fn2-pool-gen r p))))))
  ; D26: open only the setters fn2-pool-reserve's put writes and the readers
  ; the statement names; the class lists and the row's other readers stay
  ; closed (8.4 s -> 1.0 s)
  :hints (("Goal" :in-theory (e/d (fn2-pool-reserve fn2-pool-set-state update-fn2-pool-state$ai fn2-pool-state fn2-pool-state$ai
                                   fn2-pool-set-owner-kind update-fn2-pool-owner-kind$ai fn2-pool-set-owner-slot
                                   update-fn2-pool-owner-slot$ai fn2-pool-owner-slot fn2-pool-owner-slot$ai
                                   fn2-pool-set-owner-gen update-fn2-pool-owner-gen$ai fn2-pool-set-out-count
                                   update-fn2-pool-out-count$ai fn2-pool-set-fill update-fn2-pool-fill$ai
                                   fn2-pool-base fn2-pool-base$ai fn2-pool-cap fn2-pool-cap$ai fn2-pool-gen fn2-pool-gen$ai
                                   update-nth-array)
                                  (fn2-pool-next-free fn2-pool-class fn2-pool-out-count fn2-pool-mrefp
                                   fn2-pool-class-headsi fn2-pool-class-countsi fn2-pool-nclasses)))))
(defthm fn2-env-pool-release-keeps
  ; a release writes no octet, moves no row, and leaves every row but a
  ; workspace the releaser owns
  (let ((q (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen p))))
    (and (equal (nth *fn2-pool-datai* q) (nth *fn2-pool-datai* p))
         (equal (fn2-pool-rows q) (fn2-pool-rows p))
         (equal (fn2-pool-base r q) (fn2-pool-base r p))
         (implies (not (equal (fn2-pool-owner-slot r p) oslot))
                  (and (equal (fn2-pool-state r q) (fn2-pool-state r p))
                       (equal (fn2-pool-owner-slot r q) (fn2-pool-owner-slot r p))
                       (equal (fn2-pool-cap r q) (fn2-pool-cap r p))
                       (equal (fn2-pool-gen r q) (fn2-pool-gen r p))))))
  :hints (("Goal" :in-theory (enable fn2-pool-release fn2-pool-workspace-code fn2-pool-ownerp fn2-pool-set-gen update-fn2-pool-gen$ai fn2-pool-gen fn2-pool-gen$ai fn2-pool-set-base update-fn2-pool-base$ai fn2-pool-base fn2-pool-base$ai fn2-pool-set-cap update-fn2-pool-cap$ai fn2-pool-cap fn2-pool-cap$ai fn2-pool-set-state update-fn2-pool-state$ai fn2-pool-state fn2-pool-state$ai fn2-pool-set-owner-kind update-fn2-pool-owner-kind$ai fn2-pool-owner-kind fn2-pool-owner-kind$ai fn2-pool-set-owner-slot update-fn2-pool-owner-slot$ai fn2-pool-owner-slot fn2-pool-owner-slot$ai fn2-pool-set-owner-gen update-fn2-pool-owner-gen$ai fn2-pool-owner-gen fn2-pool-owner-gen$ai fn2-pool-set-lease-op-slot update-fn2-pool-lease-op-slot$ai fn2-pool-lease-op-slot fn2-pool-lease-op-slot$ai fn2-pool-set-lease-op-gen update-fn2-pool-lease-op-gen$ai fn2-pool-lease-op-gen fn2-pool-lease-op-gen$ai fn2-pool-set-lease-off update-fn2-pool-lease-off$ai fn2-pool-lease-off fn2-pool-lease-off$ai fn2-pool-set-lease-len update-fn2-pool-lease-len$ai fn2-pool-lease-len fn2-pool-lease-len$ai fn2-pool-set-out-count update-fn2-pool-out-count$ai fn2-pool-out-count fn2-pool-out-count$ai fn2-pool-set-fill update-fn2-pool-fill$ai fn2-pool-fill fn2-pool-fill$ai fn2-pool-set-hand-to-kind update-fn2-pool-hand-to-kind$ai fn2-pool-hand-to-kind fn2-pool-hand-to-kind$ai fn2-pool-set-hand-to-slot update-fn2-pool-hand-to-slot$ai fn2-pool-hand-to-slot fn2-pool-hand-to-slot$ai fn2-pool-set-hand-to-gen update-fn2-pool-hand-to-gen$ai fn2-pool-hand-to-gen fn2-pool-hand-to-gen$ai fn2-pool-set-next-free update-fn2-pool-next-free$ai fn2-pool-next-free fn2-pool-next-free$ai fn2-pool-set-class update-fn2-pool-class$ai fn2-pool-class fn2-pool-class$ai update-nth-array))))
(defun fn2-env-mk-read-events (fields)
  (declare (xargs :mode :program))
  (if (atom fields) nil
    (let* ((f (car fields))
           (r (fn2-columns-col-name 'fn2-machine f))
           (tr (fn2-columns-col-name 'fn2-commit f)) (ai (fn2-columns-sym tr "$AI")))
      (cons
       `(defthm ,(fn2-columns-sym r "-OF-MK")
          (implies (and (fn2-env-tk b a) (fn2-env-mk b a) (equal (fn2-machine-kind id a) *fn2-commit-kind*))
                   (equal (,r id b) (,r id a)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(fn2-env-tk fn2-env-mk fn2-ctf-dir fn2-machines-directory-keeps
                                          ,r ,(fn2-columns-sym r "-READ-CODE") fn2-commit-table fn2-commit-rows ,tr ,ai)
                                         (theory 'minimal-theory))
                   :do-not-induct t
                   :use ((:instance fn2-ctf-dir-readers)))))
       (fn2-env-mk-read-events (cdr fields))))))
(defun fn2-env-view-keep-1 (views fn hyps out)
  (declare (xargs :mode :program))
  (if (atom views) nil
    (cons `(fn2-with-column-projections (,(car views))
            (defthm ,(fn2-env-rel-name fn (car views))
              (implies (and (,(car views) fn2-core fn2-rel-c0) ,@hyps) (,(car views) ,out fn2-rel-c0))
              :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
                      (and stable-under-simplificationp (fn2-column-view-hint '(,(car views)) clause world)))))
          (fn2-env-view-keep-1 (cdr views) fn hyps out))))
(defun fn2-env-view-keep-events (views fns world)
  ; FN-<VIEW>: FN's producer footprint keeps each VIEW
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (let* ((fn (if (consp (car fns)) (caar fns) (car fns))) (hyps (and (consp (car fns)) (cdar fns)))
           (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
      (append (fn2-env-view-keep-1 views fn hyps out)
              (fn2-env-view-keep-events views (cdr fns) world)))))
(defthm fn2-env-release-children-pool
  (let ((q (mv-nth 1 (fn2-core-release-children slot gen okind oslot ogen p ctl))))
    (or (equal q p) (equal q (mv-nth 1 (fn2-pool-release slot gen okind oslot ogen p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-core-release-children mv-nth (:e mv-nth) car-cons cdr-cons (:e zp) (:e binary-+)))))
(defmacro fn2-env-unit-chain (name call hyps base)
  ; NAME: a chain through CALL keeps the units and pool rows of row I since A
  `(defthm ,name
     (implies (and (fn2-env-j5-unit-kept i a c) ,@hyps)
              (fn2-env-j5-unit-kept i a ,call))
     :hints (("Goal" :in-theory nil
              :use ((:instance ,base) (:instance fn2-env-j5-unit-kept-trans (id i) (a a) (b c) (c ,call)))))))
(defun fn2-env-keeps-ids-events (calls)
  ; each call keeps every id's readability and slot (by TK)
  (declare (xargs :mode :program))
  (if (atom calls) nil
    (let* ((name (car (car calls))) (call (cadr (car calls))) (tk (caddr (car calls))))
      (cons `(defthm ,name
               (and (equal (fn2-commit-idp x ,call) (fn2-commit-idp x c))
                    (equal (fn2-machine-slot x ,call) (fn2-machine-slot x c)))
               :hints (("Goal" :in-theory '(fn2-env-tk-reflexive)
                        :use ((:instance ,tk (fn2-core c) (fn2-rel-c0 c))
                              (:instance fn2-env-read-codes-of-tk (id x) (a c) (b ,call))))))
            (fn2-env-keeps-ids-events (cdr calls))))))
(defun fn2-env-start-j5-rf-uses (rules row cs ch call)
  (declare (xargs :mode :program))
  (if (atom rules) nil
    (cons `(:instance ,(car rules) (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
          (fn2-env-start-j5-rf-uses (cdr rules) row cs ch call))))
(defun fn2-env-call-fn (call)
  (declare (xargs :mode :program))
  (if (eq (car call) 'mv-nth) (car (caddr call)) (car call)))
(defmacro fn2-env-kept-chain (name call hyps uses)
  ; NAME: a chain through CALL keeps J5's evidence of the commit row I since
  ; A; USES give TK, MK, OK and the units and pool rows from C to CALL
  (let ((fn (fn2-env-call-fn call)))
    `(defthm ,name
       (implies (and (fn2-env-j5-kept i a c) (fn2-commit-idp i c) ,@hyps)
                (fn2-env-j5-kept i a ,call))
       :hints (("Goal" :in-theory '(fn2-env-tk-reflexive fn2-env-mk-reflexive fn2-env-ok-reflexive fn2-env-j5-unit-kept-refl
                                    fn2-env-io-view-reflexive fn2-env-pk-reflexive)
                :use ((:instance ,(fn2-env-rel-name fn 'fn2-env-tk) (fn2-core c) (fn2-rel-c0 c))
                      (:instance ,(fn2-env-rel-name fn 'fn2-env-mk) (fn2-core c) (fn2-rel-c0 c))
                      (:instance ,(fn2-env-rel-name fn 'fn2-env-ok) (fn2-core c) (fn2-rel-c0 c))
                      ,@uses
                      (:instance fn2-env-commit-idp-kind (id i) (fn2-core c))
                      (:instance fn2-env-j5-kept-of-parts (id i) (a c) (b ,call))
                      (:instance fn2-env-j5-kept-trans (id i) (a a) (b c) (c ,call))))))))
(defmacro fn2-env-kept-chain-views (name call)
  `(fn2-env-kept-chain ,name ,call nil
     ((:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-io-view) (fn2-core c) (fn2-rel-c0 c))
      (:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-pk) (fn2-core c) (fn2-rel-c0 c))
      (:instance fn2-env-j5-unit-kept-of-views (id i) (a c) (b ,call)))))
;; THE ADMITTED ROW THROUGH ADMISSION. Its own row is left free (refused)
;; or opened at :collect (accepted); every other row keeps its evidence.
(defmacro fn2-env-row-chain (rel name call hyps)
  ; NAME: CALL keeps REL (FN2-ENV-FREE-KEPT or -FREE-TO-COLLECT) of row ID
  ; since A, by its TK, MK and OK footprints
  (let ((fn (fn2-env-call-fn call)))
    `(defthm ,name
       (implies (and (,rel id a c) (fn2-commit-idp id a) ,@hyps) (,rel id a ,call))
       :hints (("Goal" :in-theory '(,rel fn2-env-tk-reflexive fn2-env-mk-reflexive)
                :use ((:instance ,(fn2-env-rel-name fn 'fn2-env-tk) (fn2-core c) (fn2-rel-c0 c))
                      (:instance ,(fn2-env-rel-name fn 'fn2-env-mk) (fn2-core c) (fn2-rel-c0 c))
                      (:instance ,(fn2-env-rel-name fn 'fn2-env-ok) (fn2-core c) (fn2-rel-c0 a))
                      (:instance fn2-env-commit-idp-kind (fn2-core c))
                      (:instance fn2-env-read-codes-of-tk (b ,call) (a c))
                      (:instance fn2-machine-phase-of-tk (b ,call) (a c))
                      (:instance fn2-machine-generation-of-mk (b ,call) (a c))
                      (:instance fn2-machine-cb-fence-live-of-mk (b ,call) (a c))))))))
(defmacro fn2-env-j56-step (name call chain keeps)
  ; NAME: CALL keeps J5, J6 and J6P of every commit row (its kept CHAIN)
  `(defthm ,name
     (implies (fn2-env-j56-row i log c) (fn2-env-j56-row i log ,call))
     :hints (("Goal" :in-theory '(fn2-env-j56-row fn2-env-j5-kept-refl) :do-not-induct t
              :use ((:instance ,chain (a c))
                    (:instance fn2-env-j5-kept-transfer (id i) (a c) (b ,call))
                    (:instance fn2-env-j6ls-kept-transfer (id i) (a c) (b ,call))
                    (:instance ,keeps (x i))
                    (:instance fn2-env-j56-not-idp (c ,call)))))))
(defmacro fn2-env-sem-by-pk (name call)
  `(defthm ,name
     (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp ,call))
     :hints (("Goal" :in-theory '(fn2-env-pk fn2-env-pk-reflexive)
              :use ((:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-pk) (fn2-core c) (fn2-rel-c0 c))
                    (:instance fn2-env-semanticp-of-pool-child (a c) (b ,call)))))))
(defmacro fn2-env-j5e-step (name call)
  `(defthm ,name
     (equal (fn2-env-j5e-row i ,call) (fn2-env-j5e-row i c))
     :hints (("Goal" :in-theory '(fn2-env-tk-reflexive fn2-env-mk-reflexive fn2-env-ok-reflexive fn2-env-pdk-reflexive fn2-env-lk-reflexive)
              :use ((:instance fn2-env-j5e-row-of-views (id i) (a c) (b ,call))
                    (:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-tk) (fn2-core c) (fn2-rel-c0 c))
                    (:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-mk) (fn2-core c) (fn2-rel-c0 c))
                    (:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-ok) (fn2-core c) (fn2-rel-c0 c))
                    (:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-pdk) (fn2-core c) (fn2-rel-c0 c))
                    (:instance ,(fn2-env-rel-name (fn2-env-call-fn call) 'fn2-env-lk) (fn2-core c) (fn2-rel-c0 c)))))))
(defmacro fn2-env-cs-b () '(mv-nth 1 (fn2-commit-start id members first-key mode partner c)))
(defthm fn2-env-ops-op-of-op-finish-gen
  ; finishing an op leaves it, retires it at its generation, or frees it at
  ; the next generation
  (implies (fn2-opsp fn2-ops)
           (let ((o (fn2-env-ops-op h (mv-nth 1 (fn2-op-finish h g fn2-ops)))) (o0 (fn2-env-ops-op h fn2-ops)))
             (or (equal o o0)
                 (and (equal (nth 0 o) (nth 0 o0)) (equal (nth 2 o) *fn2-op-phase-retired*) (equal (nth 1 o) (nth 1 o0)))
                 (and (equal (nth 0 o) (nth 0 o0)) (equal (nth 2 o) *fn2-op-phase-free*) (equal (nth 1 o) (+ 1 (nth 1 o0)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-finish fn2-op-recycle fn2-ops-clear-row fn2-op-phase-code fn2-op-handle-code
                            fn2-op-slotp fn2-env-ops-op)
                           (fn2-opsp)))))
;; FRESHNESS AND LENT-OK ACROSS :TAKE AND :ADMIT. :take acks the outbox
;; head and finishes it unless it is a completion: the taken op is then
;; submitted, done or retired at its generation, or free at the next
;; (FN2-ENV-OPS-OP-OF-OP-FINISH-GEN at the acked table), so every op's head
;; advances (FN2-ENV-OP-HEADS-ADVANCED), the taken incarnation was queued,
;; and no unit changes. :admit writes neither the ops table (FN2-ENV-OK) nor
;; commit-io's operation and loan columns (FN2-ENV-LK).
;; An op's head advanced from O to O2: same validity, and either the same
;; generation with a phase that stays out of free/reserved if it was out, or
;; a newer generation. Every incarnation that began and was issued stays so.
(defun fn2-env-head-advanced (o o2)
  (declare (xargs :verify-guards nil))
  (and (equal (nth 0 o2) (nth 0 o))
       (or (and (equal (nth 1 o2) (nth 1 o))
                (implies (not (member-equal (nth 2 o) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))
                         (not (member-equal (nth 2 o2) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))
           (and (natp (nth 1 o)) (natp (nth 1 o2)) (< (nth 1 o) (nth 1 o2))))))
(defthm fn2-env-head-advanced-refl (fn2-env-head-advanced o o))
(in-theory (disable fn2-env-head-advanced))
(defthm fn2-env-ops-ack-finish-advanced
  ; the outbox head acked, then finished: its head advanced
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (equal (mv-nth 0 (fn2-outbox-ack 1 fn2-ops)) :ok)
                (equal h (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops))
                (natp (nth 1 (fn2-env-ops-op h fn2-ops))))
           (let ((a (mv-nth 1 (fn2-outbox-ack 1 fn2-ops))) (o (fn2-env-ops-op h fn2-ops)))
             (and (fn2-env-head-advanced o (fn2-env-ops-op h a))
                  (fn2-env-head-advanced o (fn2-env-ops-op h (mv-nth 1 (fn2-op-finish h g a)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-env-head-advanced fn2-op-ack-phase fn2-env-ops-op-of-outbox-ack-1)
                           (fn2-env-ops-op fn2-op-finish fn2-outbox-ack fn2-opsp fn2-ops-wfp fn2-action-completionp))
           :use ((:instance fn2-env-outbox-ack-1-head-op)
                 (:instance fn2-env-ops-op-of-op-finish-gen (fn2-ops (mv-nth 1 (fn2-outbox-ack 1 fn2-ops))))))))
(defthm fn2-env-ops-take-cases-advanced
  ; each of :take's three ops outcomes advances every op's head
  (implies (and (fn2-opsp o) (fn2-ops-wfp o)
                (implies (equal (mv-nth 0 (fn2-outbox-ack 1 o)) :ok)
                         (natp (nth 1 (fn2-env-ops-op (fn2-ops-out-sloti (fn2-ops-out-head o) o) o))))
                (let ((a (mv-nth 1 (fn2-outbox-ack 1 o))))
                  (or (equal o2 o)
                      (and (equal (mv-nth 0 (fn2-outbox-ack 1 o)) :ok) (equal (mv-nth 0 (fn2-outbox-peek 0 o)) :ok)
                           (or (equal o2 a)
                               (equal o2 (mv-nth 1 (fn2-op-finish (mv-nth 1 (fn2-outbox-peek 0 o)) (mv-nth 2 (fn2-outbox-peek 0 o)) a))))))))
           (fn2-env-head-advanced (fn2-env-ops-op s o) (fn2-env-ops-op s o2)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((equal s (fn2-ops-out-sloti (fn2-ops-out-head o) o)))
           :in-theory (union-theories '(fn2-env-ops-op-of-outbox-ack-1 fn2-env-ops-op-of-op-finish-other
                                        fn2-env-head-advanced-refl fn2-outbox-ack-preserves-type)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-outbox-peek-0 (fn2-ops o))
                 (:instance fn2-env-ops-ack-finish-advanced (fn2-ops o)
                            (h (fn2-ops-out-sloti (fn2-ops-out-head o) o)) (g (mv-nth 2 (fn2-outbox-peek 0 o))))))))
;; FRESHNESS AND LENT-OK ACROSS THE ISSUES. FN2-ENV-OPS-ADVANCED: every op
;; of the table keeps its head or advances it (FN2-ENV-HEAD-ADVANCED). The
;; op primitives an issue chains (reserve, the reserved op's setters,
;; enqueue, unreserve) keep the rows and generations and move one op out of
;; free or reserved at most (their -HEADS lemmas), so every issue wrapper
;; advances the heads and keeps commit-io; an accepted issue names an op
;; free at its generation before and queued at it after
;; (FN2-ENV-ISSUE-CHILDREN-OK), an issued incarnation.
(defun fn2-env-ops-head (s fn2-ops)
  ; (VALID GEN PHASE) of op slot S
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
      (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops))
    (list nil)))
(defun-sk fn2-env-ops-advanced (a b)
  (forall s (fn2-env-head-advanced (fn2-env-ops-head s a) (fn2-env-ops-head s b))))
(defthm fn2-env-head-advanced-trans
  (implies (and (fn2-env-head-advanced x y) (fn2-env-head-advanced y z)) (fn2-env-head-advanced x z))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-head-advanced))))
(defthm fn2-env-ops-advanced-refl (fn2-env-ops-advanced a a)
  :hints (("Goal" :in-theory '(fn2-env-ops-advanced fn2-env-head-advanced-refl))))
(defthm fn2-env-ops-advanced-trans
  (implies (and (fn2-env-ops-advanced a b) (fn2-env-ops-advanced b c)) (fn2-env-ops-advanced a c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-ops-advanced)
           :use ((:instance fn2-env-ops-advanced-necc (a a) (b b) (s (fn2-env-ops-advanced-witness a c)))
                 (:instance fn2-env-ops-advanced-necc (a b) (b c) (s (fn2-env-ops-advanced-witness a c)))
                 (:instance fn2-env-head-advanced-trans (x (fn2-env-ops-head (fn2-env-ops-advanced-witness a c) a))
                            (y (fn2-env-ops-head (fn2-env-ops-advanced-witness a c) b))
                            (z (fn2-env-ops-head (fn2-env-ops-advanced-witness a c) c)))))))
(in-theory (disable fn2-env-ops-head))
(defthm fn2-env-ops-advanced-step
  ; B advances A at S when the rows stay, and S keeps its generation and
  ; keeps its phase unless it is X, moved out of free or reserved
  (implies (and (equal (fn2-ops-rows b) (fn2-ops-rows a))
                (implies (and (natp s) (< s (fn2-ops-rows a)))
                         (and (equal (fn2-ops-gen s b) (fn2-ops-gen s a))
                              (or (equal (fn2-ops-phase s b) (fn2-ops-phase s a))
                                  (and (equal s x)
                                       (member-equal (fn2-ops-phase s a) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))))
           (fn2-env-head-advanced (fn2-env-ops-head s a) (fn2-env-ops-head s b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-ops-head fn2-env-head-advanced) (fn2-ops-gen fn2-ops-phase fn2-ops-rows)))))
(defthm fn2-env-op-reserve-heads
  ; reservation keeps every generation and the rows, and moves the free
  ; head's phase alone, and only from free
  (let ((b (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (equal (fn2-ops-gen s b) (fn2-ops-gen s o)))
         (implies (and (natp s) (not (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))
                  (and (equal s (fn2-ops-free-head o)) (equal (fn2-ops-phase s o) *fn2-op-phase-free*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-reserve fn2-ops-clear-row fn2-op-slotp)
                           (fn2-op-cleanup-reserve fn2-op-cleanup-kindp fn2-ops-queued fn2-ops-reserved-credits
                            fn2-ops-out-slot-length fn2-ops-free-count unsigned-byte-p fn2-ops-next-free)))))
(defthm fn2-env-op-unreserve-heads
  (let ((b (mv-nth 1 (fn2-op-unreserve slot gen o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (equal (fn2-ops-gen s b) (fn2-ops-gen s o)))
         (implies (and (natp s) (not (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))
                  (and (equal s slot) (equal (fn2-ops-phase s o) *fn2-op-phase-reserved*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-unreserve fn2-ops-clear-row fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)
                           (fn2-ops-queued fn2-ops-reserved-credits fn2-ops-out-slot-length fn2-ops-free-count
                            unsigned-byte-p fn2-ops-next-free fn2-ops-out-tail fn2-ops-out-gen-length fn2-ring-next)))))
(defthm fn2-env-op-enqueue-heads
  (let ((b (mv-nth 1 (fn2-op-enqueue slot gen o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (equal (fn2-ops-gen s b) (fn2-ops-gen s o)))
         (implies (and (natp s) (not (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))
                  (and (equal s slot) (equal (fn2-ops-phase s o) *fn2-op-phase-reserved*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-enqueue fn2-ops-clear-row fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)
                           (fn2-ops-queued fn2-ops-reserved-credits fn2-ops-out-slot-length fn2-ops-free-count
                            unsigned-byte-p fn2-ops-next-free fn2-ops-out-tail fn2-ops-out-gen-length fn2-ring-next)))))
(defthm fn2-env-op-set-range-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-range fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-set-capability-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-capability slot gen index nonce o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-capability fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-set-storage-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-storage slot gen offset fua o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-storage fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-set-cancel-target-heads
  ; a reserved op's field setter keeps every head
  (let ((b (mv-nth 1 (fn2-op-set-cancel-target slot gen tslot tgen o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (and (equal (fn2-ops-gen s b) (fn2-ops-gen s o)) (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-set-cancel-target fn2-op-slotp fn2-op-phase-code fn2-op-handle-code) (unsigned-byte-p)))))
(defthm fn2-env-op-reserve-ok-facts
  ; a reservation takes the free head, free at its generation, and leaves it reserved there
  (let ((r (fn2-op-reserve kind okind oslot ogen principal may-release o)))
    (implies (equal (mv-nth 0 r) :ok)
             (and (equal (mv-nth 1 r) (fn2-ops-free-head o)) (natp (mv-nth 1 r)) (< (mv-nth 1 r) (fn2-ops-rows o))
                  (equal (mv-nth 2 r) (fn2-ops-gen (mv-nth 1 r) o))
                  (equal (fn2-ops-phase (mv-nth 1 r) o) *fn2-op-phase-free*)
                  (equal (fn2-ops-gen (mv-nth 1 r) (mv-nth 3 r)) (mv-nth 2 r))
                  (equal (fn2-ops-phase (mv-nth 1 r) (mv-nth 3 r)) *fn2-op-phase-reserved*))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-reserve fn2-ops-clear-row fn2-op-slotp)
                           (fn2-op-cleanup-reserve fn2-op-cleanup-kindp fn2-ops-queued fn2-ops-reserved-credits
                            fn2-ops-out-slot-length fn2-ops-free-count unsigned-byte-p fn2-ops-next-free)))))
(defthm fn2-env-op-enqueue-ok-facts
  ; an accepted enqueue leaves the op queued at its generation
  (implies (and (natp slot) (equal (mv-nth 0 (fn2-op-enqueue slot gen o)) :ok))
           (and (equal (fn2-ops-gen slot (mv-nth 1 (fn2-op-enqueue slot gen o))) (fn2-ops-gen slot o))
                (equal (fn2-ops-phase slot (mv-nth 1 (fn2-op-enqueue slot gen o))) *fn2-op-phase-queued*)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-enqueue fn2-op-slotp fn2-op-phase-code fn2-op-handle-code)
                           (fn2-ops-queued fn2-ops-reserved-credits fn2-ops-out-slot-length unsigned-byte-p
                            fn2-ops-out-tail fn2-ops-out-gen-length fn2-ring-next)))))
(in-theory (disable fn2-env-op-reserve-ok-facts fn2-env-op-enqueue-ok-facts))
(defmacro fn2-env-ops-advanced-by-heads (name call heads x)
  ; NAME: CALL's ops result advances every op head (its HEADS lemma: the
  ; rows and generations stay, and only X moves, out of free or reserved)
  (let ((w `(fn2-env-ops-advanced-witness o ,call)))
    `(defthm ,name
       (implies (fn2-env-ops-advanced a o) (fn2-env-ops-advanced a ,call))
       :hints (("Goal" :in-theory '((:e member-equal) member-equal car-cons cdr-cons)
                :use ((:instance fn2-env-ops-advanced-trans (a a) (b o) (c ,call))
                      (:instance fn2-env-ops-advanced (a o) (b ,call))
                      (:instance ,heads (s ,w))
                      (:instance fn2-env-ops-advanced-step (a o) (b ,call) (s ,w) (x ,x))))))))
(fn2-env-ops-advanced-by-heads fn2-env-op-reserve-advanced
  (mv-nth 3 (fn2-op-reserve kind okind oslot ogen principal may-release o)) fn2-env-op-reserve-heads (fn2-ops-free-head o))
(fn2-env-ops-advanced-by-heads fn2-env-op-unreserve-advanced (mv-nth 1 (fn2-op-unreserve slot gen o)) fn2-env-op-unreserve-heads slot)
(fn2-env-ops-advanced-by-heads fn2-env-op-enqueue-advanced (mv-nth 1 (fn2-op-enqueue slot gen o)) fn2-env-op-enqueue-heads slot)
(fn2-env-ops-advanced-by-heads fn2-env-op-set-range-advanced
  (mv-nth 1 (fn2-op-set-range slot gen rslot rgen off len o)) fn2-env-op-set-range-heads slot)
(fn2-env-ops-advanced-by-heads fn2-env-op-set-capability-advanced
  (mv-nth 1 (fn2-op-set-capability slot gen index nonce o)) fn2-env-op-set-capability-heads slot)
(fn2-env-ops-advanced-by-heads fn2-env-op-set-storage-advanced
  (mv-nth 1 (fn2-op-set-storage slot gen offset fua o)) fn2-env-op-set-storage-heads slot)
(fn2-env-ops-advanced-by-heads fn2-env-op-set-cancel-target-advanced
  (mv-nth 1 (fn2-op-set-cancel-target slot gen tslot tgen o)) fn2-env-op-set-cancel-target-heads slot)
(defthm fn2-env-issue-children-advanced
  ; an issue advances every op head: it moves one free op through reserved
  ; to queued at its generation, or leaves it reserved or free
  (fn2-env-ops-advanced ops (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                                                          target-slot target-gen okind oslot ogen principal pool ops control)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-issue-children)
                           (fn2-env-ops-advanced fn2-op-reserve fn2-op-unreserve fn2-op-enqueue fn2-op-set-range
                            fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target
                            fn2-core-lease fn2-control-record-stop fn2-core-outbox-ready unsigned-byte-p)))))
(defthm fn2-env-issue-children-ok
  ; an accepted issue names an op free at its generation before and queued
  ; at it after
  (let ((r (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                               target-slot target-gen okind oslot ogen principal pool ops control)))
    (implies (equal (mv-nth 0 r) :ok)
             (and (natp (mv-nth 1 r)) (< (mv-nth 1 r) (fn2-ops-rows ops))
                  (equal (fn2-ops-gen (mv-nth 1 r) ops) (mv-nth 2 r))
                  (equal (fn2-ops-phase (mv-nth 1 r) ops) *fn2-op-phase-free*)
                  (equal (fn2-ops-gen (mv-nth 1 r) (mv-nth 4 r)) (mv-nth 2 r))
                  (equal (fn2-ops-phase (mv-nth 1 r) (mv-nth 4 r)) *fn2-op-phase-queued*))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-issue-children fn2-env-op-set-range-heads fn2-env-op-set-capability-heads
                            fn2-env-op-set-storage-heads fn2-env-op-set-cancel-target-heads
                            fn2-env-op-reserve-ok-facts fn2-env-op-enqueue-ok-facts)
                           (fn2-env-ops-advanced fn2-op-reserve fn2-op-unreserve fn2-op-enqueue fn2-op-set-range
                            fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target
                            fn2-core-lease fn2-control-record-stop fn2-core-outbox-ready unsigned-byte-p
                            fn2-ops-gen fn2-ops-phase fn2-ops-rows fn2-ops-free-head))
           :use ((:instance fn2-env-op-reserve-ok-facts (o ops))))))
(defmacro fn2-env-issue-advanced (name args kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen)
  ; NAME's core result advances every op head and keeps every unit; an
  ; accepted issue names an op free at its generation before, queued after
  (let ((call `(,name ,@args okind oslot ogen principal core))
        (children (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-CHILDREN") name)))
    `(defthm ,(intern-in-package-of-symbol (concatenate 'string "FN2-ENV-" (subseq (symbol-name name) 4 nil) "-ADVANCED") name)
       (and (fn2-env-ops-advanced (fn2-core-ops core) (fn2-core-ops (mv-nth 3 ,call)))
            (equal (nth *fn2-core-commit-io* (mv-nth 3 ,call)) (nth *fn2-core-commit-io* core))
            (implies (equal (mv-nth 0 ,call) :ok)
                     (and (natp (mv-nth 1 ,call)) (< (mv-nth 1 ,call) (fn2-ops-rows (fn2-core-ops core)))
                          (equal (fn2-ops-gen (mv-nth 1 ,call) (fn2-core-ops core)) (mv-nth 2 ,call))
                          (equal (fn2-ops-phase (mv-nth 1 ,call) (fn2-core-ops core)) *fn2-op-phase-free*)
                          (equal (fn2-ops-gen (mv-nth 1 ,call) (fn2-core-ops (mv-nth 3 ,call))) (mv-nth 2 ,call))
                          (equal (fn2-ops-phase (mv-nth 1 ,call) (fn2-core-ops (mv-nth 3 ,call))) *fn2-op-phase-queued*))))
       :rule-classes nil
       :hints (("Goal" :in-theory (e/d (,name ,children fn2-env-issue-children-advanced update-fn2-core-control update-fn2-core-ops update-fn2-core-pool fn2-core-ops)
                                       (fn2-issue-children fn2-env-ops-advanced fn2-ops-gen fn2-ops-phase fn2-ops-rows))
                :use ((:instance fn2-env-issue-children-ok (ops (fn2-core-ops core)) (pool (fn2-core-pool core))
                                 (control (fn2-core-control core)) (okind okind) (oslot oslot) (ogen ogen) (principal principal)
                                 (kind ,kind) (cap-index ,cap-index) (cap-nonce ,cap-nonce) (offset ,offset) (fua ,fua)
                                 (slot ,slot) (gen ,gen) (off ,off) (len ,len) (may-release ,may-release)
                                 (target-slot ,target-slot) (target-gen ,target-gen))))))))
(defconst *fn2-env-fl-commit-callees*
  '(fn2-commit-write+pending+cb-issued+cb-wrote
    fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok
    fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok
    fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason
    fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason
    fn2-commit-write+phase+cb-stage+cb-cursor+outcome+cb-open
    fn2-commit-write+deadline+pending+cb-fence-live fn2-commit-write+phase fn2-commit-mark-abort))
(defun fn2-env-fl-keep-events (fns world)
  ; FN-FN2-ENV-FL: FN keeps FRESHNESS and LENT-OK by its HK and LK frames
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (let* ((fn (car fns)) (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
      (cons `(defthm ,(fn2-env-rel-name fn 'fn2-env-fl)
               (implies (fn2-env-fl log fn2-core) (fn2-env-fl log ,out))
               :hints (("Goal" :in-theory nil
                        :use ((:instance fn2-env-fl-of-hk-lk (a fn2-core) (b ,out))
                              (:instance ,(fn2-env-rel-name fn 'fn2-env-hk) (fn2-rel-c0 fn2-core))
                              (:instance ,(fn2-env-rel-name fn 'fn2-env-lk) (fn2-rel-c0 fn2-core))
                              (:instance fn2-env-hk-reflexive (a fn2-core))
                              (:instance fn2-env-lk-reflexive (a fn2-core))))))
            (fn2-env-fl-keep-events (cdr fns) world)))))
(defmacro fn2-env-issue-fl (name args)
  ; NAME keeps FRESHNESS and LENT-OK; an accepted issue's op is an issued incarnation
  (let* ((call `(,name ,@args okind oslot ogen principal c))
         (adv (intern-in-package-of-symbol (concatenate 'string "FN2-ENV-" (subseq (symbol-name name) 4 nil) "-ADVANCED") name)))
    `(progn
       (defthm ,(intern-in-package-of-symbol (concatenate 'string "FN2-ENV-" (subseq (symbol-name name) 4 nil) "-FL") name)
         (implies (fn2-env-fl log c) (fn2-env-fl log (mv-nth 3 ,call)))
         :hints (("Goal" :in-theory '(fn2-env-fl fn2-env-freshness-of-advanced fn2-env-lent-ok-of-advanced
                                      fn2-env-heads-advanced-of-ops fn2-env-units-kept-of-io)
                  :use ((:instance ,adv (core c))))))
       (defthm ,(intern-in-package-of-symbol (concatenate 'string "FN2-ENV-" (subseq (symbol-name name) 4 nil) "-ISSUED") name)
         (implies (and (fn2-corep c) (fn2-core-wfp c) (equal (car ,call) :ok))
                  (fn2-env-incarnation-ok (mv-nth 1 ,call) (mv-nth 2 ,call) (mv-nth 3 ,call)))
         :hints (("Goal" :in-theory (e/d (fn2-env-incarnation-ok fn2-env-op-is-ops-op fn2-env-ops-op fn2-env-ops-head
                                          fn2-env-head-advanced)
                                         (fn2-ops-gen fn2-ops-phase fn2-ops-rows fn2-env-ops-advanced ,name))
                  :use ((:instance ,adv (core c))
                        (:instance fn2-env-op-gen-natp (s (mv-nth 1 ,call)))
                        (:instance fn2-env-ops-advanced-necc (a (fn2-core-ops c)) (b (fn2-core-ops (mv-nth 3 ,call)))
                                   (s (mv-nth 1 ,call))))))))))
(defun fn2-env-fl-rule-names (fns)
  (declare (xargs :mode :program))
  (if (atom fns) nil (cons (fn2-env-rel-name (car fns) 'fn2-env-fl) (fn2-env-fl-rule-names (cdr fns)))))
(defmacro fn2-env-fl-issuing-arm (arm)
  ; ARM keeps FRESHNESS and LENT-OK: its issue advances the op heads and the
  ; unit it lends names the issued incarnation
  `(make-event
    (value
     '(defthm ,(fn2-env-rel-name arm 'fn2-env-fl)
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-fl log fn2-core))
                 (fn2-env-fl log (mv-nth 4 (,arm id budget fn2-core))))
        :hints (("Goal" :do-not-induct t
                 :in-theory (union-theories '(,arm fn2-env-issue-write-fl fn2-env-issue-fence-fl fn2-env-issue-write-edge-fl
                                              ,@(fn2-env-fl-rule-names (cons 'fn2-core-stop *fn2-env-fl-commit-callees*)))
                                            (theory 'fn2-arm-frame-base))))))))
(defun fn2-env-io-drop-p (x y)
  ; unit Y is unit X, or X with its loan flag cleared
  (declare (xargs :verify-guards nil))
  (or (equal y x) (equal y (update-nth 3 0 x))))
(defthm fn2-env-io-drop-p-refl (fn2-env-io-drop-p x x) :hints (("Goal" :in-theory '(fn2-env-io-drop-p))))
(defthm fn2-env-update-nth-twice
  (equal (update-nth n v (update-nth n w x)) (update-nth n v x)))
(defthm fn2-env-io-drop-p-trans
  (implies (and (fn2-env-io-drop-p x y) (fn2-env-io-drop-p y z)) (fn2-env-io-drop-p x z))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-io-drop-p fn2-env-update-nth-twice))))
(defthm fn2-env-update-nth-3-of-unit
  (equal (update-nth 3 v (list a b c d e f)) (list a b c v e f))
  :hints (("Goal" :in-theory '(update-nth (:e zp) (:e binary-+) car-cons cdr-cons zp))))
(defmacro fn2-env-fl-row-writer (w)
  ; W writes the commit table and the control child alone (its ARM-KIDS)
  `(make-event
    (let ((out (fn2-arm-frame-out-term ',w (cons ',w (formals ',w (w state))) (w state))))
      (value
       `(defthm ,(fn2-env-rel-name ',w 'fn2-env-fl)
          (implies (fn2-env-fl log fn2-core) (fn2-env-fl log ,out))
          :hints (("Goal" :in-theory '((:e subsetp-equal) (:e natp) (:e member-equal) fn2-arm-kids-refl)
                   :use ((:instance fn2-env-fl-of-children (a fn2-core) (b ,out))
                         (:instance ,(fn2-columns-sym ',w "-ARM-KIDS") (fn2-arm-free '(9 5)) (fn2-arm-c0 fn2-core))
                         (:instance fn2-arm-kids-nth (i 0) (k 1) (free '(9 5)) (a fn2-core) (b ,out))
                         (:instance fn2-arm-kids-nth (i 0) (k 30) (free '(9 5)) (a fn2-core) (b ,out))))))))))
(defmacro fn2-env-fl-handler (fn)
  ; FN keeps FRESHNESS and LENT-OK: it writes its row and drops loans
  `(make-event
    (let ((out (fn2-arm-frame-out-term ',fn (cons ',fn (formals ',fn (w state))) (w state))))
      (value
       `(defthm ,(fn2-env-rel-name ',fn 'fn2-env-fl)
          (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-fl log fn2-core))
                   (fn2-env-fl log ,out))
          :hints (("Goal" :do-not-induct t
                   :in-theory (union-theories '(,',fn fn2-commit-drop-io-fn2-env-fl fn2-core-stop-fn2-env-fl
                                                fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live-fn2-env-fl
                                                fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok-fn2-env-fl)
                                              (theory 'fn2-arm-frame-base)))))))))
(defthm fn2-env-ops-advanced-step-into
  ; B advances A at S when the rows and S's generation stay and S's phase
  ; stays or becomes one outside free and reserved
  (implies (and (equal (fn2-ops-rows b) (fn2-ops-rows a))
                (implies (and (natp s) (< s (fn2-ops-rows a)))
                         (and (equal (fn2-ops-gen s b) (fn2-ops-gen s a))
                              (or (equal (fn2-ops-phase s b) (fn2-ops-phase s a))
                                  (not (member-equal (fn2-ops-phase s b) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))))
           (fn2-env-head-advanced (fn2-env-ops-head s a) (fn2-env-ops-head s b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-ops-head fn2-env-head-advanced) (fn2-ops-gen fn2-ops-phase fn2-ops-rows)))))
(defthm fn2-env-harvest-next-heads
  ; a harvest keeps the rows and generations; the harvested op's phase becomes
  ; submitted, release-pending or done
  (let ((b (mv-nth 4 (fn2-harvest-next o))))
    (and (equal (fn2-ops-rows b) (fn2-ops-rows o))
         (implies (natp s) (equal (fn2-ops-gen s b) (fn2-ops-gen s o)))
         (implies (and (natp s) (not (equal (fn2-ops-phase s b) (fn2-ops-phase s o))))
                  (member-equal (fn2-ops-phase s b)
                                (list *fn2-op-phase-submitted* *fn2-op-phase-release-pending* *fn2-op-phase-done*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-harvest-next fn2-op-harvest-phase fn2-ops-latch-peer fn2-op-slotp)
                           (fn2-ops-peek-posted fn2-ring-next))
           :use ((:instance fn2-env-peek-posted-cell (fn2-ops o))))))
(defthm fn2-env-harvest-next-advanced
  (implies (fn2-env-ops-advanced a o) (fn2-env-ops-advanced a (mv-nth 4 (fn2-harvest-next o))))
  :hints (("Goal" :in-theory '((:e member-equal) member-equal car-cons cdr-cons)
           :use ((:instance fn2-env-ops-advanced-trans (a a) (b o) (c (mv-nth 4 (fn2-harvest-next o))))
                 (:instance fn2-env-ops-advanced (a o) (b (mv-nth 4 (fn2-harvest-next o))))
                 (:instance fn2-env-harvest-next-heads (s (fn2-env-ops-advanced-witness o (mv-nth 4 (fn2-harvest-next o)))))
                 (:instance fn2-env-ops-advanced-step-into (a o) (b (mv-nth 4 (fn2-harvest-next o)))
                            (s (fn2-env-ops-advanced-witness o (mv-nth 4 (fn2-harvest-next o)))))))))
(defthm fn2-env-head-advanced-of-ops-op
  (equal (fn2-env-head-advanced (fn2-env-ops-head s a) (fn2-env-ops-head s b))
         (fn2-env-head-advanced (fn2-env-ops-op s a) (fn2-env-ops-op s b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-ops-head fn2-env-ops-op fn2-env-head-advanced)
                                  (fn2-ops-gen fn2-ops-phase fn2-ops-rows)))))
(defthm fn2-env-ops-op-gen-natp
  (implies (and (fn2-opsp o) (fn2-ops-wfp o) (fn2-op-slotp h o)) (natp (nth 1 (fn2-env-ops-op h o))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-ops-op fn2-ops-gen fn2-op-slotp) (fn2-opsp fn2-ops-wfp))
           :use ((:instance fn2-ops-gen-raw-nth-natp (fn2-ops o) (i h))))))
(defthm fn2-env-op-finish-not-slot
  (implies (not (fn2-op-slotp h o)) (equal (mv-nth 1 (fn2-op-finish h g o)) o))
  :hints (("Goal" :in-theory (enable fn2-op-finish fn2-op-phase-code fn2-op-handle-code))))
(defthm fn2-env-op-finish-head-advanced
  ; finishing an op leaves it, retires it at its generation, or frees it at the next
  (implies (and (fn2-opsp o) (fn2-ops-wfp o))
           (fn2-env-head-advanced (fn2-env-ops-op s o) (fn2-env-ops-op s (mv-nth 1 (fn2-op-finish h g o)))))
  :rule-classes nil
  :hints (("Goal" :cases ((and (equal s h) (fn2-op-slotp h o)) (equal s h))
           :in-theory (e/d (fn2-env-head-advanced fn2-env-ops-op-of-op-finish-other fn2-env-op-finish-not-slot)
                           (fn2-env-ops-op fn2-op-finish fn2-opsp fn2-ops-wfp))
           :use ((:instance fn2-env-ops-op-of-op-finish-gen (fn2-ops o))
                 (:instance fn2-env-ops-op-gen-natp)))))
(defthm fn2-env-op-finish-advanced
  (implies (and (fn2-env-ops-advanced a o) (fn2-opsp o) (fn2-ops-wfp o))
           (fn2-env-ops-advanced a (mv-nth 1 (fn2-op-finish h g o))))
  :hints (("Goal" :in-theory '(fn2-env-head-advanced-refl)
           :use ((:instance fn2-env-ops-advanced-trans (a a) (b o) (c (mv-nth 1 (fn2-op-finish h g o))))
                 (:instance fn2-env-ops-advanced (a o) (b (mv-nth 1 (fn2-op-finish h g o))))
                 (:instance fn2-env-head-advanced-of-ops-op (a o) (b (mv-nth 1 (fn2-op-finish h g o)))
                            (s (fn2-env-ops-advanced-witness o (mv-nth 1 (fn2-op-finish h g o)))))
                 (:instance fn2-env-op-finish-head-advanced (s (fn2-env-ops-advanced-witness o (mv-nth 1 (fn2-op-finish h g o)))))))))
(defthm fn2-env-harvest-cases-advanced
  (implies (and (fn2-opsp o) (fn2-ops-wfp o)
                (let ((hn (fn2-harvest-next o)))
                  (or (equal o2 (mv-nth 4 hn))
                      (equal o2 (mv-nth 1 (fn2-op-finish (mv-nth 1 hn) (mv-nth 2 hn) (mv-nth 4 hn)))))))
           (fn2-env-ops-advanced o o2))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-harvest-next-advanced fn2-env-op-finish-advanced fn2-env-ops-advanced-refl
                               fn2-harvest-next-preserves-type fn2-harvest-next-preserves-wfp))))
;; THE HANDLERS' READERS (J5 across the handlers, in commit-durable-all):
;; generators for "a commit row's row readers are its machine readers" and
;; "a row writer keeps commit-io"; an IF lift for the conditional loan drop.
(defmacro fn2-env-row-is-machine (fields)
  ; under a readable commit row, the row reader is the machine reader
  (if (atom fields) '(progn)
    (let* ((f (car fields)) (r (fn2-columns-col-name 'fn2-machine f)) (tr (fn2-columns-col-name 'fn2-commit-row f))
           (rc (fn2-columns-sym r "-READ-CODE")))
      `(progn
         (defthmd ,(fn2-columns-sym tr "-IS-MACHINE")
           (implies (equal (fn2-commit-snapshot-read-code id c) :ok) (equal (,tr id c) (,r id c)))
           :hints (("Goal" :in-theory '(,tr ,r ,rc fn2-commit-snapshot-read-code fn2-machine-phase-read-code (:e equal)))))
         (fn2-env-row-is-machine ,(cdr fields))))))
(defmacro fn2-env-writer-keeps-io (w)
  ; W writes the commit table and the control child alone: commit-io stays
  `(make-event
    (let ((out (fn2-arm-frame-out-term ',w (cons ',w (formals ',w (w state))) (w state))))
      (value
       `(defthm ,(fn2-columns-sym ',w "-KEEPS-IO")
          (equal (nth 30 ,out) (nth 30 fn2-core))
          :hints (("Goal" :in-theory '((:e subsetp-equal) (:e natp) (:e member-equal) fn2-arm-kids-refl)
                   :use ((:instance ,(fn2-columns-sym ',w "-ARM-KIDS") (fn2-arm-free '(9 5)) (fn2-arm-c0 fn2-core))
                         (:instance fn2-arm-kids-nth (i 0) (k 30) (free '(9 5)) (a fn2-core) (b ,out))))))))))
(defthmd fn2-env-nth-of-if
  (equal (nth k (if c a b)) (if c (nth k a) (nth k b))))
(defthmd fn2-env-member-pair
  (and (member-equal a (list a b)) (member-equal b (list a b))))
