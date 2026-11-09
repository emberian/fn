; FN2-CORE-OPS-SEMANTIC: fn2-ops-semanticp across every core step that
; writes the ops child, from the per-operation exports of ops-conservation.
(in-package "ACL2")
(include-book "host-boundary")
(include-book "ops-conservation")

(defun-nx fn2-core-ops-semanticp (core) (fn2-ops-semanticp (fn2-core-ops core)))
(local (in-theory (disable fn2-ops-semanticp)))

;; ---------------------------------------------------------------------------
;; Children faces. Each body is a chain of ops operations; each link is one
;; export (implies (fn2-ops-semanticp x) (fn2-ops-semanticp (op .. x))).
(defthm fn2-issue-children-ops-semanticp
  (implies (fn2-ops-semanticp ops)
           (fn2-ops-semanticp
            (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release
                                          target-slot target-gen okind oslot ogen principal pool ops control))))
  :hints (("Goal" :in-theory (e/d (fn2-issue-children)
                                  (fn2-ops-semanticp fn2-op-reserve fn2-op-unreserve fn2-op-set-range
                                   fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target
                                   fn2-op-enqueue fn2-core-lease fn2-control-record-stop
                                   fn2-core-outbox-ready)))))
(defmacro fn2-oss-issue (name args)
  (let ((call `(,name ,@args okind oslot ogen principal core))
        (children (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-CHILDREN") name)))
    `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-OPS-SEMANTICP") name)
       (implies (fn2-core-ops-semanticp core)
                (fn2-core-ops-semanticp (mv-nth 3 ,call)))
       :hints (("Goal" :in-theory (e/d (,name ,children fn2-core-ops-semanticp)
                                       (fn2-issue-children fn2-ops-semanticp)))))))
(fn2-oss-issue fn2-issue-receive (cap-index cap-nonce slot gen len))
(fn2-oss-issue fn2-issue-send (cap-index cap-nonce slot gen off len may-release))
(fn2-oss-issue fn2-issue-read (offset slot gen len))
(fn2-oss-issue fn2-issue-write (offset slot gen off len fua))
(fn2-oss-issue fn2-issue-fence ())
(fn2-oss-issue fn2-issue-accept (cap-index cap-nonce))
(fn2-oss-issue fn2-issue-close (cap-index cap-nonce))
(fn2-oss-issue fn2-issue-cancel (target-slot target-gen))
(fn2-oss-issue fn2-issue-entropy (slot gen len))

(defthm fn2-oss-core-stop-ops
  (equal (fn2-core-ops (fn2-core-stop reason core)) (fn2-core-ops core))
  :hints (("Goal" :in-theory (enable fn2-core-stop))))
(defthm fn2-issue-arm-wake-ops-semanticp
  (implies (fn2-core-ops-semanticp core)
           (fn2-core-ops-semanticp (mv-nth 3 (fn2-issue-arm-wake deadline observation-gen core))))
  :hints (("Goal" :in-theory (e/d (fn2-issue-arm-wake fn2-core-ops-semanticp)
                                  (fn2-ops-semanticp fn2-op-reserve fn2-op-set-wake fn2-op-enqueue
                                   fn2-core-stop fn2-core-outbox-ready)))))
(defthm fn2-harvest-one-ops-semanticp
  (implies (fn2-core-ops-semanticp core)
           (fn2-core-ops-semanticp (mv-nth 10 (fn2-harvest-one core))))
  :hints (("Goal" :in-theory (e/d (fn2-harvest-one fn2-core-ops-semanticp)
                                  (fn2-ops-semanticp fn2-harvest-next fn2-op-finish fn2-op-cell fn2-op-range
                                   fn2-op-phase fn2-op-slotp fn2-pool-complete-in fn2-pool-release-out
                                   fn2-core-stop)))))

;; The mailbox: take-clock or take-signal, then executor scalars, the stop
;; record and the trace, none of which is the ops child.
(defthm fn2-oss-exec-clock-ops
  (equal (fn2-core-ops (fn2-exec-clock mono core)) (fn2-core-ops core))
  :hints (("Goal" :in-theory (enable fn2-exec-clock fn2-core-stop fn2-exec-set-now fn2-exec-set-armed-deadline
                                     fn2-exec-set-idle-deadline fn2-exec-set-wake-generation))))
(defthm fn2-oss-exec-trace-actions-ops
  (equal (fn2-core-ops (fn2-exec-trace-actions left ordinal start core)) (fn2-core-ops core))
  :hints (("Goal" :in-theory (enable fn2-exec-trace-actions))))
(defthm fn2-oss-exec-record-ops
  (equal (fn2-core-ops (fn2-exec-record kind id principal position bytes steps actions runnable wake start core))
         (fn2-core-ops core))
  :hints (("Goal" :in-theory (e/d (fn2-exec-record fn2-core-stop) (fn2-exec-trace-actions)))))
(defthm fn2-exec-mailbox-ops-semanticp
  (implies (fn2-core-ops-semanticp core)
           (fn2-core-ops-semanticp (mv-nth 5 (fn2-exec-mailbox core))))
  :hints (("Goal" :in-theory (e/d (fn2-exec-mailbox fn2-core-ops-semanticp)
                                  (fn2-ops-semanticp fn2-take-clock fn2-take-signal fn2-exec-clock
                                   fn2-exec-record fn2-core-stop)))))

;; ---------------------------------------------------------------------------
;; The host boundary's ops writers (host-boundary.lisp).
(defmacro fn2-oss-host (name args &key position)
  (let ((call `(,name ,@args core)))
    `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-OPS-SEMANTICP") name)
       (implies (fn2-core-ops-semanticp core)
                (fn2-core-ops-semanticp ,(if position `(mv-nth ,position ,call) call)))
       :hints (("Goal" :in-theory (e/d (,name fn2-core-ops-semanticp) (fn2-ops-semanticp)))))))
(fn2-oss-host fn2-host-post-result (cell slot gen evkind outcome reason count aux0 aux1))
(fn2-oss-host fn2-host-post-accept-result (slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3))
(fn2-oss-host fn2-host-post-clock (mono real flags))
(fn2-oss-host fn2-host-post-signal (bits))
(fn2-oss-host fn2-host-count-stray ())
(fn2-oss-host fn2-host-outbox-ack (n) :position 1)
(fn2-oss-host fn2-host-op-finish (slot gen) :position 1)

;; Init establishes it.
(defthm fn2-core-init-ops-semanticp
  (implies (and (fn2-corep core) (fn2-core-profilep profile))
           (fn2-core-ops-semanticp (fn2-core-init profile core)))
  :hints (("Goal" :in-theory (e/d (fn2-core-init fn2-core-ops-semanticp fn2-core-profilep)
                                  (fn2-ops-semanticp fn2-ops-init)))))

;; ---------------------------------------------------------------------------
;; The machine arms that write the ops child: each child function's ops
;; output is a chain of the action issues above, and each core face writes
;; back its child's ops output.
(defconst *fn2-oss-ops-writers*
  '(fn2-ops-semanticp fn2-op-reserve fn2-op-unreserve fn2-op-set-range fn2-op-set-capability
    fn2-op-set-storage fn2-op-set-cancel-target fn2-op-set-wake fn2-op-enqueue fn2-op-finish
    fn2-op-request-cancel fn2-outbox-ack fn2-post-result fn2-post-accept-result fn2-post-clock
    fn2-post-signal fn2-take-clock fn2-take-signal fn2-count-stray fn2-harvest-next
    fn2-issue-children fn2-issue-receive-children fn2-issue-send-children fn2-issue-read-children
    fn2-issue-write-children fn2-issue-fence-children fn2-issue-accept-children
    fn2-issue-close-children fn2-issue-cancel-children fn2-issue-entropy-children
    fn2-block-read-children fn2-cursor-sub-art-read-children fn2-cursor-run-render-children
    fn2-echo-run-command-children fn2-echo-run-reply-children fn2-echo-run-closing-children
    fn2-scribe-run-write-children fn2-scribe-run-fence-children fn2-scribe-run-read-children))
(defmacro fn2-oss-child (name formals position)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-OPS-SEMANTICP") name)
     (implies (fn2-ops-semanticp fn2-ops)
              (fn2-ops-semanticp (mv-nth ,position (,name ,@formals))))
     :hints (("Goal" :in-theory (e/d (,name) ,(remove-eq name *fn2-oss-ops-writers*))))))
(fn2-oss-child fn2-issue-receive-children (cap-index cap-nonce slot gen len okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-send-children (cap-index cap-nonce slot gen off len may-release okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-read-children (offset slot gen len okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-write-children (offset slot gen off len fua okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-fence-children (okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-accept-children (cap-index cap-nonce okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-close-children (cap-index cap-nonce okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-cancel-children (target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-issue-entropy-children (slot gen len okind oslot ogen principal fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-block-read-children
  (pu epoch alloc off len lslot lgen okind oslot ogen principal fn2-extents fn2-pool fn2-ops fn2-control) 4)
(fn2-oss-child fn2-echo-run-command-children
  (id slot kind ordinal budget fn2-echo fn2-machines fn2-pool fn2-ops fn2-control) 7)
(fn2-oss-child fn2-echo-run-reply-children
  (id slot kind ordinal budget fn2-echo fn2-machines fn2-pool fn2-ops fn2-control) 7)
(fn2-oss-child fn2-echo-run-closing-children
  (id slot kind ordinal budget fn2-echo fn2-machines fn2-pool fn2-ops fn2-control) 7)
(fn2-oss-child fn2-scribe-run-write-children
  (id slot kind ordinal budget fn2-scribe fn2-machines fn2-pool fn2-ops fn2-control) 7)
(fn2-oss-child fn2-scribe-run-fence-children
  (id slot kind ordinal budget fn2-scribe fn2-machines fn2-pool fn2-ops fn2-control) 7)
(fn2-oss-child fn2-scribe-run-read-children
  (id slot kind ordinal budget fn2-scribe fn2-machines fn2-pool fn2-ops fn2-control) 7)
(fn2-oss-child fn2-cursor-sub-art-read-children
  (id slot kind ordinal budget fn2-cursor fn2-machines fn2-pool fn2-ops fn2-control fn2-extents) 7)
(fn2-oss-child fn2-cursor-run-render-children
  (id slot kind ordinal budget fn2-cursor fn2-machines fn2-pool fn2-ops fn2-control fn2-extents fn2-fc
   fn2-fields fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors
   fn2-run-paths fn2-run-cache fn2-succ-txns fn2-reads fn2-ranges fn2-range-sources fn2-seeks) 7)
(defmacro fn2-oss-face (name formals position)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-OPS-SEMANTICP") name)
     (implies (fn2-core-ops-semanticp core)
              (fn2-core-ops-semanticp (mv-nth ,position (,name ,@formals core))))
     :hints (("Goal" :in-theory (e/d (,name fn2-core-ops-semanticp) (fn2-core-stop ,@*fn2-oss-ops-writers*))))))
(fn2-oss-face fn2-block-read (pu epoch alloc off len lslot lgen okind oslot ogen principal) 3)
(fn2-oss-face fn2-echo-run-command (id budget) 4)
(fn2-oss-face fn2-echo-run-reply (id budget) 4)
(fn2-oss-face fn2-echo-run-closing (id budget) 4)
(fn2-oss-face fn2-scribe-run-write (id budget) 4)
(fn2-oss-face fn2-scribe-run-fence (id budget) 4)
(fn2-oss-face fn2-scribe-run-read (id budget) 4)
(fn2-oss-face fn2-cursor-run-render (id budget) 4)

;; ---------------------------------------------------------------------------
;; FN2-CORE-OPS-SEMANTIC: fn2-ops-semanticp holds at init and is kept by
;; every core-level function that writes the ops child: the nine action
;; issues and arm-wake, one harvest, the executor's mailbox, the machine arms
;; whose children write ops (echo, scribe, the cursor's render, the block
;; read), and the host boundary's seven ops entries. Each step's arguments
;; are A's elements, so the statement is over every argument.
(defconst *fn2-core-ops-steps*
  ;; (key function arity-of-args values-before-core)
  '((:receive fn2-issue-receive 9 3) (:send fn2-issue-send 11 3) (:read fn2-issue-read 8 3)
    (:write fn2-issue-write 10 3) (:fence fn2-issue-fence 4 3) (:accept fn2-issue-accept 6 3)
    (:close fn2-issue-close 6 3) (:cancel fn2-issue-cancel 6 3) (:entropy fn2-issue-entropy 7 3)
    (:arm-wake fn2-issue-arm-wake 2 3) (:harvest fn2-harvest-one 0 10) (:mailbox fn2-exec-mailbox 0 5)
    (:block-read fn2-block-read 11 3)
    (:echo-command fn2-echo-run-command 2 4) (:echo-reply fn2-echo-run-reply 2 4)
    (:echo-closing fn2-echo-run-closing 2 4) (:scribe-write fn2-scribe-run-write 2 4)
    (:scribe-fence fn2-scribe-run-fence 2 4) (:scribe-read fn2-scribe-run-read 2 4)
    (:cursor-render fn2-cursor-run-render 2 4)
    (:post-result fn2-host-post-result 9 0) (:post-accept-result fn2-host-post-accept-result 12 0)
    (:post-clock fn2-host-post-clock 3 0) (:post-signal fn2-host-post-signal 1 0)
    (:count-stray fn2-host-count-stray 0 0) (:outbox-ack fn2-host-outbox-ack 1 1)
    (:finish fn2-host-op-finish 2 1)))
(defun fn2-oss-nths (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) nil (cons `(nth ,i a) (fn2-oss-nths (+ 1 i) n))))
(defun fn2-oss-vars (k)
  (declare (xargs :verify-guards nil))
  (if (zp k) nil
    (cons (intern-in-package-of-symbol (concatenate 'string "FN2-OSS-V" (coerce (explode-nonnegative-integer k 10 nil) 'string)) 'fn2-oss-vars)
          (fn2-oss-vars (- k 1)))))
(defun fn2-oss-step-clauses (steps)
  (declare (xargs :verify-guards nil))
  (if (atom steps) nil
    (let* ((s (car steps)) (key (nth 0 s)) (fn (nth 1 s)) (call `(,fn ,@(fn2-oss-nths 0 (nfix (nth 2 s))) fn2-core))
           (vars (fn2-oss-vars (nfix (nth 3 s)))))
      (cons `(,key ,(if vars `(mv-let (,@vars fn2-core) ,call (declare (ignore ,@vars)) fn2-core) call))
            (fn2-oss-step-clauses (cdr steps))))))
(make-event
 `(defun fn2-core-ops-step (op a fn2-core)
    (declare (xargs :stobjs fn2-core :verify-guards nil))
    (case op ,@(fn2-oss-step-clauses *fn2-core-ops-steps*) (otherwise fn2-core))))
(defun fn2-core-ops-semantic-check (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (ok) (fn2-ops-semanticp fn2-ops) ok))
(defun fn2-core-ops-semantic-hyps (op fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (assoc-eq op *fn2-core-ops-steps*) (fn2-core-ops-semantic-check fn2-core)))
(defun-nx fn2-core-ops-semantic-conclusion (op a core)
  (fn2-core-ops-semantic-check (fn2-core-ops-step op a core)))
(defthm-owed fn2-core-ops-semantic (op a profile core)
  (and (implies (and (fn2-corep core) (fn2-core-profilep profile))
                (fn2-core-ops-semantic-check (fn2-core-init profile core)))
       (implies (fn2-core-ops-semantic-hyps op core)
                (fn2-core-ops-semantic-conclusion op a core)))
  :schema :invariant :from (:columns fn2-ops)
  :teeth (fn2-core-ops-semantic-teeth)
  :doc "fn2-ops-semanticp (the ops child's credit, phase-class, free-chain, outbox and posted-FIFO invariant) holds after init and is kept by every core-level writer of the ops child, over all arguments: the nine action issues and arm-wake, one harvest, the executor's mailbox, each machine arm whose child writes ops (echo command/reply/closing, scribe write/fence/read, cursor render, block read), and the host boundary's post-result, post-accept-result, post-clock, post-signal, count-stray, outbox-ack and finish.")
(defthm fn2-core-ops-semantic-check-fold
  (equal (fn2-core-ops-semantic-check core) (fn2-core-ops-semanticp core))
  :hints (("Goal" :in-theory (enable fn2-core-ops-semanticp))))
(make-event
 `(defthm fn2-core-ops-semantic-proved
    (and (implies (and (fn2-corep core) (fn2-core-profilep profile))
                  (fn2-core-ops-semantic-check (fn2-core-init profile core)))
         (implies (fn2-core-ops-semantic-hyps op core)
                  (fn2-core-ops-semantic-conclusion op a core)))
    :hints (("Goal" :in-theory (e/d (fn2-core-ops-semantic-hyps fn2-core-ops-semantic-conclusion fn2-core-ops-step)
                                    (fn2-core-ops-semanticp fn2-core-ops-semantic-check fn2-core-init fn2-core-profilep
                                     ,@(strip-cadrs *fn2-core-ops-steps*)))))))
(defthm fn2-core-ops-semantic-statement
  (fn2-core-ops-semantic$owed op a profile core)
  :hints (("Goal" :in-theory '(fn2-core-ops-semantic$owed) :use fn2-core-ops-semantic-proved)))
(fn2-owed-discharge fn2-core-ops-semantic fn2-core-ops-semantic-statement)
