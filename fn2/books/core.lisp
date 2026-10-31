; Core event library: bounded transitions over registered children.
(in-package "ACL2")
(include-book "pool-ranges")
(include-book "vocab")
(include-book "std/util/bstar" :dir :system)

(include-book "sched")
(include-book "trace")
(include-book "exec-state")
(include-book "arm-children")

(include-book "core-children-a")
(defmacro fn2-core-events ()
 '(progn
(make-event
 (value (cons 'progn (fn2-core-register-machine-children (fn2-machine-names (w state)) (w state) 0))))
(fn2-seal :children :core :core-child)
(fn2-resolve :core)
(make-event (value (fn2-declare '(:operation-set fn2-core-issue) nil nil
                      (list (fn2-columns-preserves-macro 'fn2-core)))))
(make-event (value (fn2-declare '(:operation-set fn2-core-harvest) nil nil nil)))
(make-event
 (value `(defconst *fn2-core-children*
           ',(fn2-core-registered-pairs (fn2-core-child-registry (w state))))))
(defun fn2-core-child-fields (children)
  (if (atom children) nil
    (cons (list (caar children) :type (cadar children))
          (fn2-core-child-fields (cdr children)))))
(make-event (value `(defstobj fn2-core ,@(fn2-core-child-fields *fn2-core-children*))))

; Generate the rectangular read-over-write matrix once: adding a child does
; not require hand-maintaining every old child's frame facts.
(defun fn2-core-child-read-facts (reader children)
  (if (endp children) nil
    (let* ((writer (caar children))
           (update (fn2-columns-pre "UPDATE-" writer)))
      (cons `(defthm ,(fn2-columns-sym reader
                       (concatenate 'string "-OF-" (symbol-name update)))
               (equal (,reader (,update p c))
                      ,(if (eq reader writer) 'p `(,reader c))))
            (fn2-core-child-read-facts reader (cdr children))))))
(defun fn2-core-child-facts (children all)
  (if (endp children) nil
    (let* ((field (caar children)) (type (cadar children))
           (pred (fn2-columns-sym type "P"))
           (update (fn2-columns-pre "UPDATE-" field)))
      (append
       `((defthm ,(fn2-columns-sym field "-TYPE")
           (implies (fn2-corep fn2-core) (,pred (,field fn2-core))))
         (defthm ,(fn2-columns-sym update "-TYPE")
           (implies (and (fn2-corep fn2-core) (,pred p))
                    (fn2-corep (,update p fn2-core)))
           ; Symbolic positions: without it the child at position 0 splits
           ; one case per child and costs seconds per registered kind.
           :hints (("Goal" :in-theory (disable nth update-nth)))))
       (fn2-core-child-read-facts field all)
       (fn2-core-child-facts (cdr children) all)))))
(defmacro fn2-core-children-facts (&rest children)
  `(progn ,@(fn2-core-child-facts children children)))
; Expansion fixture catches wrong same-child and cross-child equations.
(assert-event
 (equal (fn2-core-child-read-facts 'fn2-core-pool
          '((fn2-core-pool fn2-pool) (fn2-core-ops fn2-ops)))
        '((defthm fn2-core-pool-of-update-fn2-core-pool
            (equal (fn2-core-pool (update-fn2-core-pool p c)) p))
          (defthm fn2-core-pool-of-update-fn2-core-ops
            (equal (fn2-core-pool (update-fn2-core-ops p c))
                   (fn2-core-pool c))))))
(make-event (value (cons 'fn2-core-children-facts *fn2-core-children*)))
(defun fn2-core-child-writers (children)
  (if (atom children) nil
    (cons (fn2-columns-pre "UPDATE-" (caar children))
          (fn2-core-child-writers (cdr children)))))
(defun fn2-core-child-bindings (children)
  (if (atom children) nil
    (cons `(,(cadar children) (,(caar children) fn2-core))
          (fn2-core-child-bindings (cdr children)))))
(defun fn2-core-child-wfps (children)
  (if (atom children) nil
    (cons `(,(fn2-columns-sym (cadar children) "-WFP") ,(cadar children))
          (fn2-core-child-wfps (cdr children)))))
(make-event
 (value `(in-theory (disable fn2-corep ,@(strip-cars *fn2-core-children*)
                  ,@(fn2-core-child-writers *fn2-core-children*)))))

(make-event
 (value `(defun fn2-core-wfp (fn2-core)
           (declare (xargs :stobjs fn2-core))
           (stobj-let ,(fn2-core-child-bindings *fn2-core-children*)
             (answer)
             (and ,@(fn2-core-child-wfps *fn2-core-children*)) answer))))
; The core's well-formedness through its children, stated once per child and
; then closed: a proof about an operation sees only the children it touches,
; so its cost does not grow with the number of registered kinds.
(defun fn2-core-child-wfp-facts (children)
  (if (atom children) nil
    (let* ((field (caar children)) (type (cadar children))
           (wfp (fn2-columns-sym type "-WFP"))
           (update (fn2-columns-pre "UPDATE-" field)))
      (list* `(defthm ,(fn2-columns-pre "FN2-CORE-WFP-OF-" update)
                (implies (and (fn2-core-wfp fn2-core) (,wfp p))
                         (fn2-core-wfp (,update p fn2-core)))
                :hints (("Goal" :in-theory (enable fn2-core-wfp))))
             `(defthm ,(fn2-columns-sym wfp (concatenate 'string "-OF-" (symbol-name field)))
                (implies (fn2-core-wfp fn2-core) (,wfp (,field fn2-core)))
                :rule-classes (:rewrite :forward-chaining)
                :hints (("Goal" :in-theory (enable fn2-core-wfp))))
             (fn2-core-child-wfp-facts (cdr children))))))
; The forward-chaining class of each child fact is off by default; a section
; whose guard proofs read child bounds from a core hypothesis (B's commit and
; recovery sections) enables it locally.
(defun fn2-core-child-wfp-forward-runes (children)
  (if (atom children) nil
    (cons (list :forward-chaining
                (fn2-columns-sym (fn2-columns-sym (cadar children) "-WFP")
                                 (concatenate 'string "-OF-" (symbol-name (caar children)))))
          (fn2-core-child-wfp-forward-runes (cdr children)))))
(make-event (value `(progn ,@(fn2-core-child-wfp-facts *fn2-core-children*))))
(make-event (value `(in-theory (disable ,@(fn2-core-child-wfp-forward-runes *fn2-core-children*)))))
(in-theory (disable fn2-core-wfp))

; The pool has at most sixteen size classes; general profile validity alone
; does not impose that representation constraint.
(make-event
 (value `(defun fn2-core-profilep (profile)
           (declare (xargs :guard t
                    :guard-hints (("Goal" :in-theory (enable fn2-profilep)))))
           (and (fn2-profilep profile)
                ,@(fn2-core-registered-forms (fn2-core-child-registry (w state)) :profilep)))))

(in-theory (disable fn2-pool-init fn2-pool-reserve fn2-pool-release
                    fn2-pool-release-countp
                    fn2-pool-lease-in fn2-pool-lease-out fn2-pool-complete-in
                    fn2-pool-release-out fn2-pool-adapter-write
                    fn2-pool-write fn2-pool-reset fn2-pool-read fn2-pool-rows
                    fn2-pool-copy-range fn2-pool-drop-prefix fn2-pool-compare fn2-pool-fold fn2-pool-scan
                    fn2-op-cell fn2-op-range fn2-op-phase))

(in-theory (disable fn2-core-profilep))

; First corruption wins: later cleanup cannot erase the diagnostic.
(in-theory (disable fn2-control-stop fn2-control-stop-reason
                    fn2-stop-reason-code->keyword))
(defun fn2-core-stop (reason fn2-core)
  (declare (xargs :stobjs fn2-core
                  :guard (and (fn2-core-wfp fn2-core) (unsigned-byte-p 8 reason)
                              (fn2-stop-reason-code->keyword reason)
                              (not (= reason *fn2-stop-reason-none*)))))
  (stobj-let ((fn2-control (fn2-core-control fn2-core)))
    (fn2-control) (fn2-control-record-stop reason fn2-control) fn2-core))
(defthm fn2-core-stop-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (unsigned-byte-p 8 reason))
           (fn2-corep (fn2-core-stop reason fn2-core))))
(defthm fn2-core-stop-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (unsigned-byte-p 8 reason))
           (fn2-core-wfp (fn2-core-stop reason fn2-core))))
(in-theory (disable fn2-core-stop))
(defun fn2-core-stop-reason (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-control (fn2-core-control fn2-core)))
    (reason) (fn2-control-stop-reason fn2-control) reason))
(defthm fn2-core-stop-reason-byte
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (unsigned-byte-p 8 (fn2-core-stop-reason fn2-core))))
(in-theory (disable fn2-core-stop-reason))

; DSL for bounded pool operations through the parent. Lists exist only at
; macro expansion, never in the emitted runtime paths.
(defmacro fn2-core-pool-wrapper (name target args results position)
  (declare (ignore position))
  (fn2-operation-events '(:operation-set fn2-core-issue) name 'fn2-core args
    (append results '(fn2-core)) nil :core
    '(declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    `((stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
        (,@results fn2-pool) (,target ,@args fn2-pool) (mv ,@results fn2-core)))
    `((fn2-core-preserves ,name ,(append args '(fn2-core)) :position ,(len results) :rows nil)) nil))
(fn2-core-pool-wrapper fn2-core-reserve fn2-pool-reserve
  (class okind oslot ogen) (code slot gen) 3)
(fn2-defoperation (:operation-set fn2-core-issue) :core :infer
(defun fn2-core-release (slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-control (fn2-core-control fn2-core)))
    (code fn2-pool fn2-control)
    (fn2-core-release-children slot gen okind oslot ogen fn2-pool fn2-control)
    (mv code fn2-core))))
(fn2-core-preserves fn2-core-release (slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
(fn2-core-pool-wrapper fn2-core-reset fn2-pool-reset
  (slot gen okind oslot ogen) (code) 1)
(fn2-core-pool-wrapper fn2-core-write fn2-pool-write
  (slot gen idx byte okind oslot ogen) (code) 1)
; The range primitives through the parent (R6a1): one check, one loop.
(fn2-core-pool-wrapper fn2-core-copy-range fn2-pool-copy-range
  (src sgen soff dst dgen doff len okind oslot ogen) (code) 1)
(fn2-core-pool-wrapper fn2-core-drop-prefix fn2-pool-drop-prefix
  (slot gen k cursor limit okind oslot ogen) (code cursor) 2)
(fn2-defoperation (:operation-set fn2-core-issue) :core :infer
(defun fn2-core-compare (s1 g1 off1 k1 os1 og1 s2 g2 off2 k2 os2 og2 len fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code result at) (fn2-pool-compare s1 g1 off1 k1 os1 og1 s2 g2 off2 k2 os2 og2 len fn2-pool)
    (mv code result at))))
(fn2-defoperation (:operation-set fn2-core-issue) :core :infer
(defun fn2-core-fold (slot gen off len hash okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code value) (fn2-pool-fold slot gen off len hash okind oslot ogen fn2-pool)
    (mv code value))))
(fn2-defoperation (:operation-set fn2-core-issue) :core :infer
(defun fn2-core-scan (slot gen off len target okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code at) (fn2-pool-scan slot gen off len target okind oslot ogen fn2-pool)
    (mv code at))))
(fn2-defoperation (:operation-set fn2-core-issue) :core :infer
(defun fn2-core-read (slot gen idx okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code byte) (fn2-pool-read slot gen idx okind oslot ogen fn2-pool)
    (mv code byte))))

; No row traversal: these are the scalar outbox preconditions needed by
; enqueue. A reservation takes the row and credit before a pool loan.
; The core face of an action's issue (its body is arm-children.lisp's NAME-CHILDREN).
(defmacro fn2-core-issue-wrapper (name args)
  (fn2-operation-events '(:operation-set fn2-core-issue) name 'fn2-core
    (append args '(okind oslot ogen principal)) '(code slot gen fn2-core) nil :core
    '(declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    `((stobj-let ((fn2-pool (fn2-core-pool fn2-core))
                  (fn2-ops (fn2-core-ops fn2-core))
                  (fn2-control (fn2-core-control fn2-core)))
        (code slot gen fn2-pool fn2-ops fn2-control)
        (,(fn2-columns-sym name "-CHILDREN") ,@args okind oslot ogen principal fn2-pool fn2-ops fn2-control)
        (mv code slot gen fn2-core)))
    `((fn2-core-preserves ,name (,@args okind oslot ogen principal fn2-core) :position 3 :rows nil))
    (list :refusal (list :square (fn2-columns-sym name "-REFUSAL")))))
(fn2-core-issue-wrapper fn2-issue-receive (cap-index cap-nonce slot gen len))
(fn2-core-issue-wrapper fn2-issue-send (cap-index cap-nonce slot gen off len may-release))
(fn2-core-issue-wrapper fn2-issue-read (offset slot gen len))
(fn2-core-issue-wrapper fn2-issue-write (offset slot gen off len fua))
(fn2-core-issue-wrapper fn2-issue-fence ())
(fn2-core-issue-wrapper fn2-issue-accept (cap-index cap-nonce))
(fn2-core-issue-wrapper fn2-issue-close (cap-index cap-nonce))
(fn2-core-issue-wrapper fn2-issue-cancel (target-slot target-gen))

(fn2-core-issue-wrapper fn2-issue-entropy (slot gen len))

 ; ArmWake owns an ordinary outbox credit but no completion cell is posted.
; Its separate scalar payload is never overloaded onto a storage offset.
(fn2-defoperation (:operation-set fn2-core-issue) :core :infer
(defun fn2-issue-arm-wake (deadline observation-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (stop-reason code opslot opgen fn2-ops)
    (b* (((unless (and (unsigned-byte-p 60 deadline)
                       (unsigned-byte-p 60 observation-gen)))
          (mv *fn2-stop-reason-none* :bounds 0 0 fn2-ops))
         ((unless (fn2-core-outbox-ready fn2-ops))
          (mv *fn2-stop-reason-none* :state 0 0 fn2-ops))
         ((mv code opslot opgen fn2-ops)
          (fn2-op-reserve *fn2-action-arm-wake* 0 0 0 0 0 fn2-ops))
         ((unless (eq code :ok)) (mv *fn2-stop-reason-none* code 0 0 fn2-ops))
         ((mv code fn2-ops) (fn2-op-set-wake opslot opgen deadline observation-gen fn2-ops))
         ((unless (eq code :ok)) (mv *fn2-stop-reason-issue-wake* code opslot opgen fn2-ops))
         ((mv code fn2-ops) (fn2-op-enqueue opslot opgen fn2-ops)))
      (mv (if (eq code :ok) *fn2-stop-reason-none* *fn2-stop-reason-issue-enqueue*)
          code opslot opgen fn2-ops))
    (let ((fn2-core (if (= stop-reason *fn2-stop-reason-none*) fn2-core
                     (fn2-core-stop stop-reason fn2-core))))
      (mv code opslot opgen fn2-core)))))
(fn2-core-preserves fn2-issue-arm-wake (deadline observation-gen fn2-core) :position 3 :rows nil)

; Peek before harvest finishes/recycles a row, preserving its machine identity
; for observation routing. This is bounded scalar work, not a FIFO traversal.
(in-theory (disable fn2-ops-post-count))
(defun fn2-core-posted-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (posted) (< 0 (fn2-ops-post-count fn2-ops)) posted))

(defun fn2-core-next-owner (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (found okind oslot ogen principal)
    (fn2-ops-next-owner fn2-ops)
    (mv found okind oslot ogen principal)))

(fn2-defoperation (:operation-set fn2-core-harvest) :core :infer
(defun fn2-harvest-one (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (stop-reason found opslot opgen cell evkind outcome reason count aux0 aux1 fn2-pool fn2-ops)
    (b* (((mv found opslot opgen cell fn2-ops) (fn2-harvest-next fn2-ops))
         ((unless (eq found t))
          (mv (if (eq found :corrupt) *fn2-stop-reason-harvest-fifo* *fn2-stop-reason-none*)
              nil 0 0 0 0 0 0 0 0 0 fn2-pool fn2-ops))
         ((unless (and (fn2-op-slotp opslot fn2-ops) (unsigned-byte-p 1 cell)))
          (mv *fn2-stop-reason-harvest-fifo* nil 0 0 0 0 0 0 0 0 0 fn2-pool fn2-ops))
         ((mv ?posted ?harvested evkind outcome reason count aux0 aux1)
          (fn2-op-cell cell opslot fn2-ops))
         ((mv slot gen ?off ?len) (fn2-op-range opslot fn2-ops))
         ((mv rp rh ?re ?ro ?rr ?rc ?ra ?rb) (fn2-op-cell 1 opslot fn2-ops))
         (inputp (or (equal evkind *fn2-event-receive-result*)
                     (equal evkind *fn2-event-read-result*)
                     (equal evkind *fn2-event-entropy-result*)))
         ((mv code fn2-pool)
          (cond ((or (equal evkind *fn2-event-receive-result*)
                     (equal evkind *fn2-event-read-result*)
                     (equal evkind *fn2-event-entropy-result*))
                 (fn2-pool-complete-in slot gen opslot opgen
                   (if (or (equal outcome *fn2-outcome-failed*)
                           (equal outcome *fn2-outcome-cancelled*)) 0 count) fn2-pool))
                ((or (equal evkind *fn2-event-borrow-released*)
                     (and (equal rh 0) (equal rp 0)
                          (or (equal evkind *fn2-event-write-result*)
                              (and (equal evkind *fn2-event-send-result*) (equal aux0 0)))))
                 (fn2-pool-release-out slot gen fn2-pool))
                (t (mv :ok fn2-pool))))
         ((unless (eq code :ok))
          (mv (if inputp *fn2-stop-reason-harvest-input* *fn2-stop-reason-harvest-output*)
              nil opslot opgen cell evkind outcome reason count aux0 aux1 fn2-pool fn2-ops))
         ((mv code fn2-ops)
          (if (equal (fn2-op-phase opslot fn2-ops) *fn2-op-phase-done*)
              (fn2-op-finish opslot opgen fn2-ops) (mv :ok fn2-ops))))
      (mv (if (or (eq code :ok) (eq code :retired))
              *fn2-stop-reason-none* *fn2-stop-reason-harvest-finish*)
          (and (or (eq code :ok) (eq code :retired)) found)
          opslot opgen cell evkind outcome reason count aux0 aux1 fn2-pool fn2-ops))
    (let ((fn2-core (if (= stop-reason *fn2-stop-reason-none*) fn2-core
                     (fn2-core-stop stop-reason fn2-core))))
      (mv found opslot opgen cell evkind outcome reason count aux0 aux1 fn2-core)))))
(fn2-core-preserves fn2-harvest-one (fn2-core) :position 10 :rows nil)

(assert-event
 (fn2-assert-compliant-p
  '(fn2-core-wfp fn2-core-profilep fn2-core-reserve fn2-core-release
    fn2-core-reset fn2-core-write fn2-core-read fn2-core-copy-range fn2-core-drop-prefix
    fn2-core-compare fn2-core-fold fn2-core-scan fn2-core-lease
    fn2-issue-receive fn2-issue-send fn2-issue-read fn2-issue-write
    fn2-issue-fence fn2-issue-accept fn2-issue-close fn2-issue-cancel fn2-issue-entropy fn2-issue-arm-wake
    fn2-ops-next-owner fn2-core-next-owner fn2-harvest-one)
  (w state)))

; Test-only evidence traversals. Free rows are canonical: their only nonzero
; fields may be generation and next-free. This is established by init/finish
; and is the exact premise required by constant-work reservation rollback.
(defun fn2-core-canonical-tests (cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (append (if (member-eq (caar cols) '(gen next-free)) nil
              (list `(equal (,(fn2-columns-col-name 'fn2-ops (caar cols)) slot fn2-ops) 0)))
            (fn2-core-canonical-tests (cdr cols)))))
(make-event
 (value `(fn2-defoperation (:operation-set fn2-core-issue) :reference :infer
   (defun fn2-core-canonical-freep (n fn2-ops)
     (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
     (if (zp n) t
       (let ((slot (- n 1)))
         (and (or (not (equal (fn2-op-phase slot fn2-ops) *fn2-op-phase-free*))
                  (and ,@(fn2-core-canonical-tests
                           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-ops) (w state))))))
              (fn2-core-canonical-freep slot fn2-ops))))))))
(defun fn2-core-refusal-hyps (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (answer)
    (and (fn2-pool-semanticp fn2-pool) (fn2-ops-semanticp fn2-ops)
         (fn2-core-canonical-freep (fn2-ops-rows fn2-ops) fn2-ops))
    answer))
(defun fn2-core-refusal-resultp (code before after)
  (declare (ignore code))
  (equal before after))
(defmacro fn2-core-owe-refusal (name args)
  `(defthm-owed ,(fn2-columns-sym name "-REFUSAL") (,@args core)
     (mv-let (code slot gen after) (,name ,@args core)
       (declare (ignore slot gen))
       (implies (and (fn2-core-refusal-hyps core) (not (eq code :ok)))
                (fn2-core-refusal-resultp code core after)))
     :schema :invariant :from (:operation-set fn2-core-issue)
     :teeth (fn2-core-unit)
     :doc "A refused issue preserves the entire logical core, including generations and free-row contents; free rows are canonical as produced by init and finish."))
(fn2-core-owe-refusal fn2-issue-receive (cap-index cap-nonce slot gen len okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-send (cap-index cap-nonce slot gen off len may-release okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-read (offset slot gen len okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-write (offset slot gen off len fua okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-fence (okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-accept (cap-index cap-nonce okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-close (cap-index cap-nonce okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-cancel (target-slot target-gen okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-entropy (slot gen len okind oslot ogen principal))

(defun fn2-core-fill-resultp (phase prefix-size off count old-prefix exposed-prefix written)
  (and (equal phase *fn2-pool-state-workspace*)
       (equal prefix-size (+ off count))
       (equal exposed-prefix (append old-prefix written))))
(defun fn2-core-fill-hyps (slot gen opslot opgen count written fn2-pool fn2-ops)
  (declare (xargs :stobjs (fn2-pool fn2-ops) :verify-guards nil))
  (and (fn2-pool-semanticp fn2-pool) (fn2-ops-semanticp fn2-ops)
       (fn2-pool-logical-slotp slot fn2-pool) (fn2-op-slotp opslot fn2-ops)
       (equal (fn2-pool-input-code slot gen opslot opgen fn2-pool) :ok)
       (< 0 (fn2-ops-post-count fn2-ops))
       (equal (fn2-ops-posted-fifoi (fn2-ops-post-head fn2-ops) fn2-ops) (* 2 opslot))
       (equal (fn2-op-gen opslot fn2-ops) opgen)
       (equal (fn2-ops-range-slot opslot fn2-ops) slot)
       (equal (fn2-ops-range-gen opslot fn2-ops) gen)
       (member-equal (fn2-ops-c0-event opslot fn2-ops)
         (list *fn2-event-receive-result* *fn2-event-read-result* *fn2-event-entropy-result*))
       (equal count (if (member-equal (fn2-ops-c0-outcome opslot fn2-ops)
                        (list *fn2-outcome-failed* *fn2-outcome-cancelled*)) 0
                      (fn2-ops-c0-count opslot fn2-ops)))
       (natp count) (<= count (fn2-pool-lease-len slot fn2-pool))
       (equal written (fn2-pool-logical-octets count
                         (+ (fn2-pool-base slot fn2-pool)
                            (fn2-pool-lease-off slot fn2-pool)) fn2-pool))
       (equal (fn2-pool-readable-code slot gen
                 (fn2-pool-owner-kind slot fn2-pool)
                 (fn2-pool-owner-slot slot fn2-pool)
                 (fn2-pool-owner-gen slot fn2-pool) fn2-pool) :state)))
 ; Evidence interpreter only: the written-byte witness is an actual sequence
; of calls to the adapter export, never a list inferred by reading memory.
; Runtime core helpers do not call this test/model traversal.
(defun fn2-core-evidence-initialize (slot gen opslot opgen idx written fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil
                  :measure (acl2-count written)))
  (if (atom written) (mv (null written) fn2-pool)
    (mv-let (code fn2-pool)
      (fn2-pool-adapter-write slot gen opslot opgen idx (car written) fn2-pool)
      (if (eq code :ok)
          (fn2-core-evidence-initialize slot gen opslot opgen (+ 1 (nfix idx))
                                        (cdr written) fn2-pool)
        (mv nil fn2-pool)))))

(defthm-owed fn2-core-harvest-byte-fill
  (slot gen opslot opgen count written loan-core ready-ops)
  (mv-let (initialized initialized-pool)
    (fn2-core-evidence-initialize slot gen opslot opgen
      (fn2-pool-lease-off slot (fn2-core-pool loan-core)) written
      (fn2-core-pool loan-core))
    (let* ((core (update-fn2-core-pool initialized-pool loan-core))
           (core (update-fn2-core-ops ready-ops core)))
      (implies
        (and initialized (equal count (len written))
             (fn2-core-fill-hyps slot gen opslot opgen count written
                                 (fn2-core-pool core) (fn2-core-ops core)))
        (let* ((before (fn2-core-pool core))
               (after (fn2-core-pool (mv-nth 10 (fn2-harvest-one core)))))
          (fn2-core-fill-resultp
            (fn2-pool-state slot after) (fn2-pool-fill slot after)
            (fn2-pool-lease-off slot before) count
            (fn2-pool-logical-octets (fn2-pool-fill slot before)
                                    (fn2-pool-base slot before) before)
            (fn2-pool-logical-octets (fn2-pool-fill slot after)
                                    (fn2-pool-base slot after) after)
            written)))))
  :schema :invariant :from (:operation-set fn2-core-harvest)
  :teeth (fn2-core-unit)
  :doc "At the composed harvest boundary, an input completion exposes exactly the initialized loan prefix. Initialization is an explicit successful trace of the real adapter-write export; ready-ops supplies the independently posted observation state. This trace premise is the environmental fidelity obligation, not an inference from bytes that happen to be in memory.")

(fn2-resolve :core)

))

; The core's init has its own assembly section book (assembly-init): its guard
; covers every child's capacity arithmetic at once and is the largest single
; proof of the core section, so it certifies beside it, not inside it.
; One init function per child, then the chain: a stobj-let over every child
; would return them all through one MV, and ACL2 allows at most 32 values
; (the 33rd child stopped D4 2/n). Each child's init sees only its own child.
(defmacro fn2-core-init-events ()
 '(progn
; The init in groups of at most 16 children, then the chain: one stobj-let
; over every child would return them all through one MV, and ACL2 allows at
; most 32 values (the 33rd child stopped D4 2/n). Each group's guard is the
; old single proof's, over its own children only.
(defun fn2-core-init-chunks (xs acc out)
  ; XS in consecutive groups of at most 16, in order (structural on XS).
  (cond ((atom xs) (reverse (if (consp acc) (cons (reverse acc) out) out)))
        ((equal (len acc) 15) (fn2-core-init-chunks (cdr xs) nil (cons (reverse (cons (car xs) acc)) out)))
        (t (fn2-core-init-chunks (cdr xs) (cons (car xs) acc) out))))
(defun fn2-core-init-group-name (k)
  (packn-pos (list 'fn2-core-init-group- k) 'fn2-core))
(defun fn2-core-init-group-events (groups igroups k)
  (if (or (atom groups) (atom igroups)) nil
    (let* ((cs (car groups)) (is (car igroups)) (stobjs (strip-cars (strip-cdrs cs))))
      (list* `(defun ,(fn2-core-init-group-name k) (profile fn2-core)
               (declare (xargs :stobjs fn2-core :guard (fn2-core-profilep profile)
                               :guard-hints (("Goal" :in-theory (enable fn2-core-profilep fn2-machines-profilep fn2-profilep))))
                        (ignorable profile))
               (stobj-let ,(fn2-core-child-bindings cs) ,stobjs
                 (let* ,is ,(if (consp (cdr stobjs)) `(mv ,@stobjs) (car stobjs)))
                 fn2-core))
             `(defthm ,(fn2-columns-sym (fn2-core-init-group-name k) "-TYPE")
                (implies (and (fn2-corep fn2-core) (fn2-core-profilep profile))
                         (fn2-corep (,(fn2-core-init-group-name k) profile fn2-core)))
                :hints (("Goal" :in-theory (enable fn2-core-profilep fn2-machines-profilep))))
             (fn2-core-init-group-events (cdr groups) (cdr igroups) (+ 1 (nfix k)))))))
(defun fn2-core-init-group-chain (n k)
  (if (zp n) nil
    (cons `(fn2-core (,(fn2-core-init-group-name k) profile fn2-core))
          (fn2-core-init-group-chain (- n 1) (+ 1 (nfix k))))))
(make-event
 (value (cons 'progn (fn2-core-init-group-events
                       (fn2-core-init-chunks *fn2-core-children* nil nil)
                       (fn2-core-init-chunks (fn2-core-registered-inits (fn2-core-child-registry (w state))) nil nil) 0))))
(make-event
 (value `(defun fn2-core-init (profile fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-profilep profile)))
  (let* ,(fn2-core-init-group-chain (len (fn2-core-init-chunks *fn2-core-children* nil nil)) 0) fn2-core))))
(defthm fn2-core-init-type
  (implies (and (fn2-corep fn2-core) (fn2-core-profilep profile))
           (fn2-corep (fn2-core-init profile fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-core-profilep fn2-machines-profilep))))
(defthm fn2-core-init-wfp
  (implies (fn2-core-profilep profile)
           (fn2-core-wfp (fn2-core-init profile fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-core-profilep fn2-machines-profilep))))
(in-theory (disable fn2-core-init))
(assert-event (fn2-assert-compliant-p '(fn2-core-init) (w state)))
))
