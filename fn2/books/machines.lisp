; Machine declarations extend columns; all lists below are expansion-time data.
; Continuation calls are finite tags, never function-valued resident fields.
(in-package "ACL2")
(include-book "vocab")
(include-book "arms")

; A wait reason names what the row waits for: nothing, an operation's
; completion (not a resource: its result cells were reserved at issue), or
; the D0 resource kind that was exhausted (fn2/books/resources.lisp).
(defconst *fn2-machine-common-fields*
  `((generation :u60) (principal-slot :u16) (account-ref :u32)
    (ready-prev :link) (ready-next :link)
    (wait-reason (:enum fn2-wait (:none :completion ,@(strip-cars *fn2-resource-order*))))
    (deadline :u60)))

(defun fn2-machine-packed-layout (fields offset)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((width (fn2-columns-width (cadar fields))))
      (cons (list (caar fields) :bit-offset offset :bit-width width
                  :tags (and (consp (cadar fields))
                             (fn2-columns-enum-cases (caddr (cadar fields)) 0 t)))
            (fn2-machine-packed-layout (cdr fields) (+ (nfix offset) width))))))



(defun fn2-machine-initial-values (cols initial)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons (list (caar cols) (let ((entry (assoc-eq (caar cols) initial)))
                              (if entry (let ((value (cadr entry)))
                                (if (and (symbolp value) (not (eql (char (symbol-name value) 0) #\*)))
                                    `(,value slot base n gen) value)) 0)))
          (fn2-machine-initial-values (cdr cols) initial))))
(defun fn2-machine-prepare-events (name cols initial)
  (declare (xargs :verify-guards nil))
  (let* ((rows (fn2-columns-sym name "-ROWS")) (wfp (fn2-columns-sym name "-WFP"))
         (pred (fn2-columns-sym name "P")) (fill-fn (fn2-columns-sym name "-INITIALIZE-ROWS"))
         (prepare (fn2-columns-sym name "-PREPARE")))
    `((defun ,fill-fn (left n base gen ,name)
        (declare (xargs :stobjs ,name :measure (nfix left)
                        :guard (and (,wfp ,name) (natp left) (natp n) (natp base)
                                    (<= left n) (<= n (,rows ,name))
                                    (< (+ base n) 4294967296) (unsigned-byte-p 60 gen))))
        (if (zp left) ,name
          (let* ((slot (- left 1))
                 ,@(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name 'slot
                      (fn2-machine-initial-values cols initial)))
            (,fill-fn (- left 1) n base gen ,name))))
      (defthm ,(fn2-columns-sym fill-fn "-TYPE")
        (implies (and (,pred ,name) (,wfp ,name) (natp left) (natp n) (natp base)
                      (<= left n) (<= n (,rows ,name)) (< (+ base n) 4294967296)
                      (unsigned-byte-p 60 gen)) (,pred (,fill-fn left n base gen ,name))))
      (defthm ,(fn2-columns-sym fill-fn "-WFP")
        (implies (and (,wfp ,name) (natp left) (natp n) (<= left n) (<= n (,rows ,name)))
                 (,wfp (,fill-fn left n base gen ,name))))
      (defthm ,(fn2-columns-sym fill-fn "-ROWS")
        (equal (,rows (,fill-fn left n base gen ,name)) (,rows ,name)))
      (in-theory (disable ,fill-fn))
      (defun ,prepare (n base gen ,name)
        (declare (xargs :stobjs ,name
                        :guard (and (natp n) (natp base) (< (+ base n) 4294967296)
                                    (unsigned-byte-p 60 gen))))
        (let ((,name (,(fn2-columns-sym name "-INIT") n ,name)))
          (,fill-fn n n base gen ,name)))
      (defthm ,(fn2-columns-sym prepare "-TYPE")
        (implies (and (,pred ,name) (natp n) (natp base) (< (+ base n) 4294967296)
                      (unsigned-byte-p 60 gen)) (,pred (,prepare n base gen ,name))))
      (defthm ,(fn2-columns-sym prepare "-WFP")
        (implies (and (natp n) (natp base) (< (+ base n) 4294967296))
                 (,wfp (,prepare n base gen ,name))))
      (in-theory (disable ,prepare)))))

; Dispatch is emitted after the containing core and named callbacks exist.
; Its generated functions are guard-verified ordinary ACL2 code.



(defun fn2-machine-write-values (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (list (fn2-columns-col-name 'fn2-write-value (caar fields)) (cadar fields))
          (fn2-machine-write-values (cdr fields)))))
(defun fn2-machine-write-fields (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (list (caar fields) (fn2-columns-col-name 'fn2-write-value (caar fields)))
          (fn2-machine-write-fields (cdr fields)))))
(defun fn2-machine-write-guards (fields columns)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (fn2-columns-fit (cadr (assoc-eq (caar fields) columns)) (cadar fields))
          (fn2-machine-write-guards (cdr fields) columns))))
(defun fn2-machine-core-put-expansion (name columns states id fields corep)
  (declare (xargs :verify-guards nil))
  (if (fn2-columns-write-formp name columns states fields)
      (if corep
          (let ((values (fn2-machine-write-fields fields)))
            ; Parallel value bindings preserve the caller's lexical scope.
            ; The whole write is checked before the first column is changed.
            `(let ((fn2-write-id ,id) ,@(fn2-machine-write-values fields))
               (if (not (and (fn2-machine-idp fn2-write-id fn2-core)
                             (equal (fn2-machine-kind fn2-write-id fn2-core)
                              ,(fn2-columns-pre "*" (fn2-columns-sym name "-KIND*")))))
                   (fn2-machine-refuse-write fn2-core)
                 (let ((fn2-write-slot (fn2-machine-slot fn2-write-id fn2-core)))
                   (stobj-let ((,name (,(fn2-columns-sym name "-TABLE") fn2-core)))
                     (fn2-write-accepted ,name)
                     (if (and (natp fn2-write-slot)
                              (< fn2-write-slot (,(fn2-columns-sym name "-ROWS") ,name))
                              ,@(fn2-machine-write-guards values columns))
                         (let* ,(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name 'fn2-write-slot values) (mv t ,name))
                       (mv nil ,name))
                     (if fn2-write-accepted fn2-core (fn2-machine-refuse-write fn2-core)))))))
        `(let* ,(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name id fields) ,name))
    (er hard 'defmachine "Invalid field list or cross-kind phase in ~x0 write: ~x1." name fields)))

(defun fn2-machine-continuationsp (entries observationp)
  (declare (xargs :verify-guards nil))
  (if (atom entries) (null entries)
    (and (true-listp (car entries)) (<= 2 (len (car entries)))
         (keywordp (caar entries)) (symbolp (cadar entries)) (cadar entries) (not (eq (cadar entries) t))
         (not (keywordp (cadar entries)))
         (or (not observationp) (fn2-event-keyword->code (caar entries)))
         (fn2-machine-continuationsp (cdr entries) observationp))))
(defun fn2-machine-observe-event-guards (observes)
  ; One (TAG t) case per observed event: the handlers' guard.
  (declare (xargs :verify-guards nil))
  (if (atom observes) nil
    (let ((tag (fn2-event-keyword->code (caar observes))))
      (if (not tag) (er hard 'defmachine "Unknown observation event ~x0." (caar observes))
        (cons (list tag t) (fn2-machine-observe-event-guards (cdr observes)))))))
(defun fn2-machine-row-vars (columns)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (cons (fn2-columns-col-name 'row (caar columns)) (fn2-machine-row-vars (cdr columns)))))
; A callback receives only the row fields its body reads (inferred from its
; ROW- references after fn2-call expansion), each through the kind's
; per-field reader K-ROW-F: no snapshot of the whole row crosses an mv, so a
; row may have more fields than ACL2's 32 multiple values.
(defun fn2-machine-row-reader (kind field)
  (declare (xargs :verify-guards nil))
  (fn2-columns-col-name kind (fn2-columns-pre "ROW-" field)))
(defun fn2-machine-var-column (var columns)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (if (eq var (fn2-columns-col-name 'row (caar columns))) (car columns)
      (fn2-machine-var-column var (cdr columns)))))
(defun fn2-machine-read-bindings (kind reads columns)
  (declare (xargs :verify-guards nil))
  (if (atom reads) nil
    (cons `(,(car reads) (,(fn2-machine-row-reader kind (car (fn2-machine-var-column (car reads) columns)))
                          id fn2-core))
          (fn2-machine-read-bindings kind (cdr reads) columns))))
(defun fn2-machine-read-columns (reads columns)
  (declare (xargs :verify-guards nil))
  (if (atom reads) nil
    (cons (fn2-machine-var-column (car reads) columns) (fn2-machine-read-columns (cdr reads) columns))))
(defun fn2-machine-occurs (var form)
  (declare (xargs :verify-guards nil))
  (cond ((atom form) (eq form var)) ((eq (car form) 'quote) nil)
        (t (or (fn2-machine-occurs var (car form)) (fn2-machine-occurs var (cdr form))))))
(defun fn2-machine-body-reads (vars body)
  (declare (xargs :verify-guards nil))
  (if (atom vars) nil
    (if (fn2-machine-occurs (car vars) body)
        (cons (car vars) (fn2-machine-body-reads (cdr vars) body))
      (fn2-machine-body-reads (cdr vars) body))))
(defun fn2-machine-initialp (name columns states fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) (null fields)
    (and (consp (car fields)) (equal (len (car fields)) 2)
         (assoc-eq (caar fields) columns)
         (or (and (integerp (cadar fields)) (<= 0 (cadar fields)))
             (and (symbolp (cadar fields)) (cadar fields) (not (keywordp (cadar fields)))))
         (or (not (eq (caar fields) 'phase))
             (and (symbolp (cadar fields)) (cadar fields)
                  (not (eql (char (symbol-name (cadar fields)) 0) #\*)))
             (fn2-columns-phase-formp (cadar fields)
              (strip-cars (strip-cdrs (fn2-columns-enum-constants (fn2-columns-sym name "-STATE") states 0)))))
         (fn2-machine-initialp name columns states (cdr fields)))))
; The machine's case catalogue (DSL-METATHEORY 3.2): one label per phase,
; then one per observed event, in declaration order. A correspondence binds
; statements to these labels; the machine states none itself.
(defun fn2-machine-phase-labels (name states)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons (list :run name (car states)) (fn2-machine-phase-labels name (cdr states)))))
(defun fn2-machine-observe-labels (name observes)
  (declare (xargs :verify-guards nil))
  (if (atom observes) nil
    (cons (list :observe name (caar observes)) (fn2-machine-observe-labels name (cdr observes)))))
(defun fn2-machine-case-labels (name states observes)
  (declare (xargs :verify-guards nil))
  (append (fn2-machine-phase-labels name states)
          (fn2-machine-observe-labels name observes)))

(defun fn2-machine-observe-kind-arms (names tag predicatep router)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons `(,tag ,(if predicatep
                     `(,(fn2-columns-sym (car names) "-OBSERVES-P") phase event)
                   `(,(fn2-columns-col-name router (car names))
                     id event outcome reason count aux0 aux1 fn2-core)))
          (fn2-machine-observe-kind-arms (cdr names) (+ 1 (nfix tag)) predicatep router))))

(defun fn2-machine-requirements (entries)
  (if (atom entries) nil
    (cons (list :function (cadar entries) :at :callbacks)
          (fn2-machine-requirements (cdr entries)))))

;; :admission (:phase P :ranges RANGES [:copy (FIELD ...)] [:clear (FIELD ...)]):
;; the kind is admitted by the listener into phase P from :free (D's section
;; 4.5). A range is :rx-range / :tx-range (fields rx-slot rx-gen, tx-slot
;; tx-gen, class 0) or (KIND :slot F :gen F [:class N]). :copy names listener
;; fields copied into the row at admission; :clear fields are zeroed. The row
;; needs a :link next-free field (its partition's free chain).
(defun fn2-machine-range-spec (range)
  (declare (xargs :verify-guards nil))
  (cond ((eq range :rx-range) '(:rx-range :slot rx-slot :gen rx-gen :class 0))
        ((eq range :tx-range) '(:tx-range :slot tx-slot :gen tx-gen :class 0))
        ((consp range) (list (car range) :slot (fn2-arm-get :slot (cdr range))
                             :gen (fn2-arm-get :gen (cdr range))
                             :class (or (fn2-arm-get :class (cdr range)) 0)))
        (t nil)))
(defun fn2-machine-range-specs (ranges)
  (declare (xargs :verify-guards nil))
  (if (atom ranges) nil
    (cons (fn2-machine-range-spec (car ranges)) (fn2-machine-range-specs (cdr ranges)))))
(defun fn2-machine-range-specs-p (specs own)
  (declare (xargs :verify-guards nil))
  (if (atom specs) t
    (and (consp (car specs)) (member-eq (caar specs) '(:rx-range :tx-range))
         (member-eq (fn2-arm-get :slot (cdar specs)) own) (member-eq (fn2-arm-get :gen (cdar specs)) own)
         (natp (fn2-arm-get :class (cdar specs)))
         (fn2-machine-range-specs-p (cdr specs) own))))
(defun fn2-machine-admission-problem (name admission states own)
  (declare (xargs :verify-guards nil))
  (cond ((null admission) nil)
        ((not (and (fn2-arm-plistp admission '(:phase :ranges :copy :clear))
                   (member-eq (fn2-arm-get :phase admission) states) (member-eq :free states)
                   (consp (fn2-arm-get :ranges admission))
                   (fn2-machine-range-specs-p (fn2-machine-range-specs (fn2-arm-get :ranges admission)) own)
                   (fn2-arm-namesp (fn2-arm-get :copy admission))
                   (fn2-arm-subsetp (fn2-arm-get :copy admission) own)
                   (fn2-arm-namesp (fn2-arm-get :clear admission))
                   (fn2-arm-subsetp (fn2-arm-get :clear admission) own)
                   (member-eq 'next-free own) (member-eq 'cap-index own) (member-eq 'cap-nonce own)))
         (msg "~x0: :admission ~x1 is (:phase P :ranges (RANGE ...) [:copy (F ...)] [:clear (F ...)]) ~
               with P a phase, a :free phase, the range fields its own, and cap-index, cap-nonce, ~
               next-free fields." name admission))
        (t nil)))
(defun fn2-machine-events (name states fields budget continuations observes capacity initial holds admission)
  (declare (xargs :verify-guards nil))
  (let* ((enum (fn2-columns-sym name "-STATE"))
         (cols (append `((phase (:enum ,enum ,states))) *fn2-machine-common-fields* fields))
         (charge (fn2-columns-sym name "-CHARGE"))
         (bytes (cadr (member-eq :bytes budget)))
         (steps (cadr (member-eq :steps budget)))
         (descriptors (cadr (member-eq :descriptors budget))))
    (fn2-declare (list :machine name)
      `(:states ,states :columns ,cols :holds ,holds :admission ,admission :budget ,budget
                :continuations ,continuations :observes ,observes :capacity ,capacity :initial ,initial
                :layout ,cols :packed ,(fn2-machine-packed-layout cols 0)
                :calling-convention (:run (id budget ,@(fn2-machine-row-vars cols) fn2-core)
                                     :observe (id event outcome reason count aux0 aux1 ,@(fn2-machine-row-vars cols) fn2-core))
                :cases ,(fn2-machine-case-labels name states observes))
      (append (list (list :declaration (list :columns name)))
              (fn2-machine-requirements (append continuations observes)))
      `((defcolumns ,name ,cols :put-policy ,states)
       (defmacro ,(fn2-columns-sym name "-PUT-CORE") (id &rest fields)
         (fn2-machine-core-put-expansion ',name ',cols ',states id fields t))
       (defconst ,(fn2-columns-pre "*" (fn2-columns-sym name "-BUDGET*")) ',budget)
       (defconst ,(fn2-columns-pre "*" (fn2-columns-sym name "-RUN-BYTES*")) ,bytes)
       (defconst ,(fn2-columns-pre "*" (fn2-columns-sym name "-RUN-STEPS*")) ,steps)
       (defconst ,(fn2-columns-pre "*" (fn2-columns-sym name "-RUN-DESCRIPTORS*")) ,descriptors)
       ; Scalar multiple values are the runtime budget record: no consing.
       ; Preflight and finish use the same simultaneous caps. A refused
       ; preflight yields before mutation; valid calls retain the scalar API.
       (defun ,charge (bytes steps descriptors)
         (declare (xargs :guard (and (natp bytes) (natp steps) (natp descriptors))))
         (if (and (<= bytes ,bytes) (<= steps ,steps) (<= descriptors ,descriptors))
             (mv bytes steps descriptors)
           (mv nil nil nil)))

       (defun ,(fn2-columns-sym name "-OBSERVES-P") (phase event)
         (declare (xargs :guard t) ,@(if (or (member-eq :free states) (member-eq :retired states)) nil '((ignore phase))))
         (and ,(if (member-eq :free states) `(not (equal phase ,(position-eq :free states))) t)
              ,(if (member-eq :retired states) `(not (equal phase ,(position-eq :retired states))) t)
              (case event ,@(fn2-machine-observe-event-guards observes) (otherwise nil))))

       ,@(fn2-machine-prepare-events name cols initial)))))

(defmacro defmachine (name &key states fields budget continuations observes (capacity '1) initial holds admission)
  (if (and (consp states)
           (fn2-columns-keyword-listp states) (no-duplicatesp-eq states)
           (<= (len states) 256) (fn2-columns-declarationsp fields)
           (no-duplicatesp-eq (append '(phase) (strip-cars *fn2-machine-common-fields*)
                                      (strip-cars fields)))
           (fn2-machine-continuationsp continuations nil)
           (fn2-machine-continuationsp observes t) (no-duplicatesp-eq (strip-cars observes))
           (doublet-listp initial) (no-duplicatesp-eq (strip-cars initial))
           (fn2-machine-initialp name
             (append `((phase (:enum state ,states))) *fn2-machine-common-fields* fields)
             states initial)
           (fn2-columns-keyword-listp (strip-cars observes))
           (equal (strip-cars continuations) states)
           (natp (cadr (member-eq :bytes budget)))
           (natp (cadr (member-eq :steps budget)))
           (natp (cadr (member-eq :descriptors budget))) capacity)
      (let* ((own (remove-eq 'phase (strip-cars (append *fn2-machine-common-fields* fields))))
             (problem (or (fn2-arm-contracts-problem name continuations states own nil)
                          (fn2-arm-contracts-problem name observes states own t)
                          (fn2-arm-holds-problem-syntax name holds states)
                          (fn2-machine-admission-problem name admission states own))))
        (if problem `(make-event (er soft 'defmachine "~@0" ',problem))
          (fn2-machine-events name states fields budget continuations observes capacity initial holds
                              admission)))
    (er hard 'defmachine "Invalid machine declaration ~x0." name)))

; Table order is declaration order, independent of TABLE-ALIST's newest first.
(defun fn2-machine-names (world)
  (declare (xargs :verify-guards nil))
  (strip-cars (fn2-decl-rows :machine world)))
(defun fn2-machine-property (name key world)
  (declare (xargs :verify-guards nil))
  (cadr (member-eq key (fn2-decl-row (list :machine name) world))))
(defun fn2-machine-arm-call (kind fn fixed bound world)
  ; FN's call with its row fields: those not already BOUND are read here.
  (declare (xargs :verify-guards nil))
  (let* ((reads (fn2-decl-get :row-bindings (fn2-operation-row fn world)))
         (bindings (fn2-machine-read-bindings kind (set-difference-eq reads bound)
                                              (fn2-machine-property kind :columns world))))
    (if bindings `(let ,bindings (,fn ,@fixed ,@reads fn2-core))
      `(,fn ,@fixed ,@reads fn2-core))))
(defun fn2-machine-state-arms (states continuations n kind world)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons `(,n ,(fn2-machine-arm-call kind (cadr (assoc-eq (car states) continuations))
                                      '(id budget) '(row-phase) world))
          (fn2-machine-state-arms (cdr states) continuations (+ 1 (nfix n)) kind world))))
(defun fn2-machine-observe-event-arms (observes predicatep args)
  ; ARGS is (KIND WORLD) for calls; each handler gets only its read fields.
  (declare (xargs :verify-guards nil))
  (if (atom observes) nil
    (let ((tag (fn2-event-keyword->code (caar observes))))
      (if (not tag) (er hard 'defmachine "Unknown observation event ~x0." (caar observes))
        (cons (list tag (if predicatep t
                          (fn2-machine-arm-call (car args) (cadar observes)
                                                '(id event outcome reason count aux0 aux1)
                                                '(row-phase) (cadr args))))
              (fn2-machine-observe-event-arms (cdr observes) predicatep args))))))

; ----------------------------------------------------------------------
; Arm contracts in the registry (R7). The contract of a callback: an arm
; entry's (the union over the arms naming it) or its own :contract.
(defun fn2-machine-arm-union (name entries acc)
  (declare (xargs :verify-guards nil))
  (if (atom entries) acc
    (fn2-machine-arm-union name (cdr entries)
      (if (eq (cadar entries) name)
          (let ((c (cddar entries)))
            (if (null acc) c
              (list :cost (fn2-arm-get :cost acc)
                    :writes (union-eq (fn2-arm-get :writes c) (fn2-arm-get :writes acc))
                    :tables (union-eq (fn2-arm-get :tables c) (fn2-arm-get :tables acc))
                    :next (union-eq (fn2-arm-get :next c) (fn2-arm-get :next acc))
                    :uses (union-equal (fn2-arm-get :uses c) (fn2-arm-get :uses acc))
                    :language (or (fn2-arm-get :language c) (fn2-arm-get :language acc)))))
        acc))))
(defun fn2-machine-arm-cost-max (name entries world acc)
  (declare (xargs :verify-guards nil))
  (if (atom entries) acc
    (fn2-machine-arm-cost-max name (cdr entries) world
      (if (eq (cadar entries) name)
          (let ((v (fn2-cost-values (fn2-arm-get :cost (cddar entries)) world)))
            (if (and acc (natp (car v)) (natp (cadr v)) (natp (caddr v)))
                (list (max (car v) (car acc)) (max (cadr v) (cadr acc)) (max (caddr v) (caddr acc)))
              (or acc v)))
        acc))))
(defun fn2-machine-phase-map (name states)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons (cons (fn2-columns-pre "*" (fn2-columns-sym (fn2-columns-col-name (fn2-columns-sym name "-STATE")
                                                                           (car states)) "*"))
                (car states))
          (fn2-machine-phase-map name (cdr states)))))
(defun fn2-machine-row-map (columns)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (cons (cons (fn2-columns-col-name 'row (caar columns)) (caar columns))
          (fn2-machine-row-map (cdr columns)))))
(defun fn2-machine-arm-env (kind contract world)
  (declare (xargs :verify-guards nil))
  (list :kind kind :put (fn2-columns-sym kind "-PUT-CORE")
        :rows (fn2-machine-row-map (fn2-machine-property kind :columns world))
        :phases (fn2-machine-phase-map kind (fn2-machine-property kind :states world))
        :writes (fn2-arm-get :writes contract) :next (fn2-arm-get :next contract)
        :uses (fn2-arm-use-names (fn2-arm-get :uses contract))
        :tables (append (fn2-arm-get :tables contract) *fn2-arm-implicit-tables*)
        :world world))
; The effective contract and its evaluated bound, or a refusal message.
(defun fn2-machine-callback-contract (name kind own body world)
  (declare (xargs :verify-guards nil))
  (let* ((arms (append (fn2-machine-property kind :continuations world)
                       (fn2-machine-property kind :observes world)))
         (entry (fn2-machine-arm-union name arms nil))
         (contract (or own entry))
         (states (fn2-machine-property kind :states world))
         (fields (remove-eq 'phase (strip-cars (fn2-machine-property kind :columns world))))
         (values (if own (fn2-cost-values (fn2-arm-get :cost own) world)
                   (fn2-machine-arm-cost-max name arms world nil))))
    (cond ((and own entry)
           (mv (msg "~x0 is an arm of ~x1: its contract is the arm entry, not :contract." name kind) nil nil))
          ((not contract)
           (mv (msg "~x0 has no contract: declare it as an arm of ~x1 or give :contract." name kind) nil nil))
          ((and own (fn2-arm-contract-problem name (list* name name own) states fields nil))
           (mv (fn2-arm-contract-problem name (list* name name own) states fields nil) nil nil))
          ((not (and (natp (car values)) (natp (cadr values)) (natp (caddr values))))
           (mv (msg "~x0's cost ~x1 cites a call with no declared cost." name (fn2-arm-get :cost contract)) nil nil))
          ((eq (fn2-arm-get :language contract) :unchecked) (mv nil contract values))
          (t (let ((problem (fn2-arm-walk-list body nil (fn2-machine-arm-env kind contract world)
                                            (+ 16 (* 4 (acl2-count body))))))
               (if problem (mv (msg "~x0 ~@1" name problem) nil nil)
                 (mv nil contract values)))))))

; Per-kind certificates: each phase's declared bound and successors, as
; guard-true functions the generated run entry asserts and the owed rows cite.
(defun fn2-machine-charge-cases (arms states n world)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (let ((v (fn2-cost-values (fn2-arm-get :cost (cddr (assoc-eq (car states) arms))) world)))
      (cons `(,n (and (<= bytes ,(car v)) (<= steps ,(cadr v)) (<= descriptors ,(caddr v))))
            (fn2-machine-charge-cases arms (cdr states) (+ 1 (nfix n)) world)))))
(defun fn2-machine-bound-cases (arms states n world)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (let ((v (fn2-cost-values (fn2-arm-get :cost (cddr (assoc-eq (car states) arms))) world)))
      (cons `(,n ,(+ (car v) (cadr v)))
            (fn2-machine-bound-cases arms (cdr states) (+ 1 (nfix n)) world)))))
(defun fn2-machine-phase-indices (phases states)
  (declare (xargs :verify-guards nil))
  (if (atom phases) nil
    (cons (position-eq (car phases) states) (fn2-machine-phase-indices (cdr phases) states))))
(defun fn2-machine-next-cases (arms states n all)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons `(,n (member-equal next ',(fn2-machine-phase-indices
                                      (fn2-arm-get :next (cddr (assoc-eq (car states) arms))) all)))
          (fn2-machine-next-cases arms (cdr states) (+ 1 (nfix n)) all))))
(defun fn2-machine-observe-default-from (states)
  (declare (xargs :verify-guards nil))
  (remove-eq :free (remove-eq :retired states)))
(defun fn2-machine-observe-next-cases (observes states)
  (declare (xargs :verify-guards nil))
  (if (atom observes) nil
    (let ((c (cddar observes)))
      (cons `(,(fn2-event-keyword->code (caar observes))
              (and (member-equal from ',(fn2-machine-phase-indices
                                          (or (fn2-arm-get :from c) (fn2-machine-observe-default-from states))
                                          states))
                   (or (equal next from)
                       (member-equal next ',(fn2-machine-phase-indices (fn2-arm-get :next c) states)))))
            (fn2-machine-observe-next-cases (cdr observes) states)))))
(defun fn2-machine-certificate-events (name world)
  (declare (xargs :verify-guards nil))
  (let ((arms (fn2-machine-property name :continuations world))
        (observes (fn2-machine-property name :observes world))
        (states (fn2-machine-property name :states world)))
    `((defun ,(fn2-columns-sym name "-ARM-CHARGE-OK-P") (phase bytes steps descriptors)
        (declare (xargs :guard t))
        (and (natp bytes) (natp steps) (natp descriptors)
             (case phase ,@(fn2-machine-charge-cases arms states 0 world) (otherwise nil))))
      (defun ,(fn2-columns-sym name "-ARM-BOUND") (phase)
        (declare (xargs :guard t))
        (case phase ,@(fn2-machine-bound-cases arms states 0 world) (otherwise 0)))
      (defun ,(fn2-columns-sym name "-ARM-NEXT-OK-P") (phase next)
        (declare (xargs :guard t))
        (case phase ,@(fn2-machine-next-cases arms states 0 states) (otherwise nil)))
      (defun ,(fn2-columns-sym name "-OBSERVE-NEXT-OK-P") (event from next)
        (declare (xargs :guard t) (ignorable from next))
        (case event ,@(fn2-machine-observe-next-cases observes states) (otherwise nil)))
      ; The asserts' conditions as opaque calls, so the generated entries'
      ; shape proofs never open them.
      (defun ,(fn2-columns-sym name "-ARM-OK-P") (id phase bytes steps descriptors fn2-core)
        (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
        (or (not (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*))
            (and (,(fn2-columns-sym name "-ARM-CHARGE-OK-P") phase bytes steps descriptors)
                 (eq (fn2-machine-phase-read-code id fn2-core) :ok)
                 (,(fn2-columns-sym name "-ARM-NEXT-OK-P") phase (fn2-machine-phase id fn2-core)))))
      (defun ,(fn2-columns-sym name "-OBSERVE-OK-P") (id event from fn2-core)
        (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
        (or (not (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*))
            (and (eq (fn2-machine-phase-read-code id fn2-core) :ok)
                 (,(fn2-columns-sym name "-OBSERVE-NEXT-OK-P") event from (fn2-machine-phase id fn2-core)))))
      (in-theory (disable ,(fn2-columns-sym name "-ARM-OK-P") ,(fn2-columns-sym name "-OBSERVE-OK-P"))))))

; Semantic checks over every arm once its callbacks exist (the :callbacks
; section): the evaluated cost within the kind's caps, a cap-reaching arm
; that can continue in its own phase, every use resolvable, the resource
; moves its phases imply, D0's effect rows, and its refusal posture.
(defun fn2-machine-unresolved-use (name uses world)
  (declare (xargs :verify-guards nil))
  (if (atom uses) nil
    (let ((u (fn2-arm-use-name (car uses))))
      (if (or (fn2-decl-row (list :cost u) world)
              (equal (fn2-decl-get :owner (fn2-operation-row u world)) (list :machine name)))
          (fn2-machine-unresolved-use name (cdr uses) world)
        u))))
(defconst *fn2-arm-postures* '(:close-and-release :discard-to-terminator :refuse-by-word :stop))
(defun fn2-machine-arm-problem (name entry observationp world)
  (declare (xargs :verify-guards nil))
  (let* ((tag (car entry)) (c (cddr entry))
         (budget (fn2-machine-property name :budget world))
         (caps (list (fn2-arm-get :bytes budget) (fn2-arm-get :steps budget) (fn2-arm-get :descriptors budget)))
         (v (fn2-cost-values (fn2-arm-get :cost c) world))
         (states (fn2-machine-property name :states world))
         (holds (fn2-machine-property name :holds world))
         (sources (if observationp (or (fn2-arm-get :from c) (fn2-machine-observe-default-from states))
                    (list tag)))
         (uses (fn2-arm-get :uses c))
         (posture (fn2-arm-get :on-refusal c)))
    (cond
     ((not (and (natp (car v)) (natp (cadr v)) (natp (caddr v))))
      (msg "~x0: arm ~x1's cost ~x2 cites a call with no declared cost." name tag (fn2-arm-get :cost c)))
     ((not (and (<= (car v) (car caps)) (<= (cadr v) (cadr caps)) (<= (caddr v) (caddr caps))))
      (msg "~x0: arm ~x1 costs ~x2 (bytes steps descriptors), over the per-run caps ~x3."
           name tag v caps))
     ((and (not observationp)
           (or (equal (car v) (car caps)) (equal (cadr v) (cadr caps)) (equal (caddr v) (caddr caps)))
           (not (member-eq tag (fn2-arm-get :next c))))
      (msg "~x0: arm ~x1 can reach a per-run cap (~x2 of ~x3) and must list its own phase in :next ~
            to continue there." name tag v caps))
     ((fn2-machine-unresolved-use name uses world)
      (msg "~x0: arm ~x1 uses ~x2, which is neither a defcost nor a callback of ~x0."
           name tag (fn2-machine-unresolved-use name uses world)))
     ((and (not (eq (fn2-arm-get :language c) :unchecked))
           (fn2-arm-resource-problem sources (fn2-arm-get :next c) holds uses world))
      (msg "~x0: arm ~x1 ~@2" name tag (fn2-arm-resource-problem sources (fn2-arm-get :next c) holds uses world)))
     ((not (fn2-resource-effects-p (remove-duplicates-equal (fn2-arm-effect-rows name sources uses holds world))
                                   *fn2-resource-order*))
      (msg "~x0: arm ~x1's resource effects fail D0's order: ~x2." name tag
           (fn2-arm-effect-rows name sources uses holds world)))
     ((and posture
           (not (and (true-listp posture) (member-eq (car posture) *fn2-arm-postures*)
                     (member-eq (fn2-arm-get :to (cdr posture)) (fn2-arm-get :next c)))))
      (msg "~x0: arm ~x1's :on-refusal ~x2 is (POSTURE :to PHASE [:releases KINDS]) with POSTURE in ~x3 ~
            and PHASE in its :next." name tag posture *fn2-arm-postures*))
     ((and posture
           (let ((released (fn2-arm-minus (fn2-arm-holds-of (car sources) holds)
                                          (fn2-arm-holds-of (fn2-arm-get :to (cdr posture)) holds))))
             (not (and (fn2-arm-subsetp released (fn2-arm-get :releases (cdr posture)))
                       (fn2-arm-subsetp (fn2-arm-get :releases (cdr posture)) released)))))
      (msg "~x0: arm ~x1's :on-refusal releases ~x2, but moving ~x3 -> ~x4 gives up ~x5." name tag
           (fn2-arm-get :releases (cdr posture)) (car sources) (fn2-arm-get :to (cdr posture))
           (fn2-arm-minus (fn2-arm-holds-of (car sources) holds)
                          (fn2-arm-holds-of (fn2-arm-get :to (cdr posture)) holds))))
     (t nil))))
(defun fn2-machine-arms-problem (name entries observationp world)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (or (fn2-machine-arm-problem name (car entries) observationp world)
        (fn2-machine-arms-problem name (cdr entries) observationp world))))

; ----------------------------------------------------------------------
; Owed obligations per arm (D's section 4 item 4), into fn2-squares with
; :from (:machine K): :bound, the arm's charge within its certificate;
; :invariant, its frame (only declared fields of its row and declared
; children change) and its continuation (the row's next phase is declared);
; per kind, phase totality. Teeth evaluate the certificates and the frame
; predicate on witnesses that satisfy and that falsify them.
(defun fn2-machine-child-index (field world)
  (declare (xargs :verify-guards nil))
  (position-eq field (strip-cars (unquote (getpropc '*fn2-core-children* 'const nil world)))))
(defun fn2-machine-table-children (names)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (fn2-columns-sym (car names) "-TABLE") (fn2-machine-table-children (cdr names)))))
(defun fn2-machine-machine-tables (world)
  (declare (xargs :verify-guards nil))
  (fn2-machine-table-children (fn2-machine-names world)))
(defun fn2-machine-child-indices-of (tables world)
  (declare (xargs :verify-guards nil))
  (if (atom tables) nil
    (let ((i (fn2-machine-child-index (car tables) world)))
      (append (and i (list i)) (fn2-machine-child-indices-of (cdr tables) world)))))
; fn2-core-machine-tables names every machine kind's table child.
(defun fn2-machine-child-indices (tables world)
  (declare (xargs :verify-guards nil))
  (fn2-machine-child-indices-of
   (if (member-eq 'fn2-core-machine-tables tables)
       (append (remove-eq 'fn2-core-machine-tables tables) (fn2-machine-machine-tables world))
     tables)
   world))
(defun fn2-machine-column-indices (fields columns)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((i (position-eq (car fields) (strip-cars columns))))
      (append (and i (list i)) (fn2-machine-column-indices (cdr fields) columns)))))
(defun fn2-machine-arm-pre (name phase-constant)
  (declare (xargs :verify-guards nil))
  `(and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
        (eq (,(fn2-columns-sym name "-SNAPSHOT-READ-CODE") id fn2-core) :ok)
        ,@(and phase-constant `((equal (fn2-machine-phase id fn2-core) ,phase-constant)))
        (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*)))
(defun fn2-machine-arm-rows (name arms world)
  (declare (xargs :verify-guards nil))
  (if (atom arms) nil
    (let* ((tag (caar arms)) (fn (cadar arms)) (c (cddar arms))
           (phase (fn2-columns-pre "*" (fn2-columns-sym (fn2-columns-col-name (fn2-columns-sym name "-STATE") tag) "*")))
           (cols (fn2-machine-property name :columns world))
           (table (fn2-machine-child-index (fn2-columns-sym name "-TABLE") world))
           (columns (fn2-machine-column-indices (cons 'phase (fn2-arm-get :writes c)) cols))
           (children (fn2-machine-child-indices (append (fn2-arm-get :tables c) *fn2-arm-implicit-tables*) world))
           (charge (fn2-columns-sym name "-ARM-CHARGE-OK-P"))
           (next (fn2-columns-sym name "-ARM-NEXT-OK-P"))
           (stem (fn2-columns-sym (fn2-columns-col-name name tag) "")))
      (append
       (list
       `(defthm-owed ,(fn2-columns-sym stem "-BOUND") (id budget fn2-core)
          (implies ,(fn2-machine-arm-pre name phase)
                   (mv-let (bytes steps descriptors runnable after) ,(fn2-machine-arm-call name fn '(id budget) nil world)
                     (declare (ignore runnable after))
                     (,charge ,phase bytes steps descriptors)))
          :schema :bound :from (:machine ,name)
          :teeth (,(fn2-columns-sym name "-ARM-CERTIFICATE-POSITIVE") ,(fn2-columns-sym name "-ARM-CERTIFICATE-NEGATIVE"))
          :doc ,(concatenate 'string "Arm " (symbol-name tag) " of " (symbol-name name)
                             " charges within its declared cost (the scalar-work certificate).")))
       ; An arm declared :language :unchecked states no frame: its body was not
       ; checked against :writes and :tables.
       (and (not (eq (fn2-arm-get :language c) :unchecked)) (list
       `(defthm-owed ,(fn2-columns-sym stem "-FRAME") (id budget fn2-core)
          (implies ,(fn2-machine-arm-pre name phase)
                   (let ((after (mv-nth 4 ,(fn2-machine-arm-call name fn '(id budget) nil world))))
                     (and (or (not (equal (fn2-core-stop-reason after) *fn2-stop-reason-none*))
                              (,next ,phase (fn2-machine-phase id after)))
                          (fn2-arm-framep ,table (fn2-machine-slot id fn2-core) ',columns ',children
                                          fn2-core after))))
          :schema :invariant :from (:machine ,name)
          :teeth (,(fn2-columns-sym name "-ARM-NEXT-POSITIVE") ,(fn2-columns-sym name "-ARM-NEXT-NEGATIVE")
                  fn2-arm-frame-positive fn2-arm-frame-negative)
          :doc ,(concatenate 'string "Arm " (symbol-name tag) " of " (symbol-name name)
                             " changes only its declared fields and children and moves only to a declared phase."))))
       (fn2-machine-arm-rows name (cdr arms) world)))))
(defun fn2-machine-observe-rows (name observes world)
  (declare (xargs :verify-guards nil))
  (if (atom observes) nil
    (let* ((tag (caar observes)) (fn (cadar observes)) (c (cddar observes))
           (cols (fn2-machine-property name :columns world))
           (table (fn2-machine-child-index (fn2-columns-sym name "-TABLE") world))
           (columns (fn2-machine-column-indices (cons 'phase (fn2-arm-get :writes c)) cols))
           (children (fn2-machine-child-indices (append (fn2-arm-get :tables c) *fn2-arm-implicit-tables*) world))
           (event (fn2-event-keyword->code tag))
           (stem (fn2-columns-sym (fn2-columns-col-name (fn2-columns-sym name "-OBSERVE") tag) "")))
      (append (and (not (eq (fn2-arm-get :language c) :unchecked)) (list
       `(defthm-owed ,(fn2-columns-sym stem "-FRAME") (id outcome reason count aux0 aux1 fn2-core)
          (implies ,(fn2-machine-arm-pre name nil)
                   (let ((after (mv-nth 1 ,(fn2-machine-arm-call name fn
                                             `(id ,event outcome reason count aux0 aux1) nil world))))
                     (and (or (not (equal (fn2-core-stop-reason after) *fn2-stop-reason-none*))
                              (,(fn2-columns-sym name "-OBSERVE-NEXT-OK-P") ,event
                               (fn2-machine-phase id fn2-core) (fn2-machine-phase id after)))
                          (fn2-arm-framep ,table (fn2-machine-slot id fn2-core) ',columns ',children
                                          fn2-core after))))
          :schema :invariant :from (:machine ,name)
          :teeth (fn2-arm-frame-positive fn2-arm-frame-negative)
          :doc ,(concatenate 'string "Handler " (symbol-name tag) " of " (symbol-name name)
                             " changes only its declared fields and children and moves only to a declared phase."))))
       (fn2-machine-observe-rows name (cdr observes) world)))))

; Teeth: the certificates accept every declared bound and successor and
; refuse one step beyond, an undeclared successor and an out-of-range phase.
(defun fn2-machine-certificate-positive-terms (charge arms states n world)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (let ((v (fn2-cost-values (fn2-arm-get :cost (cddr (assoc-eq (car states) arms))) world)))
      (cons `(,charge ,n ,(car v) ,(cadr v) ,(caddr v))
            (fn2-machine-certificate-positive-terms charge arms (cdr states) (+ 1 (nfix n)) world)))))
(defun fn2-machine-certificate-negative-terms (charge arms states n world)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (let ((v (fn2-cost-values (fn2-arm-get :cost (cddr (assoc-eq (car states) arms))) world)))
      (list* `(not (,charge ,n ,(+ 1 (car v)) ,(cadr v) ,(caddr v)))
             `(not (,charge ,n ,(car v) ,(+ 1 (cadr v)) ,(caddr v)))
             `(not (,charge ,n ,(car v) ,(cadr v) ,(+ 1 (caddr v))))
             (fn2-machine-certificate-negative-terms charge arms (cdr states) (+ 1 (nfix n)) world)))))
(defun fn2-machine-next-each (next n targets positivep)
  (declare (xargs :verify-guards nil))
  (if (atom targets) nil
    (cons (if positivep `(,next ,n ,(car targets)) `(not (,next ,n ,(car targets))))
          (fn2-machine-next-each next n (cdr targets) positivep))))
(defun fn2-machine-next-positive-terms (next arms states n all)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (append (fn2-machine-next-each next n (fn2-machine-phase-indices
                                           (fn2-arm-get :next (cddr (assoc-eq (car states) arms))) all) t)
            (fn2-machine-next-positive-terms next arms (cdr states) (+ 1 (nfix n)) all))))
(defun fn2-machine-next-negative-terms (next arms states n count all)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (append (fn2-machine-next-each next n
              (cons count (fn2-arm-minus (fn2-machine-phase-indices all all)
                                         (fn2-machine-phase-indices
                                          (fn2-arm-get :next (cddr (assoc-eq (car states) arms))) all)))
              nil)
            (fn2-machine-next-negative-terms next arms (cdr states) (+ 1 (nfix n)) count all))))
(defun fn2-machine-teeth-events (name world)
  (declare (xargs :verify-guards nil))
  (let* ((arms (fn2-machine-property name :continuations world))
         (states (fn2-machine-property name :states world))
         (charge (fn2-columns-sym name "-ARM-CHARGE-OK-P"))
         (next (fn2-columns-sym name "-ARM-NEXT-OK-P")))
    `((defun ,(fn2-columns-sym name "-ARM-CERTIFICATE-POSITIVE") ()
        (declare (xargs :guard t))
        (and ,@(fn2-machine-certificate-positive-terms charge arms states 0 world)))
      (defun ,(fn2-columns-sym name "-ARM-CERTIFICATE-NEGATIVE") ()
        (declare (xargs :guard t))
        (and (not (,charge ,(len states) 0 0 0))
             ,@(fn2-machine-certificate-negative-terms charge arms states 0 world)))
      (defun ,(fn2-columns-sym name "-ARM-NEXT-POSITIVE") ()
        (declare (xargs :guard t))
        (if (and ,@(fn2-machine-next-positive-terms next arms states 0 states)) t nil))
      (defun ,(fn2-columns-sym name "-ARM-NEXT-NEGATIVE") ()
        (declare (xargs :guard t))
        (and ,@(fn2-machine-next-negative-terms next arms states 0 (len states) states)))
      (defthm-owed ,(fn2-columns-sym name "-PHASE-TOTALITY") (id fn2-core)
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (eq (,(fn2-columns-sym name "-SNAPSHOT-READ-CODE") id fn2-core) :ok))
                 (< (fn2-machine-phase id fn2-core) ,(fn2-columns-pre "*" (fn2-columns-sym name "-STATE-COUNT*"))))
        :schema :invariant :from (:machine ,name)
        :teeth (,(fn2-columns-sym name "-ARM-CERTIFICATE-POSITIVE") ,(fn2-columns-sym name "-ARM-CERTIFICATE-NEGATIVE"))
        :doc ,(concatenate 'string "Every reachable " (symbol-name name)
                           " row is in a declared phase, each of which has an arm.")))))

(defun fn2-machine-capacities (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons `(nfix ,(fn2-machine-property (car names) :capacity world))
          (fn2-machine-capacities (cdr names) world))))
(defun fn2-machine-snapshot-calls (name columns)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (cons `(,(fn2-columns-col-name name (caar columns)) slot ,name)
          (fn2-machine-snapshot-calls name (cdr columns)))))
(defun fn2-machine-value-guards (columns vars)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (cons `(unsigned-byte-p ,(fn2-columns-width (cadar columns)) ,(car vars))
          (fn2-machine-value-guards (cdr columns) (cdr vars)))))
(defun fn2-machine-mv-fields (vars n call)
  (declare (xargs :verify-guards nil))
  (if (atom vars) nil
    (cons `(mv-nth ,n ,call) (fn2-machine-mv-fields (cdr vars) (+ 1 (nfix n)) call))))
(defun fn2-machine-row-reader-events (name columns code)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (let* ((reader (fn2-machine-row-reader name (caar columns)))
           (value `(,reader id fn2-core))
           (hyps '(and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))))
      (list* (fn2-operation-events (list :machine name) reader 'fn2-core '(id) :infer nil :access
               `(declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core)
                                                            (eq (,code id fn2-core) :ok))))
               `((if (eq (,code id fn2-core) :ok)
                     (let ((slot (fn2-machine-slot id fn2-core)))
                       (stobj-let ((,name (,(fn2-columns-sym name "-TABLE") fn2-core)))
                         (value) (,(fn2-columns-col-name name (caar columns)) slot ,name) value))
                   (prog2$ (hard-error ',reader "Invalid internal row read." nil) 0))) nil nil)
             `(defthm ,(fn2-columns-sym reader "-WIDTH")
                (implies ,hyps (unsigned-byte-p ,(fn2-columns-width (cadar columns)) ,value))
                :rule-classes (:rewrite
                  (:type-prescription :corollary (implies ,hyps (natp ,value)))
                  (:linear :corollary (implies ,hyps (< ,value ,(expt 2 (fn2-columns-width (cadar columns))))))
                  (:rewrite :corollary (implies ,hyps (and (rationalp ,value) (acl2-numberp ,value)))))
                :hints (("Goal" :in-theory (enable ,reader))))
             `(in-theory (disable ,reader))
             (fn2-machine-row-reader-events name (cdr columns) code)))))
(defun fn2-machine-snapshot-events (name columns)
  (declare (xargs :verify-guards nil))
  (let* ((code (fn2-columns-sym name "-SNAPSHOT-READ-CODE")) (owner (list :machine name)))
    `(,(fn2-operation-events owner code 'fn2-core '(id) :infer nil :access
         '(declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         `((let ((code (fn2-machine-phase-read-code id fn2-core)))
             (if (not (eq code :ok)) code
               (if (equal (fn2-machine-kind id fn2-core)
                          ,(fn2-columns-pre "*" (fn2-columns-sym name "-KIND*"))) :ok :kind)))) nil nil)
      ,@(fn2-machine-row-reader-events name columns code))))
(defun fn2-machine-all-snapshots (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (append (fn2-machine-snapshot-events (car names) (fn2-machine-property (car names) :columns world))
            (fn2-machine-all-snapshots (cdr names) world))))
; The submitted spelling check ignores quoted data and shadowed row names.
(defun fn2-callback-forwarding (form vars world)
  ; The registry lookup in a ruler is opaque to the termination proof.
  (declare (xargs :verify-guards nil :measure (acl2-count form)
                  :hints (("Goal" :in-theory (disable fn2-operation-row)))))
  (cond ((atom form) nil) ((eq (car form) 'quote) nil)
        ((and (symbolp (car form)) (fn2-decl-get :row-bindings (fn2-operation-row (car form) world))
              (intersection-eq vars (cdr form))) (car form))
        ((member-eq (car form) '(let let*))
         (or (fn2-callback-forwarding (cadr form) vars world)
             (fn2-callback-forwarding (cddr form)
               (set-difference-eq vars (strip-cars (cadr form))) world)))
        ((eq (car form) 'mv-let)
         (or (fn2-callback-forwarding (caddr form) vars world)
             (fn2-callback-forwarding (cdddr form)
               (set-difference-eq vars (cadr form)) world)))
        (t (or (fn2-callback-forwarding (car form) vars world)
               (fn2-callback-forwarding (cdr form) vars world)))))
(defun fn2-call-expand (form world)
  (declare (xargs :verify-guards nil))
  (cond ((atom form) form) ((eq (car form) 'quote) form)
        ((eq (car form) 'fn2-call)
         (let* ((row (fn2-operation-row (cadr form) world))
                (args (fn2-decl-get :args row)))
           (if (and row (equal (len args) (len (cddr form))))
               (cons (cadr form)
                 (sublis (pairlis$ args (cddr form)) (fn2-decl-get :calling-convention row)))
             (er hard 'fn2-call "Unknown callback or wrong argument count: ~x0." form))))
        (t (cons (fn2-call-expand (car form) world) (fn2-call-expand (cdr form) world)))))
(defun fn2-callback-reads (form vars)
  (cond ((atom form) (member-eq form vars)) ((eq (car form) 'quote) nil)
        (t (or (fn2-callback-reads (car form) vars) (fn2-callback-reads (cdr form) vars)))))
(defun fn2-callback-checked-body (body kind position)
  (declare (xargs :verify-guards nil))
  `((if (eq (,(fn2-columns-sym kind "-SNAPSHOT-READ-CODE") id fn2-core) :ok)
        (let () ,@body)
      (let ((fn2-core (fn2-core-stop
                       ,(if (equal position 1) '*fn2-stop-reason-machine-observation*
                          '*fn2-stop-reason-machine-phase*) fn2-core)))
        (mv ,@(if (equal position 1) '(*fn2-none*)
                (if (equal position 4) '(0 *fn2-work-empty* 0 nil)
                  (make-list position :initial-element 0))) fn2-core)))))
(defun fn2-callback-fresh-body (body kind vars all position)
  (declare (xargs :verify-guards nil))
  (if (eq (caar body) 'declare)
      (cons (car body) (fn2-callback-fresh-body (cdr body) kind vars all position))
    (if (fn2-callback-reads body vars)
        (fn2-callback-checked-body
         `((let ,(fn2-machine-read-bindings kind (fn2-machine-body-reads vars body) all)
            (declare (ignorable ,@(fn2-machine-body-reads vars body)))
            ,@body)) kind position)
      body)))
; Refresh from the returned core, never the proposed write values. LET* is
; lowered to nested LETs so every intervening read sees the current core.
; Fuel bounds the syntax transformation (three times the submitted tree size).
(defun fn2-callback-refresh (form kind vars all position fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((or (zp fuel) (atom form)) form)
        ((member-eq (car form) '(quote declare)) form)
        ((and (eq (car form) 'b*) (consp (cadr form)))
         (let ((binding (caadr form)))
           (fn2-callback-refresh
             (cond ((symbolp (car binding))
                    `(let (,binding) (b* ,(cdadr form) ,@(cddr form))))
                   ((eq (caar binding) 'mv)
                    `(mv-let ,(cdar binding) ,(cadr binding)
                       (b* ,(cdadr form) ,@(cddr form))))
                   (t (er hard 'defmachine-callback "Unsupported b* binder ~x0." binding)))
             kind vars all position (1- fuel))))
        ((and (eq (car form) 'let*) (consp (cadr form)))
         (fn2-callback-refresh
           `(let (,(caadr form))
              ,@(if (cdadr form) `((let* ,(cdadr form) ,@(cddr form))) (cddr form)))
           kind vars all position (1- fuel)))
        ((member-eq (car form) '(let mv-let))
         (let* ((mvp (eq (car form) 'mv-let))
                (bound (if mvp (cadr form) (strip-cars (cadr form))))
                (active (set-difference-eq vars bound))
                (body (fn2-callback-refresh (if mvp (cdddr form) (cddr form))
                                            kind active all position (1- fuel)))
                (body (if (member-eq 'fn2-core bound)
                          (fn2-callback-fresh-body body kind active all position) body)))
           (if mvp `(mv-let ,(cadr form)
                       ,(fn2-callback-refresh (caddr form) kind vars all position (1- fuel)) ,@body)
             `(let ,(fn2-callback-refresh (cadr form) kind vars all position (1- fuel)) ,@body))))
        (t (cons (fn2-callback-refresh (car form) kind vars all position (1- fuel))
                 (fn2-callback-refresh (cdr form) kind vars all position (1- fuel))))))
(defun fn2-callback-bad-binder (bindings)
  (if (atom bindings) nil
    (if (or (symbolp (caar bindings)) (eq (caaar bindings) 'mv))
        (fn2-callback-bad-binder (cdr bindings)) (car bindings))))
(defun fn2-callback-input-error (form world)
  (declare (xargs :verify-guards nil))
  (cond ((atom form) nil) ((eq (car form) 'quote) nil)
        ((and (eq (car form) 'fn2-call)
              (let ((row (fn2-operation-row (cadr form) world)))
                (or (not row) (not (equal (len (fn2-decl-get :args row)) (len (cddr form))))))) form)
        ((and (eq (car form) 'b*) (fn2-callback-bad-binder (cadr form))) form)
        (t (or (fn2-callback-input-error (car form) world)
               (fn2-callback-input-error (cdr form) world)))))
(defun fn2-machine-callback-event (name kind args position own body world)
  (declare (xargs :verify-guards nil))
  (let* ((all (butlast (cddr (fn2-decl-get :run
                                (fn2-machine-property kind :calling-convention world))) 1))
         (columns (fn2-machine-property kind :columns world))
         (vars (fn2-machine-body-reads all (fn2-call-expand body world)))
         (problem (fn2-callback-forwarding body all world)))
    (cond ((fn2-callback-input-error body world)
           `(make-event (er soft 'defmachine-callback
                          "~x0 has an unknown call, wrong arity or unsupported binder: ~x1."
                          ',name ',(fn2-callback-input-error body world))))
          (problem
        `(make-event (er soft 'defmachine-callback
                       "~x0 calls callback ~x1 with positional row fields; use fn2-call."
                       ',name ',problem)))
          (t (mv-let (refusal contract values) (fn2-machine-callback-contract name kind own body world)
           (if refusal `(make-event (er soft 'defmachine-callback "~@0" ',refusal))
            (fn2-operation-events (list :machine kind) name 'fn2-core args
          (append (make-list position :initial-element :value) '(fn2-core)) vars :callbacks
          `(declare (xargs :stobjs fn2-core
                     :guard (and (fn2-core-wfp fn2-core)
                                 ,@(fn2-machine-value-guards (fn2-machine-read-columns vars columns) vars)))
                    (ignorable ,@args ,@vars))
          (fn2-callback-checked-body
           (fn2-callback-refresh (fn2-call-expand body world) kind vars columns position (* 3 (acl2-count (fn2-call-expand body world)))) kind position)
          `((fn2-core-preserves ,name (,@args ,@vars fn2-core) :position ,position :rows nil))
          (list :writes (fn2-arm-get :writes contract) :cost (fn2-arm-get :cost contract)
                :refusal (fn2-arm-get :on-refusal contract) :contract contract :cost-values values))))))))
; ROW-<field> is the public scalar argument vocabulary, in declaration order.
; No resident list and no child/core alias crosses the callback boundary.
; An arm's callback takes its contract from its arm entry; a callback only
; forwarded to (fn2-call) gives :contract (:cost :writes :next :uses ...).
(defmacro defmachine-callback (name kind args position &rest body)
  (let ((own (and (eq (car body) :contract) (cadr body)))
        (body (if (eq (car body) :contract) (cddr body) body)))
    `(make-event (value (fn2-machine-callback-event ',name ',kind ',args ',position ',own ',body (w state))))))
(defun fn2-machine-run-event (name world)
  (declare (xargs :verify-guards nil))
  (let* ((run (fn2-columns-sym name "-RUN"))
         (problem (or (fn2-machine-arms-problem name (fn2-machine-property name :continuations world) nil world)
                      (fn2-machine-arms-problem name (fn2-machine-property name :observes world) t world))))
    (if problem `(make-event (er soft 'defmachine-run "~@0" ',problem))
    `(progn
       ,@(fn2-machine-certificate-events name world)
       ,(fn2-operation-events (list :machine name) run 'fn2-core '(id budget)
      '(bytes steps descriptors runnable fn2-core) nil :callbacks
      `(declare (xargs :stobjs fn2-core
                    :guard (and (fn2-core-wfp fn2-core)
                   (fn2-machine-idp id fn2-core)
                   (equal (fn2-machine-kind id fn2-core)
                          ,(fn2-columns-pre "*" (fn2-columns-sym name "-KIND*"))))))
      (fn2-callback-checked-body `((let ((row-phase (,(fn2-machine-row-reader name 'phase) id fn2-core)))
           (mv-let (bytes steps descriptors runnable fn2-core)
             (case row-phase
               ,@(fn2-machine-state-arms (fn2-machine-property name :states world)
                  (fn2-machine-property name :continuations world) 0 name world)
               (otherwise (fn2-machine-refuse-phase id fn2-core)))
             ; The arm's contract, asserted where it holds: its charge is
             ; within its certificate and its row moves only to a declared
             ; phase, or the core stops with a named reason.
             (fn2-machine-contract-check
              (,(fn2-columns-sym name "-ARM-OK-P") id row-phase bytes steps descriptors fn2-core)
              bytes steps descriptors runnable fn2-core)))) name 4)
      `((fn2-core-preserves ,run (id budget fn2-core) :position 4 :rows nil)) nil)
       ,@(fn2-machine-teeth-events name world)
       ,@(fn2-machine-arm-rows name (fn2-machine-property name :continuations world) world)
       ))))
(defmacro defmachine-run (name)
  `(make-event (value (fn2-machine-run-event ',name (w state)))))
(defun fn2-machine-observe-handlers (router names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names)) (handler (fn2-columns-col-name router name)))
      (append
       `((defun ,handler (id event outcome reason count aux0 aux1 fn2-core)
           (declare (xargs :stobjs fn2-core
                    :guard (and (fn2-core-wfp fn2-core)
                     (case event ,@(fn2-machine-observe-event-guards
                                    (fn2-machine-property name :observes world)) (otherwise nil)))))
           ,@(fn2-callback-checked-body `((let ((row-phase (,(fn2-machine-row-reader name 'phase) id fn2-core)))
             (mv-let (wake fn2-core)
               (case event
                 ,@(fn2-machine-observe-event-arms (fn2-machine-property name :observes world) nil
                    (list name world))
                 (otherwise (fn2-machine-refuse-observation fn2-core)))
               (fn2-machine-observe-contract-check
                (,(fn2-columns-sym name "-OBSERVE-OK-P") id event row-phase fn2-core)
                wake fn2-core)))) name 1))
         (fn2-core-preserves ,handler (id event outcome reason count aux0 aux1 fn2-core) :position 1 :rows nil))
       (fn2-machine-observe-handlers router (cdr names) world)))))
; The handlers' owed rows, once for the served router (machine-dispatch).
(defun fn2-machine-all-observe-rows (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (append (fn2-machine-observe-rows (car names) (fn2-machine-property (car names) :observes world) world)
            (fn2-machine-all-observe-rows (cdr names) world))))
(defun fn2-machine-observe-events (router names world)
  (declare (xargs :verify-guards nil))
  (let ((accepts (fn2-columns-sym router "-ACCEPTS-P")))
    (append (fn2-machine-observe-handlers router names world)
     `((defun ,accepts (kind phase event)
         (declare (xargs :guard t))
         (case kind ,@(fn2-machine-observe-kind-arms names 0 t router) (otherwise nil)))
       (defun ,router (okind id gen event outcome reason count aux0 aux1 fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (if (not (and (eq (fn2-machine-generation-read-code id fn2-core) :ok)
                       (eq (fn2-machine-phase-read-code id fn2-core) :ok)
                       (equal gen (fn2-machine-generation id fn2-core))
                       (equal okind (fn2-machine-kind id fn2-core))
                       (,accepts okind (fn2-machine-phase id fn2-core) event)))
             (fn2-machine-refuse-observation fn2-core)
           (mv-let (wake fn2-core)
             (case okind ,@(fn2-machine-observe-kind-arms names 0 nil router)
               (otherwise (fn2-machine-refuse-observation fn2-core)))
             ; Consume every completion before generic bookkeeping. A handler
             ; may accumulate many in-flight results without an event cell.
             (let ((fn2-core (if (equal event *fn2-event-borrow-released*) fn2-core
                               (fn2-machine-observe-terminal id fn2-core))))
               (if (not (and (eq (fn2-machine-wait-reason-read-code id fn2-core) :ok)
                             (eq (fn2-machine-stopped-read-code id fn2-core) :ok)))
                   (fn2-machine-refuse-observation fn2-core)
               (mv (if (or (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-operation*)
                           (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-storage-window*)
                           (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-connection-row*)
                           (equal (fn2-machine-stopped id fn2-core) 1)) *fn2-none* wake)
                   fn2-core))))))
       (fn2-core-preserves ,router (okind id gen event outcome reason count aux0 aux1 fn2-core) :position 1 :rows nil)))))

(defun fn2-machine-index-arms (names capacities base tag inverse)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (if inverse
              `(,tag (if (and (natp slot) (< slot ,(car capacities)))
                         (+ ,base slot) *fn2-none*))
            `((< id (+ ,base ,(car capacities))) (mv ,tag (- id ,base))))
          (fn2-machine-index-arms (cdr names) (cdr capacities)
                                  `(+ ,base ,(car capacities)) (+ 1 (nfix tag)) inverse))))
(defun fn2-machine-kind-constants (names tag)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons `(defconst ,(fn2-columns-pre "*" (fn2-columns-sym (car names) "-KIND*")) ,tag)
          (fn2-machine-kind-constants (cdr names) (+ 1 (nfix tag))))))
; The kinds the listener admits, in declaration order: each owns one slot of
; the directory's partition arrays (its ordinal).
(defconst *fn2-machine-admitted-max* 16)
(defun fn2-machine-admitted-in (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (if (fn2-machine-property (car names) :admission world)
        (cons (car names) (fn2-machine-admitted-in (cdr names) world))
      (fn2-machine-admitted-in (cdr names) world))))
(defun fn2-machine-admitted (world)
  (declare (xargs :verify-guards nil))
  (fn2-machine-admitted-in (fn2-machine-names world) world))
(defun fn2-machine-admission-cases (kinds n world what)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (cons (case what
            (:capacity `(,n (nfix ,(fn2-machine-property (car kinds) :capacity world))))
            (:base `(,n (fn2-machine-global-id ,(fn2-columns-pre "*" (fn2-columns-sym (car kinds) "-KIND*")) 0 profile)))
            (otherwise `(,(car kinds) ,n)))
          (fn2-machine-admission-cases (cdr kinds) (+ 1 (nfix n)) world what))))
(defun fn2-machine-admission-ordinal-constants (kinds n)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (cons `(defconst ,(fn2-columns-pre "*" (fn2-columns-sym (car kinds) "-ADMISSION-ORDINAL*")) ,n)
          (fn2-machine-admission-ordinal-constants (cdr kinds) (+ 1 (nfix n))))))
(defun fn2-machine-admission-index-events (kinds world)
  (declare (xargs :verify-guards nil))
  (if (> (len kinds) *fn2-machine-admitted-max*)
      (er hard 'defmachine "At most ~x0 kinds may be admitted by the listener: ~x1." *fn2-machine-admitted-max* kinds)
    `((defconst *fn2-machine-admitted* ',kinds)
      ,@(fn2-machine-admission-ordinal-constants kinds 0)
      (defun fn2-machine-admitted-capacity (ord profile)
        (declare (xargs :guard t) (ignorable profile))
        (case ord ,@(fn2-machine-admission-cases kinds 0 world :capacity) (otherwise 0)))
      (defun fn2-machine-admitted-base (ord profile)
        (declare (xargs :guard t) (ignorable profile))
        (case ord ,@(fn2-machine-admission-cases kinds 0 world :base) (otherwise *fn2-none*)))
      ; A profile names the kind its listeners admit (:listener-targets);
      ; absent or unknown, the first admitted kind (echo in layer A).
      (defun fn2-machine-admission-ordinal-of (name)
        (declare (xargs :guard t))
        (case name ,@(fn2-machine-admission-cases kinds 0 world :ordinal) (otherwise 0))))))
(defmacro fn2-machine-index-events ()
  '(progn (fn2-seal :machines :index :machine)
    (make-event
    (let* ((names (fn2-machine-names (w state)))
           (caps (fn2-machine-capacities names (w state))))
      (value
       `(progn
          ,@(fn2-machine-kind-constants names 0)
          (defun fn2-machine-index-count (profile)
            (declare (xargs :guard t))
            (+ ,@caps))
          (defun fn2-machine-global-id (kind slot profile)
            (declare (xargs :guard t))
            (case kind ,@(fn2-machine-index-arms names caps 0 0 t)
              (otherwise *fn2-none*)))
          (defun fn2-machine-local-id (id profile)
            (declare (xargs :guard t))
            (if (not (natp id)) (mv 255 0)
              (cond ,@(fn2-machine-index-arms names caps 0 0 nil)
                    (t (mv 255 0)))))
          ,@(fn2-machine-admission-index-events (fn2-machine-admitted (w state)) (w state))))))
(fn2-resolve :index)
))

(defun fn2-machine-run-arms (names tag)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons `(,tag (,(fn2-columns-sym (car names) "-RUN") id budget fn2-core))
          (fn2-machine-run-arms (cdr names) (+ 1 (nfix tag))))))
(defun fn2-machine-arm-certificate-arms (names tag boundp)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (if boundp `(,tag (,(fn2-columns-sym (car names) "-ARM-BOUND") phase))
            `(,tag (,(fn2-columns-sym (car names) "-ARM-CHARGE-OK-P") phase bytes steps descriptors)))
          (fn2-machine-arm-certificate-arms (cdr names) (+ 1 (nfix tag)) boundp))))
(defun fn2-machine-charge-arms (names tag)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons `(,tag (,(fn2-columns-sym (car names) "-CHARGE") bytes steps descriptors))
          (fn2-machine-charge-arms (cdr names) (+ 1 (nfix tag))))))

(defun fn2-machine-charge-guards (names world tag)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((budget (fn2-machine-property (car names) :budget world)))
      (cons `(,tag (and (natp bytes) (<= bytes ,(cadr (member-eq :bytes budget)))
                        (natp steps) (<= steps ,(cadr (member-eq :steps budget)))
                        (natp descriptors) (<= descriptors ,(cadr (member-eq :descriptors budget)))))
            (fn2-machine-charge-guards (cdr names) world (+ 1 (nfix tag)))))))

; Core access and dispatch emitters consume the same registry.
(defun fn2-machine-child-shapes (children)
  (if (atom children) nil
    (cons `(,(fn2-columns-sym (cadar children) "-WFP") (,(caar children) fn2-core))
          (fn2-machine-child-shapes (cdr children)))))
(defun fn2-machine-row-readers (names)
  (if (atom names) nil
    (cons (fn2-columns-sym (car names) "-ROWS") (fn2-machine-row-readers (cdr names)))))
(defun fn2-machine-checked-reader-events (get args code-body value-body)
  (declare (xargs :verify-guards nil))
  (let* ((code (fn2-columns-sym get "-READ-CODE"))
         (read (fn2-columns-sym get "-READ"))
         (call `(,@args fn2-core)) (owner '(:columns fn2-machines))
         (guard '(fn2-core-wfp fn2-core)))
    (list
     (fn2-operation-events owner code 'fn2-core args :infer nil :access
       `(declare (xargs :stobjs fn2-core :guard ,guard)) (list code-body) nil nil)
     (fn2-operation-events owner get 'fn2-core args :infer nil :access
       `(declare (xargs :stobjs fn2-core :guard (and ,guard (eq (,code ,@call) :ok))))
       `((if (eq (,code ,@call) :ok) ,value-body
           (prog2$ (hard-error ',get "Invalid internal machine read." nil) 0))) nil nil)
     (fn2-operation-events owner read 'fn2-core args :infer nil :access
       `(declare (xargs :stobjs fn2-core :guard ,guard))
       `((let ((code (,code ,@call)))
           (if (eq code :ok) (mv :ok (,get ,@call)) (mv code nil)))) nil nil))))

(defun fn2-machine-field-cases (field names world tag writep)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names)) (cols (fn2-machine-property name :columns world))
           (entry (assoc-eq field cols))
           (reader (fn2-columns-col-name name field))
           (writer (fn2-columns-col-name name (fn2-columns-pre "SET-" field))))
      (append
       (if entry
           `((,tag (stobj-let ((,name (,(fn2-columns-sym name "-TABLE") fn2-core)))
                     ,(if (eq writep t) (list name) '(answer))
                     ,(cond ((eq writep :code)
                              `(if (and (natp slot) (< slot (,(fn2-columns-sym name "-ROWS") ,name))) :ok :bounds))
                             ((eq writep :value) `(,reader slot ,name))
                             (t `(if (and (natp slot) (< slot (,(fn2-columns-sym name "-ROWS") ,name)))
                                     (,writer slot value ,name) ,name)))
                     ,(if (eq writep t) 'fn2-core 'answer)))) nil)
       (fn2-machine-field-cases field (cdr names) world (+ 1 (nfix tag)) writep)))))
(defun fn2-machine-field-readers (field names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (append (and (assoc-eq field (fn2-machine-property (car names) :columns world))
                 (list (fn2-columns-col-name (car names) field)))
            (fn2-machine-field-readers field (cdr names) world))))
(defun fn2-machine-field-kinds (field names world tag)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (append (and (assoc-eq field (fn2-machine-property (car names) :columns world))
                 (list tag))
            (fn2-machine-field-kinds field (cdr names) world (+ 1 (nfix tag))))))
(defun fn2-machine-field-fits (field names world tag)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((entry (assoc-eq field (fn2-machine-property (car names) :columns world))))
      (append (and entry (list (list tag (fn2-columns-fit (cadr entry) 'value))))
              (fn2-machine-field-fits field (cdr names) world (+ 1 (nfix tag)))))))
(defun fn2-machine-field-events (field kind names world)
  (declare (xargs :verify-guards nil))
  (let* ((get (fn2-columns-col-name 'fn2-machine field))
         (put (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "SET-" field)))
         (write (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "WRITE-" field)))
         (width (fn2-columns-width kind))
         (supported (fn2-machine-field-kinds field names world 0))
         (valid `(and (unsigned-byte-p ,width value) (fn2-machine-idp id fn2-core)
                      (member-equal (fn2-machine-kind id fn2-core) ',supported)
                      (case (fn2-machine-kind id fn2-core)
                        ,@(fn2-machine-field-fits field names world 0) (otherwise nil)))))
    `((in-theory (disable ,@(fn2-machine-field-readers field names world)))
      ,@(fn2-machine-checked-reader-events get '(id)
          `(if (not (fn2-machine-idp id fn2-core)) :bounds
             (let ((slot (fn2-machine-slot id fn2-core)))
               (case (fn2-machine-kind id fn2-core)
                 ,@(fn2-machine-field-cases field names world 0 :code) (otherwise :kind))))
          `(let ((slot (fn2-machine-slot id fn2-core)))
             (case (fn2-machine-kind id fn2-core)
               ,@(fn2-machine-field-cases field names world 0 :value) (otherwise 0))))
      (defthm ,(fn2-columns-sym get "-NATP")
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (natp (,get id fn2-core)))
        :rule-classes :type-prescription)
      (defthm ,(fn2-columns-sym get "-BOUND")
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                 (< (,get id fn2-core) ,(expt 2 width))) :rule-classes :linear)
      (defun ,put (id value fn2-core)
        (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) ,valid)))
        (if (not ,valid) fn2-core
          (let ((slot (if (fn2-machine-idp id fn2-core) (fn2-machine-slot id fn2-core) *fn2-none*)))
            (case (fn2-machine-kind id fn2-core)
              ,@(fn2-machine-field-cases field names world 0 t) (otherwise fn2-core)))))
      (defthm ,(fn2-columns-sym put "-TYPE")
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (fn2-corep (,put id value fn2-core))))
      ; Through core.lisp's per-child facts: each case sees only its own table.
      (defthm ,(fn2-columns-sym put "-WFP")
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                 (fn2-core-wfp (,put id value fn2-core))))
      (in-theory (disable ,get ,put))
      (defun ,write (id value fn2-core)
        (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
        (if ,valid (,put id value fn2-core) (fn2-machine-refuse-write fn2-core)))
      (defthm ,(fn2-columns-sym write "-TYPE")
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                 (fn2-corep (,write id value fn2-core))))
      (defthm ,(fn2-columns-sym write "-WFP")
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                 (fn2-core-wfp (,write id value fn2-core))))
      (in-theory (disable ,write)))))
(defun fn2-machine-fields-events (fields cols names world)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (append (fn2-machine-field-events (car fields) (cadr (assoc-eq (car fields) cols)) names world)
            (fn2-machine-fields-events (cdr fields) cols names world))))
(defun fn2-machine-all-field-events (names all world seen)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((cols (fn2-machine-property (car names) :columns world))
           (new (set-difference-eq (strip-cars cols) seen)))
      (append (fn2-machine-fields-events new cols all world)
              (fn2-machine-all-field-events (cdr names) all world (append new seen))))))
(defmacro fn2-machine-put (id &rest fields)
  (if (assoc-eq 'phase fields)
      (er hard 'defmachine "Phase writes require the kind's PUT-CORE macro.")
    `(let* ,(fn2-columns-put-bindings 'fn2-machine-write 'fn2-core id fields) fn2-core)))
(defmacro fn2-machine-result (bytes steps descriptors runnable core)
  `(fn2-machine-finish id ,bytes ,steps ,descriptors ,runnable ,core))


(defmacro fn2-machine-scalar-access (field width)
  (let* ((reader (fn2-columns-col-name 'fn2-machines field))
         (writer (fn2-columns-pre "UPDATE-" reader))
         (get (fn2-columns-col-name 'fn2-machine field))
         (put (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "SET-" field))))
    `(progn
       (in-theory (disable ,reader))
       (defun ,get (fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
           (answer) (,reader fn2-machines) answer))
       (defthm ,(fn2-columns-sym get "-NATP")
         (implies (fn2-corep fn2-core) (natp (,get fn2-core)))
         :rule-classes :type-prescription)
       (defthm ,(fn2-columns-sym get "-BOUND")
         (implies (fn2-corep fn2-core) (< (,get fn2-core) ,(expt 2 width)))
         :rule-classes :linear)
       ; An over-width value is a caller's bug: the core stops with the
       ; machine-write reason, never a dropped write (REVIEW-20261030).
       (defun ,put (value fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (if (not (unsigned-byte-p ,width value))
             (fn2-core-stop *fn2-stop-reason-machine-write* fn2-core)
           (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
             (fn2-machines) (,writer value fn2-machines) fn2-core)))
       (defthm ,(fn2-columns-sym put "-TYPE")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (fn2-corep (,put value fn2-core))))
       (defthm ,(fn2-columns-sym put "-WFP")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (fn2-core-wfp (,put value fn2-core))))
       (in-theory (disable ,get ,put)))))

; The generated router's one case: an observation it cannot deliver (stale
; generation, wrong kind, a phase that does not observe the event). Its
; contract is the composite effect of the executor's harvest transition.
(make-event
 (value (fn2-declare '(:operation-set fn2-machine-router)
          '(:cases ((:router :fallback))
            :doc "Unrouted observation: the generated router's refusal inside harvest.")
          nil nil)))

; ----------------------------------------------------------------------
; Admission (D's section 4.5): per admitted kind K with ordinal O, the
; allocator operations the listener's admission uses, generated from K's
; :admission. fn2-machine-admit-K takes O's free head, reserves K's ranges
; (all or none), installs the row in its admission phase and wakes it;
; fn2-machine-reclaim-K returns a drained row to O's free chain with its
; credit (unless it retires). fn2-machine-admit dispatches on the target
; ordinal a listener row carries. Each K's operation declares its exact
; effects and target, checked against K's :holds here.
;; The listener's offer: the fields of a listener row an admitted kind may copy
;; (`:copy`), in the dispatcher's argument order. Fixed, so the listener's call
;; is one form whatever kinds a build admits.
(defconst *fn2-machine-listener-offer* '(mode principal-slot account-ref))
(defun fn2-machine-admission-copies (kinds world)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (union-eq (fn2-arm-get :copy (fn2-machine-property (car kinds) :admission world))
              (fn2-machine-admission-copies (cdr kinds) world))))
(defun fn2-machine-copy-guards (copies kind world)
  (declare (xargs :verify-guards nil))
  (if (atom copies) nil
    (cons `(unsigned-byte-p ,(fn2-columns-width (cadr (assoc-eq (car copies) (fn2-machine-property kind :columns world))))
                            ,(car copies))
          (fn2-machine-copy-guards (cdr copies) kind world))))
(defun fn2-machine-range-puts (specs n)
  (declare (xargs :verify-guards nil))
  (if (atom specs) nil
    (list* (list (fn2-arm-get :slot (cdar specs)) (packn-pos (list 'slot n) 'fn2-core))
           (list (fn2-arm-get :gen (cdar specs)) (packn-pos (list 'pgen n) 'fn2-core))
           (fn2-machine-range-puts (cdr specs) (+ 1 (nfix n))))))
(defun fn2-machine-range-releases (n kind body)
  ; release ranges 0..n-1 (descending) then BODY
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) body
    (let ((i (- n 1)))
      `(mv-let (rc fn2-core)
         (fn2-core-release ,(packn-pos (list 'slot i) 'fn2-core) ,(packn-pos (list 'pgen i) 'fn2-core)
                           ,kind target gen fn2-core)
         (declare (ignore rc))
         ,(fn2-machine-range-releases i kind body)))))
(defun fn2-machine-range-reserves (specs n kind install)
  (declare (xargs :verify-guards nil))
  (if (atom specs) install
    (let ((code (packn-pos (list 'code n) 'fn2-core)))
      `(mv-let (,code ,(packn-pos (list 'slot n) 'fn2-core) ,(packn-pos (list 'pgen n) 'fn2-core) fn2-core)
         (fn2-core-reserve ,(fn2-arm-get :class (cdar specs)) ,kind target gen fn2-core)
         (if (not (eq ,code :ok))
             ,(fn2-machine-range-releases n kind '(mv :pool fn2-core))
           ,(fn2-machine-range-reserves (cdr specs) (+ 1 (nfix n)) kind install))))))
(defun fn2-machine-zero-puts (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil (cons (list (car fields) 0) (fn2-machine-zero-puts (cdr fields)))))
(defun fn2-machine-copy-puts (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil (cons (list (car fields) (car fields)) (fn2-machine-copy-puts (cdr fields)))))
(defun fn2-machine-admission-kind-events (kind o world)
  (declare (xargs :verify-guards nil))
  (let* ((adm (fn2-machine-property kind :admission world))
         (specs (fn2-machine-range-specs (fn2-arm-get :ranges adm)))
         (copies (fn2-arm-get :copy adm))
         (kconst (fn2-columns-pre "*" (fn2-columns-sym kind "-KIND*")))
         (phase (fn2-columns-pre "*" (fn2-columns-sym (fn2-columns-col-name (fn2-columns-sym kind "-STATE")
                                                                           (fn2-arm-get :phase adm)) "*")))
         (admit (fn2-columns-sym 'fn2-machine-admit- (symbol-name kind)))
         (reclaim (fn2-columns-sym 'fn2-machine-reclaim- (symbol-name kind)))
         (install
          `(let* ((fn2-core (fn2-machine-set-free-head ,o next fn2-core))
                  (fn2-core (fn2-machine-set-active-count ,o (+ 1 (fn2-machine-active-count ,o fn2-core)) fn2-core))
                  (fn2-core (,(fn2-columns-sym kind "-PUT-CORE") target
                             (phase ,phase) (cap-index index) (cap-nonce nonce)
                             ,@(fn2-machine-range-puts specs 0)
                             ,@(fn2-machine-copy-puts copies)
                             ,@(fn2-machine-zero-puts (fn2-arm-get :clear adm))
                             (wait-reason *fn2-wait-none*)))
                  (fn2-core (fn2-machine-set-wake-id target fn2-core)))
             (mv :ok fn2-core))))
    `((fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
       (defun ,admit (index nonce ,@copies fn2-core)
         (declare (xargs :stobjs fn2-core
                         :guard (and (fn2-core-wfp fn2-core) (unsigned-byte-p 32 index) (unsigned-byte-p 32 nonce)
                                     ,@(fn2-machine-copy-guards copies kind world))))
         (let ((target (fn2-machine-free-head ,o fn2-core)))
           (if (or (equal target *fn2-none*)
                   (not (eq (fn2-machine-generation-read-code target fn2-core) :ok))
                   (not (eq (fn2-machine-next-free-read-code target fn2-core) :ok))
                   (>= (fn2-machine-active-count ,o fn2-core) (fn2-machine-connection-count ,o fn2-core)))
               (mv :no-row fn2-core)
             (let ((gen (fn2-machine-generation target fn2-core))
                   (next (fn2-machine-next-free target fn2-core)))
               ,(fn2-machine-range-reserves specs 0 kconst install))))))
      (fn2-core-preserves ,admit (index nonce ,@copies fn2-core) :position 1 :rows nil :prefix "")
      (fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
       (defun ,reclaim (id retire fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (let* ((fn2-core (if retire fn2-core (fn2-machine-set-free-head ,o id fn2-core)))
                (fn2-core (if retire fn2-core
                            (fn2-machine-set-admission-credits ,o (+ 1 (fn2-machine-admission-credits ,o fn2-core))
                                                               fn2-core)))
                (active (fn2-machine-active-count ,o fn2-core)))
           (fn2-machine-set-active-count ,o (if (zp active) 0 (- active 1)) fn2-core))))
      (fn2-core-preserves ,reclaim (id retire fn2-core) :rows nil :prefix "")
      (defcost ,admit :tables (fn2-core-machines fn2-core-pool ,(fn2-columns-sym kind "-TABLE"))
        :effects ((:transfer (:connection-row) :to ,kind)
                  (:acquire ,(strip-cars specs) :for ,kind))
        :target (,kind :free ,(fn2-arm-get :phase adm))
        :doc ,(concatenate 'string "Admit an accepted connection as a " (symbol-name kind) " row."))
      (defcost ,reclaim :tables (fn2-core-machines) :effects ((:release (:connection-row)))
        :doc ,(concatenate 'string "Return a drained " (symbol-name kind) " row to its partition.")))))
(defun fn2-machine-admission-all-events (kinds o world)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (append (fn2-machine-admission-kind-events (car kinds) o world)
            (fn2-machine-admission-all-events (cdr kinds) (+ 1 (nfix o)) world))))
(defun fn2-machine-admit-arms (kinds o world)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (cons `(,o (,(fn2-columns-sym 'fn2-machine-admit- (symbol-name (car kinds))) index nonce
                ,@(fn2-arm-get :copy (fn2-machine-property (car kinds) :admission world)) fn2-core))
          (fn2-machine-admit-arms (cdr kinds) (+ 1 (nfix o)) world))))
(defun fn2-machine-admit-names (kinds)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (cons (fn2-columns-sym 'fn2-machine-admit- (symbol-name (car kinds))) (fn2-machine-admit-names (cdr kinds)))))
(defun fn2-machine-books-arms (kinds o world)
  ; ordinals of the admitted kinds whose admission copies account-ref (D7's S1)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (append (and (member-eq 'account-ref (fn2-arm-get :copy (fn2-machine-property (car kinds) :admission world)))
                 (list o))
            (fn2-machine-books-arms (cdr kinds) (+ 1 (nfix o)) world))))
(defun fn2-machine-admission-events-form (world)
  (declare (xargs :verify-guards nil))
  (let* ((kinds (fn2-machine-admitted world))
         (copies *fn2-machine-listener-offer*))
    (if (not (subsetp-eq (fn2-machine-admission-copies kinds world) copies))
        (er hard 'fn2-machine-admission "An admitted kind's :copy names a field outside the listener's offer ~x0: ~x1."
            copies (fn2-machine-admission-copies kinds world))
    `(progn
       ,@(fn2-machine-admission-all-events kinds 0 world)
       (fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
        (defun fn2-machine-admit (target index nonce ,@copies fn2-core)
          (declare (xargs :stobjs fn2-core
                          :guard (and (fn2-core-wfp fn2-core) (unsigned-byte-p 32 index) (unsigned-byte-p 32 nonce)
                                      ,@(fn2-machine-copy-guards copies 'fn2-listener world)))
                   (ignorable ,@copies))
          (case target ,@(fn2-machine-admit-arms kinds 0 world) (otherwise (mv :no-row fn2-core)))))
       (fn2-core-preserves fn2-machine-admit (target index nonce ,@copies fn2-core) :position 1 :rows nil :prefix "")
       ; D7's S1: a listener books its principal's :connection-row at Accept
       ; issue only for a target kind whose admission copies account-ref (the
       ; row then carries the booking and releases it at drain).
       (defun fn2-machine-admission-books-p (target)
         (declare (xargs :guard t))
         (if (member-equal target ',(fn2-machine-books-arms kinds 0 world)) t nil))
       (defcost fn2-machine-admission-books-p
         :doc "Whether the listener's target kind carries a principal booking (its admission copies account-ref).")
       ; The listener sees one transfer of its reserved row; each kind's own
       ; operation carries the exact effects, checked against its :holds below.
       (defcost fn2-machine-admit :tables (fn2-core-machines fn2-core-pool fn2-core-machine-tables)
         :effects ((:transfer (:connection-row) :to :admitted))
         :doc "Admit into the listener's target kind (dispatch on the admitted-kind ordinal).")
       (make-event
        (let ((problem (fn2-arm-target-problem ',(fn2-machine-admit-names kinds) (w state))))
          (if problem (er soft 'fn2-machine-admission "~@0" problem)
            (value '(value-triple :admission-effects-checked)))))))))
(defmacro fn2-machine-admission-events ()
  '(make-event (value (fn2-machine-admission-events-form (w state)))))
