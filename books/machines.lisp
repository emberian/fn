; Machine declarations extend columns; all lists below are expansion-time data.
; Continuation calls are finite tags, never function-valued resident fields.
(in-package "ACL2")
(include-book "vocab")
(include-book "arms")

; A wait reason names what the row waits for: nothing, an operation's
; completion (not a resource: its result cells were reserved at issue), or
; the D0 resource kind that was exhausted (books/resources.lisp).
(defconst *fn2-machine-common-fields*
  `((generation :u60) (principal-slot :u16) (account-ref :u32)
    (ready-prev :link) (ready-next :link)
    (wait-reason (:enum fn2-wait (:none :completion ,@(strip-cars *fn2-resource-order*))))
    (deadline :u60)))
; MACHINE-FORM 6.5 P1: the row fields generic code writes across rows (the
; resource FIFOs' links, the wait reason the grant service clears) are
; columns of the directory fn2-machines, indexed by id, not of each kind's
; table: a park or a grant touches the directory and no kind's table. A
; kind's row is still all of *fn2-machine-common-fields* (its :columns);
; its table (:table) is the rest.
(defconst *fn2-machine-directory-fields*
  (list (assoc-eq 'ready-prev *fn2-machine-common-fields*)
        (assoc-eq 'ready-next *fn2-machine-common-fields*)
        (assoc-eq 'wait-reason *fn2-machine-common-fields*)))
(defun fn2-machine-directory-fieldp (field)
  (declare (xargs :guard t))
  (and (assoc-eq field *fn2-machine-directory-fields*) t))
(defun fn2-machine-table-columns (cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (if (fn2-machine-directory-fieldp (caar cols)) (fn2-machine-table-columns (cdr cols))
      (cons (car cols) (fn2-machine-table-columns (cdr cols))))))
; A kind's :initial for a directory field may only restate its default (the
; directory initializes every row).
(defun fn2-machine-directory-initial-p (initial)
  (declare (xargs :verify-guards nil))
  (if (atom initial) t
    (and (or (not (fn2-machine-directory-fieldp (caar initial)))
             (equal (cadar initial)
                    (if (eq (cadr (assoc-eq (caar initial) *fn2-machine-directory-fields*)) :link)
                        '*fn2-none* 0)))
         (fn2-machine-directory-initial-p (cdr initial)))))
(make-event (value (cons 'progn (fn2-columns-enum-events *fn2-machine-directory-fields*))))

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
(defun fn2-machine-directory-writes (fields directoryp)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (if (eq (fn2-machine-directory-fieldp (caar fields)) directoryp)
        (cons (car fields) (fn2-machine-directory-writes (cdr fields) directoryp))
      (fn2-machine-directory-writes (cdr fields) directoryp))))
(defun fn2-machine-core-put-expansion (name columns states id fields corep)
  (declare (xargs :verify-guards nil))
  (if (fn2-columns-write-formp name columns states fields)
      (if corep
          (let* ((values (fn2-machine-write-fields fields))
                 (own (fn2-machine-directory-writes values nil))
                 (dir (fn2-machine-directory-writes values t)))
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
                         (let* ,(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name 'fn2-write-slot own) (mv t ,name))
                       (mv nil ,name))
                     (if fn2-write-accepted
                         ,(if dir
                              ; The directory's fields of the batch, checked with the rest above.
                              `(stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
                                 (fn2-machines)
                                 (if (and (natp fn2-write-id) (< fn2-write-id (fn2-machines-rows fn2-machines)))
                                     (let* ,(fn2-columns-put-bindings 'fn2-machines-set 'fn2-machines 'fn2-write-id dir)
                                       fn2-machines)
                                   fn2-machines)
                                 fn2-core)
                            'fn2-core)
                       (fn2-machine-refuse-write fn2-core)))))))
        `(let* ,(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name id fields) ,name))
    (er hard 'defmachine "Invalid field list or cross-kind phase in ~x0 write: ~x1." name fields)))

;; The child-form write (MACHINE-FORM 6.5 P3): the row at SLOT of the
;; kind's table and at ID of the directory, the whole batch checked first; a
;; refused batch stops the core. Returns (mv K fn2-machines fn2-control).
(defun fn2-machine-children-put-expansion (name columns states id slot fields)
  (declare (xargs :verify-guards nil))
  (if (fn2-columns-write-formp name columns states fields)
      (let* ((values (fn2-machine-write-fields fields))
             (own (fn2-machine-directory-writes values nil))
             (dir (fn2-machine-directory-writes values t)))
        `(let ((fn2-write-id ,id) (fn2-write-slot ,slot) ,@(fn2-machine-write-values fields))
           (declare (ignorable fn2-write-id))
           (if (and (natp fn2-write-slot) (< fn2-write-slot (,(fn2-columns-sym name "-ROWS") ,name))
                    ,@(and dir '((natp fn2-write-id) (< fn2-write-id (fn2-machines-rows fn2-machines))))
                    ,@(fn2-machine-write-guards values columns))
               (let* (,@(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name 'fn2-write-slot own)
                      ,@(fn2-columns-put-bindings 'fn2-machines-set 'fn2-machines 'fn2-write-id dir))
                 (mv ,name fn2-machines fn2-control))
             (let ((fn2-control (fn2-control-record-stop *fn2-stop-reason-machine-write* fn2-control)))
               (mv ,name fn2-machines fn2-control)))))
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
;; tx-gen, class 0) or (KIND :slot F :gen F [:class C]). C is a class number
;; or (:bytes B): the profile's smallest class of at least B octets
;; (fn2-pool-class-for, chosen at admission; none such refuses it :pool), B a
;; number or a constant's name; (:bytes B) is for a kind whose registry is in
;; child form (defmachine-registry). :copy names listener fields copied into
;; the row at admission; :clear fields are zeroed. The row needs a :link
;; next-free field (its partition's free chain).
(defun fn2-machine-class-specp (c)
  (declare (xargs :guard t))
  (or (natp c)
      (and (true-listp c) (equal (len c) 2) (eq (car c) :bytes)
           (or (natp (cadr c)) (and (symbolp (cadr c)) (cadr c) (not (keywordp (cadr c))))))))
;; The class expression a reservation takes over the pool stobj POOL.
(defun fn2-machine-class-form (c pool)
  (declare (xargs :guard t))
  (if (and (consp c) (eq (car c) :bytes) (consp (cdr c)))
      `(fn2-pool-class-for ,(cadr c) ,pool)
    c))
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
         (fn2-machine-class-specp (fn2-arm-get :class (cdar specs)))
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
;; :taken (:phase P :rows ROWKIND :ranges RANGES [:copy (FIELD ...)] [:clear (FIELD ...)])
;; (D's A-S7, layer doc 14.7): the kind's rows are taken by another machine's
;; arm, not by the listener. It owns a partition like an admitted kind (free
;; chain, credits, active count, FIFO of parked takers), and gets
;; fn2-machine-take-K (WAITER COPIES... fn2-core) -> (mv code id fn2-core)
;; and fn2-machine-reclaim-K. ROWKIND is the D0 kind its row stands for; a
;; range is (KIND :slot F :gen F :class N) with KIND a D0 kind.
(defun fn2-machine-taken-ranges-p (specs own)
  (declare (xargs :verify-guards nil))
  (if (atom specs) t
    (and (consp (car specs)) (assoc-eq (caar specs) *fn2-resource-order*)
         (member-eq (fn2-arm-get :slot (cdar specs)) own) (member-eq (fn2-arm-get :gen (cdar specs)) own)
         (natp (fn2-arm-get :class (cdar specs)))
         (fn2-machine-taken-ranges-p (cdr specs) own))))
(defun fn2-machine-taken-problem (name taken admission states own)
  (declare (xargs :verify-guards nil))
  (cond ((null taken) nil)
        (admission (msg "~x0: a kind is admitted by the listener or taken by a machine, not both." name))
        ((not (and (fn2-arm-plistp taken '(:phase :rows :ranges :copy :clear))
                   (member-eq (fn2-arm-get :phase taken) states) (member-eq :free states)
                   (assoc-eq (fn2-arm-get :rows taken) *fn2-resource-order*)
                   (fn2-machine-taken-ranges-p (fn2-machine-range-specs (fn2-arm-get :ranges taken)) own)
                   (fn2-arm-namesp (fn2-arm-get :copy taken))
                   (fn2-arm-subsetp (fn2-arm-get :copy taken) own)
                   (fn2-arm-namesp (fn2-arm-get :clear taken))
                   (fn2-arm-subsetp (fn2-arm-get :clear taken) own)
                   ;; the run dispatcher and the router read every row's stopped bit
                   (member-eq 'next-free own) (member-eq 'stopped own)))
         (msg "~x0: :taken ~x1 is (:phase P :rows ROWKIND :ranges ((KIND :slot F :gen F :class N) ...) ~
               [:copy (F ...)] [:clear (F ...)]) with P a phase, a :free phase, ROWKIND and each KIND ~
               D0 kinds, the range fields its own, and next-free and stopped fields." name taken))
        (t nil)))
(defun fn2-machine-events (name states fields budget continuations observes capacity initial holds admission taken arms)
  (declare (xargs :verify-guards nil))
  (let* ((enum (fn2-columns-sym name "-STATE"))
         (cols (append `((phase (:enum ,enum ,states))) *fn2-machine-common-fields* fields))
         (tcols (fn2-machine-table-columns cols))
         (charge (fn2-columns-sym name "-CHARGE"))
         (bytes (cadr (member-eq :bytes budget)))
         (steps (cadr (member-eq :steps budget)))
         (descriptors (cadr (member-eq :descriptors budget))))
    (fn2-declare (list :machine name)
      `(:states ,states :columns ,cols :table ,tcols :holds ,holds :admission ,admission :taken ,taken :budget ,budget
                :continuations ,continuations :observes ,observes :capacity ,capacity :initial ,initial
                :layout ,cols :packed ,(fn2-machine-packed-layout cols 0)
                :calling-convention (:run (id budget ,@(fn2-machine-row-vars cols) fn2-core)
                                     :observe (id event outcome reason count aux0 aux1 ,@(fn2-machine-row-vars cols) fn2-core))
                :cases ,(fn2-machine-case-labels name states observes) ,@arms)
      (append (list (list :declaration (list :columns name)))
              (let ((raw-arms (fn2-arm-get :arms arms)))
                (and (or (not raw-arms) (consp (cdar raw-arms)))
                     (fn2-machine-requirements (append continuations observes)))))
      `((defcolumns ,name ,tcols :put-policy ,states)
       (defmacro ,(fn2-columns-sym name "-PUT-CORE") (id &rest fields)
         (fn2-machine-core-put-expansion ',name ',cols ',states id fields t))
       (defmacro ,(fn2-columns-sym name "-PUT-CHILDREN") (id slot &rest fields)
         (fn2-machine-children-put-expansion ',name ',cols ',states id slot fields))
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
         ;; a kind with no observation handler reads no event (A-S7's taken kinds may observe nothing)
         (declare (xargs :guard t) (ignorable phase event))
         (and ,(if (member-eq :free states) `(not (equal phase ,(position-eq :free states))) t)
              ,(if (member-eq :retired states) `(not (equal phase ,(position-eq :retired states))) t)
              (case event ,@(fn2-machine-observe-event-guards observes) (otherwise nil))))

       ,@(fn2-machine-prepare-events name tcols initial)))))

; The new form (MACHINE-FORM 6.2): :arms ((PHASE [:on-refusal (STEP ...)] STEP ...) ...)
; with :observes ((EVENT [:from (P ...)] STEP ...) ...) and :subarms ((NAME STEP ...) ...);
; the registry holds a skeleton (TAG FN) per arm until defmachine-arms derives
; the contracts. :phases names :states.
(defun fn2-machine-arm-skeleton (name entries infix)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (list (caar entries) (fn2-columns-sym name (concatenate 'string infix (symbol-name (caar entries)))))
          (fn2-machine-arm-skeleton name (cdr entries) infix))))
(defun fn2-machine-arm-entriesp (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) (null entries)
    (and (consp (car entries)) (keywordp (caar entries)) (true-listp (car entries))
         (fn2-machine-arm-entriesp (cdr entries)))))
; Phase-valued fields (G3, D F10): (F (:phase-subset (P ...))) holds one of
; the kind's phases P, stored as the phase's code (u8). Its writers are
; checked: an arm's :set writes a phase of the subset (or a phase field whose
; subset is within it), its :initial is a phase of the subset (written as the
; keyword), and with no :initial, or cleared at admission, the kind's first
; phase must be in the subset; so (:next row-F) reaches exactly the subset.
(defun fn2-machine-phase-fields (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((f (car fields)))
      (if (and (consp f) (consp (cdr f)) (consp (cadr f)) (eq (car (cadr f)) :phase-subset))
          (cons (cons (car f) (cadr (cadr f))) (fn2-machine-phase-fields (cdr fields)))
        (fn2-machine-phase-fields (cdr fields))))))
(defun fn2-machine-lower-phase-fields (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (if (and (consp (car fields)) (assoc-eq (caar fields) (fn2-machine-phase-fields (list (car fields)))))
              (list (caar fields) :u8)
            (car fields))
          (fn2-machine-lower-phase-fields (cdr fields)))))
(defun fn2-machine-phase-constant (name phase)
  (declare (xargs :verify-guards nil))
  (fn2-columns-pre "*" (fn2-columns-sym (fn2-columns-col-name (fn2-columns-sym name "-STATE") phase) "*")))
(defun fn2-machine-lower-phase-initial (name pfields initial)
  (declare (xargs :verify-guards nil))
  (if (atom initial) initial
    (cons (if (and (consp (car initial)) (assoc-eq (caar initial) pfields) (keywordp (cadar initial)))
              (list (caar initial) (fn2-machine-phase-constant name (cadar initial)))
            (car initial))
          (fn2-machine-lower-phase-initial name pfields (cdr initial)))))
(defun fn2-machine-phase-fields-problem (name pfields states initial admission taken newp)
  (declare (xargs :verify-guards nil))
  (if (atom pfields) nil
    (let* ((f (caar pfields)) (sub (cdar pfields)) (init (assoc-eq f initial))
           (cleared (or (member-eq f (fn2-arm-get :clear admission)) (member-eq f (fn2-arm-get :clear taken)))))
      (cond ((not newp) (msg "~x0: phase field ~x1 needs the arm language (:arms)." name f))
            ((not (and (consp sub) (fn2-columns-keyword-listp sub) (subsetp-eq sub states)))
             (msg "~x0: field ~x1 is (:phase-subset (P ...)) over its phases ~x2." name f states))
            ((and init (not (and (keywordp (cadr init)) (member-eq (cadr init) sub))))
             (msg "~x0: phase field ~x1's :initial is a phase of ~x2, written as its keyword." name f sub))
            ((and (or (not init) cleared) (not (member-eq (car states) sub)))
             (msg "~x0: phase field ~x1 starts or is cleared at ~x2, outside ~x3; give it an :initial and never :clear it."
                  name f (car states) sub))
            (t (fn2-machine-phase-fields-problem name (cdr pfields) states initial admission taken newp))))))
;; Inner state machines (G3, C gap 4): :sub ((NAME :field F :phases (Q ...)
;; [:on-refusal (STEP ...)] :arms ((Q STEP ...) ...)) ...) is the enum field F
;; over the inner phases (enum K-NAME, starting at the first) and a sub-arm
;; NAME after the declared ones, one :cond clause per inner phase on ROW-F;
;; (:sub-next NAME Q) is (:set (F *K-NAME-Q*)). An arm runs the inner machine
;; with (:goto NAME), and each path's knowledge of F (G3 F11, F14) keeps the
;; inner phases' costs, moves and holds apart.
(defun fn2-machine-sub-enum (name sub)
  (declare (xargs :verify-guards nil))
  (fn2-columns-sym name (concatenate 'string "-" (symbol-name sub))))
(defun fn2-machine-sub-const (name sub q)
  (declare (xargs :verify-guards nil))
  (fn2-columns-pre "*" (fn2-columns-sym (fn2-columns-col-name (fn2-machine-sub-enum name sub) q) "*")))
(defun fn2-machine-sub-get (key spec)
  (declare (xargs :verify-guards nil))
  (cadr (member-eq key (cdr spec))))
(defun fn2-machine-sub-problem (name subs fields)
  (declare (xargs :verify-guards nil))
  (cond ((atom subs) (and subs (msg "~x0: :sub is a list of (NAME :field F :phases (Q ...) :arms ((Q STEP ...) ...))." name)))
        ((not (let* ((spec (car subs)) (qs (fn2-machine-sub-get :phases spec)) (arms (fn2-machine-sub-get :arms spec)))
                (and (consp spec) (symbolp (car spec)) (keyword-value-listp (cdr spec))
                     (subsetp-eq (evens (cdr spec)) '(:field :phases :arms :on-refusal))
                     (symbolp (fn2-machine-sub-get :field spec)) (fn2-machine-sub-get :field spec)
                     (not (assoc-eq (fn2-machine-sub-get :field spec) fields))
                     (consp qs) (fn2-columns-keyword-listp qs) (no-duplicatesp-eq qs) (<= (len qs) 256)
                     (alistp arms) (equal (strip-cars arms) qs) (true-list-listp arms))))
         (msg "~x0: inner machine ~x1 is (NAME :field F :phases (Q ...) [:on-refusal (STEP ...)] :arms ((Q STEP ...) ...)), ~
               F a new field and one arm per inner phase, in order." name (car subs)))
        (t (fn2-machine-sub-problem name (cdr subs) fields))))
(defun fn2-machine-sub-fields (name subs)
  (declare (xargs :verify-guards nil))
  (if (atom subs) nil
    (cons `(,(fn2-machine-sub-get :field (car subs)) (:enum ,(fn2-machine-sub-enum name (caar subs)) ,(fn2-machine-sub-get :phases (car subs))))
          (fn2-machine-sub-fields name (cdr subs)))))
(defun fn2-machine-sub-clauses (name sub f arms)
  (declare (xargs :verify-guards nil))
  (if (atom arms) '((t (:stop :machine-phase)))
    (cons `((equal ,(fn2-columns-col-name 'row f) ,(fn2-machine-sub-const name sub (caar arms))) ,@(cdar arms))
          (fn2-machine-sub-clauses name sub f (cdr arms)))))
(defun fn2-machine-sub-subarms (name subs)
  (declare (xargs :verify-guards nil))
  (if (atom subs) nil
    (let ((spec (car subs)))
      (cons `(,(car spec) ,@(and (member-eq :on-refusal (cdr spec)) `(:on-refusal ,(fn2-machine-sub-get :on-refusal spec)))
              (:cond ,@(fn2-machine-sub-clauses name (car spec) (fn2-machine-sub-get :field spec) (fn2-machine-sub-get :arms spec))))
            (fn2-machine-sub-subarms name (cdr subs))))))
(defun fn2-machine-sub-nexts (name subs x)
  ; X with each (:sub-next NAME Q) as its field write
  (declare (xargs :verify-guards nil))
  (cond ((atom x) x)
        ((and (eq (car x) :sub-next) (true-listp x) (equal (len x) 3) (assoc-eq (cadr x) subs)
              (member-eq (caddr x) (fn2-machine-sub-get :phases (assoc-eq (cadr x) subs))))
         `(:set (,(fn2-machine-sub-get :field (assoc-eq (cadr x) subs)) ,(fn2-machine-sub-const name (cadr x) (caddr x)))))
        (t (cons (fn2-machine-sub-nexts name subs (car x)) (fn2-machine-sub-nexts name subs (cdr x))))))
; Conditional holds (G3, D F14): an element (K :while (F V ...)) of a :holds
; entry holds K in its phase only while the enum field F is one of V. The
; declaration's :holds keeps each phase's unconditional kinds; :holds-while
; lists ((PHASE K F V ...) ...), and the kind's arms are checked per path.
(defun fn2-machine-holds-plain (xs)
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil
    (if (consp (car xs)) (fn2-machine-holds-plain (cdr xs)) (cons (car xs) (fn2-machine-holds-plain (cdr xs))))))
(defun fn2-machine-holds-kinds (xs)
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil (cons (if (consp (car xs)) (caar xs) (car xs)) (fn2-machine-holds-kinds (cdr xs)))))
(defun fn2-machine-holds-base (holds kindsp)
  ; each entry's unconditional kinds (KINDSP: every kind, for the rank check)
  (declare (xargs :verify-guards nil))
  (if (atom holds) holds
    (cons (if (consp (car holds))
              (cons (caar holds) (if kindsp (fn2-machine-holds-kinds (cdar holds)) (fn2-machine-holds-plain (cdar holds))))
            (car holds))
          (fn2-machine-holds-base (cdr holds) kindsp))))
(defun fn2-machine-holds-while-of (phase xs)
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil
    (append (and (consp (car xs)) (consp (cdar xs)) (consp (cddar xs))
                 (list (list* phase (caar xs) (caddar xs))))
            (fn2-machine-holds-while-of phase (cdr xs)))))
(defun fn2-machine-holds-while (holds)
  (declare (xargs :verify-guards nil))
  (if (atom holds) nil
    (append (and (consp (car holds)) (fn2-machine-holds-while-of (caar holds) (cdar holds)))
            (fn2-machine-holds-while (cdr holds)))))
(defun fn2-machine-holds-while-entry-problem (name phase xs fields newp)
  (declare (xargs :verify-guards nil))
  (cond ((atom xs) nil)
        ((atom (car xs)) (fn2-machine-holds-while-entry-problem name phase (cdr xs) fields newp))
        ((not newp) (msg "~x0: the conditional hold ~x1 in ~x2 needs the arm language (:arms)." name (car xs) phase))
        ((not (let* ((x (car xs)) (c (and (true-listp x) (equal (len x) 3) (eq (cadr x) :while) (caddr x)))
                     (ty (and (consp c) (cadr (assoc-eq (car c) fields)))))
                (and (consp c) (true-listp c) (consp (cdr c)) (consp ty) (eq (car ty) :enum) (true-listp ty)
                     (equal (len ty) 3) (subsetp-eq (cdr c) (caddr ty)))))
         (msg "~x0: ~x1 in ~x2's holds is (KIND :while (F V ...)), F an enum field and V its values."
              name (car xs) phase))
        (t (fn2-machine-holds-while-entry-problem name phase (cdr xs) fields newp))))
(defun fn2-machine-holds-while-problem (name holds fields newp)
  (declare (xargs :verify-guards nil))
  (if (atom holds) nil
    (or (and (consp (car holds)) (true-listp (car holds))
             (fn2-machine-holds-while-entry-problem name (caar holds) (cdar holds) fields newp))
        (fn2-machine-holds-while-problem name (cdr holds) fields newp))))
(defun fn2-machine-holds-domains (while fields)
  ; ((F V ...) ...): each conditional field and every value it takes
  (declare (xargs :verify-guards nil))
  (if (atom while) nil
    (let ((rest (fn2-machine-holds-domains (cdr while) fields)) (f (caddr (car while))))
      (if (assoc-eq f rest) rest (cons (cons f (caddr (cadr (assoc-eq f fields)))) rest)))))
;; The declaration's shape, every failed rule by name (DEV-LOOP 2; it was one
;; "Invalid machine declaration"). States and fields first: the rest read them.
(defun fn2-machine-declaration-problems (name states fields stops newp arms observe-arms subarms links
                                              genesis continuations observes initial budget capacity)
  ;; :normalize nil: the twenty independent conditionals would otherwise be
  ;; case-split into the definition's normal form (105 s; 0.02 s without)
  (declare (xargs :verify-guards nil :normalize nil))
  (cond
   ((not (and (consp states) (fn2-columns-keyword-listp states) (no-duplicatesp-eq states) (<= (len states) 256)))
    (list (msg ":states ~x0 is one to 256 distinct keywords." states)))
   ((not (fn2-columns-declarationsp fields))
    (list (msg ":fields ~x0 is a list of column declarations (NAME TYPE)." fields)))
   (t
    (fn2-arm-nonnil
     (list
      (and (not (no-duplicatesp-eq (append '(phase) (strip-cars *fn2-machine-common-fields*) (strip-cars fields))))
           (msg ":fields names a field twice, or PHASE or a common field ~x0: ~x1."
                (strip-cars *fn2-machine-common-fields*) (strip-cars fields)))
      ;; a kind's own stop reasons, by index (MACHINE-FORM 6.10)
      (and (not (and (fn2-columns-keyword-listp stops) (no-duplicatesp-eq stops) (< (len stops) 256)))
           (msg ":stops ~x0 is fewer than 256 distinct keywords." stops))
      (and newp (not (fn2-machine-arm-entriesp arms))
           (msg ":arms is a list of (PHASE [:from ..] [:on-refusal ..] STEP ...) entries."))
      (and newp (not (fn2-machine-arm-entriesp observe-arms))
           (msg ":observes (handlers) is a list of (EVENT [:from ..] [:on-refusal ..] STEP ...) entries."))
      (and newp (not (and (alistp subarms) (symbol-listp (strip-cars subarms))))
           (msg ":subarms is a list of (NAME STEP ...) entries."))
      ;; typed links (G3, D F8), checked whole by defmachine-arms
      (and (not (and (alistp links) (symbol-listp (strip-cars links)) (no-duplicatesp-eq (strip-cars links))))
           (msg ":links is a list of (NAME ...) entries with distinct names."))
      (and links (not newp) (msg ":links need the arm language (:arms)."))
      (and (not (true-listp genesis)) (msg ":genesis is a list of steps."))
      (and genesis (not newp) (msg ":genesis needs the arm language (:arms)."))
      (and (not (fn2-machine-continuationsp continuations nil))
           (msg "the continuations ~x0 are not well-formed arm contracts." (strip-cars continuations)))
      (and (not (fn2-machine-continuationsp observes t))
           (msg "the handlers ~x0 are not well-formed arm contracts." (strip-cars observes)))
      (and (not (no-duplicatesp-eq (strip-cars observes)))
           (msg "two handlers observe one event: ~x0." (strip-cars observes)))
      (and (not (fn2-columns-keyword-listp (strip-cars observes)))
           (msg "handler events ~x0 are keywords." (strip-cars observes)))
      (and (not (equal (strip-cars continuations) states))
           (msg "the arms' phases ~x0 are not :states ~x1, one arm per phase in order." (strip-cars continuations) states))
      (and (not (and (doublet-listp initial) (no-duplicatesp-eq (strip-cars initial))))
           (msg ":initial ~x0 is ((FIELD VALUE) ...), each field once." initial))
      (and (not (fn2-machine-directory-initial-p initial))
           (msg ":initial ~x0 gives a directory field a value it cannot start with." initial))
      (and (doublet-listp initial)
           (not (fn2-machine-initialp name (append `((phase (:enum state ,states))) *fn2-machine-common-fields* fields)
                                      states initial))
           (msg ":initial ~x0 names a field ~x1 lacks or a value outside its type." initial name))
      (and (not (and (natp (cadr (member-eq :bytes budget))) (natp (cadr (member-eq :steps budget)))
                     (natp (cadr (member-eq :descriptors budget)))))
           (msg ":budget ~x0 is (:bytes N :steps N :descriptors N), naturals." budget))
      (and (not capacity) (msg ":capacity is nil.")))))))
(defmacro defmachine (name &key states phases fields budget continuations observes (capacity '1) initial holds
                           admission taken arms subarms stops links sub genesis)
  (let* ((states (or states phases))
         (sub-problem (fn2-machine-sub-problem name sub fields))
         ;; (G3, C gap 5) :genesis (STEP ...): an arm the executor's init runs
         ;; once on each row of the kind, from the row's initial phase
         (genesis (if sub-problem genesis (fn2-machine-sub-nexts name sub genesis)))
         (fields (if sub-problem fields (append fields (fn2-machine-sub-fields name sub))))
         (subarms (if sub-problem subarms (fn2-machine-sub-nexts name sub (append subarms (fn2-machine-sub-subarms name sub)))))
         (arms (if sub-problem arms (fn2-machine-sub-nexts name sub arms)))
         (observes (if (and arms (not sub-problem)) (fn2-machine-sub-nexts name sub observes) observes))
         (phase-fields (fn2-machine-phase-fields fields))
         (phase-problem (fn2-machine-phase-fields-problem name phase-fields states initial admission taken
                                                          (and arms t)))
         (fields (fn2-machine-lower-phase-fields fields))
         (initial (fn2-machine-lower-phase-initial name phase-fields initial))
         (newp (and arms t))
         (holds-while (fn2-machine-holds-while holds))
         (while-problem (fn2-machine-holds-while-problem name holds fields newp))
         (rank-holds (fn2-machine-holds-base holds t))
         (holds (fn2-machine-holds-base holds nil))
         (observe-arms (and newp observes))
         (continuations (if newp (fn2-machine-arm-skeleton name arms "-RUN-") continuations))
         (observes (if newp (fn2-machine-arm-skeleton name observes "-ON-") observes)))
  (if (null (fn2-machine-declaration-problems name states fields stops newp arms observe-arms subarms links
                                               genesis continuations observes initial budget capacity))
      (let* ((own (remove-eq 'phase (strip-cars (append *fn2-machine-common-fields* fields))))
             (problem (or sub-problem (and sub (not newp) (msg "~x0: an inner machine needs the arm language (:arms)." name))
                          phase-problem while-problem
                          (and (not newp) (fn2-arm-retained-phases holds)
                               (msg "~x0: the retained phase(s) ~x1 need the arm language (:arms)."
                                    name (fn2-arm-retained-phases holds)))
                          (and (not newp) (fn2-arm-contracts-problem name continuations states own nil))
                          (and (not newp) (fn2-arm-contracts-problem name observes states own t))
                          (fn2-arm-holds-problem-syntax name rank-holds states)
                          (fn2-machine-admission-problem name admission states own)
                          (fn2-machine-taken-problem name taken admission states own))))
        (if problem `(make-event (er soft 'defmachine "~@0" ',problem))
          `(progn
             ;; fields of one name across kinds share one dispatcher (assembly-access)
             (make-event (let ((p (fn2-arm-nonnil (fn2-machine-shared-field-problems ',name ',fields (fn2-machine-names (w state)) (w state)))))
                           (if p (er soft 'defmachine "~@0" (fn2-arm-problems (msg "~x0 " ',name) p))
                             (value '(value-triple :shared-fields-ok)))))
             ,(fn2-machine-events name states fields budget continuations observes capacity initial holds
                              admission taken (and newp (list* :arms arms :subarms subarms :observe-arms observe-arms :stops stops
                                                    (append (and phase-fields (list :phase-fields phase-fields))
                                                            (and holds-while (list :holds-while holds-while))
                                                            (and links (list :links links))
                                                            (and genesis (list :genesis genesis)))))))))
    (er hard 'defmachine "Invalid machine declaration ~x0: ~@1" name
        (fn2-arm-problems "" (fn2-machine-declaration-problems name states fields stops newp arms observe-arms subarms
                                                               links genesis continuations observes initial budget capacity))))))

; ----------------------------------------------------------------------
; Owner-declared wait kinds (MACHINE-FORM 6.10, D F4): a D0 wait kind whose
; waker is its owner's. (defwait K :ready R :grant G [:park OP]) in the
; owner's book registers it; the grant service checks (R core) after A's
; sources and runs (G core), which returns the woken row and clears its wait;
; the arm language's (:park K) calls OP (a declared operation) or, without
; one, records K as the row's wait reason (the owner's grant finds the row).
(defun fn2-machine-wait-id (kind)
  ; a declaration's name is a symbol, never a keyword
  (declare (xargs :verify-guards nil))
  (list :wait (fn2-columns-sym 'fn2-wait (concatenate 'string "-" (symbol-name kind)))))
(defmacro defwait (kind &key ready grant park tables doc)
  ; TABLES: the children the grant may change (defcost :tables; control is
  ; implicit), the frame its constraint states and its attachment proves
  (if (not (and (keywordp kind) (symbolp ready) ready (symbolp grant) grant (symbolp park) (stringp doc)
                (consp tables) (true-listp tables)
                (assoc-eq kind *fn2-resource-order*)))
      (er hard 'defwait "~x0: (defwait K :ready R :grant G [:park OP] :tables (CHILD ...) :doc \"...\") for a D0 kind K." kind)
    (fn2-declare (fn2-machine-wait-id kind) (list :kind kind :ready ready :grant grant :park park :tables tables :doc doc) nil nil)))
(defun fn2-machine-wait-kinds (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil (cons (fn2-decl-get :kind (cdar rows)) (fn2-machine-wait-kinds (cdr rows)))))
(defun fn2-machine-waits (world)
  ; the declared wait kinds, in registration order
  (declare (xargs :verify-guards nil))
  (fn2-machine-wait-kinds (fn2-decl-rows :wait world)))
(defun fn2-machine-wait-get (kind key world)
  (declare (xargs :verify-guards nil))
  (fn2-decl-get key (fn2-decl-row (fn2-machine-wait-id kind) world)))
(defun fn2-machine-wait-ready-calls (waits world)
  (declare (xargs :verify-guards nil))
  (if (atom waits) nil
    (cons `(,(fn2-machine-wait-get (car waits) :ready world) fn2-core)
          (fn2-machine-wait-ready-calls (cdr waits) world))))
(defun fn2-machine-wait-grant-clauses (waits world)
  (declare (xargs :verify-guards nil))
  (if (atom waits) nil
    (cons `((,(fn2-machine-wait-get (car waits) :ready world) fn2-core)
            (,(fn2-machine-wait-get (car waits) :grant world) fn2-core))
          (fn2-machine-wait-grant-clauses (cdr waits) world))))

; Table order is declaration order, independent of TABLE-ALIST's newest first.
(defun fn2-machine-names (world)
  (declare (xargs :verify-guards nil))
  (strip-cars (fn2-decl-rows :machine world)))
(defun fn2-machine-declared (name key world)
  (declare (xargs :verify-guards nil))
  (let ((bodies (and (member-eq key '(:arms :subarms :observe-arms :genesis :book))
                     (cdr (assoc-eq name (table-alist 'fn2-machine-arm-bodies world))))))
    (if (and bodies (member-eq key bodies))
        (cadr (member-eq key bodies))
      (cadr (member-eq key (fn2-decl-row (list :machine name) world))))))
; A kind declared with :arms has its arm contracts derived by defmachine-arms
; (machine-arms.lisp) in its callbacks section; they are read from there.
(defun fn2-machine-property (name key world)
  (declare (xargs :verify-guards nil))
  (let ((derived (and (member-eq key '(:continuations :observes :genesis-arm))
                      (cdr (assoc-eq name (table-alist 'fn2-machine-arm-contracts world))))))
    (if derived (cadr (member-eq key derived))
      (fn2-machine-declared name key world))))
;; A field F of kinds K1 ... Kn is one dispatcher FN2-MACHINE-F over all of
;; them, typed by the first kind's F (fn2-machine-all-field-events): a later
;; kind's wider F would fail the dispatcher's -BOUND in assembly-access, and a
;; new F whose dispatcher name is already a function collides. Checked when
;; the kind registers, every field at once.
(defun fn2-machine-field-first-kind (field names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((e (assoc-eq field (fn2-machine-property (car names) :columns world))))
      (if e (list (car names) (cadr e)) (fn2-machine-field-first-kind field (cdr names) world)))))
(defun fn2-machine-dispatch-names (field)
  (declare (xargs :verify-guards nil))
  (let ((get (fn2-columns-col-name 'fn2-machine field)))
    (list get (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "SET-" field))
          (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "WRITE-" field))
          (fn2-columns-sym get "-READ-CODE") (fn2-columns-sym get "-READ"))))
(defun fn2-machine-defined-names (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (if (or (function-symbolp (car names) world) (getpropc (car names) 'macro-body nil world))
        (cons (car names) (fn2-machine-defined-names (cdr names) world))
      (fn2-machine-defined-names (cdr names) world))))
(defun fn2-machine-shared-field-problems (name fields names world)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((f (caar fields)) (ty (cadar fields))
           (first (fn2-machine-field-first-kind f (remove-eq name names) world))
           (taken (and (not first) (fn2-machine-defined-names (fn2-machine-dispatch-names f) world))))
      (cons (cond ((and first (< (fn2-columns-width (cadr first)) (fn2-columns-width ty)))
                   (msg "field ~x0 is ~x1 (~x2 bits), wider than ~x3's field ~x0 (~x4, ~x5 bits): one dispatcher ~
                         ~x6 serves every kind's ~x0, bounded by the first kind's width; rename the field or narrow it."
                        f ty (fn2-columns-width ty) (car first) (cadr first) (fn2-columns-width (cadr first))
                        (car (fn2-machine-dispatch-names f))))
                  (taken
                   (msg "field ~x0's dispatcher names ~x1 are already defined; rename the field." f taken))
                  (t nil))
            (fn2-machine-shared-field-problems name (cdr fields) names world)))))
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
        (declare (xargs :guard t) (ignorable event from next))
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
;; D0's moves: per path for a generated arm of a kind with conditional holds
;; (its :paths, G3 D F14), else per arm over its :next and :uses. Every other
;; generated arm's paths are checked too and reported, not refused, until
;; their owners have read them (fn2-machine-arm-path-report).
(defun fn2-machine-arm-paths-problem (name sources c holds ret world)
  (declare (xargs :verify-guards nil))
  (let ((while (fn2-machine-declared name :holds-while world)))
    (fn2-arm-paths-problem sources (fn2-arm-get :paths c)
                           (fn2-machine-holds-domains while (fn2-machine-property name :columns world))
                           holds while ret world)))
(defun fn2-machine-arm-path-report (name entries world)
  ; every generated arm with :paths is checked and enforced by fn2-machine-arm-resource-problem
  (declare (xargs :verify-guards nil) (ignore name entries world))
  nil)
(defun fn2-machine-path-report-events (name report)
  (declare (xargs :verify-guards nil))
  (if (atom report) nil
    (cons `(value-triple (cw "~x0 arm ~x1, D0 per path (reported, G3 F14): ~@2~%" ',name ',(caar report) ',(cdar report)))
          (fn2-machine-path-report-events name (cdr report)))))
(defun fn2-machine-arm-resource-problem (name sources c holds ret world)
  (declare (xargs :verify-guards nil))
  (cond ((member-eq :paths c) (fn2-machine-arm-paths-problem name sources c holds ret world))
        ((intersection-eq (fn2-arm-retained-phases holds) (append sources (fn2-arm-get :next c)))
         (msg "moves through the retained phase(s) ~x0, which D0 checks per path: a generated arm's :paths."
              (intersection-eq (fn2-arm-retained-phases holds) (append sources (fn2-arm-get :next c)))))
        (t (fn2-arm-resource-problem sources (fn2-arm-get :next c) holds (fn2-arm-get :uses c) world))))
(defun fn2-machine-arm-effect-rows (name sources c uses holds ret world)
  (declare (xargs :verify-guards nil))
  (if (member-eq :paths c)
      (let ((while (fn2-machine-declared name :holds-while world)))
        (fn2-arm-paths-effect-rows name sources (fn2-arm-get :paths c)
                                   (fn2-machine-holds-domains while (fn2-machine-property name :columns world))
                                   holds while ret world))
    (fn2-arm-effect-rows name sources uses holds world)))
;; D0's effect table is keyed by call site. A call on paths whose entry a
;; conditional hold splits (G3) has one row per holding set: each row is
;; checked on its own, and the table keeps one row per site whose
;; :holds-before is everything any of those paths may hold.
(defun fn2-machine-effect-rows-each-p (rows order)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (and (fn2-resource-effects-p (list (car rows)) order)
         (fn2-machine-effect-rows-each-p (cdr rows) order))))
(defun fn2-machine-effect-row-holds (row)
  (declare (xargs :verify-guards nil))
  (cadr (member-eq :holds-before (cdr row))))
(defun fn2-machine-effect-row-effects (row)
  (declare (xargs :verify-guards nil))
  (cadr (member-eq :effects (cdr row))))
(defun fn2-machine-effect-rows-join (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((row (car rows)) (rest (fn2-machine-effect-rows-join (cdr rows)))
           (same (and (consp row) (assoc-equal (car row) rest))))
      (if (and same (equal (fn2-machine-effect-row-effects row) (fn2-machine-effect-row-effects same)))
          (cons (list (car row)
                      :holds-before (union-equal (fn2-machine-effect-row-holds row) (fn2-machine-effect-row-holds same))
                      :effects (fn2-machine-effect-row-effects row))
                (remove1-equal same rest))
        (cons row rest)))))
(defun fn2-machine-effect-rows-ok-p (rows order)
  (declare (xargs :verify-guards nil))
  (and (fn2-machine-effect-rows-each-p rows order)
       (fn2-resource-effects-p (fn2-machine-effect-rows-join rows) order)))
;; Teeth: a site acquiring :operation with and without :storage-window held
;; is one row holding both; a variant acquiring below what it holds fails,
;; though the joined row alone would not.
(assert-event
 (let* ((k '((fn2-upload :store-write) fn2-issue-write)) (e '((:acquire (:operation))))
        (a (list k :holds-before '(:upload-row :chunk-window) :effects e))
        (b (list k :holds-before '(:upload-row :chunk-window :storage-window) :effects e))
        (bad (list k :holds-before '(:upload-row :fence-slot) :effects '((:acquire (:storage-window))))))
   (and (not (fn2-resource-effects-p (list a b) *fn2-resource-order*))
        (fn2-machine-effect-rows-ok-p (list a b) *fn2-resource-order*)
        (equal (fn2-machine-effect-rows-join (list a b))
               (list (list k :holds-before '(:upload-row :chunk-window :storage-window) :effects e)))
        (not (fn2-machine-effect-rows-ok-p (list a bad) *fn2-resource-order*)))))
;; A retained phase's entering sets (G3): every set a path into it from
;; another phase starts with, over every arm and handler (ENTRIES with the
;; kind's registered ones); a path into it keeps that set, so it is the set
;; a path out of it starts with.
(defun fn2-machine-path-entering-sets-at (s as holds while)
  (declare (xargs :verify-guards nil))
  (if (atom as) nil
    (cons (fn2-arm-holds-under s (car as) holds while)
          (fn2-machine-path-entering-sets-at s (cdr as) holds while))))
(defun fn2-machine-path-entering-sets (r srcs as holds while)
  (declare (xargs :verify-guards nil))
  (cond ((atom srcs) nil)
        ((or (eq (car srcs) r) (fn2-arm-retained-p (car srcs) holds))
         (fn2-machine-path-entering-sets r (cdr srcs) as holds while))
        (t (append (fn2-machine-path-entering-sets-at (car srcs) as holds while)
                   (fn2-machine-path-entering-sets r (cdr srcs) as holds while)))))
(defun fn2-machine-paths-entering-sets (r sources paths doms holds while)
  (declare (xargs :verify-guards nil))
  (if (atom paths) nil
    (let ((path (car paths)))
      (append (and (not (nth 5 path)) (not (eq (cadr path) :stay)) (member-eq r (cadr path))
                   (fn2-machine-path-entering-sets
                    r (if (eq (car path) :any) sources (intersection-eq (car path) sources))
                    (fn2-arm-assignments (fn2-arm-entry-doms doms (nth 3 path))) holds while))
              (fn2-machine-paths-entering-sets r sources (cdr paths) doms holds while)))))
(defun fn2-machine-entries-entering-sets (r entries observationp states doms holds while)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (let ((c (cddar entries)))
      (append (fn2-machine-paths-entering-sets
               r (if observationp (or (fn2-arm-get :from c) (fn2-machine-observe-default-from states))
                   (list (caar entries)))
               (fn2-arm-get :paths c) doms holds while)
              (fn2-machine-entries-entering-sets r (cdr entries) observationp states doms holds while)))))
(defun fn2-machine-retained-sets-of (rs name entries observationp world)
  (declare (xargs :verify-guards nil))
  (if (atom rs) nil
    (let* ((states (fn2-machine-property name :states world))
           (holds (fn2-machine-property name :holds world))
           (while (fn2-machine-declared name :holds-while world))
           (doms (fn2-machine-holds-domains while (fn2-machine-property name :columns world)))
           (r (car rs)))
      (cons (cons r (remove-duplicates-equal
                     (append (fn2-machine-entries-entering-sets r entries observationp states doms holds while)
                             (fn2-machine-entries-entering-sets r (append (fn2-machine-property name :continuations world)
                                                                          (fn2-machine-property name :genesis-arm world))
                                                                nil states doms holds while)
                             (fn2-machine-entries-entering-sets r (fn2-machine-property name :observes world)
                                                                t states doms holds while))))
            (fn2-machine-retained-sets-of (cdr rs) name entries observationp world)))))
(defun fn2-machine-retained-sets (name entries observationp world)
  ; ((R SET ...) ...) for each retained phase R of NAME
  (declare (xargs :verify-guards nil))
  (fn2-machine-retained-sets-of (fn2-arm-retained-phases (fn2-machine-property name :holds world))
                                name entries observationp world))
(defun fn2-machine-in-any-p (k sets)
  (declare (xargs :verify-guards nil))
  (and (consp sets) (or (member-equal k (car sets)) (fn2-machine-in-any-p k (cdr sets))) t))
(defun fn2-machine-rank-union (order sets)
  ; every kind in SETS, in ORDER's rank order
  (declare (xargs :verify-guards nil))
  (if (atom order) nil
    (if (fn2-machine-in-any-p (car order) sets) (cons (car order) (fn2-machine-rank-union (cdr order) sets))
      (fn2-machine-rank-union (cdr order) sets))))
(defun fn2-machine-holds-resolved-1 (holds ret)
  (declare (xargs :verify-guards nil))
  (if (atom holds) holds
    (cons (if (and (consp (car holds)) (equal (cdar holds) '(:retained)))
              (cons (caar holds) (fn2-machine-rank-union (strip-cars *fn2-resource-order*)
                                                         (cdr (assoc-eq (caar holds) ret))))
            (car holds))
          (fn2-machine-holds-resolved-1 (cdr holds) ret))))
(defun fn2-machine-holds-resolved (name world)
  ; NAME's holds with each retained phase's potential: the union of its
  ; entering sets (the D0 deadlock table's static row for the phase)
  (declare (xargs :verify-guards nil))
  (fn2-machine-holds-resolved-1 (fn2-machine-property name :holds world)
                                (fn2-machine-retained-sets name nil nil world)))
(defun fn2-machine-arm-problem (name entry observationp ret world)
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
    ;; every independent problem of the arm (cost, uses, D0, refusal posture), each its first
    (fn2-arm-nonnil
     (list
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
       (t nil))
      (cond
       ((fn2-machine-unresolved-use name uses world)
        (msg "~x0: arm ~x1 uses ~x2, which is neither a defcost nor a callback of ~x0."
             name tag (fn2-machine-unresolved-use name uses world)))
       ((and (not (eq (fn2-arm-get :language c) :unchecked))
             (fn2-machine-arm-resource-problem name sources c holds ret world))
        (msg "~x0: arm ~x1 ~@2" name tag (fn2-machine-arm-resource-problem name sources c holds ret world)))
       ((not (fn2-machine-effect-rows-ok-p (remove-duplicates-equal (fn2-machine-arm-effect-rows name sources c uses holds ret world))
                                           *fn2-resource-order*))
        (msg "~x0: arm ~x1's resource effects fail D0's order: ~x2." name tag
             (fn2-machine-arm-effect-rows name sources c uses holds ret world)))
       (t nil))
      (cond
       ((and posture (or (fn2-arm-retained-p (car sources) holds)
                         (fn2-arm-retained-p (fn2-arm-get :to (cdr posture)) holds)))
        (msg "~x0: arm ~x1's :on-refusal ~x2 moves through a retained phase; route the refusal in the arm." name tag posture))
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
       (t nil))))))
(defun fn2-machine-arms-problem-1 (name entries observationp ret world)
  ; every arm's problems, a list
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (append (fn2-machine-arm-problem name (car entries) observationp ret world)
            (fn2-machine-arms-problem-1 name (cdr entries) observationp ret world))))
(defun fn2-machine-arms-problem (name entries observationp world)
  (declare (xargs :verify-guards nil))
  (fn2-machine-arms-problem-1 name entries observationp
                              (fn2-machine-retained-sets name entries observationp world) world))

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
; P1: an arm writing a directory field changes the directory child.
(defun fn2-machine-directory-child (writes)
  (declare (xargs :verify-guards nil))
  (and (intersectp-eq writes (strip-cars *fn2-machine-directory-fields*)) '(fn2-core-machines)))
(defun fn2-machine-arm-pre (name phase-constant)
  (declare (xargs :verify-guards nil))
  `(and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
        (eq (,(fn2-columns-sym name "-SNAPSHOT-READ-CODE") id fn2-core) :ok)
        ,@(and phase-constant `((equal (fn2-machine-phase id fn2-core) ,phase-constant)))
        (equal (fn2-core-stop-reason fn2-core) *fn2-stop-reason-none*)))
; ----------------------------------------------------------------------
; The frame proved by construction (lane arm-frames). Every writer,
; operation and arm the generator meets gets chained contracts over
; arms.lisp's length-free relations, each proved once by opening its own
; definition with its callees' contracts:
;   F-ARM-KIDS       children outside the declared set S are unchanged
;   F-ARM-ROW-FRAME  the same within a caller's frame (FN2-ARM-ROW-FRAME):
;                    S among the caller's children and, for a writer of the
;                    row, its columns among the caller's at the caller's row
;   F-ARM-SLOT       the directory's slot of every id is unchanged
;   F-ARM-PHASE      the row's phase stays, or moves within the caller's
;                    declared successors
; An arm's FRAME follows from its own chained contracts at its own sets and
; the kind's conversion lemma K-ARM-FRAMEP; its definition is opened once.
(defun fn2-arm-frame-children-of (world)
  (declare (xargs :verify-guards nil))
  (unquote (getpropc '*fn2-core-children* 'const nil world)))
(defun fn2-arm-frame-child-index (field world)
  (declare (xargs :verify-guards nil))
  (position-eq field (strip-cars (fn2-arm-frame-children-of world))))
(defun fn2-arm-frame-indices (fields world)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((i (fn2-arm-frame-child-index (car fields) world)))
      (if i (add-to-set-eql i (fn2-arm-frame-indices (cdr fields) world))
        (fn2-arm-frame-indices (cdr fields) world)))))
(defun fn2-arm-frame-ctl (world) (declare (xargs :verify-guards nil)) (fn2-arm-frame-child-index 'fn2-core-control world))
(defun fn2-arm-frame-m (world) (declare (xargs :verify-guards nil)) (fn2-arm-frame-child-index 'fn2-core-machines world))
(defun fn2-arm-frame-out-term (fn call world)
  ; FN's core result in CALL
  (declare (xargs :verify-guards nil))
  (let ((outs (getpropc fn 'stobjs-out nil world)))
    (if (equal outs '(fn2-core)) call `(mv-nth ,(position-eq 'fn2-core outs) ,call))))
(defun fn2-arm-frame-corep-fn (fn world)
  (declare (xargs :verify-guards nil))
  (and (symbolp fn) (member-eq 'fn2-core (getpropc fn 'stobjs-out nil world))
       (member-eq 'fn2-core (getpropc fn 'stobjs-in nil world))))
(defun fn2-arm-frame-name (fn suffix) (declare (xargs :verify-guards nil)) (fn2-columns-sym fn suffix))
(defun fn2-arm-frame-kids-runes (children)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (cons (fn2-columns-pre "FN2-ARM-KIDS-OF-" (fn2-columns-pre "UPDATE-" (caar children)))
          (fn2-arm-frame-kids-runes (cdr children)))))
(defun fn2-arm-frame-hints (runes)
  (declare (xargs :verify-guards nil))
  `(("Goal" :in-theory (union-theories ',runes (theory 'fn2-arm-frame-base)))))
(defun fn2-arm-frame-phase-indices (world)
  (declare (xargs :verify-guards nil))
  (cons (fn2-arm-frame-m world) (fn2-arm-frame-indices (fn2-machine-machine-tables world) world)))
(defun fn2-arm-frame-nth-equalities (indices)
  (declare (xargs :verify-guards nil))
  (if (atom indices) nil
    (cons `(equal (nth ,(car indices) a) (nth ,(car indices) b)) (fn2-arm-frame-nth-equalities (cdr indices)))))
(defun fn2-arm-frame-nth-uses (indices s out)
  (declare (xargs :verify-guards nil))
  (if (atom indices) nil
    (cons `(:instance fn2-arm-kids-nth (i 0) (k ,(car indices)) (free ',s) (a fn2-core) (b ,out))
          (fn2-arm-frame-nth-uses (cdr indices) s out))))

;; An operation's contracts at its declared children S (its defcost's
;; :tables, the control child, and its own table when it writes its row).
;; ENABLE: the helpers without a defcost its body calls, opened with it.
(defun fn2-arm-frame-op-events (fn s enable world)
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals fn world))
         (out (fn2-arm-frame-out-term fn (cons fn formals) world))
         (m (fn2-arm-frame-m world))
         (phasep (not (intersectp-equal (fn2-arm-frame-phase-indices world) s)))
         (kids (fn2-arm-frame-name fn "-ARM-KIDS"))
         (frame (fn2-arm-frame-name fn "-ARM-ROW-FRAME"))
         (slot (fn2-arm-frame-name fn "-ARM-SLOT"))
         (phase (fn2-arm-frame-name fn "-ARM-PHASE")))
    (append
     ; a constrained FN's KIDS is its constraint (commit.lisp's hooks)
     (and (not (getpropc kids 'theorem nil world))
          `((defthm ,kids
              (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',s fn2-arm-free))
                       (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,out))
              :hints ,(fn2-arm-frame-hints (append (list fn) enable (fn2-arm-frame-kids-runes (fn2-arm-frame-children-of world)))))))
     `((defthm ,frame
         (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core) (natp fn2-arm-tb) (subsetp-equal ',s fn2-arm-ch))
                  (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 ,out))
         :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                  :use ((:instance fn2-arm-row-frame-kids (table fn2-arm-tb) (columns fn2-arm-cs) (children fn2-arm-ch) (a fn2-arm-c0) (b fn2-core)
                                   (c ,out) (free ',s) (row fn2-arm-row))
                        (:instance ,kids (fn2-arm-free ',s) (fn2-arm-c0 fn2-core)))))))
     (and (not (member m s))
          `((defthm ,slot
              (equal (fn2-machine-slot fn2-arm-id ,out) (fn2-machine-slot fn2-arm-id fn2-core))
              :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                       :use ((:instance ,kids (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                             (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',s) (a fn2-core) (b ,out))
                             (:instance fn2-arm-slot-congruence (id fn2-arm-id) (a fn2-core) (b ,out))))))))
     (and phasep
          `((defthm ,phase
              (equal (fn2-machine-phase fn2-arm-id ,out) (fn2-machine-phase fn2-arm-id fn2-core))
              :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                       :use ((:instance ,kids (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                             ,@(fn2-arm-frame-nth-uses (fn2-arm-frame-phase-indices world) s out)
                             (:instance fn2-arm-phase-congruence (id fn2-arm-id) (a fn2-core) (b ,out))))))))
     `((in-theory (disable ,kids ,frame ,@(and (not (member m s)) (list slot)) ,@(and phasep (list phase))))
       (table fn2-arm-frame-fns ',fn '(:op ,s))))))

(defun fn2-arm-frame-range (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) nil (cons i (fn2-arm-frame-range (+ 1 i) n))))
(defun fn2-arm-frame-length-facts (kind fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (fn2-columns-sym (fn2-columns-col-name kind (car fields)) "-LENGTH-WHEN-WFP")
          (fn2-arm-frame-length-facts kind (cdr fields)))))
;; Each own column's row reader after the kind's table is replaced.
(defun fn2-arm-frame-own-fields (fields)
  (declare (xargs :verify-guards nil))
  (cond ((atom fields) nil)
        ((or (eq (car fields) 'phase) (assoc-eq (car fields) *fn2-machine-directory-fields*))
         (fn2-arm-frame-own-fields (cdr fields)))
        (t (cons (car fields) (fn2-arm-frame-own-fields (cdr fields))))))
(defun fn2-arm-frame-directory-fields (fields)
  (declare (xargs :verify-guards nil))
  (cond ((atom fields) nil)
        ((assoc-eq (car fields) *fn2-machine-directory-fields*) (cons (car fields) (fn2-arm-frame-directory-fields (cdr fields))))
        (t (fn2-arm-frame-directory-fields (cdr fields)))))
(defun fn2-arm-frame-table-fields (fields)
  ; the fields that are columns of the kind's table (the phase among them):
  ; a directory field is the directory's
  (declare (xargs :verify-guards nil))
  (cond ((atom fields) nil)
        ((assoc-eq (car fields) *fn2-machine-directory-fields*) (fn2-arm-frame-table-fields (cdr fields)))
        (t (cons (car fields) (fn2-arm-frame-table-fields (cdr fields))))))
(defun fn2-arm-frame-row-after-name (kind field)
  (declare (xargs :verify-guards nil))
  (fn2-columns-pre "FN2-ARM-AFTER-" (fn2-machine-row-reader kind field)))
(defun fn2-arm-frame-row-after-events (kind fields world)
  (declare (xargs :verify-guards nil) (ignorable world))
  (if (atom fields) nil
    (let* ((table (fn2-columns-sym kind "-TABLE"))
           (reader (fn2-machine-row-reader kind (car fields)))
           (name (fn2-arm-frame-row-after-name kind (car fields))))
      (cons `(defthm ,name
                (implies (equal (fn2-machine-kind id fn2-core) ,(fn2-columns-pre "*" (fn2-columns-sym kind "-KIND*")))
                         (equal (,reader id (,(fn2-columns-pre "UPDATE-" table) tbl fn2-core))
                                (if (and (fn2-machine-idp id fn2-core) (natp (fn2-machine-slot id fn2-core))
                                         (< (fn2-machine-slot id fn2-core) (,(fn2-columns-sym kind "-ROWS") tbl)))
                                    (,(fn2-columns-col-name kind (car fields)) (fn2-machine-slot id fn2-core) tbl)
                                  0)))
                :hints (("Goal" :in-theory (enable ,reader ,(fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                                                   fn2-machine-phase-read-code fn2-machine-kind
                                                   fn2-machine-kind-read-code fn2-machine-slot fn2-machine-slot-read-code
                                                   fn2-machine-idp))))
             (fn2-arm-frame-row-after-events kind (cdr fields) world)))))
(defun fn2-arm-frame-row-after-names (kind fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (fn2-arm-frame-row-after-name kind (car fields)) (fn2-arm-frame-row-after-names kind (cdr fields)))))
;; Once per kind: its columns' setters, the phase through its table, and the
;; conversion to the frame predicate.
(defun fn2-arm-frame-setter (kind field)
  (declare (xargs :verify-guards nil))
  (fn2-columns-col-name kind (fn2-columns-pre "SET-" field)))
(defun fn2-arm-frame-setter-events (kind fn2-arm-cs j)
  (declare (xargs :verify-guards nil))
  (if (atom fn2-arm-cs) nil
    (let* ((set (fn2-arm-frame-setter kind (caar fn2-arm-cs)))
           (raw (fn2-columns-pre "UPDATE-" (fn2-columns-sym (fn2-columns-col-name kind (caar fn2-arm-cs)) "$AI"))))
      (cons `(defthm ,(fn2-columns-pre "FN2-ARM-COLS-OF-" set)
               (implies (and (fn2-arm-cols 0 fn2-arm-row fn2-arm-cs t0 tbl) (member-equal ,j fn2-arm-cs) (equal i fn2-arm-row))
                        (fn2-arm-cols 0 fn2-arm-row fn2-arm-cs t0 (,set i v tbl)))
               :hints (("Goal" :in-theory (union-theories '(,set ,raw update-nth-array) (theory 'fn2-arm-frame-base))
                        :use ((:instance fn2-arm-cols-update (k 0) (columns fn2-arm-cs) (a t0) (b tbl) (j ,j) (row i))))))
            (fn2-arm-frame-setter-events kind (cdr fn2-arm-cs) (+ 1 j))))))
(defun fn2-arm-frame-setter-runes (kind fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (fn2-columns-pre "FN2-ARM-COLS-OF-" (fn2-arm-frame-setter kind (car fields)))
          (fn2-arm-frame-setter-runes kind (cdr fields)))))
(defun fn2-arm-frame-setter-facts (kind fields)
  ; each setter's column and rows facts (columns.lisp), for reading a written row
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((set (fn2-arm-frame-setter kind (car fields))))
      (list* (fn2-columns-sym set "-NTH") (fn2-columns-sym set "-ROWS")
             (fn2-arm-frame-setter-facts kind (cdr fields))))))
(defun fn2-arm-frame-not-members (xs v)
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil (cons `(not (member-equal ,(car xs) ,v)) (fn2-arm-frame-not-members (cdr xs) v))))
(defun fn2-arm-frame-kids-nth-uses (indices tk)
  (declare (xargs :verify-guards nil))
  (if (atom indices) nil
    (cons `(:instance fn2-arm-kids-nth (i 0) (k ,(car indices)) (free (cons ,tk fn2-arm-ch)))
          (fn2-arm-frame-kids-nth-uses (cdr indices) tk))))
(defun fn2-arm-frame-machines-over (kind)
  (declare (xargs :verify-guards nil))
  (fn2-columns-pre "FN2-ARM-MACHINES-OVER-UPDATE-" (fn2-columns-sym kind "-TABLE")))
;; A kind's table written back keeping its phase column and rows keeps every
;; id's phase (a column setter off the phase writes neither): the
;; dispatchers that reach several kinds' tables read it (kind events).
(defun fn2-arm-frame-table-keep-name (kind)
  (declare (xargs :verify-guards nil))
  (fn2-columns-pre "FN2-ARM-PHASE-OF-UPDATE-" (fn2-columns-sym kind "-TABLE-KEEPING-PHASE")))
(defun fn2-arm-frame-kind-events (kind world)
  (declare (xargs :verify-guards nil))
  (let* ((tcols (fn2-machine-property kind :table world))
         (table (fn2-columns-sym kind "-TABLE"))
         (tk (fn2-arm-frame-child-index table world))
         (code (fn2-columns-pre "*" (fn2-columns-sym kind "-KIND*")))
         (rows (fn2-columns-sym kind "-ROWS"))
         (read (fn2-columns-col-name kind 'phase))
         (view (fn2-columns-pre "FN2-ARM-PHASE-VIEW-" kind))
         (upd (fn2-columns-pre "FN2-ARM-PHASE-OF-UPDATE-" table))
         (framep (fn2-columns-sym kind "-ARM-FRAMEP"))
         (lens (fn2-columns-sym kind "-ARM-COL-LENS"))
         (klen (fn2-columns-sym kind "-ARM-LEN"))
         (ri (len tcols))
         (pc (position-eq 'phase (strip-cars tcols))))
    `(,@(fn2-arm-frame-setter-events kind tcols 0)
      (defthm ,view
        (implies (equal (fn2-machine-kind id fn2-core) ,code)
                 (equal (fn2-machine-phase id fn2-core)
                        (if (and (fn2-machine-idp id fn2-core) (natp (fn2-machine-slot id fn2-core))
                                 (< (fn2-machine-slot id fn2-core) (,rows (,table fn2-core))))
                            (,read (fn2-machine-slot id fn2-core) (,table fn2-core))
                          0)))
        :hints (("Goal" :in-theory (e/d (fn2-machine-phase fn2-machine-phase-read-code)
                                        (fn2-machine-kind fn2-machine-slot fn2-machine-idp)))))
      (defthm ,upd
        (implies (equal (fn2-machine-kind id fn2-core) ,code)
                 (equal (fn2-machine-phase id (,(fn2-columns-pre "UPDATE-" table) tbl fn2-core))
                        (if (and (fn2-machine-idp id fn2-core) (natp (fn2-machine-slot id fn2-core))
                                 (< (fn2-machine-slot id fn2-core) (,rows tbl)))
                            (,read (fn2-machine-slot id fn2-core) tbl)
                          0)))
        :hints (("Goal" :in-theory (enable fn2-machine-phase fn2-machine-phase-read-code fn2-machine-kind
                                           fn2-machine-kind-read-code fn2-machine-slot fn2-machine-slot-read-code
                                           fn2-machine-idp))))
      ;; a batch's directory write lands over its table write: moved inside, the
      ;; row readers' FN2-ARM-AFTER- facts read the table through it
      (defthm ,(fn2-arm-frame-machines-over kind)
        (equal (update-fn2-core-machines x (,(fn2-columns-pre "UPDATE-" table) y c))
               (,(fn2-columns-pre "UPDATE-" table) y (update-fn2-core-machines x c)))
        :hints (("Goal" :in-theory (union-theories '(update-fn2-core-machines ,(fn2-columns-pre "UPDATE-" table))
                                                   (theory 'fn2-arm-frame-base))
                 :use ((:instance fn2-arm-update-nth-commute (i ,(fn2-arm-frame-m world)) (j ,tk) (a x) (b y) (l c))))))
      ,@(fn2-arm-frame-row-after-events kind (fn2-arm-frame-own-fields (strip-cars tcols)) world)
      ;; the rows field follows the columns in the table's layout; each column
      ;; of a well-formed table is as long as its rows
      (defthm ,lens
        (implies (and (fn2-corep a) (fn2-core-wfp a) (fn2-corep b) (fn2-core-wfp b)
                      (equal (,rows (,table b)) (,rows (,table a))))
                 (fn2-arm-col-lens-at 0 ',(fn2-arm-frame-range 0 ri) (,table a) (,table b)))
        ; each column's length by its LENGTH-WHEN-WFP fact, the well-formedness closed
        :hints (("Goal" :in-theory (union-theories '(fn2-arm-col-lens-at fn2-arm-nth-0 ,@(fn2-arm-frame-length-facts kind (strip-cars tcols)))
                                                   (theory 'fn2-arm-frame-base))
                 :use ((:instance ,(fn2-columns-sym (fn2-columns-sym kind "-WFP") (concatenate 'string "-OF-" (symbol-name table)))
                                  (fn2-core a))
                       (:instance ,(fn2-columns-sym (fn2-columns-sym kind "-WFP") (concatenate 'string "-OF-" (symbol-name table)))
                                  (fn2-core b))))))
      (defthm ,klen
        (implies (,(fn2-columns-sym kind "P") x) (equal (len x) ,(+ 1 ri)))
        :hints (("Goal" :in-theory (enable ,(fn2-columns-sym kind "P")))))
      (defthm ,framep
        (implies (and (fn2-arm-row-frame ,tk fn2-arm-row fn2-arm-cs fn2-arm-ch a b) (subsetp-equal fn2-arm-cs ',(fn2-arm-frame-range 0 ri))
                      (fn2-corep a) (fn2-core-wfp a) (fn2-corep b) (fn2-core-wfp b))
                 (fn2-arm-framep ,tk fn2-arm-row fn2-arm-cs fn2-arm-ch a b))
        :hints (("Goal" :in-theory (union-theories '(,table ,rows ,klen fn2-arm-core-len fn2-arm-row-frame)
                                                   (theory 'fn2-arm-frame-base))
                 :use ((:instance fn2-arm-row-frame-framep (table ,tk) (columns fn2-arm-cs) (children fn2-arm-ch) (row fn2-arm-row))
                       (:instance ,(fn2-columns-sym table "-TYPE") (fn2-core a))
                       (:instance ,(fn2-columns-sym table "-TYPE") (fn2-core b))
                       (:instance fn2-arm-cols-nth (k 0) (j ,ri) (columns fn2-arm-cs) (a (nth ,tk a)) (b (nth ,tk b)) (row fn2-arm-row))
                       (:instance ,lens)
                       (:instance fn2-arm-col-lens-at-mono (k 0) (columns fn2-arm-cs) (big ',(fn2-arm-frame-range 0 ri))
                                  (a (nth ,tk a)) (b (nth ,tk b)))
                       (:instance fn2-arm-col-lens-of-at (k 0) (columns fn2-arm-cs) (a (nth ,tk a)) (b (nth ,tk b)))))))
      ;; the phase reads the directory, the other kinds' tables, and of this
      ;; kind's table only its phase column and rows: a row-level change
      ;; outside them keeps every id's phase
      (defthm ,(fn2-columns-sym kind "-ARM-PHASE-CONGRUENCE")
        (implies (and ,@(fn2-arm-frame-nth-equalities (remove-equal tk (fn2-arm-frame-phase-indices world)))
                      (equal (nth ,pc (nth ,tk a)) (nth ,pc (nth ,tk b)))
                      (equal (nth ,ri (nth ,tk a)) (nth ,ri (nth ,tk b))))
                 (equal (fn2-machine-phase id a) (fn2-machine-phase id b)))
        :rule-classes nil
        :hints (("Goal" :in-theory (enable fn2-machine-phase fn2-machine-phase-read-code fn2-machine-idp fn2-core-machines
                                           ,@(fn2-machine-machine-tables world) ,read ,(fn2-columns-sym read "$AI") ,rows)
                 :use ((:instance fn2-arm-slot-congruence) (:instance fn2-arm-kind-congruence)))))
      (defthm ,(fn2-columns-sym kind "-ARM-PHASE-OF-ROW-FRAME")
        (implies (and (fn2-arm-row-frame ,tk fn2-arm-row fn2-arm-cs fn2-arm-ch a b) (not (member-equal ,pc fn2-arm-cs)) (not (member-equal ,ri fn2-arm-cs))
                      (not (member-equal ,tk fn2-arm-ch))
                      ,@(fn2-arm-frame-not-members (remove-equal tk (fn2-arm-frame-phase-indices world)) 'fn2-arm-ch))
                 (equal (fn2-machine-phase id b) (fn2-machine-phase id a)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-arm-row-frame) (theory 'fn2-arm-frame-base))
                 :use ((:instance ,(fn2-columns-sym kind "-ARM-PHASE-CONGRUENCE"))
                       (:instance fn2-arm-row-frame-cols (table ,tk) (columns fn2-arm-cs) (children fn2-arm-ch) (row fn2-arm-row))
                       (:instance fn2-arm-cols-nth (k 0) (j ,pc) (columns fn2-arm-cs) (a (nth ,tk a)) (b (nth ,tk b)) (row fn2-arm-row))
                       (:instance fn2-arm-cols-nth (k 0) (j ,ri) (columns fn2-arm-cs) (a (nth ,tk a)) (b (nth ,tk b)) (row fn2-arm-row))
                       ,@(fn2-arm-frame-kids-nth-uses (remove-equal tk (fn2-arm-frame-phase-indices world)) tk)))))
      (defthm ,(fn2-arm-frame-table-keep-name kind)
        (implies (and (equal (nth ,pc x) (nth ,pc (,table c))) (equal (nth ,ri x) (nth ,ri (,table c))))
                 (equal (fn2-machine-phase fn2-arm-id (,(fn2-columns-pre "UPDATE-" table) x c)) (fn2-machine-phase fn2-arm-id c)))
        :hints (("Goal" :in-theory (union-theories '(,(fn2-columns-pre "UPDATE-" table) ,table) (theory 'fn2-arm-frame-base))
                 :use ((:instance ,(fn2-columns-sym kind "-ARM-PHASE-CONGRUENCE") (id fn2-arm-id)
                                  (a (,(fn2-columns-pre "UPDATE-" table) x c)) (b c))))))
      (defthm ,(fn2-columns-sym kind "-ARM-ROW-PHASE")
        (implies (equal (,(fn2-columns-sym kind "-SNAPSHOT-READ-CODE") id fn2-core) :ok)
                 (equal (,(fn2-columns-sym kind "-ROW-PHASE") id fn2-core) (fn2-machine-phase id fn2-core)))
        :hints (("Goal" :in-theory (enable ,(fn2-columns-sym kind "-ROW-PHASE") ,(fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                                           fn2-machine-phase))))
      ; the kind's facts, disabled by one theory event (each costs a theory
      ; computation over the whole world)
      (in-theory (disable ,@(fn2-arm-frame-setter-runes kind (strip-cars tcols)) ,view ,upd ,(fn2-arm-frame-machines-over kind)
                          ,@(fn2-arm-frame-row-after-names kind (fn2-arm-frame-own-fields (strip-cars tcols)))
                          ,lens ,klen ,framep ,(fn2-arm-frame-table-keep-name kind) ,(fn2-columns-sym kind "-ARM-ROW-PHASE")))
      (table fn2-arm-frame-kinds ',kind t))))

;; Once per world: the base theory, each child's update facts, the readers'
;; congruences, and the stop's contracts.
(defun fn2-arm-frame-child-events (children k m pidx)
  ; M the directory's index, PIDX the children the phase reads
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (let* ((field (caar children)) (update (fn2-columns-pre "UPDATE-" field)))
      (append
       (and (not (equal k m))
            `((defthm ,(fn2-columns-pre "FN2-ARM-SLOT-OF-" update)
                (equal (fn2-machine-slot fn2-arm-id (,update v c)) (fn2-machine-slot fn2-arm-id c))
                :hints (("Goal" :in-theory (union-theories '(,update) (theory 'fn2-arm-frame-base))
                         :use ((:instance fn2-arm-slot-congruence (id fn2-arm-id) (a (,update v c)) (b c))))))))
       (and (not (member k pidx))
            `((defthm ,(fn2-columns-pre "FN2-ARM-PHASE-OF-" update)
                (equal (fn2-machine-phase fn2-arm-id (,update v c)) (fn2-machine-phase fn2-arm-id c))
                :hints (("Goal" :in-theory (union-theories '(,update) (theory 'fn2-arm-frame-base))
                         :use ((:instance fn2-arm-phase-congruence (id fn2-arm-id) (a (,update v c)) (b c))))))))
      (list*
       ; a declared child, or a write-back of the child as read
       `(defthm ,(fn2-columns-pre "FN2-ARM-KIDS-OF-" update)
          (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 c) (or (member-equal ,k fn2-arm-free) (equal v (,field c))))
                   (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 (,update v c)))
          :hints (("Goal" :in-theory (union-theories '(,update ,field) (theory 'fn2-arm-frame-base))
                   :use ((:instance fn2-arm-kids-update (i 0) (a fn2-arm-c0) (b c) (k ,k) (free fn2-arm-free))
                         (:instance fn2-arm-kids-update-same (i 0) (a fn2-arm-c0) (b c) (k ,k) (free fn2-arm-free))))))
       ; the written child against its current value (an inline put of the
       ; row builds V from it by setters; a write-back of it is V = it)
       `(defthm ,(fn2-columns-pre "FN2-ARM-ROW-FRAME-OF-" update)
          (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 c) (natp fn2-arm-tb)
                        (or (member-equal ,k fn2-arm-ch) (and (equal fn2-arm-tb ,k) (fn2-arm-cols 0 fn2-arm-row fn2-arm-cs (,field c) v))))
                   (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 (,update v c)))
          :hints (("Goal" :in-theory (union-theories '(,update ,field) (theory 'fn2-arm-frame-base))
                   :use ((:instance fn2-arm-row-frame-child (table fn2-arm-tb) (columns fn2-arm-cs) (children fn2-arm-ch) (a fn2-arm-c0) (b c) (k ,k) (row fn2-arm-row))
                         (:instance fn2-arm-row-frame-table (table fn2-arm-tb) (columns fn2-arm-cs) (children fn2-arm-ch) (a fn2-arm-c0) (b c) (row fn2-arm-row))
                         (:instance fn2-arm-row-frame-cols (table fn2-arm-tb) (columns fn2-arm-cs) (children fn2-arm-ch) (a fn2-arm-c0) (b c) (row fn2-arm-row))
                         (:instance fn2-arm-cols-trans (k 0) (row fn2-arm-row) (columns fn2-arm-cs) (a (nth fn2-arm-tb fn2-arm-c0)) (b (nth fn2-arm-tb c)) (c v))))))
       `(defthm ,(fn2-columns-pre "FN2-ARM-COLS-OF-" field)
          (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 c) (equal fn2-arm-tb ,k) (not (member-equal ,k fn2-arm-ch)))
                   (fn2-arm-cols 0 fn2-arm-row fn2-arm-cs (nth fn2-arm-tb fn2-arm-c0) (,field c)))
          :hints (("Goal" :in-theory (union-theories '(,field) (theory 'fn2-arm-frame-base))
                   :use ((:instance fn2-arm-row-frame-cols (table fn2-arm-tb) (columns fn2-arm-cs) (children fn2-arm-ch) (a fn2-arm-c0) (b c) (row fn2-arm-row))))))
       (fn2-arm-frame-child-events (cdr children) (+ 1 k) m pidx))))))
(defun fn2-arm-frame-child-runes (children k m pidx)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (let* ((field (caar children)) (update (fn2-columns-pre "UPDATE-" field)))
      (list* (fn2-columns-pre "FN2-ARM-KIDS-OF-" update) (fn2-columns-pre "FN2-ARM-ROW-FRAME-OF-" update)
             (fn2-columns-pre "FN2-ARM-COLS-OF-" field)
             (append (and (not (equal k m)) (list (fn2-columns-pre "FN2-ARM-SLOT-OF-" update)))
                     (and (not (member k pidx)) (list (fn2-columns-pre "FN2-ARM-PHASE-OF-" update)))
                     (fn2-arm-frame-child-runes (cdr children) (+ 1 k) m pidx))))))
;; A directory field's write at any id keeps every id's slot, kind, idp and phase
;; (the directory's slot and kind columns and its rows are not written):
;; the writers' SLOT and PHASE contracts by these, never by opening the
;; directory. MM is the directory as read from the same core.
(defun fn2-arm-frame-directory-name (reader field)
  (declare (xargs :verify-guards nil))
  (fn2-columns-pre (concatenate 'string "FN2-ARM-" (symbol-name reader) "-OF-")
                   (fn2-arm-frame-setter 'fn2-machines field)))
(defun fn2-arm-frame-directory-events (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let ((set (fn2-arm-frame-setter 'fn2-machines (car fields))))
      (append
       `((defthm ,(fn2-arm-frame-directory-name 'kind (car fields))
           (implies (equal mm (fn2-core-machines c))
                    (equal (fn2-machine-kind i (update-fn2-core-machines (,set j v mm) c)) (fn2-machine-kind i c)))
           :hints (("Goal" :in-theory (enable fn2-machine-kind fn2-machine-kind-read-code fn2-machine-idp fn2-machines-kind))))
         (defthm ,(fn2-arm-frame-directory-name 'slot (car fields))
           (implies (equal mm (fn2-core-machines c))
                    (equal (fn2-machine-slot i (update-fn2-core-machines (,set j v mm) c)) (fn2-machine-slot i c)))
           :hints (("Goal" :in-theory (enable fn2-machine-slot fn2-machine-slot-read-code fn2-machine-idp fn2-machines-slot))))
         (defthm ,(fn2-arm-frame-directory-name 'idp (car fields))
           (implies (equal mm (fn2-core-machines c))
                    (equal (fn2-machine-idp i (update-fn2-core-machines (,set j v mm) c)) (fn2-machine-idp i c)))
           :hints (("Goal" :in-theory (enable fn2-machine-idp))))
         (defthm ,(fn2-arm-frame-directory-name 'phase (car fields))
           (implies (equal mm (fn2-core-machines c))
                    (equal (fn2-machine-phase i (update-fn2-core-machines (,set j v mm) c)) (fn2-machine-phase i c)))
           :hints (("Goal" :in-theory (enable fn2-machine-phase fn2-machine-phase-read-code fn2-machine-idp
                                              fn2-machines-slot fn2-machines-kind)))))
       (fn2-arm-frame-directory-events (cdr fields))))))
(defun fn2-arm-frame-directory-runes (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (list* (fn2-arm-frame-directory-name 'kind (car fields)) (fn2-arm-frame-directory-name 'slot (car fields))
           (fn2-arm-frame-directory-name 'idp (car fields)) (fn2-arm-frame-directory-name 'phase (car fields))
           (fn2-arm-frame-directory-runes (cdr fields)))))
(defun fn2-arm-frame-directory-reader-runes (reader fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (fn2-arm-frame-directory-name reader (car fields)) (fn2-arm-frame-directory-reader-runes reader (cdr fields)))))
(defun fn2-arm-frame-basis-events (world)
  (declare (xargs :verify-guards nil))
  (let* ((children (fn2-arm-frame-children-of world)) (m (fn2-arm-frame-m world)) (ctl (fn2-arm-frame-ctl world)))
    `((deftheory fn2-arm-frame-base
        (union-theories '(mv-nth car-cons cdr-cons nth-update-nth fn2-arm-kids-refl fn2-arm-row-frame-refl fn2-arm-cols-refl
                          fn2-arm-member-of-subsetp-free fn2-arm-not-member-of-subsetp subsetp-equal member-equal)
                        (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))
      (defthm fn2-arm-core-len
        (implies (fn2-corep c) (equal (len c) ,(len children)))
        :hints (("Goal" :in-theory (enable fn2-corep))))
      (in-theory (disable fn2-arm-core-len))
      (defthm fn2-arm-slot-congruence
        (implies (equal (nth ,m a) (nth ,m b)) (equal (fn2-machine-slot id a) (fn2-machine-slot id b)))
        :rule-classes nil
        :hints (("Goal" :in-theory (enable fn2-machine-slot fn2-machine-slot-read-code fn2-machine-idp fn2-core-machines))))
      (defthm fn2-arm-kind-congruence
        (implies (equal (nth ,m a) (nth ,m b)) (equal (fn2-machine-kind id a) (fn2-machine-kind id b)))
        :rule-classes nil
        :hints (("Goal" :in-theory (enable fn2-machine-kind fn2-machine-kind-read-code fn2-machine-idp fn2-core-machines))))
      (defthm fn2-arm-phase-congruence
        (implies (and ,@(fn2-arm-frame-nth-equalities (fn2-arm-frame-phase-indices world)))
                 (equal (fn2-machine-phase id a) (fn2-machine-phase id b)))
        :rule-classes nil
        :hints (("Goal" :in-theory (enable fn2-machine-phase fn2-machine-phase-read-code fn2-machine-idp fn2-core-machines
                                           ,@(fn2-machine-machine-tables world))
                 :use ((:instance fn2-arm-slot-congruence) (:instance fn2-arm-kind-congruence)))))
      ,@(fn2-arm-frame-child-events children 0 m (fn2-arm-frame-phase-indices world))
      (in-theory (disable ,@(fn2-arm-frame-child-runes children 0 m (fn2-arm-frame-phase-indices world))))
      ,@(fn2-arm-frame-directory-events (strip-cars *fn2-machine-directory-fields*))
      (in-theory (disable ,@(fn2-arm-frame-directory-runes (strip-cars *fn2-machine-directory-fields*))))
      ;; a directory written back keeping its kind and slot columns and rows
      ;; (a child function's -KEEPS-DIRECTORY, table fn2-arm-frame-directory-keeps)
      (defthm fn2-arm-kind-of-directory-keeps
        (implies (fn2-machines-directory-keeps x (fn2-core-machines c))
                 (equal (fn2-machine-kind fn2-arm-id (update-fn2-core-machines x c)) (fn2-machine-kind fn2-arm-id c)))
        :hints (("Goal" :in-theory (enable fn2-machines-directory-keeps fn2-machine-kind fn2-machine-kind-read-code
                                           fn2-machine-idp fn2-machines-kind fn2-machines-rows))))
      (defthm fn2-arm-slot-of-directory-keeps
        (implies (fn2-machines-directory-keeps x (fn2-core-machines c))
                 (equal (fn2-machine-slot fn2-arm-id (update-fn2-core-machines x c)) (fn2-machine-slot fn2-arm-id c)))
        :hints (("Goal" :in-theory (enable fn2-machines-directory-keeps fn2-machine-slot fn2-machine-slot-read-code
                                           fn2-machine-idp fn2-machines-slot fn2-machines-rows))))
      (defthm fn2-arm-phase-of-directory-keeps
        (implies (fn2-machines-directory-keeps x (fn2-core-machines c))
                 (equal (fn2-machine-phase fn2-arm-id (update-fn2-core-machines x c)) (fn2-machine-phase fn2-arm-id c)))
        :hints (("Goal" :in-theory (enable fn2-machines-directory-keeps fn2-machine-phase fn2-machine-phase-read-code
                                           fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code fn2-machine-slot
                                           fn2-machine-slot-read-code fn2-machines-slot fn2-machines-kind fn2-machines-rows))))
      (in-theory (disable fn2-arm-kind-of-directory-keeps fn2-arm-slot-of-directory-keeps fn2-arm-phase-of-directory-keeps))
      ,@(fn2-arm-frame-op-events 'fn2-core-stop (list ctl) nil world)
      ,@(fn2-arm-frame-op-events 'fn2-machine-refuse-write (list ctl) '(fn2-core-stop-arm-kids) world))))
;; A batched write function's contracts (machine-arms.lisp emits it): the
;; chained ones above, the phase it leaves, and its readable contract
;; K-WRITE+...-CONTRACT: every column outside its fields, every other row
;; and every other child unchanged (the directory too, but for its own
;; directory fields at ID), and, accepted, its fields of row ID read back as
;; given.
(defun fn2-arm-frame-row-frame-hyps (tk s j id)
  (declare (xargs :verify-guards nil))
  `((natp fn2-arm-tb) (subsetp-equal ',s fn2-arm-ch)
    (or (member-equal ,tk fn2-arm-ch)
        (and (equal fn2-arm-tb ,tk) (subsetp-equal ',j fn2-arm-cs) (equal (fn2-machine-slot ,id fn2-core) fn2-arm-row)))))
(defun fn2-arm-frame-read-backs (kind fields formals)
  ; every written field's value: the phase's, the own fields' through the
  ; kind's row reader, a directory field's through the directory's reader at
  ; the id (fn2-machine-<field>)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (cond ((eq (car fields) 'phase) `(equal (fn2-machine-phase id after) ,(car formals)))
                ((assoc-eq (car fields) *fn2-machine-directory-fields*)
                 `(equal (,(fn2-columns-col-name 'fn2-machine (car fields)) id after) ,(car formals)))
                (t `(equal (,(fn2-machine-row-reader kind (car fields)) id after) ,(car formals))))
          (fn2-arm-frame-read-backs kind (cdr fields) (cdr formals)))))
;; A directory field's read back: its dispatcher over the directory written
;; at the id, the directory's column setter's facts.
(defun fn2-arm-frame-directory-read-back-runes (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) '(fn2-machine-idp fn2-core-machines-of-update-fn2-core-machines)
    (let ((get (fn2-columns-col-name 'fn2-machine (car fields)))
          (column (fn2-columns-col-name 'fn2-machines (car fields))))
      (list* get (fn2-columns-sym get "-READ-CODE") column (fn2-columns-sym column "$AI")
             (append (fn2-arm-frame-setter-facts 'fn2-machines (list (car fields)))
                     (fn2-arm-frame-directory-read-back-runes (cdr fields)))))))
(defun fn2-arm-frame-write-guards (kind fields formals world)
  ; the batch's acceptance, as the put expansion tests it
  (declare (xargs :verify-guards nil))
  `(and (fn2-machine-idp id fn2-core)
        (equal (fn2-machine-kind id fn2-core) ,(fn2-columns-pre "*" (fn2-columns-sym kind "-KIND*")))
        (natp (fn2-machine-slot id fn2-core))
        (< (fn2-machine-slot id fn2-core) (,(fn2-columns-sym kind "-ROWS") (,(fn2-columns-sym kind "-TABLE") fn2-core)))
        ,@(fn2-machine-write-guards (pairlis$ fields (pairlis$ formals nil)) (fn2-machine-property kind :columns world))))
(defun fn2-arm-frame-read-back-runes (kind fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (append (if (eq (car fields) 'phase)
                (list (fn2-columns-pre "FN2-ARM-PHASE-OF-UPDATE-" (fn2-columns-sym kind "-TABLE"))
                      (fn2-columns-col-name kind 'phase) (fn2-columns-sym (fn2-columns-col-name kind 'phase) "$AI"))
              (list (fn2-arm-frame-row-after-name kind (car fields))
                    (fn2-columns-col-name kind (car fields)) (fn2-columns-sym (fn2-columns-col-name kind (car fields)) "$AI")))
            (fn2-arm-frame-read-back-runes kind (cdr fields)))))
(defun fn2-arm-frame-write-events (kind fields w world)
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals w world))
         (wformals (butlast (cdr formals) 1))
         (call (cons w formals))
         (tcols (fn2-machine-property kind :table world))
         (states (fn2-machine-property kind :states world))
         (j (fn2-machine-column-indices fields tcols))
         (dirp (intersectp-eq fields (strip-cars *fn2-machine-directory-fields*)))
         (table (fn2-columns-sym kind "-TABLE"))
         (tk (fn2-arm-frame-child-index table world))
         (ctl (fn2-arm-frame-ctl world))
         (m (fn2-arm-frame-m world))
         (s (if dirp (list tk ctl m) (list tk ctl)))
         (s1 (if dirp (list ctl m) (list ctl)))
         (pf (and (member-eq 'phase fields) (nth (position-eq 'phase fields) wformals)))
         (kids (fn2-arm-frame-name w "-ARM-KIDS"))
         (frame (fn2-arm-frame-name w "-ARM-ROW-FRAME"))
         (slot (fn2-arm-frame-name w "-ARM-SLOT"))
         (phase (fn2-arm-frame-name w "-ARM-PHASE"))
         (contract (fn2-arm-frame-name w "-CONTRACT"))
         (update-table (fn2-columns-pre "UPDATE-" table))
         (machines-of (fn2-columns-pre "FN2-CORE-MACHINES-OF-" update-table))
         (open (list* w 'fn2-machine-refuse-write (fn2-arm-frame-setter-facts kind (fn2-arm-frame-table-fields fields)))))
    `((defthm ,kids
        (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',s fn2-arm-free))
                 (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,call))
        :hints ,(fn2-arm-frame-hints (list* w 'fn2-machine-refuse-write 'fn2-core-stop-arm-kids
                                            (fn2-arm-frame-kids-runes (fn2-arm-frame-children-of world)))))
      (defthm ,frame
        (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core) ,@(fn2-arm-frame-row-frame-hyps tk s1 j 'id))
                 (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 ,call))
        :hints ,(fn2-arm-frame-hints
                 (list* w 'fn2-machine-refuse-write-arm-row-frame
                        (fn2-columns-pre "FN2-ARM-ROW-FRAME-OF-" update-table)
                        (fn2-columns-pre "FN2-ARM-COLS-OF-" table)
                        (append (and dirp '(fn2-arm-row-frame-of-update-fn2-core-machines))
                                (fn2-arm-frame-setter-runes kind (fn2-arm-frame-table-fields fields))))))
      ,(if dirp
           ; the table's write keeps every slot (FN2-ARM-SLOT-OF-UPDATE-<table>), the
           ; directory fields' too: one opening of W, no setter opened
           `(defthm ,slot
              (equal (fn2-machine-slot fn2-arm-id ,call) (fn2-machine-slot fn2-arm-id fn2-core))
              :hints ,(fn2-arm-frame-hints
                       (list* w 'fn2-machine-refuse-write 'fn2-core-stop-arm-slot 'fn2-machine-idp-bounds
                              (fn2-columns-pre "FN2-ARM-SLOT-OF-" update-table) machines-of
                              (fn2-arm-frame-directory-reader-runes 'slot (fn2-arm-frame-directory-fields fields)))))
         `(defthm ,slot
            (equal (fn2-machine-slot fn2-arm-id ,call) (fn2-machine-slot fn2-arm-id fn2-core))
            :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                     :use ((:instance ,kids (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                           (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',s) (a fn2-core) (b ,call))
                           (:instance fn2-arm-slot-congruence (id fn2-arm-id) (a fn2-core) (b ,call)))))))
      (defthm ,phase
        ,(if pf
             `(implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (member-equal ,pf fn2-arm-pset)
                            (natp ,pf) (< ,pf ,(len states)))
                       (member-equal (fn2-machine-phase id ,call) fn2-arm-pset))
           `(implies (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset)
                     (member-equal (fn2-machine-phase id ,call) fn2-arm-pset)))
        :hints ,(fn2-arm-frame-hints
                 (list* 'fn2-core-stop-arm-phase (fn2-columns-pre "FN2-ARM-PHASE-OF-UPDATE-" table)
                        (fn2-columns-pre "FN2-ARM-PHASE-VIEW-" kind) (fn2-columns-col-name kind 'phase)
                        (fn2-columns-sym (fn2-columns-col-name kind 'phase) "$AI")
                        (fn2-columns-sym table (concatenate 'string "-OF-" (symbol-name update-table)))
                        'natp 'nfix 'zp 'fix
                        (append open (fn2-arm-frame-setter-facts kind (list 'phase))
                                (and dirp (list* 'fn2-machine-idp-bounds machines-of
                                                 (fn2-arm-frame-directory-reader-runes
                                                  'phase (fn2-arm-frame-directory-fields fields))))))))
      (defthm ,(fn2-arm-frame-name w "-FRAME")
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                 (fn2-arm-framep ,tk (fn2-machine-slot id fn2-core) ',j ',s1 fn2-core ,call))
        :hints (("Goal" :in-theory (union-theories '(,(fn2-columns-sym w "-PRESERVES-TYPE") ,(fn2-columns-sym w "-PRESERVES-WFP"))
                                                   (theory 'fn2-arm-frame-base))
                 :use ((:instance ,frame (fn2-arm-tb ,tk) (fn2-arm-row (fn2-machine-slot id fn2-core)) (fn2-arm-cs ',j) (fn2-arm-ch ',s1) (fn2-arm-c0 fn2-core))
                       (:instance ,(fn2-columns-sym kind "-ARM-FRAMEP") (fn2-arm-row (fn2-machine-slot id fn2-core)) (fn2-arm-cs ',j)
                                  (fn2-arm-ch ',s1) (a fn2-core) (b ,call))))))
      (defthm ,(fn2-arm-frame-name w "-READS")
        (implies ,(fn2-arm-frame-write-guards kind fields wformals world)
                 (let ((after ,call)) (and ,@(fn2-arm-frame-read-backs kind fields wformals))))
        :hints ,(fn2-arm-frame-hints (append (list w 'natp 'nfix 'fix 'unsigned-byte-p 'integer-range-p)
                                             (fn2-arm-frame-setter-facts kind (fn2-arm-frame-table-fields fields))
                                             (fn2-arm-frame-read-back-runes kind (fn2-arm-frame-table-fields fields))
                                             (and dirp (list* (fn2-arm-frame-machines-over kind) machines-of 'fn2-machine-idp-bounds
                                                              (append (fn2-arm-frame-directory-read-back-runes (fn2-arm-frame-directory-fields fields))
                                                                      (fn2-arm-frame-directory-reader-runes 'slot (fn2-arm-frame-directory-fields fields))
                                                                      (fn2-arm-frame-directory-reader-runes 'kind (fn2-arm-frame-directory-fields fields))
                                                                      (fn2-arm-frame-directory-reader-runes 'idp (fn2-arm-frame-directory-fields fields))))))))
      (defthm ,contract
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                 (let ((after ,call))
                   (and (fn2-arm-framep ,tk (fn2-machine-slot id fn2-core) ',j ',s1 fn2-core after)
                        (implies ,(fn2-arm-frame-write-guards kind fields wformals world)
                                 (and ,@(fn2-arm-frame-read-backs kind fields wformals))))))
        :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                 :use (,(fn2-arm-frame-name w "-FRAME") ,(fn2-arm-frame-name w "-READS")))))
      ; one theory event for the seven (each proof above names its own theory)
      (in-theory (disable ,kids ,frame ,slot ,phase ,(fn2-arm-frame-name w "-FRAME") ,(fn2-arm-frame-name w "-READS") ,contract))
      (table fn2-arm-frame-fns ',w '(:write ,kind ,j ,s1)))))
;; The core-changing functions a body calls.
(mutual-recursion
 (defun fn2-arm-frame-callees (x world acc)
   (declare (xargs :verify-guards nil :measure (acl2-count x)))
   (cond ((atom x) acc)
         ((eq (car x) 'quote) acc)
         (t (fn2-arm-frame-callees-list (cdr x) world
              (cond ((consp (car x)) (fn2-arm-frame-callees (caddr (car x)) world acc))
                    ((fn2-arm-frame-corep-fn (car x) world) (add-to-set-eq (car x) acc))
                    (t acc))))))
 (defun fn2-arm-frame-callees-list (l world acc)
   (declare (xargs :verify-guards nil :measure (acl2-count l)))
   (if (atom l) acc (fn2-arm-frame-callees-list (cdr l) world (fn2-arm-frame-callees (car l) world acc)))))
(defun fn2-arm-frame-body-callees (fn world)
  (declare (xargs :verify-guards nil))
  (remove-eq fn (fn2-arm-frame-callees (getpropc fn 'unnormalized-body nil world) world nil)))
(defun fn2-arm-frame-child-updater (fn world)
  ; the index of the core child FN updates (UPDATE-<child>), else nil
  (declare (xargs :verify-guards nil))
  (and (symbolp fn)
       (let ((name (symbol-name fn)))
         (and (< 7 (length name)) (equal (subseq name 0 7) "UPDATE-")
              (fn2-arm-frame-child-index (intern-in-package-of-symbol (subseq name 7 (length name)) fn) world)))))
(defun fn2-arm-frame-kname (kind fn suffix)
  ; KIND~FN-SUFFIX: a callee's contract derived under KIND
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name kind) "~" (symbol-name fn) suffix) fn))
(defun fn2-arm-frame-phase-record (fn kind world)
  ; the phase values FN writes, recorded under (KIND . FN)
  (declare (xargs :verify-guards nil))
  (assoc-equal (cons kind fn) (table-alist 'fn2-arm-frame-phases world)))
(defun fn2-arm-frame-scoped-p (fn kind world)
  ; FN's contracts were derived under KIND (a callee outside the basis and
  ; the write functions): their names and entry carry the kind, so sibling
  ; books deriving the same callee under other kinds never collide
  (declare (xargs :verify-guards nil))
  (and (assoc-equal (cons kind fn) (table-alist 'fn2-arm-frame-fns world)) t))
(defun fn2-arm-frame-known (fn kind world)
  ; FN's contract entry: from table fn2-arm-frame-fns (under (KIND . FN),
  ; else FN), or (:child K) for a core child's updater (the basis's facts).
  ; Entries: (:write KIND J S), (:row TK S J), (:op S), (:child K),
  ; (:arm CH J NEXT), (:failed REASON).
  (declare (xargs :verify-guards nil))
  (or (cdr (assoc-equal (cons kind fn) (table-alist 'fn2-arm-frame-fns world)))
      (cdr (assoc-eq fn (table-alist 'fn2-arm-frame-fns world)))
      (let ((k (fn2-arm-frame-child-updater fn world))) (and k (list :child k)))))
(defun fn2-arm-frame-op-set (fn kind world)
  ; an operation's declared children: its :tables and control; its kind's
  ; table when its :own-writes name columns of its row, the directory when
  ; they name directory fields
  (declare (xargs :verify-guards nil))
  (let* ((row (fn2-decl-row (list :cost fn) world)) (own (fn2-decl-get :own-writes row)))
    (fn2-arm-frame-indices (append (fn2-cost-tables (fn2-decl-get :tables row) world) '(fn2-core-control)
                                   (fn2-machine-directory-child own)
                                   (and (fn2-machine-column-indices own (fn2-machine-property kind :table world))
                                        (list (fn2-columns-sym kind "-TABLE"))))
                           world)))
;; An entry's parts: the table it writes at its id's row (row level), those
;; columns, and its other children.
(defun fn2-arm-frame-entry-tk (e world)
  (declare (xargs :verify-guards nil))
  (cond ((eq (car e) :write) (fn2-arm-frame-child-index (fn2-columns-sym (cadr e) "-TABLE") world))
        ((eq (car e) :row) (cadr e))
        (t nil)))
(defun fn2-arm-frame-entry-j (e)
  (declare (xargs :verify-guards nil))
  (cond ((eq (car e) :write) (caddr e)) ((eq (car e) :row) (cadddr e)) (t nil)))
(defun fn2-arm-frame-entry-s (e)
  (declare (xargs :verify-guards nil))
  (cond ((eq (car e) :write) (cadddr e)) ((eq (car e) :row) (caddr e))
        ((eq (car e) :op) (cadr e)) ((eq (car e) :child) (list (cadr e))) (t nil)))
(defun fn2-arm-frame-entry-kids (e world)
  ; every child the function may change
  (declare (xargs :verify-guards nil))
  (let ((tk (fn2-arm-frame-entry-tk e world)))
    (if tk (add-to-set-eql tk (fn2-arm-frame-entry-s e)) (fn2-arm-frame-entry-s e))))
(defun fn2-arm-frame-lemma (fn e suffix kind world)
  ; the name of FN's contract SUFFIX (-ARM-KIDS, -ARM-ROW-FRAME, -ARM-SLOT,
  ; -ARM-PHASE); a child updater's are the basis's
  (declare (xargs :verify-guards nil))
  (if (eq (car e) :child)
      (fn2-columns-pre (cond ((equal suffix "-ARM-KIDS") "FN2-ARM-KIDS-OF-")
                             ((equal suffix "-ARM-ROW-FRAME") "FN2-ARM-ROW-FRAME-OF-")
                             ((equal suffix "-ARM-SLOT") "FN2-ARM-SLOT-OF-")
                             (t "FN2-ARM-PHASE-OF-"))
                       fn)
    (if (fn2-arm-frame-scoped-p fn kind world) (fn2-arm-frame-kname kind fn suffix) (fn2-arm-frame-name fn suffix))))
(defun fn2-arm-frame-lemmas-1 (fn e suffixes kind world)
  (declare (xargs :verify-guards nil))
  (cond ((atom suffixes) nil)
        ((getpropc (fn2-arm-frame-lemma fn e (car suffixes) kind world) 'theorem nil world)
         (cons (fn2-arm-frame-lemma fn e (car suffixes) kind world) (fn2-arm-frame-lemmas-1 fn e (cdr suffixes) kind world)))
        (t (fn2-arm-frame-lemmas-1 fn e (cdr suffixes) kind world))))
(defun fn2-arm-frame-lemmas (fns suffixes kind world)
  ; the contracts SUFFIXES of the callees FNS that exist in WORLD
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (let ((e (fn2-arm-frame-known (car fns) kind world)))
      (append (fn2-arm-frame-lemmas-1 (car fns) e suffixes kind world)
              (fn2-arm-frame-lemmas (cdr fns) suffixes kind world)))))
;; The functions under FNS without an entry, callees first.
(defun fn2-arm-frame-todo (fns kind world acc fuel)
  (declare (xargs :verify-guards nil :measure (make-ord 1 (+ 1 (nfix fuel)) (acl2-count fns))))
  (cond ((or (zp fuel) (atom fns)) acc)
        ((or (member-eq (car fns) acc) (fn2-arm-frame-known (car fns) kind world))
         (fn2-arm-frame-todo (cdr fns) kind world acc fuel))
        (t (fn2-arm-frame-todo (cdr fns) kind world
             (append (fn2-arm-frame-todo (fn2-arm-frame-body-callees (car fns) world) kind world acc (1- fuel))
                     (list (car fns)))
             fuel))))
;; The columns of KIND's table whose setters a body calls directly (an
;; inline put of its row).
(mutual-recursion
 (defun fn2-arm-frame-fnsyms (x acc)
   (declare (xargs :verify-guards nil :measure (acl2-count x)))
   (cond ((atom x) acc)
         ((eq (car x) 'quote) acc)
         (t (fn2-arm-frame-fnsyms-list (cdr x)
              (cond ((consp (car x)) (fn2-arm-frame-fnsyms (caddr (car x)) acc))
                    (t (add-to-set-eq (car x) acc)))))))
 (defun fn2-arm-frame-fnsyms-list (l acc)
   (declare (xargs :verify-guards nil :measure (acl2-count l)))
   (if (atom l) acc (fn2-arm-frame-fnsyms-list (cdr l) (fn2-arm-frame-fnsyms (car l) acc)))))
(defun fn2-arm-frame-setter-columns (kind fn2-arm-cs fns j)
  (declare (xargs :verify-guards nil))
  (cond ((atom fn2-arm-cs) nil)
        ((member-eq (fn2-arm-frame-setter kind (caar fn2-arm-cs)) fns)
         (cons j (fn2-arm-frame-setter-columns kind (cdr fn2-arm-cs) fns (+ 1 j))))
        (t (fn2-arm-frame-setter-columns kind (cdr fn2-arm-cs) fns (+ 1 j)))))
(defun fn2-arm-frame-body-setters (fn kind world)
  (declare (xargs :verify-guards nil))
  (fn2-arm-frame-setter-columns kind (fn2-machine-property kind :table world)
                                (fn2-arm-frame-fnsyms (getpropc fn 'unnormalized-body nil world) nil) 0))
(defun fn2-arm-frame-column-fields (j fn2-arm-cs)
  (declare (xargs :verify-guards nil))
  (if (atom j) nil (cons (car (nth (car j) fn2-arm-cs)) (fn2-arm-frame-column-fields (cdr j) fn2-arm-cs))))
;; A function's entry from its callees' entries: (mv entry problem). An
;; operation's sets are its defcost's (its :own-writes the columns of its
;; row); a helper's are its callees'. PROBLEM names a callee without
;; contracts or the children a callee changes beyond the declaration.
(defun fn2-arm-frame-infer (fns tk inline c r kind world)
  ; (mv children row-columns failed-callee); INLINE: the body puts its own
  ; row through the table's setters, so its table update is row level
  (declare (xargs :verify-guards nil))
  (if (atom fns) (mv c r nil)
    (let* ((e (fn2-arm-frame-known (car fns) kind world)) (etk (fn2-arm-frame-entry-tk e world)))
      (cond ((or (null e) (member-eq (car e) '(:failed :arm))) (mv c r (car fns)))
            ((and inline (eq (car e) :child) (equal (cadr e) tk))
             (fn2-arm-frame-infer (cdr fns) tk inline c r kind world))
            ((and etk (equal etk tk))
             (fn2-arm-frame-infer (cdr fns) tk inline (union-equal (fn2-arm-frame-entry-s e) c)
                                  (union-equal (fn2-arm-frame-entry-j e) r) kind world))
            (t (fn2-arm-frame-infer (cdr fns) tk inline (union-equal (fn2-arm-frame-entry-kids e world) c) r kind world))))))
(defun fn2-arm-frame-kept (keeps fns world)
  ; the children a keeps lemma (table fn2-arm-frame-keeps: (FN CHILD)) shows
  ; written back unchanged, for the child functions in FNS
  (declare (xargs :verify-guards nil))
  (cond ((atom keeps) nil)
        ((and (consp (cdar keeps)) (member-eq (cadar keeps) fns))
         (add-to-set-eql (fn2-arm-frame-child-index (caddar keeps) world) (fn2-arm-frame-kept (cdr keeps) fns world)))
        (t (fn2-arm-frame-kept (cdr keeps) fns world))))
(defun fn2-arm-frame-fn-entry (fn kind world)
  (declare (xargs :verify-guards nil))
  (let* ((tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world))
         (kept (fn2-arm-frame-kept (table-alist 'fn2-arm-frame-keeps world)
                                   (fn2-arm-frame-fnsyms (getpropc fn 'unnormalized-body nil world) nil) world))
         (row (fn2-decl-row (list :cost fn) world))
         (idp (member-eq 'id (formals fn world))))
    (mv-let (c r bad) (fn2-arm-frame-infer (fn2-arm-frame-body-callees fn world) tk
                                           (and idp (fn2-arm-frame-body-setters fn kind world)) nil
                                           (fn2-arm-frame-body-setters fn kind world) kind world)
      (let* ((rowp (and r idp (not (member tk c))))
             (inferred (if rowp c (if r (add-to-set-eql tk c) c))))
        ; (mv entry problem why): WHY names the failure if the proof fails
        ; (a callee writes beyond the declaration, unless it writes back
        ; what it read: the proof decides)
        (cond ((not (getpropc fn 'unnormalized-body nil world)) (mv nil '(:constrained) nil))
              (bad (mv nil (list :callee bad (fn2-arm-frame-known bad kind world)) nil))
              ((not row) (mv (if rowp (list :row tk c r) (list :op inferred)) nil '(:kids)))
              (t (let* ((s (fn2-arm-frame-op-set fn kind world))
                        (sd (remove-equal tk s))
                        (jd (fn2-machine-column-indices (fn2-decl-get :own-writes row) (fn2-machine-property kind :table world)))
                        (why (cond ((not (subsetp-equal (set-difference-equal (if rowp c inferred) kept) (if rowp sd s)))
                                    (list :children (set-difference-equal (set-difference-equal (if rowp c inferred) kept)
                                                                          (if rowp sd s))))
                                   ((and rowp (not (subsetp-equal r jd)))
                                    (list :columns (set-difference-equal r jd)))
                                   (t '(:kids)))))
                   (if (and (member tk s) idp) (mv (list :row tk sd jd) nil why) (mv (list :op s) nil why)))))))))
;; The phase values a body writes: each write function's phase argument
;; (a constant, else :any) and each callee's recorded set (table
;; fn2-arm-frame-phases).
(mutual-recursion
 (defun fn2-arm-frame-phase-args (x kind world acc)
   (declare (xargs :verify-guards nil :measure (acl2-count x)))
   (cond ((atom x) acc)
         ((eq (car x) 'quote) acc)
         ((consp (car x))
          (fn2-arm-frame-phase-args-list (cdr x) kind world (fn2-arm-frame-phase-args (caddr (car x)) kind world acc)))
         (t (let* ((pos (and (eq (car (fn2-arm-frame-known (car x) kind world)) :write)
                             (position-eq 'fn2-arms-w-phase (formals (car x) world))))
                   (a (and pos (nth pos (cdr x))))
                   (rec (fn2-arm-frame-phase-record (car x) kind world))
                   (acc (cond (pos (add-to-set-equal (if (quotep a) (unquote a) :any) acc))
                              (rec (union-equal (cdr rec) acc))
                              (t acc))))
              (fn2-arm-frame-phase-args-list (cdr x) kind world acc)))))
 (defun fn2-arm-frame-phase-args-list (l kind world acc)
   (declare (xargs :verify-guards nil :measure (acl2-count l)))
   (if (atom l) acc (fn2-arm-frame-phase-args-list (cdr l) kind world (fn2-arm-frame-phase-args (car l) kind world acc)))))
(defun fn2-arm-frame-inline-runes (fn kind world)
  ; a body's inline put of its row: the table's current-value fact and its
  ; setters' column facts
  (declare (xargs :verify-guards nil))
  (let ((j (fn2-arm-frame-body-setters fn kind world)))
    (and j (cons (fn2-columns-pre "FN2-ARM-COLS-OF-" (fn2-columns-sym kind "-TABLE"))
                 (fn2-arm-frame-setter-runes kind (fn2-arm-frame-column-fields j (fn2-machine-property kind :table world)))))))
(defun fn2-arm-frame-inline-phase-runes (fn kind world)
  ; an arm's inline put of its row: the phase through the kind's table after
  ; its setters (as a write function's phase contract)
  (declare (xargs :verify-guards nil))
  (let ((j (fn2-arm-frame-body-setters fn kind world)) (table (fn2-columns-sym kind "-TABLE")))
    (and j (list* (fn2-columns-pre "FN2-ARM-PHASE-OF-UPDATE-" table) (fn2-columns-pre "FN2-ARM-PHASE-VIEW-" kind)
                  (fn2-columns-col-name kind 'phase) (fn2-columns-sym (fn2-columns-col-name kind 'phase) "$AI")
                  (fn2-columns-sym table (concatenate 'string "-OF-" (symbol-name (fn2-columns-pre "UPDATE-" table))))
                  'natp 'nfix 'zp 'fix
                  (fn2-arm-frame-setter-facts kind (cons 'phase (fn2-arm-frame-column-fields
                                                                 j (fn2-machine-property kind :table world))))))))
(defun fn2-arm-frame-all-have (fns suffix kind world)
  ; every callee has its contract SUFFIX (an opening proof without one is
  ; not attempted)
  (declare (xargs :verify-guards nil))
  (or (atom fns)
      (and (getpropc (fn2-arm-frame-lemma (car fns) (fn2-arm-frame-known (car fns) kind world) suffix kind world) 'theorem nil world)
           (fn2-arm-frame-all-have (cdr fns) suffix kind world))))
(defun fn2-arm-frame-maybe (event)
  ; an optional contract: proved, or absent (callers look it up)
  (declare (xargs :verify-guards nil))
  `(make-event '(:or ,event (value-triple :absent))))
(defun fn2-arm-frame-directory-keeps-of (fns keeps)
  (declare (xargs :verify-guards nil))
  (cond ((atom keeps) nil)
        ((member-eq (caar keeps) fns) (cons (cdar keeps) (fn2-arm-frame-directory-keeps-of fns (cdr keeps))))
        (t (fn2-arm-frame-directory-keeps-of fns (cdr keeps)))))
;; A core face that writes the directory back through child functions that
;; keep it (their -KEEPS-DIRECTORY): those lemmas, the directory-keep facts
;; of the reader SUFFIX names, and the machines read across the control
;; write. Nil when the body calls no such child.
(defun fn2-arm-frame-directory-keep-runes (fn reader world)
  (declare (xargs :verify-guards nil))
  (let* ((fns (fn2-arm-frame-fnsyms (getpropc fn 'unnormalized-body nil world) nil))
         (keeps (fn2-arm-frame-directory-keeps-of fns (table-alist 'fn2-arm-frame-directory-keeps world))))
    (and keeps (list* (if (eq reader 'slot) 'fn2-arm-slot-of-directory-keeps 'fn2-arm-phase-of-directory-keeps)
                      'fn2-core-machines-of-update-fn2-core-control keeps))))
;; The kind a table child belongs to, else nil.
(defun fn2-arm-frame-table-kind (k names world)
  (declare (xargs :verify-guards nil))
  (cond ((atom names) nil)
        ((equal (fn2-arm-frame-child-index (fn2-columns-sym (car names) "-TABLE") world) k) (car names))
        (t (fn2-arm-frame-table-kind k (cdr names) world))))
(defun fn2-arm-frame-equality-phase-p (fn kind world)
  ; FN's phase contract keeps every id's phase (not a write function's or a
  ; recorded subarm's membership form)
  (declare (xargs :verify-guards nil))
  (and (fn2-arm-frame-all-have (list fn) "-ARM-PHASE" kind world)
       (not (eq (car (fn2-arm-frame-known fn kind world)) :write))
       (not (fn2-arm-frame-phase-record fn kind world))))
;; (t . RUNES) when every callee of FN keeps every phase: equality contracts;
;; the directory's update through child functions that keep it; a kind
;; table's update through its setters off the phase column (its
;; -TABLE-KEEPING-PHASE fact and the setters' -NTH facts). Else nil.
(defun fn2-arm-frame-phase-keep-runes-1 (callees fn fnsyms kind world acc)
  (declare (xargs :verify-guards nil))
  (if (atom callees) (cons t acc)
    (let* ((c (car callees)) (e (fn2-arm-frame-known c kind world))
           (k (and (eq (car e) :child) (cadr e)))
           (tkind (and k (fn2-arm-frame-table-kind k (fn2-machine-names world) world))))
      (cond ((fn2-arm-frame-equality-phase-p c kind world)
             (fn2-arm-frame-phase-keep-runes-1 (cdr callees) fn fnsyms kind world
                                               (append (fn2-arm-frame-lemmas (list c) '("-ARM-PHASE") kind world) acc)))
            ((and k (equal k (fn2-arm-frame-m world)) (fn2-arm-frame-directory-keep-runes fn 'phase world))
             (fn2-arm-frame-phase-keep-runes-1 (cdr callees) fn fnsyms kind world
                                               (append (fn2-arm-frame-directory-keep-runes fn 'phase world) acc)))
            ((and tkind
                  (getpropc (fn2-arm-frame-table-keep-name tkind) 'theorem nil world)
                  (not (member-eq (fn2-arm-frame-setter tkind 'phase) fnsyms)))
             (fn2-arm-frame-phase-keep-runes-1
              (cdr callees) fn fnsyms kind world
              (cons (fn2-arm-frame-table-keep-name tkind)
                    (append (fn2-arm-frame-setter-facts
                             tkind (fn2-arm-frame-column-fields (fn2-arm-frame-body-setters fn tkind world)
                                                                (fn2-machine-property tkind :table world)))
                            acc))))
            (t nil)))))
(defun fn2-arm-frame-phase-keep-runes (fn callees kind world)
  (declare (xargs :verify-guards nil))
  (and (not (fn2-arm-frame-phase-args (getpropc fn 'unnormalized-body nil world) kind world nil))
       (fn2-arm-frame-phase-keep-runes-1 callees fn (fn2-arm-frame-fnsyms (getpropc fn 'unnormalized-body nil world) nil)
                                         kind world nil)))
;; FN's contracts at ENTRY, each by one opening of FN with its callees'
;; contracts: KIDS (required), ROW-FRAME (row level: within a caller's
;; frame at its row; else from KIDS), SLOT and PHASE (optional).
(defun fn2-arm-frame-fn-events (fn e kind world)
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals fn world))
         (out (fn2-arm-frame-out-term fn (cons fn formals) world))
         (callees (fn2-arm-frame-body-callees fn world))
         (m (fn2-arm-frame-m world))
         (s (fn2-arm-frame-entry-kids e world))
         (tk (fn2-arm-frame-entry-tk e world))
         (kids (fn2-arm-frame-kname kind fn "-ARM-KIDS"))
         (frame (fn2-arm-frame-kname kind fn "-ARM-ROW-FRAME"))
         (slot (fn2-arm-frame-kname kind fn "-ARM-SLOT"))
         (phase (fn2-arm-frame-kname kind fn "-ARM-PHASE"))
         (all '("-ARM-ROW-FRAME" "-ARM-SLOT" "-ARM-PHASE")))
    `((defthm ,kids
        (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',s fn2-arm-free))
                 (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,out))
        :hints ,(fn2-arm-frame-hints (cons fn (append (strip-cars (table-alist 'fn2-arm-frame-keeps world))
                                                      (fn2-arm-frame-lemmas callees '("-ARM-KIDS") kind world)))))
      ,(if (eq (car e) :row)
           `(defthm ,frame
              (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                            ,@(fn2-arm-frame-row-frame-hyps tk (fn2-arm-frame-entry-s e) (fn2-arm-frame-entry-j e) 'id))
                       (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 ,out))
              :hints ,(fn2-arm-frame-hints
                       (cons fn (append (fn2-arm-frame-inline-runes fn kind world)
                                        (fn2-arm-frame-lemmas callees all kind world)))))
         `(defthm ,frame
            (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core) (natp fn2-arm-tb) (subsetp-equal ',s fn2-arm-ch))
                     (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 ,out))
            :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                     :use ((:instance fn2-arm-row-frame-kids (table fn2-arm-tb) (columns fn2-arm-cs) (children fn2-arm-ch) (a fn2-arm-c0) (b fn2-core)
                                      (c ,out) (free ',s) (row fn2-arm-row))
                           (:instance ,kids (fn2-arm-free ',s) (fn2-arm-c0 fn2-core)))))))
      ,(fn2-arm-frame-maybe
        (if (not (member m s))
            `(defthm ,slot
               (equal (fn2-machine-slot fn2-arm-id ,out) (fn2-machine-slot fn2-arm-id fn2-core))
               :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                        :use ((:instance ,kids (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                              (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',s) (a fn2-core) (b ,out))
                              (:instance fn2-arm-slot-congruence (id fn2-arm-id) (a fn2-core) (b ,out))))))
          (cond ((fn2-arm-frame-all-have callees "-ARM-SLOT" kind world)
                 `(defthm ,slot
                    (equal (fn2-machine-slot fn2-arm-id ,out) (fn2-machine-slot fn2-arm-id fn2-core))
                    :hints ,(fn2-arm-frame-hints (cons fn (fn2-arm-frame-lemmas callees '("-ARM-SLOT") kind world)))))
                ; the directory written back through child functions that keep it
                ((and (fn2-arm-frame-directory-keep-runes fn 'slot world)
                      (fn2-arm-frame-all-have (remove-eq 'update-fn2-core-machines callees) "-ARM-SLOT" kind world))
                 `(defthm ,slot
                    (equal (fn2-machine-slot fn2-arm-id ,out) (fn2-machine-slot fn2-arm-id fn2-core))
                    :hints ,(fn2-arm-frame-hints
                             (cons fn (append (fn2-arm-frame-directory-keep-runes fn 'slot world)
                                              (fn2-arm-frame-lemmas callees '("-ARM-SLOT") kind world))))))
                (t '(value-triple :absent)))))
      ,(fn2-arm-frame-maybe
        (cond
         ((and (eq (car e) :row)
               (not (member (position-eq 'phase (strip-cars (fn2-machine-property kind :table world))) (fn2-arm-frame-entry-j e)))
               (not (intersectp-equal (fn2-arm-frame-phase-indices world) (fn2-arm-frame-entry-s e))))
          ; within its row frame, off the phase column
          `(defthm ,phase
             (equal (fn2-machine-phase fn2-arm-id ,out) (fn2-machine-phase fn2-arm-id fn2-core))
             :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                      :use ((:instance ,frame (fn2-arm-tb ,tk) (fn2-arm-row (fn2-machine-slot id fn2-core)) (fn2-arm-cs ',(fn2-arm-frame-entry-j e))
                                       (fn2-arm-ch ',(fn2-arm-frame-entry-s e)) (fn2-arm-c0 fn2-core))
                            (:instance ,(fn2-columns-sym kind "-ARM-PHASE-OF-ROW-FRAME") (id fn2-arm-id)
                                       (fn2-arm-row (fn2-machine-slot id fn2-core)) (fn2-arm-cs ',(fn2-arm-frame-entry-j e))
                                       (fn2-arm-ch ',(fn2-arm-frame-entry-s e)) (a fn2-core) (b ,out)))))))
         ((not (intersectp-equal (fn2-arm-frame-phase-indices world) s))
            `(defthm ,phase
               (equal (fn2-machine-phase fn2-arm-id ,out) (fn2-machine-phase fn2-arm-id fn2-core))
               :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                        :use ((:instance ,kids (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                              ,@(fn2-arm-frame-nth-uses (fn2-arm-frame-phase-indices world) s out)
                              (:instance fn2-arm-phase-congruence (id fn2-arm-id) (a fn2-core) (b ,out)))))))
         ((fn2-arm-frame-phase-keep-runes fn callees kind world)
          ; every callee keeps every phase: the directory and kinds' tables
          ; written back through what keeps it, the other callees by their
          ; equality contracts
          `(defthm ,phase
             (equal (fn2-machine-phase fn2-arm-id ,out) (fn2-machine-phase fn2-arm-id fn2-core))
             :hints ,(fn2-arm-frame-hints (cons fn (cdr (fn2-arm-frame-phase-keep-runes fn callees kind world))))))
         ((and (member-eq 'id formals) (fn2-arm-frame-all-have callees "-ARM-PHASE" kind world)
               (not (member-eq :any (fn2-arm-frame-phase-args (getpropc fn 'unnormalized-body nil world) kind world nil))))
          ; the phase stays or moves to a value it writes
          (let ((pv (fn2-arm-frame-phase-args (getpropc fn 'unnormalized-body nil world) kind world nil)))
            `(progn
               (defthm ,phase
                 (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) ,@(and pv `((subsetp-equal ',pv fn2-arm-pset))))
                          (member-equal (fn2-machine-phase id ,out) fn2-arm-pset))
                 :hints ,(fn2-arm-frame-hints (list* fn 'fn2-arm-member-of-subsetp-free
                                                     (fn2-arm-frame-lemmas callees '("-ARM-PHASE") kind world))))
               (table fn2-arm-frame-phases '(,kind . ,fn) ',pv))))
         (t '(value-triple :absent))))
      (table fn2-arm-frame-fns '(,kind . ,fn) ',e))))
(defun fn2-arm-frame-fn-form (fn kind world)
  ; FN's contracts, or its entry (:failed REASON): a callee without
  ; contracts, children beyond its declaration, or a proof (:kids); a row
  ; level contract whose ROW-FRAME fails falls back to the children level
  (declare (xargs :verify-guards nil))
  (if (fn2-arm-frame-known fn kind world) '(value-triple :known)
    (mv-let (e problem why) (fn2-arm-frame-fn-entry fn kind world)
      ; a body that changes children beyond its declaration cannot meet it:
      ; owed with them, no attempt; columns beyond it leave the row level
      ; for the operation level, the only attempt
      (let ((fallback (and e (list :op (fn2-arm-frame-entry-kids e world)))))
        (cond (problem `(table fn2-arm-frame-fns '(,kind . ,fn) '(:failed ,problem)))
              ((eq (car why) :children) `(table fn2-arm-frame-fns '(,kind . ,fn) '(:failed ,why)))
              ((and (eq (car why) :columns) (eq (car e) :row))
               `(:or (progn ,@(fn2-arm-frame-fn-events fn fallback kind world))
                     (table fn2-arm-frame-fns '(,kind . ,fn) '(:failed ,why))))
              (t `(:or (progn ,@(fn2-arm-frame-fn-events fn e kind world))
                       ,@(and (eq (car e) :row) `((progn ,@(fn2-arm-frame-fn-events fn fallback kind world))))
                       (table fn2-arm-frame-fns '(,kind . ,fn) '(:failed ,why)))))))))
(defun fn2-arm-frame-disable-form (fns kind world)
  ; after an arm's contracts: all disabled at once (the chained rules stay off by default)
  (declare (xargs :verify-guards nil))
  (let ((names (fn2-arm-frame-lemmas fns '("-ARM-KIDS" "-ARM-ROW-FRAME" "-ARM-SLOT" "-ARM-PHASE") kind world)))
    (if names `(in-theory (disable ,@names)) '(value-triple :none))))
(defun fn2-arm-frame-fns-forms (fns kind)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (cons `(make-event (fn2-arm-frame-fn-form ',(car fns) ',kind (w state)))
          (fn2-arm-frame-fns-forms (cdr fns) kind))))
;; ---------------------------------------------------------------------------
;; FOOTPRINT CONTRACTS (-DC-KIDS): a function's KIDS contract at the children
;; its callees' contracts show it may change, with no declaration to meet.
;; An attachment proves its constrained function's frame from these (the
;; footprint within the frame's children): the dispatch stubs' attachments
;; (assembly-attach) and the wait sources' (defwait, below). A function with
;; a KIDS contract of its own (table fn2-arm-frame-fns, or the basis's child
;; updaters) is not rederived.
;; Table fn2-dc-kids: (KIND . FN) -> the children of FN's -DC-KIDS contract.
(table fn2-dc-kids nil nil)
(defun fn2-dc-name (kind fn)
  (declare (xargs :verify-guards nil))
  (if kind (fn2-arm-frame-kname kind fn "-DC-KIDS") (fn2-arm-frame-name fn "-DC-KIDS")))
(defun fn2-dc-entry (fn kind world)
  ; (children . lemma) of FN's KIDS contract under KIND, else nil
  (declare (xargs :verify-guards nil))
  (let ((d (assoc-equal (cons kind fn) (table-alist 'fn2-dc-kids world))))
    (if d (cons (cdr d) (fn2-dc-name kind fn))
      (let ((e (fn2-arm-frame-known fn kind world)))
        (and e (not (member-eq (car e) '(:failed :arm)))
             (let ((lemma (fn2-arm-frame-lemma fn e "-ARM-KIDS" kind world)))
               (and (getpropc lemma 'theorem nil world)
                    (cons (fn2-arm-frame-entry-kids e world) lemma))))))))
(defun fn2-dc-todo (fns kind world acc fuel)
  ; the functions under FNS that return the core and have no KIDS contract, callees first
  (declare (xargs :verify-guards nil :measure (make-ord 1 (+ 1 (nfix fuel)) (acl2-count fns))))
  (cond ((or (zp fuel) (atom fns)) acc)
        ((or (member-eq (car fns) acc) (not (fn2-arm-frame-corep-fn (car fns) world)) (fn2-dc-entry (car fns) kind world))
         (fn2-dc-todo (cdr fns) kind world acc fuel))
        (t (fn2-dc-todo (cdr fns) kind world
                        (append (fn2-dc-todo (fn2-arm-frame-body-callees (car fns) world) kind world acc (1- fuel))
                                (list (car fns)))
                        fuel))))
(defun fn2-dc-callees (fns kind world set lemmas)
  ; (mv children lemmas missing): the callees' contracts, or the first callee without one
  (declare (xargs :verify-guards nil))
  (cond ((atom fns) (mv set lemmas nil))
        ((not (fn2-arm-frame-corep-fn (car fns) world)) (fn2-dc-callees (cdr fns) kind world set lemmas))
        (t (let ((d (fn2-dc-entry (car fns) kind world)))
             (if (null d) (mv set lemmas (car fns))
               (fn2-dc-callees (cdr fns) kind world (union-equal (car d) set) (cons (cdr d) lemmas)))))))
(defun fn2-dc-form (fn kind world)
  (declare (xargs :verify-guards nil))
  (if (fn2-dc-entry fn kind world) '(value-triple :known)
    (mv-let (set lemmas missing) (fn2-dc-callees (fn2-arm-frame-body-callees fn world) kind world nil nil)
      (cond
       ((not (getpropc fn 'unnormalized-body nil world))
        `(make-event (er soft 'fn2-dispatch-frame "~x0 is constrained without a KIDS constraint: no frame of its callers can be proved." ',fn)))
       (missing
        `(make-event (er soft 'fn2-dispatch-frame "~x0 calls ~x1, which has no KIDS contract." ',fn ',missing)))
       (t `(progn
               (defthm ,(fn2-dc-name kind fn)
                 (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',set fn2-arm-free))
                          (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,(fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
                 :hints ,(fn2-arm-frame-hints (cons fn (append (strip-cars (table-alist 'fn2-arm-frame-keeps world)) lemmas))))
               (table fn2-dc-kids '(,kind . ,fn) ',set)))))))
(defun fn2-dc-forms (fns kind)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (cons `(make-event (fn2-dc-form ',(car fns) ',kind (w state))) (fn2-dc-forms (cdr fns) kind))))
(defun fn2-dc-names (fns kind world)
  (declare (xargs :verify-guards nil))
  (cond ((atom fns) nil)
        ((assoc-equal (cons kind (car fns)) (table-alist 'fn2-dc-kids world))
         (cons (fn2-dc-name kind (car fns)) (fn2-dc-names (cdr fns) kind world)))
        (t (fn2-dc-names (cdr fns) kind world))))
(defun fn2-dc-disable-form (fns kind world)
  (declare (xargs :verify-guards nil))
  (let ((names (fn2-dc-names fns kind world)))
    (if names `(in-theory (disable ,@names)) '(value-triple :none))))
;; The children whose writers in FNS's closure the footprint names beyond
;; ALLOWED: (child . the functions with a contract that change it directly).
(defun fn2-dc-writers (fns kind world allowed seen acc fuel)
  (declare (xargs :verify-guards nil :measure (make-ord 1 (+ 1 (nfix fuel)) (acl2-count fns))))
  (cond ((or (zp fuel) (atom fns)) (mv seen acc))
        ((or (member-eq (car fns) seen) (not (fn2-arm-frame-corep-fn (car fns) world)))
         (fn2-dc-writers (cdr fns) kind world allowed seen acc fuel))
        (t (let* ((f (car fns)) (seen (cons f seen))
                  (d (assoc-equal (cons kind f) (table-alist 'fn2-dc-kids world)))
                  (e (and (null d) (fn2-dc-entry f kind world))))
             (if e
                 (fn2-dc-writers (cdr fns) kind world allowed seen
                                 (if (set-difference-equal (car e) allowed)
                                     (cons (list f (set-difference-equal (car e) allowed)) acc) acc)
                                 fuel)
               (mv-let (seen acc) (fn2-dc-writers (fn2-arm-frame-body-callees f world) kind world allowed seen acc (1- fuel))
                 (fn2-dc-writers (cdr fns) kind world allowed seen acc fuel)))))))
;; An attachment FN of a constrained function whose frame children are E:
;; its footprint within E, else the children beyond E and the contracts that
;; change them, named.
(defun fn2-dc-frame-check (who fn kind e world)
  (declare (xargs :verify-guards nil))
  (let ((d (fn2-dc-entry fn kind world)))
    (cond ((null d) `(make-event (er soft 'fn2-dispatch-frame "The attachment ~x0 of ~x1 has no KIDS contract." ',fn ',who)))
          ((set-difference-equal (car d) e)
           (mv-let (seen writers) (fn2-dc-writers (list fn) kind world e nil nil 64)
             (declare (ignore seen))
             `(make-event
               (er soft 'fn2-dispatch-frame
                   "The attachment ~x0 of ~x1 changes the children ~x2 outside its frame ~x3; the contracts that change them: ~x4."
                   ',fn ',who ',(set-difference-equal (car d) e) ',e ',writers))))
          (t '(value-triple :within-frame)))))
;; FN's KIDS at exactly E (the constrained function's claim), from its footprint.
(defun fn2-dc-frame-kids (fn pos formals e kind suffix world)
  (declare (xargs :verify-guards nil))
  (let ((d (fn2-dc-entry fn kind world)) (out `(mv-nth ,pos (,fn ,@formals))))
    `(defthm ,(fn2-columns-sym fn suffix)
       (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',e fn2-arm-free))
                (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,out))
       :hints (("Goal" :in-theory (union-theories '(,(cdr d)) (theory 'fn2-arm-frame-base)))))))

;; ---------------------------------------------------------------------------
;; THE DIRECTORY: every id's kind and slot, and the directory's rows, stay
;; (FN2-MACHINES-DIRECTORY-KEEPS of the directory child), chained like the
;; frame contracts: FN-CTF-DIR for each function a visit reaches, by its KIDS
;; (or arm ROW-FRAME) contract when its children exclude the directory, else
;; by one opening with its callees' and the directory writers'
;; -KEEPS-DIRECTORY facts. The relation and its basis are emitted once, where
;; first used (fn2-ctf-dir-basis-events), after the frame basis.
(defun fn2-ctf-dir-update-events (children k m)
  (declare (xargs :verify-guards nil))
  (cond ((atom children) nil)
        ((equal k m) (fn2-ctf-dir-update-events (cdr children) (+ 1 k) m))
        (t (let ((update (fn2-columns-pre "UPDATE-" (caar children))))
             (list* `(defthm ,(fn2-columns-pre "FN2-CTF-DIR-OF-" update)
                       (equal (fn2-ctf-dir (,update v c) c0) (fn2-ctf-dir c c0))
                       :hints (("Goal" :in-theory (enable fn2-ctf-dir ,update))))
                    ;; the directory read through another child's update (a
                    ;; body writing a table before the directory)
                    `(defthm ,(fn2-columns-pre "FN2-CTF-MACHINES-OF-" update)
                       (equal (fn2-core-machines (,update v c)) (fn2-core-machines c))
                       :hints (("Goal" :in-theory (enable fn2-core-machines ,update))))
                    (fn2-ctf-dir-update-events (cdr children) (+ 1 k) m))))))
(defun fn2-ctf-dir-update-runes (children k m)
  (declare (xargs :verify-guards nil))
  (cond ((atom children) nil)
        ((equal k m) (fn2-ctf-dir-update-runes (cdr children) (+ 1 k) m))
        (t (list* (fn2-columns-pre "FN2-CTF-DIR-OF-" (fn2-columns-pre "UPDATE-" (caar children)))
                  (fn2-columns-pre "FN2-CTF-MACHINES-OF-" (fn2-columns-pre "UPDATE-" (caar children)))
                  (fn2-ctf-dir-update-runes (cdr children) (+ 1 k) m)))))
(defun fn2-ctf-dir-basis-events (world)
  (declare (xargs :verify-guards nil))
  (let ((m (fn2-arm-frame-m world)) (children (fn2-arm-frame-children-of world)))
    (append
     (and (not (fn2-arm-frame-known 'fn2-core-stop nil world)) (fn2-arm-frame-basis-events world))
     `((defun fn2-ctf-dir (b a)
         (declare (xargs :verify-guards nil))
         (fn2-machines-directory-keeps (nth ,m b) (nth ,m a)))
       (defthm fn2-ctf-dir-refl (fn2-ctf-dir a a)
         :hints (("Goal" :in-theory (enable fn2-machines-directory-keeps))))
       (defthm fn2-ctf-dir-of-nth
         (implies (and (equal (nth ,m b) (nth ,m x)) (fn2-ctf-dir x a)) (fn2-ctf-dir b a))
         :rule-classes nil)
       (defthm fn2-ctf-dir-trans
         (implies (and (fn2-ctf-dir c b) (fn2-ctf-dir b a)) (fn2-ctf-dir c a))
         :rule-classes nil
         :hints (("Goal" :in-theory (enable fn2-machines-directory-keeps))))
       (defthm fn2-ctf-dir-of-update-fn2-core-machines
         (implies (and (fn2-machines-directory-keeps x (fn2-core-machines c)) (fn2-ctf-dir c c0))
                  (fn2-ctf-dir (update-fn2-core-machines x c) c0))
         :hints (("Goal" :in-theory (enable fn2-machines-directory-keeps fn2-core-machines update-fn2-core-machines))))
       (defthm fn2-ctf-dir-readers
         ; what the directory keeps: every id's kind, slot and membership
         (implies (fn2-ctf-dir b a)
                  (and (equal (fn2-machine-kind id b) (fn2-machine-kind id a))
                       (equal (fn2-machine-slot id b) (fn2-machine-slot id a))
                       (equal (fn2-machine-idp id b) (fn2-machine-idp id a))))
         :rule-classes nil
         :hints (("Goal" :in-theory (enable fn2-machines-directory-keeps fn2-machine-kind fn2-machine-kind-read-code
                                            fn2-machine-slot fn2-machine-slot-read-code fn2-machine-idp
                                            fn2-machines-kind fn2-machines-slot fn2-machines-rows fn2-core-machines))))
       (in-theory (disable fn2-ctf-dir))
       ,@(fn2-ctf-dir-update-events children 0 m)
       (deftheory fn2-ctf-dir-base
         (union-theories '(fn2-ctf-dir-refl fn2-ctf-dir-of-update-fn2-core-machines
                           ,@(fn2-ctf-dir-update-runes children 0 m))
                         (theory 'fn2-arm-frame-base)))))))
(defun fn2-ctf-dir-basis-form (world)
  (declare (xargs :verify-guards nil))
  (if (function-symbolp 'fn2-ctf-dir world) '(value-triple :known) (cons 'progn (fn2-ctf-dir-basis-events world))))
(defun fn2-ctf-dir-name (fn) (declare (xargs :verify-guards nil)) (fn2-columns-sym fn "-CTF-DIR"))
;; The functions under FNS that return the core, callees first.
(defun fn2-ctf-postorder (fns world seen fuel)
  (declare (xargs :verify-guards nil :measure (make-ord 1 (+ 1 (nfix fuel)) (acl2-count fns))))
  (cond ((or (zp fuel) (atom fns)) seen)
        ((or (member-eq (car fns) seen) (not (fn2-arm-frame-corep-fn (car fns) world)))
         (fn2-ctf-postorder (cdr fns) world seen fuel))
        (t (fn2-ctf-postorder (cdr fns) world
             (append (fn2-ctf-postorder (fn2-arm-frame-body-callees (car fns) world) world seen (1- fuel))
                     (list (car fns)))
             fuel))))
(defun fn2-ctf-postorder-new (fns world)
  (declare (xargs :verify-guards nil))
  (let ((all (fn2-ctf-postorder fns world nil 64)))
    (remove-duplicates-eq (reverse (remove-duplicates-eq (reverse all))))))
(defun fn2-ctf-dir-callee-runes (callees world)
  (declare (xargs :verify-guards nil))
  (cond ((atom callees) nil)
        ((getpropc (fn2-ctf-dir-name (car callees)) 'theorem nil world)
         (cons (fn2-ctf-dir-name (car callees)) (fn2-ctf-dir-callee-runes (cdr callees) world)))
        (t (fn2-ctf-dir-callee-runes (cdr callees) world))))
(defun fn2-ctf-dir-event (fn kind world)
  (declare (xargs :verify-guards nil))
  (let* ((e (fn2-arm-frame-known fn kind world))
         (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (m (fn2-arm-frame-m world))
         (name (fn2-ctf-dir-name fn))
         (stmt `(implies (fn2-ctf-dir fn2-core fn2-ctf-c0) (fn2-ctf-dir ,out fn2-ctf-c0)))
         (d (fn2-dc-entry fn kind world)))
    (cond
     ((or (eq (car e) :child) (getpropc name 'theorem nil world)) nil)
     ((and (eq (car e) :arm) (not (member m (cadr e))))
      (let ((tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world)))
        `((defthm ,name ,stmt
            :hints (("Goal" :in-theory (union-theories '(fn2-arm-row-frame) (theory 'fn2-arm-frame-base))
                     :use ((:instance ,(fn2-arm-frame-name fn "-ARM-ROW-FRAME") (fn2-arm-tb ,tk) (fn2-arm-row (fn2-machine-slot id fn2-core))
                                      (fn2-arm-cs ',(caddr e)) (fn2-arm-ch ',(cadr e)) (fn2-arm-c0 fn2-core))
                           (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',(cons tk (cadr e))) (a fn2-core) (b ,out))
                           (:instance fn2-ctf-dir-of-nth (b ,out) (x fn2-core) (a fn2-ctf-c0)))))))))
     ((and (member-eq (car e) '(:op :row :write)) (not (member m (fn2-arm-frame-entry-kids e world))))
      (let ((s (fn2-arm-frame-entry-kids e world)))
        `((defthm ,name ,stmt
            :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                     :use ((:instance ,(fn2-arm-frame-lemma fn e "-ARM-KIDS" kind world) (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                           (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',s) (a fn2-core) (b ,out))
                           (:instance fn2-ctf-dir-of-nth (b ,out) (x fn2-core) (a fn2-ctf-c0)))))))))
     ((and d (not (member m (car d))))
      ; a KIDS contract off the directory (a footprint's, above)
      `((defthm ,name ,stmt
          :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                   :use ((:instance ,(cdr d) (fn2-arm-free ',(car d)) (fn2-arm-c0 fn2-core))
                         (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',(car d)) (a fn2-core) (b ,out))
                         (:instance fn2-ctf-dir-of-nth (b ,out) (x fn2-core) (a fn2-ctf-c0))))))))
     (t
      `((defthm ,name ,stmt
          :hints (("Goal" :in-theory (union-theories
                                      '(,fn fn2-machines-directory-keeps-refl
                                        ,@(strip-cdrs (table-alist 'fn2-arm-frame-directory-keeps world))
                                        ,@(strip-cdrs (table-alist 'fn2-machines-directory-any world))
                                        ,@(fn2-ctf-dir-callee-runes (fn2-arm-frame-body-callees fn world) world))
                                      (theory 'fn2-ctf-dir-base))
                   :do-not-induct t))))))))
(defun fn2-ctf-dir-forms (fns kind)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (cons `(make-event (value (cons 'progn (fn2-ctf-dir-event ',(car fns) ',kind (w state)))))
          (fn2-ctf-dir-forms (cdr fns) kind))))

;; ---------------------------------------------------------------------------
;; THE WAIT SOURCES (defwait): per registered wait kind, its ready/grant pair
;; constrained with the liveness and shape facts and the grant's frame: the
;; core changes only in the children its :tables declare (and control, for a
;; stop), and the directory keeps every id's kind, slot and rows (a grant
;; clears its row's wait). Attached to defaults that grant nothing; the owner
;; attaches its own pair after fn2-wait-attach-events proves its grant's
;; footprint within the declaration (fn2-machine-access-events materializes
;; them; machines-a-access).
(defun fn2-machine-wait-children (kind world)
  (declare (xargs :verify-guards nil))
  (fn2-arm-frame-indices (append (fn2-cost-tables (fn2-machine-wait-get kind :tables world) world) '(fn2-core-control)) world))
(defun fn2-machine-wait-source-events (waits world)
  (declare (xargs :verify-guards nil))
  (if (atom waits) nil
    (let* ((r (fn2-machine-wait-get (car waits) :ready world)) (g (fn2-machine-wait-get (car waits) :grant world))
           (s (fn2-machine-wait-children (car waits) world)) (m (fn2-arm-frame-m world))
           (dir-hints '(("Goal" :in-theory (enable fn2-machines-directory-keeps-refl)))))
      (list*
       `(encapsulate
         (((,r fn2-core) => * :formals (fn2-core) :guard (fn2-core-wfp fn2-core))
          ((,g fn2-core) => (mv * fn2-core) :formals (fn2-core) :guard (fn2-core-wfp fn2-core)))
         (local (defun ,r (fn2-core)
                  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)) (ignore fn2-core)) nil))
         (local (defun ,g (fn2-core)
                  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core))) (mv *fn2-none* fn2-core)))
         (defthm ,(fn2-columns-sym g "-TYPE")
           (and (consp (,g fn2-core)) (true-listp (,g fn2-core)))
           :rule-classes :type-prescription)
         ;; Liveness: a ready source grants a row, so the grant service never
         ;; sees a ready source forever (an attachment proves this of its pair).
         (defthm ,(fn2-columns-sym g "-LIVE")
           (implies (,r fn2-core) (not (equal (mv-nth 0 (,g fn2-core)) *fn2-none*))))
         (defthm ,(fn2-columns-sym g "-SHAPE")
           (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                    (and (fn2-corep (mv-nth 1 (,g fn2-core))) (fn2-core-wfp (mv-nth 1 (,g fn2-core))))))
         ;; the frame: only the declared children change
         (defthm ,(fn2-columns-sym g "-ARM-KIDS")
           (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',s fn2-arm-free))
                    (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 (mv-nth 1 (,g fn2-core)))))
         ;; the directory keeps every id's kind, slot and rows
         (defthm ,(fn2-columns-sym g "-KEEPS-DIRECTORY")
           (fn2-machines-directory-keeps (nth ,m (mv-nth 1 (,g fn2-core))) (nth ,m fn2-core))
           :hints ,dir-hints))
       `(defun ,(fn2-columns-sym r "-DEFAULT") (fn2-core)
          (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)) (ignore fn2-core)) nil)
       `(defun ,(fn2-columns-sym g "-DEFAULT") (fn2-core)
          (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core))) (mv *fn2-none* fn2-core))
       `(defattach (,r ,(fn2-columns-sym r "-DEFAULT")) (,g ,(fn2-columns-sym g "-DEFAULT")) :hints ,dir-hints)
       `(in-theory (disable ,(fn2-columns-sym g "-ARM-KIDS") ,(fn2-columns-sym g "-KEEPS-DIRECTORY")))
       (fn2-machine-wait-source-events (cdr waits) world)))))
;; The grants' derived contracts (row frame; a constrained hook's, as
;; fn2-arm-frame-op-events) and FN-CTF-DIR from the directory constraint,
;; once the frame and directory bases are in the world (assembly-dispatch).
(defun fn2-machine-wait-frame-events (waits world)
  (declare (xargs :verify-guards nil))
  (if (atom waits) nil
    (let ((g (fn2-machine-wait-get (car waits) :grant world)))
      (append
       (and (not (fn2-arm-frame-known g nil world))
            (fn2-arm-frame-op-events g (fn2-machine-wait-children (car waits) world) nil world))
       `((defthm ,(fn2-ctf-dir-name g)
           (implies (fn2-ctf-dir fn2-core fn2-ctf-c0) (fn2-ctf-dir (mv-nth 1 (,g fn2-core)) fn2-ctf-c0))
           :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir) (theory 'minimal-theory))
                    :use ((:instance ,(fn2-columns-sym g "-KEEPS-DIRECTORY"))
                          (:instance fn2-ctf-dir-trans (c (mv-nth 1 (,g fn2-core))) (b fn2-core) (a fn2-ctf-c0))))))
         (in-theory (disable ,(fn2-ctf-dir-name g))))
       (fn2-machine-wait-frame-events (cdr waits) world)))))
;; Before an owner's defattach of KIND's grant to FN: FN's footprint within
;; the declared children (else refused, naming the children and their
;; writers), its directory contract, and the two constraint facts the
;; defattach uses (FN-WAIT-KIDS, FN-WAIT-DIRECTORY).
(defun fn2-wait-attach-events (kind fn world)
  (declare (xargs :verify-guards nil))
  (let ((s (fn2-machine-wait-children kind world)) (m (fn2-arm-frame-m world)))
    `((make-event (value (fn2-ctf-dir-basis-form (w state))))
      (make-event (value (cons 'progn (fn2-dc-forms (fn2-dc-todo '(,fn) nil (w state) nil 64) nil))))
      (make-event (value (fn2-dc-frame-check ',(fn2-machine-wait-get kind :grant world) ',fn nil ',s (w state))))
      (make-event (value (cons 'progn (fn2-ctf-dir-forms (fn2-ctf-postorder-new '(,fn) (w state)) nil))))
      (make-event (value (fn2-dc-frame-kids ',fn 1 '(fn2-core) ',s nil "-WAIT-KIDS" (w state))))
      (defthm ,(fn2-columns-sym fn "-WAIT-DIRECTORY")
        (fn2-machines-directory-keeps (nth ,m (mv-nth 1 (,fn fn2-core))) (nth ,m fn2-core))
        :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps-refl) (theory 'minimal-theory))
                 :use ((:instance ,(fn2-ctf-dir-name fn) (fn2-ctf-c0 fn2-core))))))
      (make-event (fn2-dc-disable-form (fn2-ctf-postorder-new '(,fn) (w state)) nil (w state)))
      (in-theory (disable ,(fn2-columns-sym fn "-WAIT-KIDS") ,(fn2-columns-sym fn "-WAIT-DIRECTORY"))))))
(defmacro fn2-wait-attach (kind fn)
  `(make-event (value (cons 'progn (fn2-wait-attach-events ',kind ',fn (w state))))))

(defun fn2-arm-frame-phase-openings (fns next kind world)
  ; a callee whose phase values reach beyond NEXT out of context (a subarm
  ; entered from several phases) is opened in the arm's phase proof, with
  ; its own callees' phase contracts
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (let ((rec (fn2-arm-frame-phase-record (car fns) kind world)))
      (append (and rec (not (subsetp-equal (cdr rec) next))
                   (cons (car fns) (fn2-arm-frame-lemmas (fn2-arm-frame-body-callees (car fns) world) '("-ARM-PHASE") kind world)))
              (fn2-arm-frame-phase-openings (cdr fns) next kind world)))))
;; An arm's (or handler's) chained contracts and its FRAME, at its declared
;; sets: CH children, J columns (the phase among them), NEXT successor codes.
(defun fn2-arm-frame-arm-events (kind fn fn2-arm-ch j next pre frame-form observep world)
  (declare (xargs :verify-guards nil))
  (let* ((formals (formals fn world))
         (call (cons fn formals))
         (out (fn2-arm-frame-out-term fn call world))
         (tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world))
         (callees (fn2-arm-frame-body-callees fn world))
         (frame (fn2-arm-frame-name fn "-ARM-ROW-FRAME"))
         (phase (fn2-arm-frame-name fn "-ARM-PHASE")))
    `((defthm ,frame
        (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core) ,@(fn2-arm-frame-row-frame-hyps tk fn2-arm-ch j 'id))
                 (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 ,out))
        :hints ,(fn2-arm-frame-hints (cons fn (append (fn2-arm-frame-inline-runes fn kind world)
                                                      (fn2-arm-frame-lemmas callees '("-ARM-ROW-FRAME" "-ARM-SLOT") kind world)))))
      (defthm ,phase
        ; under the arm's precondition PRE: its entry phase decides its paths
        (implies (and ,pre (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (subsetp-equal ',next fn2-arm-pset))
                 (member-equal (fn2-machine-phase id ,out) fn2-arm-pset))
        :hints ,(fn2-arm-frame-hints (list* fn 'fn2-arm-member-of-subsetp-free (fn2-columns-sym kind "-ARM-ROW-PHASE")
                                            (append (fn2-arm-frame-inline-phase-runes fn kind world)
                                                    (fn2-arm-frame-lemmas callees '("-ARM-PHASE") kind world)
                                                    (fn2-arm-frame-phase-openings callees next kind world)))))
      (table fn2-arm-frame-fns ',fn '(:arm ,fn2-arm-ch ,j ,next))
      ,(append frame-form
               `(:rule-classes nil :hints ,(fn2-arm-frame-hints
                          (list frame phase (fn2-columns-sym kind "-ARM-FRAMEP") 'fn2-arm-row-frame-refl
                                (fn2-columns-sym kind (if observep "-OBSERVE-NEXT-OK-P" "-ARM-NEXT-OK-P"))
                                (fn2-columns-sym fn "-PRESERVES-TYPE") (fn2-columns-sym fn "-PRESERVES-WFP"))))))))
(defun fn2-arm-frame-static-problem (fns fn2-arm-ch j tk kind world)
  ; a callee without contracts, or one that changes beyond the arm's
  ; declared sets, named; an arm's own inline put of its row is the callee
  ; (:row TK () COLUMNS) (its setters' columns)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (let* ((e (fn2-arm-frame-known (car fns) kind world))
           (etk (fn2-arm-frame-entry-tk e world))
           (rowp (and etk (equal etk tk) (not (member tk fn2-arm-ch))))
           (s (if rowp (fn2-arm-frame-entry-s e) (fn2-arm-frame-entry-kids e world))))
      (cond ((or (null e) (member-eq (car e) '(:failed :arm))) (list :callee (car fns) e))
            ((and rowp (not (subsetp-equal (fn2-arm-frame-entry-j e) j)))
             (list :columns (car fns) (set-difference-equal (fn2-arm-frame-entry-j e) j)))
            ((not (subsetp-equal s fn2-arm-ch))
             (list :children (car fns) (set-difference-equal s fn2-arm-ch)))
            (t (fn2-arm-frame-static-problem (cdr fns) fn2-arm-ch j tk kind world))))))
(defun fn2-arm-frame-phase-problem (fns kind world)
  ; a callee without a phase contract (and not a subarm opened in the arm's
  ; phase proof whose own callees have theirs): the arm's phase proof is not
  ; attempted
  (declare (xargs :verify-guards nil))
  (cond ((atom fns) nil)
        ((fn2-arm-frame-all-have (list (car fns)) "-ARM-PHASE" kind world)
         (fn2-arm-frame-phase-problem (cdr fns) kind world))
        ((and (fn2-arm-frame-phase-record (car fns) kind world)
              (fn2-arm-frame-all-have (fn2-arm-frame-body-callees (car fns) world) "-ARM-PHASE" kind world))
         (fn2-arm-frame-phase-problem (cdr fns) kind world))
        (t (list :phase (car fns)))))
(defun fn2-arm-frame-slot-problem (fns kind world)
  ; a callee that may move the directory's slots: the row-level writes after
  ; it are not at the arm's row (not attempted)
  (declare (xargs :verify-guards nil))
  (cond ((atom fns) nil)
        ((fn2-arm-frame-all-have (list (car fns)) "-ARM-SLOT" kind world) (fn2-arm-frame-slot-problem (cdr fns) kind world))
        (t (list :slot (car fns)))))
(defun fn2-arm-frame-arm-final (kind fn fn2-arm-ch j next pre frame-form owed-form observep world)
  ; the FRAME proved; else the row stays owed, named in table
  ; fn2-arm-frame-owed with its reason: a callee without contracts or
  ; beyond the arm's declared sets (checked first), or :proof
  (declare (xargs :verify-guards nil))
  (let* ((tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world))
         (inline (fn2-arm-frame-body-setters fn kind world))
         (callees (fn2-arm-frame-body-callees fn world))
         (problem (cond ((and inline (not (member tk fn2-arm-ch)) (not (subsetp-equal inline j)))
                         (list :columns (fn2-columns-pre "UPDATE-" (fn2-columns-sym kind "-TABLE"))
                               (set-difference-equal inline j)))
                        (t (or (fn2-arm-frame-static-problem (if (and inline (member-eq 'id (formals fn world)))
                                                                 (remove-eq (fn2-columns-pre "UPDATE-" (fn2-columns-sym kind "-TABLE")) callees)
                                                               callees)
                                                             fn2-arm-ch j tk kind world)
                               (fn2-arm-frame-phase-problem callees kind world)
                               (fn2-arm-frame-slot-problem callees kind world))))))
    (if problem
        `(progn ,owed-form (table fn2-arm-frame-owed ',(cadr frame-form) ',problem))
      `(:or (progn ,@(fn2-arm-frame-arm-events kind fn fn2-arm-ch j next pre frame-form observep world))
            (progn ,owed-form (table fn2-arm-frame-owed ',(cadr frame-form) '(:proof ,fn)))))))
(defun fn2-arm-frame-arm-form (kind fn fn2-arm-ch j next pre frame-form owed-form observep world)
  ; the basis and kind facts once, each callee's contracts (callees first),
  ; then the arm's FRAME
  (declare (xargs :verify-guards nil))
  `(progn
     ,@(and (not (fn2-arm-frame-known 'fn2-core-stop nil world)) (fn2-arm-frame-basis-events world))
     ,@(and (not (assoc-eq kind (table-alist 'fn2-arm-frame-kinds world))) (fn2-arm-frame-kind-events kind world))
     ,@(fn2-arm-frame-fns-forms (fn2-arm-frame-todo (fn2-arm-frame-body-callees fn world) kind world nil 64) kind)
     (make-event (fn2-arm-frame-arm-final ',kind ',fn ',fn2-arm-ch ',j ',next ',pre ',frame-form ',owed-form ',observep (w state)))
     ; the contracts proved here, disabled by one theory event (each proof
     ; above names its own theory; an in-theory event per contract cost a
     ; theory computation each: 470 of them took 29 s in assembly-callbacks)
     (make-event (fn2-arm-frame-disable-form
                  ',(cons fn (fn2-arm-frame-todo (fn2-arm-frame-body-callees fn world) kind world nil 64)) ',kind (w state)))))
;; A handler's ROW-FRAME (the chained row-frame contract an arm's FRAME is
;; proved from, without the phase part): at its declared children CH and
;; columns J, after its callees' contracts; a callee without contracts or
;; beyond the declaration, or a failed proof, leaves it owed in table
;; fn2-arm-frame-owed under the ROW-FRAME's name.
;;
;; A child-form handler's face (machine-arms fn2-arms-wrapper-events) binds
;; its children, calls FN-CHILDREN and writes back what it returns, its own
;; table whole: the ROW-FRAME then follows from FN-CHILDREN's two child
;; contracts, each its body opened once in the minimal theory: -ARM-CHILD-COLS
;; (its table changes at row SLOT only, in the declared columns J: the row
;; setters' FN2-ARM-COLS-OF- rules, every column's setter enabled, so a write
;; beyond J fails the proof) and -ARM-CHILD-KEEPS (each returned child outside
;; CH is the one it was given). A write-back of an equal child keeps the frame.
(defthm fn2-arm-row-frame-update-equal
  (implies (and (fn2-arm-row-frame table row columns children a b) (natp k) (natp table) (equal (nth k b) v))
           (fn2-arm-row-frame table row columns children a (update-nth k v b)))
  :hints (("Goal" :in-theory (e/d (fn2-arm-row-frame) (fn2-arm-kids fn2-arm-cols subsetp-equal nth update-nth))
           :cases ((equal k table)))
          ("Subgoal 1" :in-theory (e/d (fn2-arm-row-frame) (fn2-arm-kids fn2-arm-cols subsetp-equal)))))
(in-theory (disable fn2-arm-row-frame-update-equal))
(defun fn2-arm-frame-child-stobj-index (s children k)
  ; the core child index of the child stobj S
  (declare (xargs :verify-guards nil))
  (cond ((atom children) nil) ((eq (cadar children) s) k)
        (t (fn2-arm-frame-child-stobj-index s (cdr children) (+ 1 k)))))
(defun fn2-arm-frame-child-keeps-terms (outs pos call kind ch children)
  (declare (xargs :verify-guards nil))
  (cond ((atom outs) nil)
        ((or (eq (car outs) kind) (member (fn2-arm-frame-child-stobj-index (car outs) children 0) ch))
         (fn2-arm-frame-child-keeps-terms (cdr outs) (+ 1 pos) call kind ch children))
        (t (cons `(equal (mv-nth ,pos ,call) ,(car outs))
                 (fn2-arm-frame-child-keeps-terms (cdr outs) (+ 1 pos) call kind ch children)))))
(defun fn2-arm-frame-child-face-runes (stobjs children)
  ; the face's core readers and updaters of the children it binds
  (declare (xargs :verify-guards nil))
  (cond ((atom children) nil)
        ((member-eq (cadar children) stobjs)
         (list* (caar children) (fn2-columns-pre "UPDATE-" (caar children))
                (fn2-arm-frame-child-face-runes stobjs (cdr children))))
        (t (fn2-arm-frame-child-face-runes stobjs (cdr children)))))
(defun fn2-arm-frame-member-hyps (j)
  (declare (xargs :verify-guards nil))
  (if (atom j) nil (cons `(member-equal ,(car j) fn2-arm-cs) (fn2-arm-frame-member-hyps (cdr j)))))
(defun fn2-arm-frame-child-handler-events (kind fn ch j world)
  ; nil when FN is not a child-form face
  (declare (xargs :verify-guards nil))
  (let* ((child (fn2-columns-sym fn "-CHILDREN"))
         (sig (and (function-symbolp child world) (cdr (assoc-eq child (table-alist 'fn2-arms-child-sigs world)))))
         (ins (car sig)) (outs (cadr sig)) (k (caddr sig))
         (children (fn2-arm-frame-children-of world))
         (tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world))
         (call (and sig (cons child (formals child world))))
         (minimal '(union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))
         (cols-name (fn2-columns-sym child "-ARM-CHILD-COLS"))
         (keeps-name (fn2-columns-sym child "-ARM-CHILD-KEEPS"))
         (keeps (fn2-arm-frame-child-keeps-terms outs k call kind ch children))
         (colsp (and (member-eq kind outs) (not (member tk ch))))
         (frame (fn2-arm-frame-name fn "-ARM-ROW-FRAME")))
    (and sig
      (append
       (and colsp
            `((defthm ,cols-name
                (implies (and (fn2-arm-cols 0 slot fn2-arm-cs fn2-arm-t0 ,kind) ,@(fn2-arm-frame-member-hyps j))
                         (fn2-arm-cols 0 slot fn2-arm-cs fn2-arm-t0 (mv-nth ,(+ k (position-eq kind outs)) ,call)))
                :hints (("Goal" :in-theory (union-theories '(,child mv-nth car-cons cdr-cons
                                                             ,@(fn2-arm-frame-setter-runes kind (strip-cars (fn2-machine-property kind :table world))))
                                                           ,minimal))))))
       (and keeps
            `((defthm ,keeps-name (and ,@keeps)
                :hints (("Goal" :in-theory (union-theories '(,child mv-nth car-cons cdr-cons) ,minimal))))))
       `((defthm ,frame
           (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                         ,@(fn2-arm-frame-row-frame-hyps tk ch j 'id))
                    (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0
                                       ,(fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
           :hints (("Goal" :in-theory (union-theories
                                       '(,fn ,@(and colsp (list cols-name)) ,@(and keeps (list keeps-name))
                                         ,@(fn2-arm-frame-lemmas (fn2-arm-frame-body-callees fn world)
                                                                 '("-ARM-ROW-FRAME" "-ARM-SLOT") kind world)
                                         ,@(fn2-arm-frame-child-face-runes (union-eq ins outs) children)
                                         nth-update-nth fn2-machine-slot fn2-machine-slot-read-code fn2-machine-idp
                                         fn2-arm-row-frame-table fn2-arm-row-frame-child fn2-arm-row-frame-update-equal
                                         fn2-arm-row-frame-cols)
                                       (theory 'fn2-arm-frame-base))
                    :do-not-induct t)))
         (in-theory (disable ,frame ,@(and colsp (list cols-name)) ,@(and keeps (list keeps-name))))
         (table fn2-arm-frame-fns ',fn '(:arm ,ch ,j nil)))))))
(defun fn2-arm-frame-handler-final (kind fn ch j world)
  (declare (xargs :verify-guards nil))
  (let* ((tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world))
         (frame (fn2-arm-frame-name fn "-ARM-ROW-FRAME"))
         (inline (fn2-arm-frame-body-setters fn kind world))
         (callees (fn2-arm-frame-body-callees fn world))
         (problem (cond ((and inline (not (member tk ch)) (not (subsetp-equal inline j)))
                         (list :columns (fn2-columns-pre "UPDATE-" (fn2-columns-sym kind "-TABLE"))
                               (set-difference-equal inline j)))
                        (t (or (fn2-arm-frame-static-problem (if (and inline (member-eq 'id (formals fn world)))
                                                                 (remove-eq (fn2-columns-pre "UPDATE-" (fn2-columns-sym kind "-TABLE")) callees)
                                                               callees)
                                                             ch j tk kind world)
                               (fn2-arm-frame-slot-problem callees kind world)))))
         (face (fn2-arm-frame-child-handler-events kind fn ch j world)))
    (cond ((getpropc frame 'theorem nil world) '(value-triple :known))
          ;; a child-form face writes its table whole: its frame is its child's
          ((and face (eq (car problem) :children)
                (eq (cadr problem) (fn2-columns-pre "UPDATE-" (fn2-columns-sym kind "-TABLE"))))
           `(:or (progn ,@face) (table fn2-arm-frame-owed ',frame '(:proof ,fn))))
          (problem `(table fn2-arm-frame-owed ',frame ',problem))
          (t `(:or (progn
                     (defthm ,frame
                       (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                                     ,@(fn2-arm-frame-row-frame-hyps tk ch j 'id))
                                (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0
                                                   ,(fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
                       :hints ,(fn2-arm-frame-hints (cons fn (append (fn2-arm-frame-inline-runes fn kind world)
                                                                    (fn2-arm-frame-lemmas callees '("-ARM-ROW-FRAME" "-ARM-SLOT") kind world)))))
                     (in-theory (disable ,frame))
                     (table fn2-arm-frame-fns ',fn '(:arm ,ch ,j nil)))
                   (table fn2-arm-frame-owed ',frame '(:proof ,fn)))))))
(defun fn2-arm-frame-handler-form (kind fn ch j world)
  (declare (xargs :verify-guards nil))
  (let ((todo (fn2-arm-frame-todo (fn2-arm-frame-body-callees fn world) kind world nil 64)))
    `(progn
       ,@(and (not (fn2-arm-frame-known 'fn2-core-stop nil world)) (fn2-arm-frame-basis-events world))
       ,@(and (not (assoc-eq kind (table-alist 'fn2-arm-frame-kinds world))) (fn2-arm-frame-kind-events kind world))
       ,@(fn2-arm-frame-fns-forms todo kind)
       (make-event (fn2-arm-frame-handler-final ',kind ',fn ',ch ',j (w state)))
       (make-event (fn2-arm-frame-disable-form ',todo ',kind (w state))))))
(defun fn2-machine-arm-rows (name arms world)
  (declare (xargs :verify-guards nil))
  (if (atom arms) nil
    (let* ((tag (caar arms)) (fn (cadar arms)) (c (cddar arms))
           (phase (fn2-columns-pre "*" (fn2-columns-sym (fn2-columns-col-name (fn2-columns-sym name "-STATE") tag) "*")))
           (cols (fn2-machine-property name :table world))
           (table (fn2-machine-child-index (fn2-columns-sym name "-TABLE") world))
           (columns (fn2-machine-column-indices (cons 'phase (fn2-arm-get :writes c)) cols))
           (children (fn2-machine-child-indices (append (fn2-arm-get :tables c) (fn2-machine-directory-child (fn2-arm-get :writes c)) *fn2-arm-implicit-tables*) world))
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
       ; checked against :writes and :tables. Every other arm's FRAME is proved
       ; from its chained contracts (fn2-arm-frame-arm-form); a FRAME whose
       ; proof fails stays owed and is named in table fn2-arm-frame-owed.
       (and (not (eq (fn2-arm-get :language c) :unchecked))
        (let* ((formula `(implies ,(fn2-machine-arm-pre name phase)
                                  (let ((after (mv-nth 4 ,(fn2-machine-arm-call name fn '(id budget) nil world))))
                                    (and (or (not (equal (fn2-core-stop-reason after) *fn2-stop-reason-none*))
                                             (,next ,phase (fn2-machine-phase id after)))
                                         (fn2-arm-framep ,table (fn2-machine-slot id fn2-core) ',columns ',children
                                                         fn2-core after)))))
               (owed `(defthm-owed ,(fn2-columns-sym stem "-FRAME") (id budget fn2-core) ,formula
                        :schema :invariant :from (:machine ,name)
                        :teeth (,(fn2-columns-sym name "-ARM-NEXT-POSITIVE") ,(fn2-columns-sym name "-ARM-NEXT-NEGATIVE")
                                fn2-arm-frame-positive fn2-arm-frame-negative)
                        :doc ,(concatenate 'string "Arm " (symbol-name tag) " of " (symbol-name name)
                                           " changes only its declared fields and children and moves only to a declared phase."))))
          (list `(make-event
                  (value (fn2-arm-frame-arm-form ',name ',fn ',children ',columns
                                                 ',(fn2-machine-phase-indices (fn2-arm-get :next c)
                                                                              (fn2-machine-property name :states world))
                                                 ',(fn2-machine-arm-pre name phase)
                                                 '(defthm ,(fn2-columns-sym stem "-FRAME") ,formula) ',owed nil (w state)))))))
       (fn2-machine-arm-rows name (cdr arms) world)))))
(defun fn2-machine-observe-rows (name observes world)
  (declare (xargs :verify-guards nil))
  (if (atom observes) nil
    (let* ((tag (caar observes)) (fn (cadar observes)) (c (cddar observes))
           (cols (fn2-machine-property name :table world))
           (table (fn2-machine-child-index (fn2-columns-sym name "-TABLE") world))
           (columns (fn2-machine-column-indices (cons 'phase (fn2-arm-get :writes c)) cols))
           (children (fn2-machine-child-indices (append (fn2-arm-get :tables c) (fn2-machine-directory-child (fn2-arm-get :writes c)) *fn2-arm-implicit-tables*) world))
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
                             " changes only its declared fields and children and moves only to a declared phase."))
       ;; its row frame, independent of the phases it moves to: proved from
       ;; its callees' contracts, else owed and named (fn2-arm-frame-handler-form)
       `(make-event (value (fn2-arm-frame-handler-form ',name ',fn ',children ',columns (w state))))))
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
                     ,(if (fn2-machine-directory-fieldp (caar columns))
                          ; P1: a directory field is the directory's column at the id.
                          `(stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
                             (value) (if (and (natp id) (< id (fn2-machines-rows fn2-machines)))
                                         (,(fn2-columns-col-name 'fn2-machines (caar columns)) id fn2-machines) 0)
                             value)
                        `(let ((slot (fn2-machine-slot id fn2-core)))
                           (stobj-let ((,name (,(fn2-columns-sym name "-TABLE") fn2-core)))
                             (value) (,(fn2-columns-col-name name (caar columns)) slot ,name) value)))
                   (prog2$ (hard-error ',reader "Invalid internal row read." nil) 0))) nil nil)
             `(defthm ,(fn2-columns-sym reader "-WIDTH")
                (implies ,hyps (unsigned-byte-p ,(fn2-columns-width (cadar columns)) ,value))
                :rule-classes (:rewrite
                  (:type-prescription :corollary (implies ,hyps (natp ,value)))
                  (:linear :corollary (implies ,hyps (< ,value ,(expt 2 (fn2-columns-width (cadar columns))))))
                  (:rewrite :corollary (implies ,hyps (and (rationalp ,value) (acl2-numberp ,value)))))
                :hints (("Goal" :in-theory (enable ,reader)
                         ,@(and (fn2-machine-directory-fieldp (caar columns))
                                `(:use ((:instance ,(fn2-columns-sym (fn2-columns-col-name 'fn2-machines (caar columns)) "-NATP")
                                         (i id) (fn2-machines (fn2-core-machines fn2-core)))
                                        (:instance ,(fn2-columns-sym (fn2-columns-col-name 'fn2-machines (caar columns)) "-BOUND")
                                         (i id) (fn2-machines (fn2-core-machines fn2-core)))))))))
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
; Row readers by layer (assembly-rows-*): a section book materializes the
; readers of its own layer's kinds only, so its cost does not grow with the
; kinds other layers add. :other is every kind outside :a, :b and :c.
(defun fn2-machine-names-in-layer (names layer world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((l (fn2-machine-property (car names) :layer world)))
      (if (if (eq layer :other) (not (member-eq l '(:a :b :c))) (eq l layer))
          (cons (car names) (fn2-machine-names-in-layer (cdr names) layer world))
        (fn2-machine-names-in-layer (cdr names) layer world)))))
;; :other-1 and :other-2 split :other's kinds where their columns halve
;; (D26: one section book of :other's row readers took 88 s, 562 events).
(defun fn2-machine-columns-count (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) 0
    (+ (len (fn2-machine-property (car names) :columns world))
       (fn2-machine-columns-count (cdr names) world))))
(defun fn2-machine-names-upto (names budget world)
  ;; the leading kinds of NAMES whose columns stay within BUDGET (at least one)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((n (len (fn2-machine-property (car names) :columns world))))
      (if (< (nfix budget) n) nil
        (cons (car names) (fn2-machine-names-upto (cdr names) (- (nfix budget) n) world))))))
(defun fn2-machine-other-part (names part world)
  (declare (xargs :verify-guards nil))
  (let* ((other (fn2-machine-names-in-layer names :other world))
         (first (or (fn2-machine-names-upto other (floor (fn2-machine-columns-count other world) 2) world)
                    (take 1 other))))
    (if (eql part 1) first (nthcdr (len first) other))))
(defun fn2-machine-names-in-layers (names layers world)
  (declare (xargs :verify-guards nil))
  (if (atom layers) nil
    (append (case (car layers)
              (:other-1 (fn2-machine-other-part names 1 world))
              (:other-2 (fn2-machine-other-part names 2 world))
              (otherwise (fn2-machine-names-in-layer names (car layers) world)))
            (fn2-machine-names-in-layers names (cdr layers) world))))
(defmacro fn2-machine-row-events (&rest layers)
  ; No LAYERS: every kind (a test instance in one book).
  `(make-event
    (value (cons 'progn
                 (fn2-machine-all-snapshots
                  ,(if layers
                       `(fn2-machine-names-in-layers (fn2-machine-names (w state)) ',layers (w state))
                     '(fn2-machine-names (w state)))
                  (w state))))))
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
(defun fn2-machine-observe-handler-events (router name world)
  (declare (xargs :verify-guards nil))
  (let ((handler (fn2-columns-col-name router name)))
    `((defun ,handler (id event outcome reason count aux0 aux1 fn2-core)
        (declare (xargs :stobjs fn2-core
                        :guard (and (fn2-core-wfp fn2-core)
                                    (case event ,@(fn2-machine-observe-event-guards
                                                   (fn2-machine-property name :observes world)) (otherwise nil))))
                 ;; a kind with no handler (A-S7's taken kinds may observe nothing) reads no payload
                 (ignorable outcome reason count aux0 aux1))
        ,@(fn2-callback-checked-body `((let ((row-phase (,(fn2-machine-row-reader name 'phase) id fn2-core)))
          (mv-let (wake fn2-core)
            (case event
              ,@(fn2-machine-observe-event-arms (fn2-machine-property name :observes world) nil
                 (list name world))
              (otherwise (fn2-machine-refuse-observation fn2-core)))
            (fn2-machine-observe-contract-check
             (,(fn2-columns-sym name "-OBSERVE-OK-P") id event row-phase fn2-core)
             wake fn2-core)))) name 1))
      (fn2-core-preserves ,handler (id event outcome reason count aux0 aux1 fn2-core) :position 1 :rows nil))))
(defun fn2-machine-run-event (name world)
  (declare (xargs :verify-guards nil))
  (let* ((run (fn2-columns-sym name "-RUN"))
         (leafp (assoc-eq name (table-alist 'fn2-machine-arm-bodies world)))
         ;; the genesis arm (G3) is checked as an arm from the row's initial phase
         (problem (fn2-arm-problems ""
                    (append (fn2-machine-arms-problem name (fn2-machine-property name :continuations world) nil world)
                            (fn2-machine-arms-problem name (fn2-machine-property name :observes world) t world)
                            (fn2-machine-arms-problem name (fn2-machine-property name :genesis-arm world) nil world)))))
    (if problem `(make-event (er soft 'defmachine-run "~@0" ',problem))
    `(progn
       ,@(fn2-machine-path-report-events name (fn2-machine-arm-path-report
                                               name (append (fn2-machine-property name :continuations world)
                                                            (fn2-machine-property name :genesis-arm world))
                                               world))
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
       ,@(and leafp (fn2-machine-observe-handler-events 'fn2-machine-observe name world))
       ,@(fn2-machine-teeth-events name world)
       ,@(fn2-machine-arm-rows name (fn2-machine-property name :continuations world) world)
       ,@(and leafp (fn2-machine-observe-rows name (fn2-machine-property name :observes world) world))
       ))))
(defmacro defmachine-run (name)
  `(make-event (value (fn2-machine-run-event ',name (w state)))))
(defun fn2-machine-observe-handlers (router names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let ((name (car names)))
      (append
       (and (function-symbolp (fn2-columns-sym name "-RUN") world)
            (fn2-machine-observe-handler-events router name world))
       (fn2-machine-observe-handlers router (cdr names) world)))))
; The handlers' owed rows, once for the served router (machine-dispatch).
(defun fn2-machine-all-observe-rows (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (append (and (function-symbolp (fn2-columns-sym (car names) "-RUN") world)
                 (fn2-machine-observe-rows (car names) (fn2-machine-property (car names) :observes world) world))
            (fn2-machine-all-observe-rows (cdr names) world))))
;; MACHINE-FORM 6.5 P4: the router is a case over kinds of one route per
;; kind. A kind's route makes the router's checks with the kind's own row
;; readers (no case over kinds), calls its handler, consumes the terminal and
;; reads the row's wait and stop state, so each proof is bounded by its kind.
(defun fn2-machine-route-read (name field)
  (declare (xargs :verify-guards nil))
  (list (fn2-machine-row-reader name field) 'id 'fn2-core))
(defun fn2-machine-route-readers (name fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (fn2-machine-row-reader name (car fields)) (fn2-machine-route-readers name (cdr fields)))))
(defun fn2-machine-observe-route-events (router names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names))
           (cols (fn2-machine-property name :columns world))
           (runp (function-symbolp (fn2-columns-sym name "-RUN") world))
           (handler (if runp
                        (fn2-columns-col-name router name)
                      ;; the kind's attachable stub is one per kind (fn2-machine-stub-events),
                      ;; named under fn2-machine-observe whichever router routes to it
                      (fn2-columns-col-name 'fn2-machine-observe (fn2-columns-sym name "-STUB"))))
           (route (fn2-columns-col-name (fn2-columns-sym router "-ROUTE") name))
           (snap `(eq (,(fn2-columns-sym name "-SNAPSHOT-READ-CODE") id fn2-core) :ok))
           ;; the generic terminal (a closed operation with its own facts)
           (terminal '(fn2-machine-observe-terminal id fn2-core)))
      (cons
       `(progn
          (defun ,route (id gen event outcome reason count aux0 aux1 fn2-core)
            (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
            (if (not (and ,snap
                          (equal gen ,(fn2-machine-route-read name 'generation))
                          (,(fn2-columns-sym name "-OBSERVES-P") ,(fn2-machine-route-read name 'phase) event)))
                (fn2-machine-refuse-observation fn2-core)
              (mv-let (wake fn2-core)
                (,handler id event outcome reason count aux0 aux1 fn2-core)
                ; Consume every completion before generic bookkeeping. A handler
                ; may accumulate many in-flight results without an event cell.
                (let ((fn2-core (if (equal event *fn2-event-borrow-released*) fn2-core ,terminal)))
                  ,(if (not (assoc-eq 'stopped cols)) '(fn2-machine-refuse-observation fn2-core)
                     `(if (not ,snap)
                          (fn2-machine-refuse-observation fn2-core)
                        ;; a row parked on a resource (any D0 kind: an operation, a pool
                        ;; window, a partition's row) stays parked; its grant wakes it
                        (mv (if (or (not (or (equal ,(fn2-machine-route-read name 'wait-reason) *fn2-wait-none*)
                                             (equal ,(fn2-machine-route-read name 'wait-reason) *fn2-wait-completion*)))
                                    (equal ,(fn2-machine-route-read name 'stopped) 1)) *fn2-none* wake)
                            fn2-core)))))))
          (fn2-core-preserves ,route (id gen event outcome reason count aux0 aux1 fn2-core) :position 1 :rows nil
            :hints (("Goal" :in-theory (e/d (,route) (,@(and runp (list handler))
                                                      fn2-machine-observe-terminal
                                                      fn2-machine-refuse-observation
                                                      ,@(fn2-machine-route-readers name (if (assoc-eq 'stopped cols) '(phase generation wait-reason stopped) '(phase generation))))))))
          (in-theory (disable ,route)))
       (fn2-machine-observe-route-events router (cdr names) world)))))
(defun fn2-machine-observe-route-arms (names tag router)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons `(,tag (,(fn2-columns-col-name (fn2-columns-sym router "-ROUTE") (car names))
                  id gen event outcome reason count aux0 aux1 fn2-core))
          (fn2-machine-observe-route-arms (cdr names) (+ 1 (nfix tag)) router))))
(defun fn2-machine-observe-events (router names world)
  (declare (xargs :verify-guards nil))
  (let ((accepts (fn2-columns-sym router "-ACCEPTS-P")))
    (append (fn2-machine-observe-handlers router names world)
     (fn2-machine-observe-route-events router names world)
     `((defun ,accepts (kind phase event)
         (declare (xargs :guard t))
         (case kind ,@(fn2-machine-observe-kind-arms names 0 t router) (otherwise nil)))
       (defun ,router (okind id gen event outcome reason count aux0 aux1 fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (if (not (and (eq (fn2-machine-kind-read-code id fn2-core) :ok)
                       (equal okind (fn2-machine-kind id fn2-core))))
             (fn2-machine-refuse-observation fn2-core)
           (case okind ,@(fn2-machine-observe-route-arms names 0 router)
             (otherwise (fn2-machine-refuse-observation fn2-core)))))
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
; The kinds taken by a machine (A-S7), in declaration order.
(defun fn2-machine-taken-in (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (if (fn2-machine-property (car names) :taken world)
        (cons (car names) (fn2-machine-taken-in (cdr names) world))
      (fn2-machine-taken-in (cdr names) world))))
(defun fn2-machine-taken (world)
  (declare (xargs :verify-guards nil))
  (fn2-machine-taken-in (fn2-machine-names world) world))
; Every kind with a partition: the admitted kinds (ordinals 0..), then the
; taken kinds, sharing the directory's arrays.
(defun fn2-machine-partitioned (world)
  (declare (xargs :verify-guards nil))
  (append (fn2-machine-admitted world) (fn2-machine-taken world)))
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
(defun fn2-machine-spec-classes (specs)
  (declare (xargs :verify-guards nil))
  (if (atom specs) nil
    (cons (fn2-arm-get :class (cdar specs)) (fn2-machine-spec-classes (cdr specs)))))
(defun fn2-machine-class-tally (classes acc)
  (declare (xargs :verify-guards nil))
  (if (atom classes) acc
    (let ((hit (assoc (car classes) acc)))
      (fn2-machine-class-tally (cdr classes)
                               (put-assoc (car classes) (+ 1 (if hit (cdr hit) 0)) acc)))))
(defun fn2-machine-taken-class-cases (kinds n world)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (let* ((specs (fn2-machine-range-specs (fn2-arm-get :ranges (fn2-machine-property (car kinds) :taken world))))
           (classes (fn2-machine-class-tally (fn2-machine-spec-classes specs) nil)))
      (cons `(,n ',classes) (fn2-machine-taken-class-cases (cdr kinds) (+ 1 (nfix n)) world)))))
(defun fn2-machine-admission-index-events (kinds world)
  ; KINDS: the admitted kinds; the taken kinds follow them in the partition arrays.
  (declare (xargs :verify-guards nil))
  (let ((parts (append kinds (fn2-machine-taken world))))
  (if (> (len parts) *fn2-machine-admitted-max*)
      (er hard 'defmachine "At most ~x0 kinds may own a partition (admitted or taken): ~x1." *fn2-machine-admitted-max* parts)
    `((defconst *fn2-machine-admitted* ',kinds)
      (defconst *fn2-machine-partitioned* ',parts)
      ,@(fn2-machine-admission-ordinal-constants parts 0)
      (defun fn2-machine-admitted-capacity (ord profile)
        (declare (xargs :guard t) (ignorable profile))
        (case ord ,@(fn2-machine-admission-cases parts 0 world :capacity) (otherwise 0)))
      ; The pool rows a partition's take reserves, as ((CLASS . COUNT) ...): the
      ; grant service wakes a parked taker only when they are free (A-S7), so a
      ; pool shortage is a wait, never a re-park loop. Admitted kinds: none.
      (defun fn2-machine-partition-classes (ord)
        (declare (xargs :guard t) (ignorable ord))
        (case ord ,@(fn2-machine-taken-class-cases (fn2-machine-taken world) (len kinds) world) (otherwise nil)))
      (defun fn2-machine-admitted-base (ord profile)
        (declare (xargs :guard t) (ignorable profile))
        (case ord ,@(fn2-machine-admission-cases parts 0 world :base) (otherwise *fn2-none*)))
      ; A profile names the kind its listeners admit (:listener-targets);
      ; absent or unknown, the first admitted kind (echo in layer A).
      (defun fn2-machine-admission-ordinal-of (name)
        (declare (xargs :guard t))
        (case name ,@(fn2-machine-admission-cases kinds 0 world :ordinal) (otherwise 0)))))))
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

;; THE DISPATCH FRAME's children. The attached kinds' arms and operations
;; are declared in their implementations, after the dispatcher; what the
;; dispatcher knows is each kind's registry, whose :holds name the resources
;; its rows hold. The commit layer's durability children
;; (*FN2-DISPATCH-COMMIT-CHILDREN*) change only by B's operations, which a
;; non-commit kind reaches through a batch membership (fn2-commit-admit-txn
;; acquires it, fn2-commit-take releases it): a kind that holds no
;; :batch-membership has every other child in its frame and none of these.
(defconst *fn2-dispatch-commit-children*
  '(fn2-commit-table fn2-core-commit-io fn2-core-commit-root fn2-core-commit-members fn2-core-commit-settled))
(defun fn2-dispatch-holds-p (class holds)
  (declare (xargs :verify-guards nil))
  (and (consp holds) (or (member-eq class (cdar holds)) (fn2-dispatch-holds-p class (cdr holds)))))
(defun fn2-dispatch-frame-children (name world)
  (declare (xargs :verify-guards nil))
  (fn2-arm-frame-indices
   (if (fn2-dispatch-holds-p :batch-membership (fn2-machine-property name :holds world))
       (strip-cars (fn2-arm-frame-children-of world))
     (set-difference-eq (strip-cars (fn2-arm-frame-children-of world)) *fn2-dispatch-commit-children*))
   world))
(defun fn2-dc-nth-keeps (ks out)
  (declare (xargs :verify-guards nil))
  (if (atom ks) nil (cons `(equal (nth ,(car ks) ,out) (nth ,(car ks) fn2-core)) (fn2-dc-nth-keeps (cdr ks) out))))
;; The commit layer's durability children a function's KIDS contract (S,
;; LEMMA) leaves: FN-KEEPS-COMMIT, their values unchanged.
(defun fn2-dc-keeps-commit-uses (ks s out)
  (declare (xargs :verify-guards nil))
  (if (atom ks) nil
    (cons `(:instance fn2-arm-kids-nth (i 0) (k ,(car ks)) (free ',s) (a fn2-core) (b ,out))
          (fn2-dc-keeps-commit-uses (cdr ks) s out))))
(defun fn2-dc-keeps-commit-event (fn s lemma world)
  (declare (xargs :verify-guards nil))
  (let* ((out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (ks (set-difference-equal (fn2-arm-frame-indices *fn2-dispatch-commit-children* world) s)))
    (if (atom ks) '(value-triple :none)
      `(defthm ,(fn2-columns-sym fn "-KEEPS-COMMIT")
         (and ,@(fn2-dc-nth-keeps ks out))
         :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                  :use ((:instance ,lemma (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                        ,@(fn2-dc-keeps-commit-uses ks s out))))))))
(defun fn2-dc-keeps-commit-form (fn kind world)
  (declare (xargs :verify-guards nil))
  (let ((d (fn2-dc-entry fn kind world)))
    (if d (fn2-dc-keeps-commit-event fn (car d) (cdr d) world)
      (er hard 'fn2-dispatch-frame "~x0 has no KIDS contract." fn))))

;; A stub's frame claims for G (the stub in its constraint, or its default):
;; KIDS at the kind's frame children E, and CTF-DIR; G's body is BODY-FN's
;; call, whose -DC-KIDS (under no kind) and -CTF-DIR contracts prove them.
(defun fn2-dispatch-claims (g formals pos e body-fn)
  (declare (xargs :verify-guards nil))
  (let ((out `(mv-nth ,pos (,g ,@formals))))
    `((defthm ,(fn2-columns-sym g "-ARM-KIDS")
        (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',e fn2-arm-free))
                 (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,out))
        :hints (("Goal" :in-theory (union-theories '(,g ,(fn2-dc-name nil body-fn)) (theory 'fn2-arm-frame-base)))))
      (defthm ,(fn2-ctf-dir-name g)
        (implies (fn2-ctf-dir fn2-core fn2-ctf-c0) (fn2-ctf-dir ,out fn2-ctf-c0))
        :hints (("Goal" :in-theory (union-theories '(,g ,(fn2-ctf-dir-name body-fn)) (theory 'fn2-arm-frame-base))))))))
;; THE OBSERVE STUBS keep the operation table and the pool whole
;; (FN2-DISPATCH-OPS-POOL, a view of those two children): no kind's handler
;; writes either (the harvest that dispatches it already did), so every op
;; and pool row -- the commit layer's among them -- is the one it observed.
;; The claim is proved from a KIDS contract at children S without them.
(defun fn2-dispatch-ops-pool-children (world)
  (declare (xargs :verify-guards nil))
  (fn2-arm-frame-indices '(fn2-core-ops fn2-core-pool) world))
(defun fn2-dispatch-ops-pool-view-form (world)
  (declare (xargs :verify-guards nil))
  (if (function-symbolp 'fn2-dispatch-ops-pool world) '(value-triple :known)
    '(fn2-defview fn2-dispatch-ops-pool :carrier fn2-core :select ((fn2-ops :whole t) (fn2-pool :whole t)))))
(defun fn2-dispatch-ops-pool-uses (ks s out)
  (declare (xargs :verify-guards nil))
  (if (atom ks) nil
    (cons `(:instance fn2-arm-kids-nth (i 0) (k ,(car ks)) (free ',s) (a fn2-core) (b ,out))
          (fn2-dispatch-ops-pool-uses (cdr ks) s out))))
;; NAME: (fn2-dispatch-ops-pool OUT fn2-core), where OUT's function has the
;; KIDS contract LEMMA at S (ENABLE opens a stub's local body to it).
(defun fn2-dispatch-ops-pool-claim (name out body-out lemma s enable world)
  (declare (xargs :verify-guards nil))
  `(defthm ,name (fn2-dispatch-ops-pool ,out fn2-core)
     :hints (("Goal" :in-theory (union-theories '(fn2-dispatch-ops-pool ,@enable) (theory 'fn2-arm-frame-base))
              :do-not-induct t
              :use ((:instance ,lemma (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                    (:instance fn2-arm-kids-refl (i 0) (free ',s) (a fn2-core))
                    ,@(fn2-dispatch-ops-pool-uses (fn2-dispatch-ops-pool-children world) s body-out))))))
;; An observe attachment FN (kind KIND): its footprint off the ops and the
;; pool, else refused naming the contracts that write them; then its claim.
(defun fn2-dispatch-ops-pool-form (who fn kind e world)
  (declare (xargs :verify-guards nil))
  (let ((d (fn2-dc-entry fn kind world))
        (out `(mv-nth 1 (,fn ,@(formals fn world)))))
    (if (and d (intersectp-equal (car d) (fn2-dispatch-ops-pool-children world)))
        (fn2-dc-frame-check who fn kind (set-difference-equal e (fn2-dispatch-ops-pool-children world)) world)
      (if (null d) (fn2-dc-frame-check who fn kind e world)
        (fn2-dispatch-ops-pool-claim (fn2-columns-sym fn "-DISPATCH-OPS-POOL") out out (cdr d) (car d) nil world)))))
;; THE OBSERVE STUBS keep the commit layer's IO units (the commit-io child):
;; with the operation table whole, no take's or lent unit's incarnation
;; changes (FRESHNESS, LENT-OK: books/dispatch-fresh.lisp). From a KIDS
;; contract LEMMA at children S without it, else refused naming S.
(defun fn2-dispatch-units-claim (name out body-out lemma s enable world)
  (declare (xargs :verify-guards nil))
  (let ((k (fn2-arm-frame-child-index 'fn2-core-commit-io world)))
    (if (member-equal k s)
        `(make-event (er soft 'fn2-dispatch-frame "~x0: its KIDS contract may change the commit-io child (~x1)." ',name ',s))
      `(defthm ,name (equal (nth ,k ,out) (nth ,k fn2-core))
         :hints (("Goal" :in-theory (union-theories '(,@enable) (theory 'fn2-arm-frame-base))
                  :do-not-induct t
                  :use ((:instance ,lemma (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                        (:instance fn2-arm-kids-refl (i 0) (free ',s) (a fn2-core))
                        (:instance fn2-arm-kids-nth (i 0) (k ,k) (free ',s) (a fn2-core) (b ,body-out)))))))))
(defun fn2-dispatch-units-form (who fn kind world)
  ; an observe attachment FN of WHO: its claim from its KIDS contract
  (declare (xargs :verify-guards nil))
  (let ((d (fn2-dc-entry fn kind world))
        (out `(mv-nth 1 (,fn ,@(formals fn world)))))
    (if (null d) `(make-event (er soft 'fn2-dispatch-frame "~x0 (of ~x1) has no KIDS contract." ',fn ',who))
      (fn2-dispatch-units-claim (fn2-columns-sym fn "-KEEPS-UNITS") out out (cdr d) (car d) nil world))))
;; THE RUN STUBS' HELD FRAME (books/dispatch-held.lisp): the rows the commit
;; kind holds in the operation table and the pool -- every held operation
;; row's columns; every row's extent, every held pool row's columns and, the
;; extents ordered, the data length and its octets -- one observation
;; (FN2-DISPATCH-HELD, an equality view of the ops and the pool), kept by the
;; run of every kind that holds no :batch-membership and writes as a
;; constant owner kind (fn2-dispatch-held-kind-p): such a kind's writes are
;; its own rows'. The commit layer's batch members (txn, auth) write
;; commit-owned pool rows themselves (fn2-commit-txn-open's member put), so
;; they carry no held claim. Emitted once, where the observation's book and
;; the commit kind are present; the stubs' default body's chain with it.
(defun fn2-dispatch-held-p (world)
  (declare (xargs :verify-guards nil))
  (and (function-symbolp 'fn2-dh-ops-obs world) (getpropc '*fn2-commit-kind* 'const nil world)))
;; A kind whose writes name an owner kind its rows hold -- the cursor
;; writes its connection's reply as its row's conn-kind and a read scan as
;; the scan row's qk (copied from that conn-kind); the successor (txn, cns,
;; auth) writes an overlay arena as the overlay row's okind -- keeps the held
;; rows under the invariant that no stored owner is the commit kind
;; (FN2-DH-OWNERS-OK over the owner tables, books/dispatch-owners.lisp),
;; which its held claim assumes and
;; every stub keeps (-DISPATCH-OWNERS). The consumer (cns) holds a batch
;; membership (its :commit run admits a transaction member, reserving pools
;; as the commit kind), so it has no held claim, as txn and auth.
(defconst *fn2-dispatch-held-owner-read* '(fn2-cursor))
(defun fn2-dispatch-held-kind-p (name world)
  (declare (xargs :verify-guards nil))
  (and (fn2-dispatch-held-p world)
       (not (fn2-dispatch-holds-p :batch-membership (fn2-machine-property name :holds world)))))
(defun fn2-dispatch-owners-p (world)
  (declare (xargs :verify-guards nil))
  (and (fn2-dispatch-held-p world) (function-symbolp 'fn2-dh-owners-ok world)))
(defun fn2-dispatch-held-view-form (world)
  (declare (xargs :verify-guards nil))
  (cond ((not (fn2-dispatch-held-p world)) '(value-triple :none))
        ((function-symbolp 'fn2-dispatch-held world) '(value-triple :known))
        (t `(progn
              (defun-nx fn2-dh-obs (k fn2-core)
                (cons (fn2-dh-ops-obs k (fn2-core-ops fn2-core)) (fn2-dh-pool-obs k (fn2-core-pool fn2-core))))
              (defun-nx fn2-dispatch-held-obs (fn2-core) (fn2-dh-obs *fn2-commit-kind* fn2-core))
              (fn2-defview fn2-dispatch-held :carrier fn2-core :select ((fn2-ops :whole t) (fn2-pool :whole t))
                :observe fn2-dispatch-held-obs :open (fn2-dispatch-held-obs fn2-dh-obs fn2-core-ops fn2-core-pool))
              (in-theory (disable fn2-dh-obs fn2-dispatch-held-obs))
              (make-event (value (cons 'progn (fn2-dh-chain-forms (fn2-dh-postorder-new '(fn2-machine-refuse-phase) (w state)) nil))))
              ;; the default bodies keep the stored owners
              ,@(and (function-symbolp 'fn2-dh-owners-ok world)
                     '((make-event (value (fn2-dh-owners-claim-form nil 'fn2-machine-refuse-phase 4 nil (w state))))
                       (make-event (value (fn2-dh-owners-claim-form nil 'fn2-machine-refuse-observation 1 nil (w state))))))))))
(defun fn2-dispatch-held-claims (g formals name world)
  ; G's held claim (the stub in its constraint, or its default), from its body's chain
  (declare (xargs :verify-guards nil))
  (and (fn2-dispatch-held-kind-p name world)
       `((defthm ,(fn2-columns-sym g "-DISPATCH-HELD")
           ,(if (member-eq name *fn2-dispatch-held-owner-read*)
                `(implies (fn2-dh-owners-ok *fn2-commit-kind* fn2-core) (fn2-dispatch-held (mv-nth 4 (,g ,@formals)) fn2-core))
              `(fn2-dispatch-held (mv-nth 4 (,g ,@formals)) fn2-core))
           :hints (("Goal" :in-theory (union-theories '(,g fn2-dispatch-held fn2-dispatch-held-obs fn2-dh-obs (:e equal) (:e not)
                                                        fn2-dh-of-fn2-machine-refuse-phase)
                                                      (theory 'minimal-theory))))))))
;; Every stub (run at POS 4, observe at 1) keeps the stored owners avoiding
;; the commit kind (FN2-DH-OWNERS-OK), as its default body does.
(defun fn2-dispatch-owners-claims (g formals pos body-fn world)
  (declare (xargs :verify-guards nil))
  (and (fn2-dispatch-owners-p world)
       `((defthm ,(fn2-columns-sym g "-DISPATCH-OWNERS")
           (implies (fn2-dh-owners-ok *fn2-commit-kind* fn2-core)
                    (fn2-dh-owners-ok *fn2-commit-kind* (mv-nth ,pos (,g ,@formals))))
           :hints (("Goal" :in-theory (union-theories '(,g ,(fn2-columns-sym body-fn "-DISPATCH-OWNERS"))
                                                      (theory 'minimal-theory))))))))
(defun fn2-machine-stub-events (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names))
           (run (fn2-columns-sym name "-RUN")))
      (if (function-symbolp run world)
          (fn2-machine-stub-events (cdr names) world)
        (let* ((run-stub (fn2-columns-sym name "-RUN-STUB"))
               (run-def (fn2-columns-sym name "-RUN-DEFAULT"))
               (obs-stub (fn2-columns-col-name 'fn2-machine-observe (fn2-columns-sym name "-STUB")))
               (obs-def (fn2-columns-col-name 'fn2-machine-observe (fn2-columns-sym name "-DEFAULT")))
               (charge-stub (fn2-columns-sym name "-ARM-CHARGE-OK-P-STUB"))
               (charge-def (fn2-columns-sym name "-ARM-CHARGE-OK-P-DEFAULT"))
               (bound-stub (fn2-columns-sym name "-ARM-BOUND-STUB"))
               (bound-def (fn2-columns-sym name "-ARM-BOUND-DEFAULT"))
               (kconst (fn2-columns-pre "*" (fn2-columns-sym name "-KIND*")))
               (observes (fn2-machine-property name :observes world))
               (er (fn2-dispatch-frame-children name world))
               (eo er)
               (refuse (fn2-dc-entry 'fn2-machine-refuse-observation nil world))
               (refuse-lemma (cdr refuse)) (refuse-kids (car refuse))
               (run-formals '(id budget fn2-core))
               (obs-formals '(id event outcome reason count aux0 aux1 fn2-core))
               (run-guard `(and (fn2-core-wfp fn2-core)
                                (fn2-machine-idp id fn2-core)
                                (equal (fn2-machine-kind id fn2-core) ,kconst)))
               (obs-guard `(and (fn2-core-wfp fn2-core)
                                (case event ,@(fn2-machine-observe-event-guards observes) (otherwise nil)))))
          (append
           `((encapsulate
              (((,run-stub * * fn2-core) => (mv * * * * fn2-core)
                :formals ,run-formals :guard ,run-guard)
               ((,obs-stub * * * * * * * fn2-core) => (mv * fn2-core)
                :formals ,obs-formals :guard ,obs-guard)
               ((,charge-stub * * * *) => *
                :formals (phase bytes steps descriptors) :guard t)
               ((,bound-stub *) => *
                :formals (phase) :guard t))
              (local (defun ,run-stub (id budget fn2-core)
                       (declare (xargs :stobjs fn2-core :guard ,run-guard) (ignore budget))
                       (fn2-machine-refuse-phase id fn2-core)))
              (local (defun ,obs-stub (id event outcome reason count aux0 aux1 fn2-core)
                       (declare (xargs :stobjs fn2-core :guard ,obs-guard)
                                (ignore id event outcome reason count aux0 aux1))
                       (fn2-machine-refuse-observation fn2-core)))
              (local (defun ,charge-stub (phase bytes steps descriptors)
                       (declare (xargs :guard t) (ignore phase bytes steps descriptors))
                       nil))
              (local (defun ,bound-stub (phase)
                       (declare (xargs :guard t) (ignore phase))
                       0))
              (defthm ,(fn2-columns-sym run-stub "-CONSP")
                (and (consp (,run-stub id budget fn2-core))
                     (true-listp (,run-stub id budget fn2-core)))
                :rule-classes :type-prescription)
              (defthm ,(fn2-columns-sym obs-stub "-CONSP")
                (and (consp (,obs-stub id event outcome reason count aux0 aux1 fn2-core))
                     (true-listp (,obs-stub id event outcome reason count aux0 aux1 fn2-core)))
                :rule-classes :type-prescription)
              (fn2-core-preserves ,run-stub (id budget fn2-core) :position 4 :rows nil :disable nil)
              (fn2-core-preserves ,obs-stub (id event outcome reason count aux0 aux1 fn2-core) :position 1 :rows nil :disable nil)
              ;; the dispatch frame: only the kind's frame children change,
              ;; and the directory keeps every id's kind, slot and membership
              ,@(fn2-dispatch-claims run-stub run-formals 4 er 'fn2-machine-refuse-phase)
              ;; the run stub keeps the rows the commit kind holds
              ,@(fn2-dispatch-held-claims run-stub run-formals name world)
              ;; both stubs keep the stored owners
              ,@(fn2-dispatch-owners-claims run-stub run-formals 4 'fn2-machine-refuse-phase world)
              ,@(fn2-dispatch-owners-claims obs-stub obs-formals 1 'fn2-machine-refuse-observation world)
              ,@(fn2-dispatch-claims obs-stub obs-formals 1 eo 'fn2-machine-refuse-observation)
              ;; the observe stub keeps the operation table and the pool
              ,(fn2-dispatch-ops-pool-claim (fn2-columns-sym obs-stub "-OPS-POOL") `(mv-nth 1 (,obs-stub ,@obs-formals))
                                            '(mv-nth 1 (fn2-machine-refuse-observation fn2-core)) refuse-lemma refuse-kids
                                            (list obs-stub) world)
              ;; and the commit layer's IO units
              ,(fn2-dispatch-units-claim (fn2-columns-sym obs-stub "-KEEPS-UNITS") `(mv-nth 1 (,obs-stub ,@obs-formals))
                                         '(mv-nth 1 (fn2-machine-refuse-observation fn2-core)) refuse-lemma refuse-kids
                                         (list obs-stub) world))
             ;; the stubs' derived contracts (row frame, slot, phase), as a
             ;; constrained hook's (machines.lisp fn2-arm-frame-op-events)
              (make-event (value (cons 'progn (fn2-arm-frame-op-events ',run-stub ',er nil (w state)))))
             (make-event (value (cons 'progn (fn2-arm-frame-op-events ',obs-stub ',eo nil (w state)))))
             (make-event (value (fn2-dc-keeps-commit-form ',run-stub nil (w state))))
             (make-event (value (fn2-dc-keeps-commit-form ',obs-stub nil (w state))))
             (in-theory (disable ,(fn2-ctf-dir-name run-stub) ,(fn2-ctf-dir-name obs-stub)))
             (defun ,run-def (id budget fn2-core)
               (declare (xargs :stobjs fn2-core :guard ,run-guard) (ignore budget))
               (fn2-machine-refuse-phase id fn2-core))
             (fn2-core-preserves ,run-def (id budget fn2-core) :position 4 :rows nil)
             (defun ,obs-def (id event outcome reason count aux0 aux1 fn2-core)
               (declare (xargs :stobjs fn2-core :guard ,obs-guard)
                        (ignore id event outcome reason count aux0 aux1))
               (fn2-machine-refuse-observation fn2-core))
             (fn2-core-preserves ,obs-def (id event outcome reason count aux0 aux1 fn2-core) :position 1 :rows nil)
             ,@(fn2-dispatch-claims run-def run-formals 4 er 'fn2-machine-refuse-phase)
             ,@(fn2-dispatch-held-claims run-def run-formals name world)
             ,@(fn2-dispatch-owners-claims run-def run-formals 4 'fn2-machine-refuse-phase world)
             ,@(fn2-dispatch-owners-claims obs-def obs-formals 1 'fn2-machine-refuse-observation world)
             ,@(fn2-dispatch-claims obs-def obs-formals 1 eo 'fn2-machine-refuse-observation)
             ,(fn2-dispatch-ops-pool-claim (fn2-columns-sym obs-def "-OPS-POOL") `(mv-nth 1 (,obs-def ,@obs-formals))
                                           '(mv-nth 1 (fn2-machine-refuse-observation fn2-core)) refuse-lemma refuse-kids
                                           (list obs-def) world)
             ,(fn2-dispatch-units-claim (fn2-columns-sym obs-def "-KEEPS-UNITS") `(mv-nth 1 (,obs-def ,@obs-formals))
                                        '(mv-nth 1 (fn2-machine-refuse-observation fn2-core)) refuse-lemma refuse-kids
                                        (list obs-def) world)
             (defun ,charge-def (phase bytes steps descriptors)
               (declare (xargs :guard t) (ignore phase bytes steps descriptors))
               nil)
             (defun ,bound-def (phase)
               (declare (xargs :guard t) (ignore phase))
               0)
             (defattach (,run-stub ,run-def)
                        (,obs-stub ,obs-def)
                        (,charge-stub ,charge-def)
                        (,bound-stub ,bound-def))
             (in-theory (disable ,(fn2-columns-sym run-def "-ARM-KIDS") ,(fn2-ctf-dir-name run-def)
                                 ,(fn2-columns-sym obs-def "-ARM-KIDS") ,(fn2-ctf-dir-name obs-def)
                                 ,(fn2-columns-sym obs-def "-OPS-POOL") ,(fn2-columns-sym obs-def "-KEEPS-UNITS"))))
           (fn2-machine-stub-events (cdr names) world)))))))

;; The stubs and their frames, after the default bodies' contracts and the
;; directory relation: one generator for every dispatch (assembly-dispatch,
;; machine-dispatch).
(defun fn2-machine-stub-all-forms ()
  (declare (xargs :verify-guards nil))
  '((make-event (value (fn2-ctf-dir-basis-form (w state))))
    (make-event
     (value (cons 'progn (append (fn2-dc-forms (fn2-dc-todo '(fn2-machine-refuse-phase fn2-machine-refuse-observation fn2-machine-idle)
                                                            nil (w state) nil 64) nil)
                                 (fn2-ctf-dir-forms (fn2-ctf-postorder-new '(fn2-machine-refuse-phase fn2-machine-refuse-observation
                                                                             fn2-machine-idle) (w state)) nil)))))
    (make-event (value (fn2-dc-keeps-commit-form 'fn2-machine-refuse-phase nil (w state))))
    (make-event (value (fn2-dc-keeps-commit-form 'fn2-machine-refuse-observation nil (w state))))
    (make-event (value (fn2-dc-keeps-commit-form 'fn2-machine-idle nil (w state))))
    (make-event (value (fn2-dispatch-ops-pool-view-form (w state))))
    (make-event (value (fn2-dispatch-held-view-form (w state))))
    (make-event (value (cons 'progn (fn2-machine-stub-events (fn2-machine-names (w state)) (w state)))))))
(defmacro fn2-machine-stub-all-events ()
  (cons 'progn (fn2-machine-stub-all-forms)))

(defun fn2-machine-run-arms (names tag world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((run (fn2-columns-sym (car names) "-RUN"))
           (fn (if (function-symbolp run world) run (fn2-columns-sym (car names) "-RUN-STUB"))))
      (cons `(,tag (,fn id budget fn2-core))
            (fn2-machine-run-arms (cdr names) (+ 1 (nfix tag)) world)))))
(defun fn2-machine-arm-certificate-arms (names tag boundp world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((runp (function-symbolp (fn2-columns-sym (car names) "-RUN") world))
           (bound (fn2-columns-sym (car names) (if runp "-ARM-BOUND" "-ARM-BOUND-STUB")))
           (charge (fn2-columns-sym (car names) (if runp "-ARM-CHARGE-OK-P" "-ARM-CHARGE-OK-P-STUB"))))
      (cons (if boundp `(,tag (,bound phase))
              `(,tag (,charge phase bytes steps descriptors)))
            (fn2-machine-arm-certificate-arms (cdr names) (+ 1 (nfix tag)) boundp world)))))
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
; A directory field's dispatcher reads and writes the directory's column at
; the id: no case over kinds.
(defun fn2-machine-directory-field-events (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((field (caar fields)) (kind (cadar fields))
           (get (fn2-columns-col-name 'fn2-machine field))
           (put (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "SET-" field)))
           (write (fn2-columns-col-name 'fn2-machine (fn2-columns-pre "WRITE-" field)))
           (column (fn2-columns-col-name 'fn2-machines field))
           (setter (fn2-columns-col-name 'fn2-machines (fn2-columns-pre "SET-" field)))
           (width (fn2-columns-width kind))
           (valid `(and (unsigned-byte-p ,width value) (fn2-machine-idp id fn2-core)
                        ,(fn2-columns-fit kind 'value))))
      (append
       `((in-theory (disable ,column))
         ,@(fn2-machine-checked-reader-events get '(id)
             '(if (fn2-machine-idp id fn2-core) :ok :bounds)
             `(stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
                (answer) (,column id fn2-machines) answer))
         (defthm ,(fn2-columns-sym get "-NATP")
           (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (natp (,get id fn2-core)))
           :rule-classes :type-prescription
           :hints (("Goal" :use ((:instance ,(fn2-columns-sym column "-NATP")
                                  (i id) (fn2-machines (fn2-core-machines fn2-core)))))))
         (defthm ,(fn2-columns-sym get "-BOUND")
           (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                    (< (,get id fn2-core) ,(expt 2 width)))
           :rule-classes :linear
           :hints (("Goal" :use ((:instance ,(fn2-columns-sym column "-BOUND")
                                  (i id) (fn2-machines (fn2-core-machines fn2-core)))))))
         (defun ,put (id value fn2-core)
           (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) ,valid)))
           (if (not ,valid) fn2-core
             (stobj-let ((fn2-machines (fn2-core-machines fn2-core)))
               (fn2-machines)
               (if (and (natp id) (< id (fn2-machines-rows fn2-machines)))
                   (,setter id value fn2-machines) fn2-machines)
               fn2-core)))
         (defthm ,(fn2-columns-sym put "-TYPE")
           (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (fn2-corep (,put id value fn2-core))))
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
         (in-theory (disable ,write)))
       (fn2-machine-directory-field-events (cdr fields))))))
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
(defconst *fn2-machine-listener-offer*
  '(mode principal-slot account-ref peer-family peer-port peer-w0 peer-w1 peer-w2 peer-w3))
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
         (fn2-core-reserve ,(let ((c (fn2-arm-get :class (cdar specs))))
                              (if (natp c) c
                                (er hard 'defmachine "A (:bytes B) range class needs the kind's registry in child form (defmachine-registry): ~x0." kind)))
                           ,kind target gen fn2-core)
         (if (not (eq ,code :ok))
             ,(fn2-machine-range-releases n kind '(mv :pool fn2-core))
           ,(fn2-machine-range-reserves (cdr specs) (+ 1 (nfix n)) kind install))))))
(defun fn2-machine-zero-puts (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil (cons (list (car fields) 0) (fn2-machine-zero-puts (cdr fields)))))
(defun fn2-machine-copy-puts (fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil (cons (list (car fields) (car fields)) (fn2-machine-copy-puts (cdr fields)))))
; MACHINE-FORM 6.5 P4: a kind whose book declares its registry operations
; in child form (defmachine-registry, machine-arms.lisp) gets a core face of
; one stobj-let here; any other kind keeps the core body below.
(defun fn2-machine-registry-child (kind world)
  (declare (xargs :verify-guards nil))
  (let ((name (fn2-columns-sym (fn2-columns-sym (if (fn2-machine-property kind :admission world)
                                                    'fn2-machine-admit- 'fn2-machine-take-)
                                                (symbol-name kind)) "-CHILDREN")))
    (and (function-symbolp name world) name)))
(defun fn2-machine-registry-face (kind child args o kconst results)
  (declare (xargs :verify-guards nil))
  `(stobj-let ((,kind (,(fn2-columns-sym kind "-TABLE") fn2-core))
               (fn2-machines (fn2-core-machines fn2-core))
               (fn2-pool (fn2-core-pool fn2-core))
               (fn2-control (fn2-core-control fn2-core)))
     (,@results ,kind fn2-machines fn2-pool fn2-control)
     (,child ,@args ,o ,kconst ,kind fn2-machines fn2-pool fn2-control)
     (mv ,@results fn2-core)))
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
         ,(if (fn2-machine-registry-child kind world)
              (fn2-machine-registry-face kind (fn2-machine-registry-child kind world)
                                         `(index nonce ,@copies) o kconst '(code))
          `(let ((target (fn2-machine-free-head ,o fn2-core)))
           (if (or (equal target *fn2-none*)
                   (not (eq (fn2-machine-generation-read-code target fn2-core) :ok))
                   (not (eq (fn2-machine-next-free-read-code target fn2-core) :ok))
                   (>= (fn2-machine-active-count ,o fn2-core) (fn2-machine-connection-count ,o fn2-core)))
               (mv :no-row fn2-core)
             (let ((gen (fn2-machine-generation target fn2-core))
                   (next (fn2-machine-next-free target fn2-core)))
               ,(fn2-machine-range-reserves specs 0 kconst install)))))))
      (fn2-core-preserves ,admit (index nonce ,@copies fn2-core) :position 1 :rows nil :prefix "")
      (fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
       (defun ,reclaim (id retire fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         ;; The partition's reclaim (fn2-machines-reclaim, arm-children.lisp).
         (fn2-machine-reclaim id ,o retire fn2-core)))
      (fn2-core-preserves ,reclaim (id retire fn2-core) :rows nil :prefix "")
      (defcost ,admit :tables (fn2-core-machines fn2-core-pool ,(fn2-columns-sym kind "-TABLE"))
        :effects ((:transfer (:connection-row) :to ,kind)
                  (:acquire ,(strip-cars specs) :for ,kind))
        :target (,kind :free ,(fn2-arm-get :phase adm))
        :doc ,(concatenate 'string "Admit an accepted connection as a " (symbol-name kind) " row."))
      (defcost ,reclaim :tables (fn2-core-machines) :effects ((:release (:connection-row)))
        :doc ,(concatenate 'string "Return a drained " (symbol-name kind) " row to its partition.")))))
;; As fn2-machine-range-reserves, for a take: a refused reservation releases
;; what it reserved, parks the taker and answers :pool.
(defun fn2-machine-taken-reserves (specs n kind install park)
  (declare (xargs :verify-guards nil))
  (if (atom specs) install
    (let ((code (packn-pos (list 'code n) 'fn2-core)))
      `(mv-let (,code ,(packn-pos (list 'slot n) 'fn2-core) ,(packn-pos (list 'pgen n) 'fn2-core) fn2-core)
         (fn2-core-reserve ,(fn2-arm-get :class (cdar specs)) ,kind target gen fn2-core)
         (if (not (eq ,code :ok))
             ,(fn2-machine-range-releases n kind `(let ((fn2-core ,park)) (mv :pool *fn2-none* 0 fn2-core)))
           ,(fn2-machine-taken-reserves (cdr specs) (+ 1 (nfix n)) kind install park))))))
;; A taken kind K with ordinal O (A-S7): fn2-machine-take-K takes O's free
;; head and a credit, reserves K's ranges (all or none), installs the row in
;; its :taken phase with the taker's copies, and wakes it; when no row,
;; credit or range is free, WAITER (a machine id, or *fn2-none*) is parked on
;; O's FIFO with the row kind as its wait reason, and the grant service wakes
;; it once a credit returns. fn2-machine-reclaim-K returns the row and its
;; credit (as an admitted kind's reclaim does).
(defun fn2-machine-taken-kind-events (kind o world)
  (declare (xargs :verify-guards nil))
  (let* ((tk (fn2-machine-property kind :taken world))
         (specs (fn2-machine-range-specs (fn2-arm-get :ranges tk)))
         (copies (fn2-arm-get :copy tk))
         (rowkind (fn2-arm-get :rows tk))
         (reason (fn2-columns-pre "*" (fn2-columns-sym 'fn2-wait- (concatenate 'string (symbol-name rowkind) "*"))))
         (kconst (fn2-columns-pre "*" (fn2-columns-sym kind "-KIND*")))
         (phase (fn2-columns-pre "*" (fn2-columns-sym (fn2-columns-col-name (fn2-columns-sym kind "-STATE")
                                                                           (fn2-arm-get :phase tk)) "*")))
         (take (fn2-columns-sym 'fn2-machine-take- (symbol-name kind)))
         (reclaim (fn2-columns-sym 'fn2-machine-reclaim- (symbol-name kind)))
         (install
          `(let* ((fn2-core (fn2-machine-set-free-head ,o next fn2-core))
                  (fn2-core (fn2-machine-set-active-count ,o (+ 1 (fn2-machine-active-count ,o fn2-core)) fn2-core))
                  (fn2-core (fn2-machine-set-admission-credits ,o (- (fn2-machine-admission-credits ,o fn2-core) 1) fn2-core))
                  (fn2-core (,(fn2-columns-sym kind "-PUT-CORE") target
                             (phase ,phase)
                             ,@(fn2-machine-range-puts specs 0)
                             ,@(fn2-machine-copy-puts copies)
                             ,@(fn2-machine-zero-puts (fn2-arm-get :clear tk))
                             (wait-reason *fn2-wait-none*)))
                  (fn2-core (fn2-machine-set-wake-id target fn2-core)))
             (mv :ok target gen fn2-core)))
         ;; WAITER *fn2-none* parks nothing; any other waiter must be a
         ;; machine not queued on a resource (else the caller is wrong:
         ;; refused). A running row may still carry :completion from the
         ;; I/O it last waited on (the router wakes it and leaves the reason).
         (park `(cond ((equal waiter *fn2-none*) fn2-core)
                      ((and (fn2-machine-idp waiter fn2-core)
                            (eq (fn2-machine-wait-reason-read-code waiter fn2-core) :ok)
                            (or (equal (fn2-machine-wait-reason waiter fn2-core) *fn2-wait-none*)
                                (equal (fn2-machine-wait-reason waiter fn2-core) *fn2-wait-completion*)))
                       (let ((fn2-core (fn2-machine-park-admission waiter ,o fn2-core)))
                         (fn2-machine-write-wait-reason waiter ,reason fn2-core)))
                      (t (fn2-machine-refuse-write fn2-core)))))
    `((fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
       (defun ,take (waiter ,@copies fn2-core)
         (declare (xargs :stobjs fn2-core
                         :guard (and (fn2-core-wfp fn2-core) ,@(fn2-machine-copy-guards copies kind world))))
         ,(if (fn2-machine-registry-child kind world)
              (fn2-machine-registry-face kind (fn2-machine-registry-child kind world)
                                         `(waiter ,@copies) o kconst '(code target gen))
          `(let ((target (fn2-machine-free-head ,o fn2-core)))
           ;; a kind with no rows in the profile: no credit ever returns, so
           ;; the taker is never parked; :none, routed by the taker's own arm
           (if (zp (fn2-machine-connection-count ,o fn2-core)) (mv :none *fn2-none* 0 fn2-core)
           (if (or (equal target *fn2-none*)
                   (not (eq (fn2-machine-generation-read-code target fn2-core) :ok))
                   (not (eq (fn2-machine-next-free-read-code target fn2-core) :ok))
                   (zp (fn2-machine-admission-credits ,o fn2-core))
                   (>= (fn2-machine-active-count ,o fn2-core) (fn2-machine-connection-count ,o fn2-core)))
               (let ((fn2-core ,park)) (mv :no-row *fn2-none* 0 fn2-core))
             (let ((gen (fn2-machine-generation target fn2-core))
                   (next (fn2-machine-next-free target fn2-core)))
               ;; a kind taken with no ranges (fn2-txn) reserves nothing
               (declare (ignorable gen))
               ,(fn2-machine-taken-reserves specs 0 kconst install park))))))))
      (fn2-core-preserves ,take (waiter ,@copies fn2-core) :position 3 :rows nil :prefix "")
      ;; the taker's park as its own operation, for the arm language's
      ;; (:park :taken K) (D F2): a take whose waiter is *fn2-none* parks nothing
      (fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
       (defun ,(fn2-columns-sym 'fn2-machine-park-taken- (symbol-name kind)) (id fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         (stobj-let ((fn2-machines (fn2-core-machines fn2-core))
                     (fn2-control (fn2-core-control fn2-core)))
           (fn2-machines fn2-control)
           (fn2-machines-park-taken id ,o ,reason fn2-machines fn2-control)
           fn2-core)))
      (fn2-core-preserves ,(fn2-columns-sym 'fn2-machine-park-taken- (symbol-name kind)) (id fn2-core) :rows nil :prefix "")
      ;; its child form (MACHINE-FORM 6.5 P3): the same body over the two
      ;; children it touches, so a child-form arm may park on a taken kind
      (defun ,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN"))
        (id fn2-machines fn2-control)
        (declare (xargs :stobjs (fn2-machines fn2-control)
                        :guard (and (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
        (fn2-machines-park-taken id ,o ,reason fn2-machines fn2-control))
      (fn2-machines-preserves ,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN"))
        (id fn2-machines fn2-control)
        :carriers ((fn2-machines 0 :prefix "-MACHINES") (fn2-control 1 :prefix "-CONTROL")))
      (defthm ,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN-ROWS"))
        (and (equal (fn2-machines-rows (car (,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN"))
                                            id fn2-machines fn2-control)))
                    (fn2-machines-rows fn2-machines))
             (equal (nth *fn2-machines-rows* (car (,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN"))
                                                  id fn2-machines fn2-control)))
                    (nth *fn2-machines-rows* fn2-machines)))
        :hints (("Goal" :in-theory (enable ,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN"))))))
      (in-theory (disable ,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN"))))
      (defcost ,(fn2-columns-sym 'fn2-machine-park-taken- (symbol-name kind))
        :child ,(fn2-columns-sym 'fn2-machine-park-taken- (concatenate 'string (symbol-name kind) "-CHILDREN"))
        :own-writes (wait-reason ready-prev ready-next) :tables (fn2-core-machines)
        :doc ,(concatenate 'string "Park the row until a " (symbol-name kind) " row is free."))
      (fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
       (defun ,reclaim (id retire fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
         ;; The partition's reclaim (fn2-machines-reclaim, arm-children.lisp).
         (fn2-machine-reclaim id ,o retire fn2-core)))
      (fn2-core-preserves ,reclaim (id retire fn2-core) :rows nil :prefix "")
      ;; (mv code target target-generation fn2-core): :ok, :no-row, :pool, or
      ;; :none when the profile gives the kind no rows (never a park: every
      ;; take site routes :none in its own :case, checked at expansion)
      (defcost ,take :answers (:ok :no-row :pool :none) :must-route (:none)
        :tables (fn2-core-machines fn2-core-pool ,(fn2-columns-sym kind "-TABLE") fn2-core-machine-tables)
        :effects ((:acquire (,rowkind) :for ,kind)
                  ,@(and specs `((:acquire ,(remove-duplicates-eq (strip-cars specs)) :for ,kind))))
        :target (,kind :free ,(fn2-arm-get :phase tk))
        :doc ,(concatenate 'string "Take a " (symbol-name kind) " row and its ranges, or park the taker."))
      (defcost ,reclaim :tables (fn2-core-machines) :effects ((:release (,rowkind)))
        :doc ,(concatenate 'string "Return a drained " (symbol-name kind) " row to its partition.")))))
(defun fn2-machine-taken-all-events (kinds o world)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (append (fn2-machine-taken-kind-events (car kinds) o world)
            (fn2-machine-taken-all-events (cdr kinds) (+ 1 (nfix o)) world))))
(defun fn2-machine-take-names (kinds)
  (declare (xargs :verify-guards nil))
  (if (atom kinds) nil
    (cons (fn2-columns-sym 'fn2-machine-take- (symbol-name (car kinds))) (fn2-machine-take-names (cdr kinds)))))
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
       ,@(fn2-machine-taken-all-events (fn2-machine-taken world) (len kinds) world)
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
       (defcost fn2-machine-admit :answers t :tables (fn2-core-machines fn2-core-pool fn2-core-machine-tables)
         :effects ((:transfer (:connection-row) :to :admitted))
         :doc "Admit into the listener's target kind (dispatch on the admitted-kind ordinal).")
       (make-event
        (let ((problem (fn2-arm-target-problem ',(append (fn2-machine-admit-names kinds)
                                                          (fn2-machine-take-names (fn2-machine-taken world)))
                                               (w state))))
          (if problem (er soft 'fn2-machine-admission "~@0" problem)
            (value '(value-triple :admission-effects-checked)))))))))
(defmacro fn2-machine-admission-events ()
  '(make-event (value (fn2-machine-admission-events-form (w state)))))

; ----------------------------------------------------------------------
; One theorem per function, for any operation over children (the form
; seat's move for the arms, 82eb2bfc2, offered to every :child operation):
; the claims about a function's returned children (type, invariant, size;
; CLAIMS, written over the variable FN2-SHAPE-R for the result) are one
; predicate FN-SHAPE-OK of the result and the input children OBJS, opened
; only on an explicit result tuple, the leaves of the function's paths after
; the if-lifting splits them, so the proof walks the paths once rather than
; once per claim. The claims follow from it by its definition, as the
; theorem NAME, for callers that rewrite with them.
(defun fn2-shape-tuple-vars (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (append (fn2-shape-tuple-vars (- n 1)) (list (packn-pos (list 'fn2-shape-x (- n 1)) 'fn2-shape-x)))))
(defun fn2-shape-one-events (name fn args hyps claims objs enables disables world)
  (declare (xargs :verify-guards nil))
  (let* ((ok (fn2-columns-sym fn "-SHAPE-OK"))
         (n (len (getpropc fn 'stobjs-out nil world)))
         (tuple (cons 'list (fn2-shape-tuple-vars n)))
         (call (cons fn args)))
    `((defun-nx ,ok (fn2-shape-r ,@objs)
        (declare (xargs :verify-guards nil))
        (and ,@claims))
      (defthm ,(fn2-columns-sym ok "-OF-TUPLE")
        (equal (,ok ,tuple ,@objs) (and ,@(sublis (list (cons 'fn2-shape-r tuple)) claims)))
        :hints (("Goal" :in-theory (enable ,ok))))
      (defthm ,(fn2-columns-sym ok "-OPEN")
        (equal (,ok fn2-shape-r ,@objs) (and ,@claims))
        :hints (("Goal" :in-theory (enable ,ok))))
      (in-theory (disable ,ok ,(fn2-columns-sym ok "-OPEN")))
      (defthm ,(fn2-columns-sym fn "-SHAPE-ONE")
        (implies (and ,@hyps) (,ok ,call ,@objs))
        ;; a leaf that is another operation's result (not a tuple) is opened
        ;; once nothing else simplifies, so its callee's claims carry it
        :hints (("Goal" :in-theory (e/d (,@enables ,(fn2-columns-sym ok "-OF-TUPLE"))
                                        (,ok (:executable-counterpart tau-system) ,@disables))
                 :do-not '(generalize fertilize eliminate-destructors))
                (and stable-under-simplificationp
                     '(:in-theory (e/d (,@enables ,(fn2-columns-sym ok "-OF-TUPLE") ,(fn2-columns-sym ok "-OPEN"))
                                       (,ok (:executable-counterpart tau-system) ,@disables))))))
      (defthm ,name
        (implies (and ,@hyps) (and ,@(sublis (list (cons 'fn2-shape-r call)) claims)))
        :hints (("Goal" :use ,(fn2-columns-sym fn "-SHAPE-ONE")
                 :in-theory (e/d (,(fn2-columns-sym ok "-OPEN")) (,fn ,(fn2-columns-sym fn "-SHAPE-ONE")))))))))
(defmacro fn2-shape-one (name fn args hyps claims objs enables disables)
  `(make-event (cons 'progn (fn2-shape-one-events ',name ',fn ',args ',hyps ',claims ',objs ',enables ',disables (w state)))))
