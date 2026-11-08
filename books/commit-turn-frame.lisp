; The commit kind's lifting lemma: what one transition of fn2-turn may change
; in the commit table, through fn2-transition's dispatch. A principal visit
; of a commit row runs the arm of the row's phase: the table changes only in
; that arm's declared columns, at the row's slot, and only that arm's declared
; children change besides the executor's own (its scheduler, control, trace
; and ledger children and the directory's wake handoff); the directory keeps
; every id's kind and slot. FN2-COMMIT-ARM-COLUMNS and -CHILDREN read the arms'
; declarations (table fn2-arm-frame-fns), so the statement is the declaration.
(in-package "ACL2")
(include-book "assembly-attach")
(include-book "executor-contracts")
(include-book "column-contracts")

;; The executor's glue between a visit and the arm, with contracts derived
;; under the commit kind (callees first).
(make-event
 (value (cons 'progn (fn2-arm-frame-fns-forms
                      (fn2-arm-frame-todo
                       '(fn2-exec-pop fn2-exec-visit fn2-exec-charge-run fn2-machine-take-wake fn2-exec-wake
                         fn2-exec-record fn2-machine-refuse-phase fn2-machine-idle fn2-machine-contract-check)
                       'fn2-commit (w state) nil 64)
                      'fn2-commit))))

;; The commit arms' declared columns and children, by phase code: the
;; (:arm CH J NEXT) entries the arms' FRAMEs were proved at.
(defun fn2-ctf-arm-decls (states code world)
  (declare (xargs :mode :program))
  (if (atom states) nil
    (let* ((fn (fn2-columns-sym (fn2-columns-col-name 'fn2-commit-run (car states)) ""))
           (e (cdr (assoc-eq fn (table-alist 'fn2-arm-frame-fns world)))))
      (if (not (eq (car e) :arm))
          (er hard 'fn2-ctf-arm-decls "The commit arm ~x0 has no proved frame: ~x1." fn e)
        (cons (list code (remove-duplicates-equal (cadr e)) (remove-duplicates-equal (caddr e)))
              (fn2-ctf-arm-decls (cdr states) (+ 1 code) world))))))
(make-event
 `(defconst *fn2-commit-arm-decls*
    ',(fn2-ctf-arm-decls (fn2-machine-property 'fn2-commit :states (w state)) 0 (w state))))
(defun fn2-commit-arm-children (phase)
  (declare (xargs :guard t))
  (cadr (assoc-equal phase *fn2-commit-arm-decls*)))
(defun fn2-commit-arm-columns (phase)
  (declare (xargs :guard t))
  (caddr (assoc-equal phase *fn2-commit-arm-decls*)))

;; A commit principal visit's arm, by its phase: the table frame at the
;; row's slot, chained as the arms' own contracts are.
(make-event
 (let* ((world (w state))
        (runes (fn2-arm-frame-lemmas (fn2-arm-frame-body-callees 'fn2-commit-run world) '("-ARM-ROW-FRAME") 'fn2-commit world))
        (n (len *fn2-commit-arm-decls*)))
   (value
    `(defthm fn2-commit-run-arm-row-frame
       (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                     (natp fn2-arm-tb)
                     (subsetp-equal (fn2-commit-arm-children (fn2-commit-row-phase id fn2-core)) fn2-arm-ch)
                     (member-equal ,(fn2-arm-frame-ctl world) fn2-arm-ch)
                     (or (member-equal ,(fn2-arm-frame-child-index 'fn2-commit-table world) fn2-arm-ch)
                         (and (equal fn2-arm-tb ,(fn2-arm-frame-child-index 'fn2-commit-table world))
                              (subsetp-equal (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core)) fn2-arm-cs)
                              (equal (fn2-machine-slot id fn2-core) fn2-arm-row))))
                (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0
                                   (mv-nth 4 (fn2-commit-run id budget fn2-core))))
       :hints (("Goal" :in-theory (union-theories '(fn2-commit-run (:e fn2-commit-arm-children) (:e fn2-commit-arm-columns) ,@runes)
                                                  (theory 'fn2-arm-frame-base))
                :do-not-induct t
                :cases ,(loop$ for i from 0 to (- n 1) collect `(equal (fn2-commit-row-phase id fn2-core) ,i))))))))

;; ---------------------------------------------------------------------------
;; THE DIRECTORY: every id's kind and slot, and the directory's rows, stay
;; (FN2-MACHINES-DIRECTORY-KEEPS of the directory child), chained like the
;; frame contracts: FN-CTF-DIR for each function a commit visit reaches, by
;; its KIDS (or arm ROW-FRAME) contract when its children exclude the
;; directory, else by one opening with its callees' and the directory
;; writers' -KEEPS-DIRECTORY facts.
(make-event
 (let ((m (fn2-arm-frame-m (w state))))
   (value
    `(progn
       (defun fn2-ctf-dir (b a)
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
       (in-theory (disable fn2-ctf-dir))))))
(defun fn2-ctf-dir-update-events (children k m)
  (declare (xargs :mode :program))
  (cond ((atom children) nil)
        ((equal k m) (fn2-ctf-dir-update-events (cdr children) (+ 1 k) m))
        (t (let ((update (fn2-columns-pre "UPDATE-" (caar children))))
             (cons `(defthm ,(fn2-columns-pre "FN2-CTF-DIR-OF-" update)
                      (equal (fn2-ctf-dir (,update v c) c0) (fn2-ctf-dir c c0))
                      :hints (("Goal" :in-theory (enable fn2-ctf-dir ,update))))
                   (fn2-ctf-dir-update-events (cdr children) (+ 1 k) m))))))
(defun fn2-ctf-dir-update-runes (children k m)
  (declare (xargs :mode :program))
  (cond ((atom children) nil)
        ((equal k m) (fn2-ctf-dir-update-runes (cdr children) (+ 1 k) m))
        (t (cons (fn2-columns-pre "FN2-CTF-DIR-OF-" (fn2-columns-pre "UPDATE-" (caar children)))
                 (fn2-ctf-dir-update-runes (cdr children) (+ 1 k) m)))))
(make-event
 (let ((world (w state)))
   (value (cons 'progn (fn2-ctf-dir-update-events (fn2-arm-frame-children-of world) 0 (fn2-arm-frame-m world))))))
(make-event
 (let ((world (w state)))
   (value `(deftheory fn2-ctf-dir-base
             (union-theories '(fn2-ctf-dir-refl fn2-ctf-dir-of-update-fn2-core-machines
                               ,@(fn2-ctf-dir-update-runes (fn2-arm-frame-children-of world) 0 (fn2-arm-frame-m world)))
                             (theory 'fn2-arm-frame-base))))))
(defun fn2-ctf-dir-name (fn) (declare (xargs :mode :program)) (fn2-columns-sym fn "-CTF-DIR"))
;; The functions under FNS that return the core, callees first.
(defun fn2-ctf-postorder (fns world seen fuel)
  (declare (xargs :mode :program))
  (cond ((or (zp fuel) (atom fns)) seen)
        ((or (member-eq (car fns) seen) (not (fn2-arm-frame-corep-fn (car fns) world)))
         (fn2-ctf-postorder (cdr fns) world seen fuel))
        (t (fn2-ctf-postorder (cdr fns) world
             (append (fn2-ctf-postorder (fn2-arm-frame-body-callees (car fns) world) world seen (1- fuel))
                     (list (car fns)))
             fuel))))
(defun fn2-ctf-postorder-new (fns world)
  (declare (xargs :mode :program))
  (let ((all (fn2-ctf-postorder fns world nil 64)))
    (remove-duplicates-eq (reverse (remove-duplicates-eq (reverse all))))))
(defun fn2-ctf-dir-callee-runes (callees world)
  (declare (xargs :mode :program))
  (cond ((atom callees) nil)
        ((getpropc (fn2-ctf-dir-name (car callees)) 'theorem nil world)
         (cons (fn2-ctf-dir-name (car callees)) (fn2-ctf-dir-callee-runes (cdr callees) world)))
        (t (fn2-ctf-dir-callee-runes (cdr callees) world))))
(defun fn2-ctf-dir-event (fn kind world)
  (declare (xargs :mode :program))
  (let* ((e (fn2-arm-frame-known fn kind world))
         (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (m (fn2-arm-frame-m world))
         (name (fn2-ctf-dir-name fn))
         (stmt `(implies (fn2-ctf-dir fn2-core fn2-ctf-c0) (fn2-ctf-dir ,out fn2-ctf-c0))))
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
     (t
      `((defthm ,name ,stmt
          :hints (("Goal" :in-theory (union-theories
                                      '(,fn ,@(strip-cdrs (table-alist 'fn2-arm-frame-directory-keeps world))
                                        ,@(fn2-ctf-dir-callee-runes (fn2-arm-frame-body-callees fn world) world))
                                      (theory 'fn2-ctf-dir-base))
                   :do-not-induct t))))))))
(defun fn2-ctf-dir-forms (fns kind)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons `(make-event (value (cons 'progn (fn2-ctf-dir-event ',(car fns) ',kind (w state)))))
          (fn2-ctf-dir-forms (cdr fns) kind))))
(make-event
 (value (cons 'progn (fn2-ctf-dir-forms
                      (fn2-ctf-postorder-new '(fn2-commit-run fn2-exec-pop fn2-exec-charge-run fn2-machine-take-wake fn2-exec-wake
                                               fn2-exec-record fn2-machine-refuse-phase fn2-machine-idle) (w state))
                      'fn2-commit))))

;; ---------------------------------------------------------------------------
;; THE DISPATCH: fn2-machine-run of a commit id runs fn2-commit-run (or
;; refuses or idles, writing only the control child).
(make-event
 (let* ((world (w state))
        (tk (fn2-arm-frame-child-index 'fn2-commit-table world))
        (ctl (fn2-arm-frame-ctl world))
        (runes (fn2-arm-frame-lemmas '(fn2-machine-refuse-phase fn2-machine-idle) '("-ARM-ROW-FRAME") 'fn2-commit world)))
   (value
    `(progn
       (defthm fn2-machine-run-commit-arm-row-frame
         (implies (and (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
                       (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                       (natp fn2-arm-tb)
                       (subsetp-equal (fn2-commit-arm-children (fn2-commit-row-phase id fn2-core)) fn2-arm-ch)
                       (member-equal ,ctl fn2-arm-ch)
                       (or (member-equal ,tk fn2-arm-ch)
                           (and (equal fn2-arm-tb ,tk)
                                (subsetp-equal (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core)) fn2-arm-cs)
                                (equal (fn2-machine-slot id fn2-core) fn2-arm-row))))
                  (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0
                                     (mv-nth 4 (fn2-machine-run id budget fn2-core))))
         :hints (("Goal" :in-theory (union-theories '(fn2-machine-run fn2-commit-run-arm-row-frame ,@runes)
                                                    (theory 'fn2-arm-frame-base))
                  :do-not-induct t)))
       (defthm fn2-machine-run-commit-ctf-dir
         (implies (and (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
                       (fn2-ctf-dir fn2-core fn2-ctf-c0))
                  (fn2-ctf-dir (mv-nth 4 (fn2-machine-run id budget fn2-core)) fn2-ctf-c0))
         :hints (("Goal" :in-theory (union-theories '(fn2-machine-run fn2-commit-run-ctf-dir fn2-machine-refuse-phase-ctf-dir
                                                      fn2-machine-idle-ctf-dir)
                                                    (theory 'fn2-arm-frame-base))
                  :do-not-induct t)))))))

;; ---------------------------------------------------------------------------
;; THE PRINCIPAL VISIT of a commit row (fn2-exec-principal): the commit
;; table changes only in the arm's declared columns at the row's slot; the
;; children that change are the arm's and the executor's glue around it
;; (FN2-COMMIT-VISIT-GLUE: the pop, the charge, the wake handoff, the wakes
;; and the trace record); the directory keeps every id's kind and slot.
(defthm fn2-ctf-pop-keeps-commit-reads
  (and (equal (fn2-commit-row-phase id (mv-nth 2 (fn2-exec-pop principal fn2-core))) (fn2-commit-row-phase id fn2-core))
       (equal (fn2-machine-kind id (mv-nth 2 (fn2-exec-pop principal fn2-core))) (fn2-machine-kind id fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-exec-pop fn2-commit-row-phase fn2-commit-snapshot-read-code fn2-machine-phase-read-code
                                     fn2-machine-kind fn2-machine-kind-read-code fn2-machine-slot fn2-machine-slot-read-code
                                     fn2-machine-idp))))
(in-theory (disable fn2-ctf-pop-keeps-commit-reads))
(defun fn2-ctf-glue-children (fns kind world)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (union-equal (fn2-arm-frame-entry-kids (fn2-arm-frame-known (car fns) kind world) world)
                 (fn2-ctf-glue-children (cdr fns) kind world))))
(make-event
 `(defconst *fn2-commit-visit-glue*
    ',(fn2-ctf-glue-children '(fn2-exec-pop fn2-exec-charge-run fn2-machine-take-wake fn2-exec-wake fn2-exec-record)
                             'fn2-commit (w state))))
(defun fn2-commit-visit-children (phase)
  (declare (xargs :guard t))
  (append *fn2-commit-visit-glue* (fn2-commit-arm-children phase)))
(defthm fn2-ctf-subsetp-refl (subsetp-equal x x)
  :hints (("Goal" :induct (len x) :in-theory (enable fn2-arm-subsetp-cons))))
(defthm fn2-ctf-subsetp-append-right (implies (subsetp-equal x z) (subsetp-equal x (append y z))))
(defthm fn2-ctf-member-append (implies (member-equal a y) (member-equal a (append y z))))
(in-theory (disable fn2-ctf-subsetp-refl fn2-ctf-subsetp-append-right fn2-ctf-member-append))
(make-event
 (let* ((world (w state))
        (tk (fn2-arm-frame-child-index 'fn2-commit-table world))
        (glue '(fn2-exec-pop fn2-exec-charge-run fn2-machine-take-wake fn2-exec-wake fn2-exec-record))
        (frames (fn2-arm-frame-lemmas glue '("-ARM-ROW-FRAME" "-ARM-SLOT") 'fn2-commit world)))
   (value
    `(defthm fn2-exec-principal-commit-frame
       (let ((id (mv-nth 1 (fn2-exec-pop principal fn2-core)))
             (after (mv-nth 5 (fn2-exec-principal principal position budget fn2-core))))
         (implies (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
                  (and (fn2-arm-row-frame ,tk (fn2-machine-slot id fn2-core)
                                          (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core))
                                          (fn2-commit-visit-children (fn2-commit-row-phase id fn2-core))
                                          fn2-core after)
                       (fn2-ctf-dir after fn2-core))))
       :hints (("Goal" :in-theory (union-theories
                                   '(fn2-exec-principal fn2-commit-visit-children (:e fn2-commit-visit-children)
                                     fn2-machine-run-commit-arm-row-frame fn2-machine-run-commit-ctf-dir
                                     fn2-ctf-pop-keeps-commit-reads fn2-ctf-subsetp-refl fn2-ctf-subsetp-append-right
                                     fn2-ctf-member-append fn2-ctf-dir-refl
                                     ,@frames ,@(fn2-ctf-dir-callee-runes glue world))
                                   (theory 'fn2-arm-frame-base))
                :do-not-induct t))))))

;; ---------------------------------------------------------------------------
;; The kind-independent turn induction is in executor-contracts.lisp.
;; Commit semantics instantiate FN2-EXECUTOR-INV-TURN after discharging
;; the registry's run/observe contracts and the executor's glue contracts.

;; ---------------------------------------------------------------------------
;; THE COMMIT HANDLERS (the dispatch states their FRAMEs owed): each
;; handler's chained row-frame contract at its declared columns and
;; children, as an arm's (machines.lisp fn2-arm-frame-arm-events), after its
;; callees' contracts.
(defun fn2-ctf-handler-forms (name observes world)
  (declare (xargs :mode :program))
  (if (atom observes) nil
    (let* ((fn (cadar observes)) (c (cddar observes))
           (cols (fn2-machine-property name :table world))
           (tk (fn2-machine-child-index (fn2-columns-sym name "-TABLE") world))
           (j (fn2-machine-column-indices (cons 'phase (fn2-arm-get :writes c)) cols))
           (ch (fn2-machine-child-indices (append (fn2-arm-get :tables c) (fn2-machine-directory-child (fn2-arm-get :writes c))
                                                  *fn2-arm-implicit-tables*) world)))
      (list*
       `(make-event
         (value (cons 'progn (fn2-arm-frame-fns-forms
                              (fn2-arm-frame-todo (fn2-arm-frame-body-callees ',fn (w state)) ',name (w state) nil 64) ',name))))
       `(make-event
         (let* ((world (w state)) (callees (fn2-arm-frame-body-callees ',fn world)))
           (value
            `(progn
               (defthm ,',(fn2-arm-frame-name fn "-ARM-ROW-FRAME")
                 (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                               ,@',(fn2-arm-frame-row-frame-hyps tk ch j 'id))
                          (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0
                                             (mv-nth 1 (,',fn ,@',(formals fn world)))))
                 :hints ,(fn2-arm-frame-hints (cons ',fn (append (fn2-arm-frame-inline-runes ',fn ',name world)
                                                                (fn2-arm-frame-lemmas callees '("-ARM-ROW-FRAME" "-ARM-SLOT") ',name world)))))
               (in-theory (disable ,',(fn2-arm-frame-name fn "-ARM-ROW-FRAME")))
               (table fn2-arm-frame-fns ',',fn '(:arm ,',ch ,',j nil))))))
       (fn2-ctf-handler-forms name (cdr observes) world)))))
(make-event
 (value (cons 'progn (fn2-ctf-handler-forms 'fn2-commit (fn2-machine-property 'fn2-commit :observes (w state)) (w state)))))
(make-event
 (value (cons 'progn (fn2-arm-frame-fns-forms
                      (fn2-arm-frame-todo '(fn2-machine-observe-terminal fn2-machine-refuse-observation fn2-machine-observe-contract-check
                                            fn2-harvest-one)
                                          'fn2-commit (w state) nil 64)
                      'fn2-commit))))
(defun fn2-ctf-handler-decls (observes world)
  (declare (xargs :mode :program))
  (if (atom observes) (mv nil nil)
    (mv-let (ch j) (fn2-ctf-handler-decls (cdr observes) world)
      (let ((e (cdr (assoc-eq (cadar observes) (table-alist 'fn2-arm-frame-fns world)))))
        (mv (union-equal (remove-duplicates-equal (cadr e)) ch) (union-equal (caddr e) j))))))
(make-event
 (mv-let (ch j) (fn2-ctf-handler-decls (fn2-machine-property 'fn2-commit :observes (w state)) (w state))
   (let ((term (fn2-arm-frame-known 'fn2-machine-observe-terminal 'fn2-commit (w state))))
     ; the route consumes the terminal (the row's pending count, through
     ; the generic row writer: its row contract names every kind's table)
     (value `(progn (defconst *fn2-commit-handler-children* ',ch)
                    (defconst *fn2-commit-handler-columns* ',j)
                    (defconst *fn2-commit-route-children* ',(union-equal ch (caddr term)))
                    (defconst *fn2-commit-route-columns* ',(union-equal j (cadddr term))))))))
;; The commit observation route and the router at a commit id.
(defun fn2-ctf-suffixed (fns suffix world)
  (declare (xargs :mode :program))
  (cond ((atom fns) nil)
        ((getpropc (fn2-columns-sym (car fns) suffix) 'theorem nil world)
         (cons (fn2-columns-sym (car fns) suffix) (fn2-ctf-suffixed (cdr fns) suffix world)))
        (t (fn2-ctf-suffixed (cdr fns) suffix world))))
(defun fn2-ctf-chained (fn out tk ch j world)
  (declare (xargs :mode :program))
  (let ((callees (fn2-arm-frame-body-callees fn world)))
    `(defthm ,(fn2-columns-sym fn "-CTF-ROW-FRAME")
       (implies (and (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                     ,@(fn2-arm-frame-row-frame-hyps tk ch j 'id))
                (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 ,out))
       :hints (("Goal" :in-theory (union-theories
                                   '(,fn ,@(fn2-arm-frame-lemmas callees '("-ARM-ROW-FRAME") 'fn2-commit world)
                                     ,@(fn2-ctf-suffixed callees "-CTF-ROW-FRAME" world)
                                     ,@(fn2-ctf-suffixed callees "-CTF-SLOT" world))
                                   (theory 'fn2-arm-frame-base))
                :do-not-induct t)))))
(make-event
 (let ((world (w state)) (tk (fn2-arm-frame-child-index 'fn2-commit-table (w state))))
   (value (fn2-ctf-chained 'fn2-machine-observe-fn2-commit
                           `(mv-nth 1 (fn2-machine-observe-fn2-commit ,@(formals 'fn2-machine-observe-fn2-commit world)))
                           tk *fn2-commit-handler-children* *fn2-commit-handler-columns* world))))
(make-event
 (value (cons 'progn (fn2-ctf-dir-forms (fn2-ctf-postorder-new '(fn2-machine-observe-fn2-commit) (w state)) 'fn2-commit))))
(defthm fn2-machine-observe-fn2-commit-ctf-slot
  (equal (fn2-machine-slot fn2-arm-id (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 fn2-core)))
         (fn2-machine-slot fn2-arm-id fn2-core))
  :hints (("Goal" :in-theory '(fn2-ctf-dir-refl)
           :use ((:instance fn2-machine-observe-fn2-commit-ctf-dir (fn2-ctf-c0 fn2-core))
                 (:instance fn2-ctf-dir-readers (id fn2-arm-id) (a fn2-core)
                            (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 fn2-core))))))))
(in-theory (disable fn2-machine-observe-fn2-commit-ctf-slot))
(make-event
 (let ((world (w state)) (tk (fn2-arm-frame-child-index 'fn2-commit-table (w state))))
   (value (fn2-ctf-chained 'fn2-machine-observe-route-fn2-commit
                           `(mv-nth 1 (fn2-machine-observe-route-fn2-commit ,@(formals 'fn2-machine-observe-route-fn2-commit world)))
                           tk *fn2-commit-route-children* *fn2-commit-route-columns* world))))
(make-event
 (value (cons 'progn (fn2-ctf-dir-forms (fn2-ctf-postorder-new '(fn2-machine-observe-route-fn2-commit fn2-harvest-one) (w state)) 'fn2-commit))))
(make-event
 (let* ((world (w state))
        (tk (fn2-arm-frame-child-index 'fn2-commit-table world))
        (refuse (fn2-arm-frame-lemmas '(fn2-machine-refuse-observation) '("-ARM-ROW-FRAME") 'fn2-commit world)))
   (value
    `(progn
       (defthm fn2-machine-observe-commit-ctf-row-frame
         (implies (and (equal okind *fn2-commit-kind*)
                       (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0 fn2-core)
                       ,@(fn2-arm-frame-row-frame-hyps tk *fn2-commit-route-children* *fn2-commit-route-columns* 'id))
                  (fn2-arm-row-frame fn2-arm-tb fn2-arm-row fn2-arm-cs fn2-arm-ch fn2-arm-c0
                                     (mv-nth 1 (fn2-machine-observe okind id gen event outcome reason count aux0 aux1 fn2-core))))
         :hints (("Goal" :in-theory (union-theories '(fn2-machine-observe fn2-machine-observe-route-fn2-commit-ctf-row-frame ,@refuse)
                                                    (theory 'fn2-arm-frame-base))
                  :do-not-induct t)))
       (defthm fn2-machine-observe-commit-ctf-dir
         (implies (and (equal okind *fn2-commit-kind*) (fn2-ctf-dir fn2-core fn2-ctf-c0))
                  (fn2-ctf-dir (mv-nth 1 (fn2-machine-observe okind id gen event outcome reason count aux0 aux1 fn2-core)) fn2-ctf-c0))
         :hints (("Goal" :in-theory (union-theories '(fn2-machine-observe fn2-machine-observe-route-fn2-commit-ctf-dir
                                                      fn2-machine-refuse-observation-ctf-dir)
                                                    (theory 'fn2-arm-frame-base))
                  :do-not-induct t)))))))
;; THE HARVEST of a commit row's completion (fn2-exec-harvest): the commit
;; table changes only in its handlers' columns and the terminal's at the
;; owner's slot; the children are the handlers', the terminal's and the
;; harvest's glue (FN2-COMMIT-HARVEST-GLUE).
(make-event
 `(defconst *fn2-commit-harvest-glue*
    ',(fn2-ctf-glue-children '(fn2-harvest-one fn2-exec-wake fn2-exec-record) 'fn2-commit (w state))))
(defthm fn2-ctf-harvest-one-keeps-commit-reads
  (and (equal (fn2-machine-kind id (mv-nth 10 (fn2-harvest-one fn2-core))) (fn2-machine-kind id fn2-core))
       (equal (fn2-machine-slot id (mv-nth 10 (fn2-harvest-one fn2-core))) (fn2-machine-slot id fn2-core)))
  :hints (("Goal" :in-theory '(fn2-ctf-dir-refl)
           :use ((:instance fn2-harvest-one-ctf-dir (fn2-ctf-c0 fn2-core))
                 (:instance fn2-ctf-dir-readers (a fn2-core) (b (mv-nth 10 (fn2-harvest-one fn2-core))))))))
(in-theory (disable fn2-ctf-harvest-one-keeps-commit-reads))
(make-event
 (let* ((world (w state))
        (tk (fn2-arm-frame-child-index 'fn2-commit-table world))
        (glue '(fn2-harvest-one fn2-exec-wake fn2-exec-record))
        (frames (fn2-arm-frame-lemmas glue '("-ARM-ROW-FRAME") 'fn2-commit world)))
   (value
    `(defthm fn2-exec-harvest-commit-frame
       (let ((id (mv-nth 2 (fn2-core-next-owner fn2-core)))
             (after (mv-nth 5 (fn2-exec-harvest fn2-core))))
         (implies (equal (mv-nth 1 (fn2-core-next-owner fn2-core)) *fn2-commit-kind*)
                  (and (fn2-arm-row-frame ,tk (fn2-machine-slot id fn2-core)
                                          *fn2-commit-route-columns*
                                          (append *fn2-commit-harvest-glue* *fn2-commit-route-children*)
                                          fn2-core after)
                       (fn2-ctf-dir after fn2-core))))
       :hints (("Goal" :in-theory (union-theories
                                   '(fn2-exec-harvest fn2-machine-observe-commit-ctf-row-frame fn2-machine-observe-commit-ctf-dir
                                     fn2-ctf-harvest-one-keeps-commit-reads fn2-ctf-dir-refl
                                     ,@frames ,@(fn2-ctf-dir-callee-runes glue world))
                                   (theory 'fn2-arm-frame-base))
                :do-not-induct t))))))

;; ---------------------------------------------------------------------------
;; THE TRANSITION (fn2-transition): its principal visit of a commit row, its
;; harvest of a commit row's completion, and its mailbox step.
(defthm fn2-ctf-visit-keeps-commit-reads
  (and (equal (fn2-commit-row-phase id (mv-nth 3 (fn2-exec-visit fn2-core))) (fn2-commit-row-phase id fn2-core))
       (equal (fn2-machine-kind id (mv-nth 3 (fn2-exec-visit fn2-core))) (fn2-machine-kind id fn2-core))
       (equal (fn2-machine-slot id (mv-nth 3 (fn2-exec-visit fn2-core))) (fn2-machine-slot id fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-exec-visit fn2-commit-row-phase fn2-commit-snapshot-read-code fn2-machine-phase-read-code
                                     fn2-machine-kind fn2-machine-kind-read-code fn2-machine-slot fn2-machine-slot-read-code
                                     fn2-machine-idp))))
(in-theory (disable fn2-ctf-visit-keeps-commit-reads))
(make-event
 (value (cons 'progn (append (fn2-arm-frame-fns-forms (fn2-arm-frame-todo '(fn2-exec-mailbox) 'fn2-commit (w state) nil 64) 'fn2-commit)
                             (list '(make-event (value (cons 'progn (fn2-ctf-dir-forms '(fn2-exec-visit fn2-exec-mailbox) 'fn2-commit)))))))))
;; The id a principal visit pops, the visit's principal and the core it pops from.
(defun-nx fn2-ctf-visit-principal (fn2-core) (mv-nth 1 (fn2-exec-visit fn2-core)))
(defun-nx fn2-ctf-visit-id (fn2-core)
  (mv-nth 1 (fn2-exec-pop (mv-nth 1 (fn2-exec-visit fn2-core)) (mv-nth 3 (fn2-exec-visit fn2-core)))))
(defun-nx fn2-ctf-principal-visit-p (allow-observation fn2-core)
  (and (not (and allow-observation (fn2-exec-observation-p fn2-core)))
       (fn2-exec-eligible-p fn2-core)
       (equal (mv-nth 0 (fn2-exec-visit fn2-core)) *fn2-visit-principal*)))
(make-event
 (let* ((world (w state)) (tk (fn2-arm-frame-child-index 'fn2-commit-table world))
        (visit (fn2-arm-frame-lemmas '(fn2-exec-visit) '("-ARM-ROW-FRAME") 'fn2-commit world)))
   (value
    `(progn
       (defthm fn2-transition-commit-principal-frame
         (let ((id (fn2-ctf-visit-id fn2-core))
               (after (mv-nth 5 (fn2-transition allow-observation action-budget fn2-core))))
           (implies (and (fn2-ctf-principal-visit-p allow-observation fn2-core)
                         (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*))
                    (and (fn2-arm-row-frame ,tk (fn2-machine-slot id fn2-core)
                                            (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core))
                                            (fn2-commit-visit-children (fn2-commit-row-phase id fn2-core))
                                            fn2-core after)
                         (fn2-ctf-dir after fn2-core))))
         :hints (("Goal" :in-theory (union-theories '(fn2-transition fn2-ctf-visit-id fn2-ctf-principal-visit-p
                                                      fn2-ctf-visit-keeps-commit-reads fn2-exec-visit-ctf-dir fn2-ctf-dir-refl
                                                      fn2-commit-visit-children fn2-ctf-member-append fn2-ctf-subsetp-refl fn2-ctf-subsetp-append-right ,@visit)
                                                    (theory 'fn2-arm-frame-base))
                  :do-not-induct t
                  :use ((:instance fn2-exec-principal-commit-frame
                                   (principal (mv-nth 1 (fn2-exec-visit fn2-core)))
                                   (position (mv-nth 2 (fn2-exec-visit fn2-core)))
                                   (budget action-budget)
                                   (fn2-core (mv-nth 3 (fn2-exec-visit fn2-core))))
                        (:instance fn2-arm-row-frame-trans (table ,tk) (row (fn2-machine-slot (fn2-ctf-visit-id fn2-core) fn2-core))
                                   (columns (fn2-commit-arm-columns (fn2-commit-row-phase (fn2-ctf-visit-id fn2-core) fn2-core)))
                                   (children (fn2-commit-visit-children (fn2-commit-row-phase (fn2-ctf-visit-id fn2-core) fn2-core)))
                                   (c2 (fn2-commit-arm-columns (fn2-commit-row-phase (fn2-ctf-visit-id fn2-core) fn2-core)))
                                   (ch2 (fn2-commit-visit-children (fn2-commit-row-phase (fn2-ctf-visit-id fn2-core) fn2-core)))
                                   (a fn2-core) (b (mv-nth 3 (fn2-exec-visit fn2-core)))
                                   (c (mv-nth 5 (fn2-exec-principal (mv-nth 1 (fn2-exec-visit fn2-core)) (mv-nth 2 (fn2-exec-visit fn2-core))
                                                                    action-budget (mv-nth 3 (fn2-exec-visit fn2-core))))))
                        (:instance fn2-ctf-dir-trans (a fn2-core) (b (mv-nth 3 (fn2-exec-visit fn2-core)))
                                   (c (mv-nth 5 (fn2-exec-principal (mv-nth 1 (fn2-exec-visit fn2-core)) (mv-nth 2 (fn2-exec-visit fn2-core))
                                                                    action-budget (mv-nth 3 (fn2-exec-visit fn2-core))))))))))))))
(make-event
 (let* ((world (w state)) (tk (fn2-arm-frame-child-index 'fn2-commit-table world)) (m (fn2-arm-frame-m world))
        (e (fn2-arm-frame-known 'fn2-exec-mailbox 'fn2-commit world))
        (s (fn2-arm-frame-entry-kids e world)))
   (if (or (member tk s) (member m s))
       (er soft 'commit-turn-frame "The mailbox step's children ~x0 reach the commit table or the directory." s)
     (value
      `(progn
         (defthm fn2-transition-commit-harvest-frame
           (let ((id (mv-nth 2 (fn2-core-next-owner fn2-core)))
                 (after (mv-nth 5 (fn2-transition allow-observation action-budget fn2-core))))
             (implies (and allow-observation (fn2-exec-observation-p fn2-core) (fn2-core-posted-p fn2-core)
                           (equal (mv-nth 1 (fn2-core-next-owner fn2-core)) *fn2-commit-kind*))
                      (and (fn2-arm-row-frame ,tk (fn2-machine-slot id fn2-core) *fn2-commit-route-columns*
                                              (append *fn2-commit-harvest-glue* *fn2-commit-route-children*)
                                              fn2-core after)
                           (fn2-ctf-dir after fn2-core))))
           :hints (("Goal" :in-theory '(fn2-transition)
                    :use ((:instance fn2-exec-harvest-commit-frame)))))
         ;; the mailbox step (clock or signal) leaves the commit table and the
         ;; directory as they were
         (defthm fn2-transition-mailbox-keeps-commit
           (let ((after (mv-nth 5 (fn2-transition allow-observation action-budget fn2-core))))
             (implies (and allow-observation (fn2-exec-observation-p fn2-core) (not (fn2-core-posted-p fn2-core)))
                      (and (equal (nth ,tk after) (nth ,tk fn2-core))
                           (equal (nth ,m after) (nth ,m fn2-core)))))
           :hints (("Goal" :in-theory (union-theories '(fn2-transition) (theory 'fn2-arm-frame-base))
                    :use ((:instance ,(fn2-arm-frame-lemma 'fn2-exec-mailbox e "-ARM-KIDS" 'fn2-commit world)
                                     (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                          (:instance fn2-arm-kids-nth (i 0) (k ,tk) (free ',s) (a fn2-core) (b (mv-nth 5 (fn2-exec-mailbox fn2-core))))
                          (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',s) (a fn2-core) (b (mv-nth 5 (fn2-exec-mailbox fn2-core)))))))))))))

;; ---------------------------------------------------------------------------
;; THE WHOLE TRANSITION, owed: every transition either is a commit row's
;; visit or harvest (proved above, with its frame) or leaves the commit
;; table and the directory's kinds and slots alone. Proved for the mailbox
;; step; owed for a principal visit of another kind, a harvest for another
;; kind's row and the grant service, whose callees are the constrained
;; functions in *FN2-COMMIT-TURN-FRAME-BLOCKERS* (dispatch stubs, wait-source
;; grants and a hook whose constraints carry no frame contract) and the arms and
;; handlers of the kinds with run bodies whose FRAMEs are owed (table
;; fn2-arm-frame-owed). With it, FN2-EXECUTOR-INV-TURN lifts any property the
;; per-transition frames preserve to fn2-turn.
(defun fn2-ctf-constrained-under (fns seen acc world fuel)
  (declare (xargs :mode :program))
  (cond ((or (zp fuel) (atom fns)) (mv seen acc))
        ((member-eq (car fns) seen) (fn2-ctf-constrained-under (cdr fns) seen acc world fuel))
        (t (let* ((f (car fns)) (seen (cons f seen))
                  (acc (if (and (getpropc f 'constrainedp nil world) (fn2-arm-frame-corep-fn f world)
                                (not (getpropc (fn2-arm-frame-name f "-ARM-KIDS") 'theorem nil world)))
                           (cons f acc) acc))
                  (body (getpropc f 'unnormalized-body nil world)))
             (mv-let (seen acc) (fn2-ctf-constrained-under (and body (all-fnnames body)) seen acc world (1- fuel))
               (fn2-ctf-constrained-under (cdr fns) seen acc world fuel))))))
(make-event
 (mv-let (seen acc) (fn2-ctf-constrained-under '(fn2-transition) nil nil (w state) 100000)
   (declare (ignore seen))
   (value `(defconst *fn2-commit-turn-frame-blockers* ',(reverse acc)))))
(defun fn2-ctf-teeth-positive ()
  (declare (xargs :verify-guards nil))
  ; the table (child 1) changes in a declared column at the row; the
  ; directory (child 3) changes outside its kind and slot columns and rows
  (and (fn2-arm-row-frame 1 1 '(0) '(2) '(a ((0 0) (5 5)) c d) '(a ((0 9) (5 5)) z d))
       (fn2-ctf-dir (list 'a 'b 'c (update-nth 2 'x (make-list 40)))
                    (list 'a 'b 'c (make-list 40)))))
(defun fn2-ctf-teeth-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-arm-row-frame 1 1 '(0) '(2) '(a ((0 0) (5 5)) c d) '(a ((9 0) (5 5)) c d)))   ; another row
       (not (fn2-arm-row-frame 1 1 '(0) '(2) '(a ((0 0) (5 5)) c d) '(a ((0 0) (5 6)) c d)))   ; an undeclared column
       (not (fn2-arm-row-frame 1 1 '(0) '(2) '(a ((0 0) (5 5)) c d) '(a ((0 0) (5 5)) c e)))   ; an undeclared child
       (not (fn2-ctf-dir (list 'a 'b 'c (update-nth 1 'x (make-list 40)))                       ; a slot moved
                         (list 'a 'b 'c (make-list 40))))))
(assert-event (and (fn2-ctf-teeth-positive) (fn2-ctf-teeth-negative)))
(make-event
 (let* ((world (w state)) (tk (fn2-arm-frame-child-index 'fn2-commit-table world)))
   (value
    `(defthm-owed fn2-transition-commit-frame (allow-observation action-budget fn2-core)
       (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                (let ((after (mv-nth 5 (fn2-transition allow-observation action-budget fn2-core)))
                      (id (fn2-ctf-visit-id fn2-core)) (owner (mv-nth 2 (fn2-core-next-owner fn2-core))))
                  (or (and (fn2-ctf-principal-visit-p allow-observation fn2-core)
                           (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
                           (fn2-arm-row-frame ,tk (fn2-machine-slot id fn2-core)
                                              (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core))
                                              (fn2-commit-visit-children (fn2-commit-row-phase id fn2-core))
                                              fn2-core after)
                           (fn2-ctf-dir after fn2-core))
                      (and allow-observation (fn2-exec-observation-p fn2-core) (fn2-core-posted-p fn2-core)
                           (equal (mv-nth 1 (fn2-core-next-owner fn2-core)) *fn2-commit-kind*)
                           (fn2-arm-row-frame ,tk (fn2-machine-slot owner fn2-core) *fn2-commit-route-columns*
                                              (append *fn2-commit-harvest-glue* *fn2-commit-route-children*)
                                              fn2-core after)
                           (fn2-ctf-dir after fn2-core))
                      (and (equal (nth ,tk after) (nth ,tk fn2-core))
                           (fn2-ctf-dir after fn2-core)))))
       :schema :invariant :from (:machine fn2-commit)
       :teeth (fn2-ctf-teeth-positive fn2-ctf-teeth-negative)
       :doc "Every transition of fn2-turn is a commit row's principal visit (the table changes only in its arm's declared columns at the row's slot), a commit row's harvest (its handlers' and the terminal's columns), or leaves the commit table unchanged; the directory keeps every id's kind and slot. Proved: the commit visit, the commit harvest and the mailbox step (fn2-transition-commit-principal-frame, -harvest-frame, fn2-transition-mailbox-keeps-commit). Owed: other kinds' visits and harvests and the grant service, whose callees include the constrained functions *fn2-commit-turn-frame-blockers*."))))

;; ---------------------------------------------------------------------------
;; THE NOTIFY ARM'S WRITES: the reply count it leaves, as a term of the
;; pre-state. A table change outside a column and the rows field, with the
;; directory kept, keeps that column's row read (and the row's readability).
(make-event
 (let* ((world (w state)) (tk (fn2-arm-frame-child-index 'fn2-commit-table world))
        (tcols (strip-cars (fn2-machine-property 'fn2-commit :table world)))
        (ri (len tcols)) (acks (position-eq 'cb-acks tcols)))
   (value
    `(progn
       (defthm fn2-ctf-commit-reads-of-row-frame
         (implies (and (fn2-arm-row-frame ,tk row cs ch a b) (not (member-equal ,tk ch))
                       (not (member-equal ,ri cs)) (not (member-equal ,acks cs))
                       (fn2-ctf-dir b a))
                  (and (equal (equal (fn2-commit-snapshot-read-code id b) :ok) (equal (fn2-commit-snapshot-read-code id a) :ok))
                       (equal (fn2-commit-row-cb-acks id b) (fn2-commit-row-cb-acks id a))))
         :rule-classes nil
         :hints (("Goal" :cases ((equal (fn2-machine-kind id a) *fn2-commit-kind*))
                  :in-theory (e/d (fn2-commit-snapshot-read-code fn2-machine-phase-read-code fn2-commit-row-cb-acks
                                   fn2-commit-table fn2-commit-rows fn2-commit-cb-acks fn2-commit-cb-acks$ai)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp nth update-nth fn2-arm-row-frame fn2-ctf-dir))
                  :use ((:instance fn2-ctf-dir-readers)
                        (:instance fn2-arm-row-frame-cols (table ,tk) (columns cs) (children ch))
                        (:instance fn2-arm-cols-nth (k 0) (j ,ri) (columns cs) (a (nth ,tk a)) (b (nth ,tk b)))
                        (:instance fn2-arm-cols-nth (k 0) (j ,acks) (columns cs) (a (nth ,tk a)) (b (nth ,tk b)))))))))))
(defun fn2-ctf-acks-event (fn kind world)
  (declare (xargs :mode :program))
  (let* ((e (fn2-arm-frame-known fn kind world))
         (tk (fn2-arm-frame-child-index 'fn2-commit-table world))
         (tcols (strip-cars (fn2-machine-property 'fn2-commit :table world)))
         (ri (len tcols)) (acks (position-eq 'cb-acks tcols))
         (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (rowp (and (member-eq (car e) '(:row :write)) (equal (fn2-arm-frame-entry-tk e world) tk)))
         (s (fn2-arm-frame-entry-s e))
         (j (and rowp (fn2-arm-frame-entry-j e)))
         (row (if rowp '(fn2-machine-slot id fn2-core) 0)))
    (if (or (not (member-eq (car e) '(:op :row :write))) (member tk s) (member ri j) (member acks j)
            (and (not rowp) (fn2-arm-frame-entry-tk e world)))
        (er hard 'fn2-ctf-acks-event "~x0's contract ~x1 may write the reply count." fn e)
      `(defthm ,(fn2-columns-sym fn "-CTF-ACKS")
         (and (equal (equal (fn2-commit-snapshot-read-code fn2-arm-id ,out) :ok)
                     (equal (fn2-commit-snapshot-read-code fn2-arm-id fn2-core) :ok))
              (equal (fn2-commit-row-cb-acks fn2-arm-id ,out) (fn2-commit-row-cb-acks fn2-arm-id fn2-core)))
         :hints (("Goal" :in-theory (union-theories '(fn2-arm-row-frame-refl fn2-ctf-dir-refl (:type-prescription fn2-machine-slot-natp)) (theory 'fn2-arm-frame-base))
                  :use ((:instance ,(fn2-arm-frame-lemma fn e "-ARM-ROW-FRAME" kind world)
                                   (fn2-arm-tb ,tk) (fn2-arm-row ,row) (fn2-arm-cs ',j) (fn2-arm-ch ',s) (fn2-arm-c0 fn2-core))
                        (:instance ,(fn2-ctf-dir-name fn) (fn2-ctf-c0 fn2-core))
                        (:instance fn2-ctf-commit-reads-of-row-frame (id fn2-arm-id) (row ,row) (cs ',j) (ch ',s)
                                   (a fn2-core) (b ,out)))))))))
(defun fn2-ctf-acks-events (fns kind world)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons (fn2-ctf-acks-event (car fns) kind world) (fn2-ctf-acks-events (cdr fns) kind world))))
(make-event
 (value (cons 'progn (fn2-ctf-acks-events '(fn2-core-stop fn2-machine-refuse-write fn2-commit-settle-member
                                            fn2-commit-write+phase+cb-stage fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason)
                                          'fn2-commit (w state)))))
(defthm fn2-ctf-update-nth-nth-same
  (implies (< (nfix i) (len l)) (equal (update-nth i (nth i l) l) l))
  :hints (("Goal" :in-theory (enable update-nth nth))))
(defthm fn2-ctf-update-commit-table-same
  (implies (fn2-corep c) (equal (update-fn2-commit-table (fn2-commit-table c) c) c))
  :hints (("Goal" :in-theory (enable update-fn2-commit-table fn2-commit-table fn2-arm-core-len))))
(in-theory (disable fn2-ctf-update-nth-nth-same))
(defthm fn2-ctf-write-cb-acks-value
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (or (equal (fn2-commit-row-cb-acks id (fn2-commit-write+cb-acks id v fn2-core)) (fn2-commit-row-cb-acks id fn2-core))
               (equal (fn2-commit-row-cb-acks id (fn2-commit-write+cb-acks id v fn2-core)) v)))
  :rule-classes nil
  :hints (("Goal" :cases ((and (fn2-machine-idp id fn2-core) (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
                               (natp (fn2-machine-slot id fn2-core))
                               (< (fn2-machine-slot id fn2-core) (fn2-commit-rows (fn2-commit-table fn2-core)))
                               (unsigned-byte-p 32 v)))
           :use ((:instance fn2-commit-write+cb-acks-reads (fn2-arms-w-cb-acks v)))
           :in-theory (e/d (fn2-commit-write+cb-acks fn2-machine-refuse-write-ctf-acks fn2-ctf-update-commit-table-same)
                           (fn2-commit-write+cb-acks-reads fn2-machine-refuse-write)))))
(defthm fn2-commit-run-notify-writes
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (let ((after (mv-nth 4 (fn2-commit-run-notify id budget fn2-core)))
                 (acks (fn2-commit-row-cb-acks id fn2-core)))
             (or (equal (fn2-commit-row-cb-acks id after) acks)
                 (and (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
                      (equal (fn2-commit-partner-state (fn2-commit-row-batch-no id fn2-core) (fn2-commit-row-partner id fn2-core)
                                                       fn2-core)
                             :ok)
                      (< acks (fn2-commit-row-member-count id fn2-core))
                      (equal (fn2-commit-row-cb-acks id after) (+ 1 acks))))))
  :hints (("Goal" :in-theory (enable fn2-commit-run-notify fn2-core-stop-ctf-acks fn2-commit-settle-member-ctf-acks
                                     fn2-commit-write+phase+cb-stage-ctf-acks
                                     fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-ctf-acks)
           :do-not-induct t
           :use ((:instance fn2-ctf-write-cb-acks-value
                            (fn2-core (fn2-commit-settle-member id (fn2-commit-row-cb-acks id fn2-core) 1
                                                                (fn2-commit-row-batch-no id fn2-core) fn2-core))
                            (v (+ 1 (fn2-commit-row-cb-acks id fn2-core))))))))
(make-event (value (cons 'progn (fn2-ctf-acks-events '(fn2-machine-contract-check fn2-machine-refuse-phase) 'fn2-commit (w state)))))
(defthm fn2-commit-run-notify-phase-writes
  ; the visit of a commit row at :notify, through the kind's run
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-notify*))
           (let ((after (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                 (acks (fn2-commit-row-cb-acks id fn2-core)))
             (or (equal (fn2-commit-row-cb-acks id after) acks)
                 (and (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
                      (equal (fn2-commit-partner-state (fn2-commit-row-batch-no id fn2-core) (fn2-commit-row-partner id fn2-core)
                                                       fn2-core)
                             :ok)
                      (< acks (fn2-commit-row-member-count id fn2-core))
                      (equal (fn2-commit-row-cb-acks id after) (+ 1 acks))))))
  :hints (("Goal" :in-theory (e/d (fn2-commit-run fn2-machine-contract-check-ctf-acks fn2-machine-refuse-phase-ctf-acks)
                                  (fn2-commit-run-notify))
           :do-not-induct t
           :use ((:instance fn2-commit-run-notify-writes)))))

(make-event
 (value (cons 'progn (fn2-arm-frame-fns-forms
                      '(fn2-commit-save-pool fn2-commit-keep-pool fn2-commit-unwind-pool fn2-core-reserve
                        fn2-commit-reserve-pools fn2-commit-reserve-extent fn2-commit-release-pools
                        fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake)
                      'fn2-commit))))

; Materialize each producer's column footprint once, after the concrete
; operations and arm contracts exist. View consumers instantiate these
; contracts; no view names appear in this producer registry.
(make-event (value (fn2-column-base-event 'fn2-core-stop 'fn2-commit (w state))))
(make-event (value (fn2-column-base-event 'fn2-core-release 'fn2-commit (w state))))
(make-event (value (fn2-column-base-event 'fn2-machine-refuse-write 'fn2-commit (w state))))
(make-event (value (cons 'progn (fn2-column-setter-events 'fn2-commit-root (fn2-view-layout 'fn2-commit-root (w state)) 0))))
(make-event (value (cons 'progn (fn2-column-setter-events 'fn2-commit-io (fn2-view-layout 'fn2-commit-io (w state)) 0))))
(fn2-defcolumn-footprint fn2-commit-mark-abort :kind fn2-commit
 :layout fn2-commit-root :columns (aborting abort-event))
(fn2-defcolumn-footprint fn2-commit-prepare-root :kind fn2-commit
 :layout fn2-commit-root :columns (parent extent first-key members proposed))
(fn2-defcolumn-footprint fn2-commit-end-abort :kind fn2-commit
 :layout fn2-commit-root :columns (proposed first-key aborting abort-event))
(fn2-defcolumn-footprint fn2-commit-save-pool :kind fn2-commit
 :layout fn2-commit-io :columns (pool-slot pool-gen ready))
(fn2-defcolumn-footprint fn2-commit-io-edge :kind fn2-commit
 :layout fn2-commit-io :columns (op-slot op-gen lent))
(fn2-defcolumn-footprint fn2-commit-unprepare :kind fn2-commit
 :layout fn2-commit-root :columns (seal-ready))
(fn2-defcolumn-footprint fn2-commit-seal-context :kind fn2-commit
 :layout fn2-commit-root :columns (seal-ready))
(fn2-defcolumn-footprint fn2-commit-release-pool :kind fn2-commit
 :layout fn2-commit-io :columns (pool-slot pool-gen ready))
(make-event (value (cons 'progn (fn2-column-events (fn2-ctf-postorder-new '(fn2-commit-run-collect fn2-commit-run-dependencies fn2-commit-run-log-write) (w state)) 'fn2-commit))))
(make-event (value (cons 'progn (fn2-column-events (fn2-ctf-postorder-new '(fn2-commit-run-seal fn2-commit-run-dropping) (w state)) 'fn2-commit))))
(make-event (value (cons 'progn (fn2-column-events (fn2-ctf-postorder-new '(fn2-commit-run-free fn2-commit-run-fence fn2-commit-run-draining fn2-commit-run-uncertain) (w state)) 'fn2-commit))))
(make-event (value (cons 'progn (fn2-column-events (fn2-ctf-postorder-new '(fn2-commit-run-install fn2-commit-run-publish fn2-commit-run-durable fn2-commit-run-notify) (w state)) 'fn2-commit))))
(make-event (value (cons 'progn (fn2-column-events (fn2-ctf-postorder-new '(fn2-commit-keep-pool fn2-commit-unwind-pool fn2-commit-reserve-pools fn2-commit-release-pools) (w state)) 'fn2-commit))))
(make-event (value (cons 'progn (fn2-column-events (fn2-ctf-postorder-new '(fn2-commit-reserve-extent fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake) (w state)) 'fn2-commit))))
(make-event (value (cons 'progn (fn2-column-events
 (fn2-ctf-postorder-new
  '(fn2-machine-contract-check fn2-machine-refuse-phase
    fn2-commit-write+phase+generation+principal-slot+deadline+stopped+batch-no+member-count+first-key+partner+cb-mode+cb-stage+cb-cursor+cb-issued+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live+cb-fence-ok+cb-deps-ok+cb-log-ok+cb-published+cb-acks+cb-seal-len+cb-wrote+cb-open+dep-bytes+rec-bytes)
  (w state)) 'fn2-commit))))
