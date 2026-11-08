; Materialize dispatch after all registered continuations.
(in-package "ACL2")
(include-book "assembly-callbacks")

;; ---------------------------------------------------------------------------
;; FOOTPRINT CONTRACTS (-DC-KIDS): a function's KIDS contract at the children
;; its callees' contracts show it may change, with no declaration to meet.
;; A dispatch attachment proves its stub's frame from these (the footprint
;; within the frame's children); a function with a KIDS contract of its own
;; (table fn2-arm-frame-fns, or the basis's child updaters) is not rederived.
;; Table fn2-dc-kids: (KIND . FN) -> the children of FN's -DC-KIDS contract.
(table fn2-dc-kids nil nil)
(defun fn2-dc-name (kind fn)
  (declare (xargs :mode :program))
  (if kind (fn2-arm-frame-kname kind fn "-DC-KIDS") (fn2-arm-frame-name fn "-DC-KIDS")))
(defun fn2-dc-entry (fn kind world)
  ; (children . lemma) of FN's KIDS contract under KIND, else nil
  (declare (xargs :mode :program))
  (let ((d (assoc-equal (cons kind fn) (table-alist 'fn2-dc-kids world))))
    (if d (cons (cdr d) (fn2-dc-name kind fn))
      (let ((e (fn2-arm-frame-known fn kind world)))
        (and e (not (member-eq (car e) '(:failed :arm)))
             (let ((lemma (fn2-arm-frame-lemma fn e "-ARM-KIDS" kind world)))
               (and (getpropc lemma 'theorem nil world)
                    (cons (fn2-arm-frame-entry-kids e world) lemma))))))))
(defun fn2-dc-todo (fns kind world acc fuel)
  ; the functions under FNS that return the core and have no KIDS contract, callees first
  (declare (xargs :mode :program))
  (cond ((or (zp fuel) (atom fns)) acc)
        ((or (member-eq (car fns) acc) (not (fn2-arm-frame-corep-fn (car fns) world)) (fn2-dc-entry (car fns) kind world))
         (fn2-dc-todo (cdr fns) kind world acc fuel))
        (t (fn2-dc-todo (cdr fns) kind world
                        (append (fn2-dc-todo (fn2-arm-frame-body-callees (car fns) world) kind world acc (1- fuel))
                                (list (car fns)))
                        fuel))))
(defun fn2-dc-callees (fns kind world set lemmas)
  ; (mv children lemmas missing): the callees' contracts, or the first callee without one
  (declare (xargs :mode :program))
  (cond ((atom fns) (mv set lemmas nil))
        ((not (fn2-arm-frame-corep-fn (car fns) world)) (fn2-dc-callees (cdr fns) kind world set lemmas))
        (t (let ((d (fn2-dc-entry (car fns) kind world)))
             (if (null d) (mv set lemmas (car fns))
               (fn2-dc-callees (cdr fns) kind world (union-equal (car d) set) (cons (cdr d) lemmas)))))))
(defun fn2-dc-form (fn kind world)
  (declare (xargs :mode :program))
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
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons `(make-event (fn2-dc-form ',(car fns) ',kind (w state))) (fn2-dc-forms (cdr fns) kind))))
(defun fn2-dc-names (fns kind world)
  (declare (xargs :mode :program))
  (cond ((atom fns) nil)
        ((assoc-equal (cons kind (car fns)) (table-alist 'fn2-dc-kids world))
         (cons (fn2-dc-name kind (car fns)) (fn2-dc-names (cdr fns) kind world)))
        (t (fn2-dc-names (cdr fns) kind world))))
(defun fn2-dc-disable-form (fns kind world)
  (declare (xargs :mode :program))
  (let ((names (fn2-dc-names fns kind world)))
    (if names `(in-theory (disable ,@names)) '(value-triple :none))))
;; The children whose writers in FNS's closure the footprint names beyond
;; ALLOWED: (child . the functions with a contract that change it directly).
(defun fn2-dc-writers (fns kind world allowed seen acc fuel)
  (declare (xargs :mode :program))
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
  (declare (xargs :mode :program))
  (cond ((atom children) nil)
        ((equal k m) (fn2-ctf-dir-update-runes (cdr children) (+ 1 k) m))
        (t (list* (fn2-columns-pre "FN2-CTF-DIR-OF-" (fn2-columns-pre "UPDATE-" (caar children)))
                  (fn2-columns-pre "FN2-CTF-MACHINES-OF-" (fn2-columns-pre "UPDATE-" (caar children)))
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
     ((let ((d (fn2-dc-entry fn kind world))) (and d (not (member m (car d)))))
      ; a KIDS contract off the directory (the dispatch frame's, below)
      (let ((d (fn2-dc-entry fn kind world)))
        `((defthm ,name ,stmt
            :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                     :use ((:instance ,(cdr d) (fn2-arm-free ',(car d)) (fn2-arm-c0 fn2-core))
                           (:instance fn2-arm-kids-nth (i 0) (k ,m) (free ',(car d)) (a fn2-core) (b ,out))
                           (:instance fn2-ctf-dir-of-nth (b ,out) (x fn2-core) (a fn2-ctf-c0)))))))))
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
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons `(make-event (value (cons 'progn (fn2-ctf-dir-event ',(car fns) ',kind (w state)))))
          (fn2-ctf-dir-forms (cdr fns) kind))))

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
  (declare (xargs :mode :program))
  (and (consp holds) (or (member-eq class (cdar holds)) (fn2-dispatch-holds-p class (cdr holds)))))
(defun fn2-dispatch-frame-children (name world)
  (declare (xargs :mode :program))
  (fn2-arm-frame-indices
   (if (fn2-dispatch-holds-p :batch-membership (fn2-machine-property name :holds world))
       (strip-cars (fn2-arm-frame-children-of world))
     (set-difference-eq (strip-cars (fn2-arm-frame-children-of world)) *fn2-dispatch-commit-children*))
   world))
(defun fn2-dc-nth-keeps (ks out)
  (declare (xargs :mode :program))
  (if (atom ks) nil (cons `(equal (nth ,(car ks) ,out) (nth ,(car ks) fn2-core)) (fn2-dc-nth-keeps (cdr ks) out))))
;; The commit layer's durability children a function's KIDS contract (S,
;; LEMMA) leaves: FN-KEEPS-COMMIT, their values unchanged.
(defun fn2-dc-keeps-commit-uses (ks s lemma out)
  (declare (xargs :mode :program))
  (if (atom ks) nil
    (cons `(:instance fn2-arm-kids-nth (i 0) (k ,(car ks)) (free ',s) (a fn2-core) (b ,out))
          (fn2-dc-keeps-commit-uses (cdr ks) s lemma out))))
(defun fn2-dc-keeps-commit-event (fn s lemma world)
  (declare (xargs :mode :program))
  (let* ((out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (ks (set-difference-equal (fn2-arm-frame-indices *fn2-dispatch-commit-children* world) s)))
    (if (atom ks) '(value-triple :none)
      `(defthm ,(fn2-columns-sym fn "-KEEPS-COMMIT")
         (and ,@(fn2-dc-nth-keeps ks out))
         :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                  :use ((:instance ,lemma (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                        ,@(fn2-dc-keeps-commit-uses ks s lemma out))))))))
(defun fn2-dc-keeps-commit-form (fn kind world)
  (declare (xargs :mode :program))
  (let ((d (fn2-dc-entry fn kind world)))
    (if d (fn2-dc-keeps-commit-event fn (car d) (cdr d) world)
      (er hard 'fn2-dispatch-frame "~x0 has no KIDS contract." fn))))

;; A stub's frame claims for G (the stub in its constraint, or its default):
;; KIDS at the kind's frame children E, and CTF-DIR; G's body is BODY-FN's
;; call, whose -DC-KIDS (under no kind) and -CTF-DIR contracts prove them.
(defun fn2-dispatch-claims (g formals pos e body-fn)
  (declare (xargs :mode :program))
  (let ((out `(mv-nth ,pos (,g ,@formals))))
    `((defthm ,(fn2-columns-sym g "-ARM-KIDS")
        (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',e fn2-arm-free))
                 (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,out))
        :hints (("Goal" :in-theory (union-theories '(,g ,(fn2-dc-name nil body-fn)) (theory 'fn2-arm-frame-base)))))
      (defthm ,(fn2-ctf-dir-name g)
        (implies (fn2-ctf-dir fn2-core fn2-ctf-c0) (fn2-ctf-dir ,out fn2-ctf-c0))
        :hints (("Goal" :in-theory (union-theories '(,g ,(fn2-ctf-dir-name body-fn)) (theory 'fn2-arm-frame-base))))))))
(defun fn2-dispatch-stub-events (names world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let* ((name (car names))
           (run (fn2-columns-sym name "-RUN")))
      (if (function-symbolp run world)
          (fn2-dispatch-stub-events (cdr names) world)
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
              ,@(fn2-dispatch-claims obs-stub obs-formals 1 eo 'fn2-machine-refuse-observation))
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
             ,@(fn2-dispatch-claims obs-def obs-formals 1 eo 'fn2-machine-refuse-observation)
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
                                 ,(fn2-columns-sym obs-def "-ARM-KIDS") ,(fn2-ctf-dir-name obs-def))))
           (fn2-dispatch-stub-events (cdr names) world)))))))

;; THE ATTACHMENTS (assembly-attach.lisp, after the kinds' implementations):
;; each kind's run and observe functions get footprint contracts (callees
;; first, under the kind), the footprint is checked within the stub's frame
;; (an attachment changing a child outside it is refused, naming the child
;; and the functions whose contracts change it), the directory contracts
;; follow, and the stub's frame claims are proved of the attachment before
;; its defattach.
(defun fn2-dispatch-attach-check (name fn e state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((world (w state)) (d (fn2-dc-entry fn name world)))
    (cond ((null d) (er soft 'fn2-dispatch-frame "The attachment ~x0 of ~x1 has no KIDS contract." fn name))
          ((set-difference-equal (car d) e)
           (mv-let (seen writers) (fn2-dc-writers (list fn) name world e nil nil 64)
             (declare (ignore seen))
             (er soft 'fn2-dispatch-frame
                 "The attachment ~x0 of ~x1's stub changes the children ~x2 outside the kind's dispatch frame ~x3; the contracts that change them: ~x4."
                 fn name (set-difference-equal (car d) e) e writers)))
          (t (value '(value-triple :within-frame))))))
(defun fn2-dispatch-attach-kids (fn pos formals e name world)
  (declare (xargs :mode :program))
  (let ((d (fn2-dc-entry fn name world)) (out `(mv-nth ,pos (,fn ,@formals))))
    `(defthm ,(fn2-columns-sym fn "-DISPATCH-KIDS")
       (implies (and (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 fn2-core) (subsetp-equal ',e fn2-arm-free))
                (fn2-arm-kids 0 fn2-arm-free fn2-arm-c0 ,out))
       :hints (("Goal" :in-theory (union-theories '(,(cdr d)) (theory 'fn2-arm-frame-base)))))))
(defun fn2-dispatch-attach-events (names world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let* ((name (car names))
           (run (fn2-columns-sym name "-RUN"))
           (run-stub (fn2-columns-sym name "-RUN-STUB"))
           (obs (fn2-columns-col-name 'fn2-machine-observe name))
           (obs-stub (fn2-columns-col-name 'fn2-machine-observe (fn2-columns-sym name "-STUB")))
           (e (fn2-dispatch-frame-children name world)))
      (if (and (function-symbolp run world) (function-symbolp run-stub world))
          (append
           `((make-event (value (cons 'progn (fn2-dc-forms (fn2-dc-todo '(,run ,obs) ',name (w state) nil 64) ',name))))
             (make-event (fn2-dispatch-attach-check ',name ',run ',e state))
             (make-event (fn2-dispatch-attach-check ',name ',obs ',e state))
             (make-event (value (cons 'progn (fn2-ctf-dir-forms (fn2-ctf-postorder-new '(,run ,obs) (w state)) ',name))))
             (make-event (value (fn2-dispatch-attach-kids ',run 4 '(id budget fn2-core) ',e ',name (w state))))
             (make-event (value (fn2-dispatch-attach-kids ',obs 1 '(id event outcome reason count aux0 aux1 fn2-core) ',e ',name (w state))))
             (defattach (,run-stub ,run)
                        (,obs-stub ,obs)
                        (,(fn2-columns-sym name "-ARM-CHARGE-OK-P-STUB") ,(fn2-columns-sym name "-ARM-CHARGE-OK-P"))
                        (,(fn2-columns-sym name "-ARM-BOUND-STUB") ,(fn2-columns-sym name "-ARM-BOUND")))
             (in-theory (disable ,(fn2-columns-sym run "-DISPATCH-KIDS") ,(fn2-columns-sym obs "-DISPATCH-KIDS")))
             (make-event (fn2-dc-disable-form (fn2-ctf-postorder-new '(,run ,obs) (w state)) ',name (w state))))
           (fn2-dispatch-attach-events (cdr names) world))
        (fn2-dispatch-attach-events (cdr names) world)))))
(defmacro fn2-dispatch-attach-all-events ()
  '(make-event (value (cons 'progn (fn2-dispatch-attach-events (fn2-machine-names (w state)) (w state))))))

(fn2-resolve :callbacks)
;; the stubs' default bodies' contracts, then the stubs
(make-event
 (value (cons 'progn (append (fn2-dc-forms (fn2-dc-todo '(fn2-machine-refuse-phase fn2-machine-refuse-observation fn2-machine-idle) nil (w state) nil 64) nil)
                             (fn2-ctf-dir-forms (fn2-ctf-postorder-new '(fn2-machine-refuse-phase fn2-machine-refuse-observation fn2-machine-idle) (w state)) nil)
                             '((make-event (value (fn2-dc-keeps-commit-form 'fn2-machine-refuse-phase nil (w state))))
                               (make-event (value (fn2-dc-keeps-commit-form 'fn2-machine-refuse-observation nil (w state))))
                               (make-event (value (fn2-dc-keeps-commit-form 'fn2-machine-idle nil (w state)))))))))
(make-event
 (value (cons 'progn (fn2-dispatch-stub-events (fn2-machine-names (w state)) (w state)))))
(make-event
 (value (cons 'progn (fn2-machine-observe-events 'fn2-machine-observe (fn2-machine-names (w state)) (w state)))))
(make-event
 (value (cons 'progn (fn2-machine-all-observe-rows (fn2-machine-names (w state)) (w state)))))
(make-event
 (value `(progn
           (defun fn2-machine-arm-charge-ok-p (kind phase bytes steps descriptors)
             (declare (xargs :guard t))
             (case kind ,@(fn2-machine-arm-certificate-arms (fn2-machine-names (w state)) 0 nil (w state))
               (otherwise nil)))
           (defun fn2-machine-arm-bound (kind phase)
             (declare (xargs :guard t))
             (case kind ,@(fn2-machine-arm-certificate-arms (fn2-machine-names (w state)) 0 t (w state))
               (otherwise 0))))))
(make-event
 (value `(defun fn2-machine-run (id budget fn2-core)
           (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
           (if (not (eq (fn2-machine-stopped-read-code id fn2-core) :ok))
               (fn2-machine-refuse-phase id fn2-core)
             (if (equal (fn2-machine-stopped id fn2-core) 1)
               (fn2-machine-idle id fn2-core)
             (case (fn2-machine-kind id fn2-core)
               ,@(fn2-machine-run-arms (fn2-machine-names (w state)) 0 (w state))
               (otherwise (fn2-machine-refuse-phase id fn2-core))))))))
(fn2-core-preserves fn2-machine-run (id budget fn2-core) :position 4 :rows nil)
(assert-event
 (fn2-assert-compliant-p
  '(fn2-machine-observe fn2-machine-run fn2-machine-take-wake
    fn2-listener-run-accepting fn2-listener-run-admitting fn2-listener-run-closing fn2-machine-admit
    fn2-echo-run-command fn2-echo-run-reply fn2-echo-run-draining fn2-machine-grant-one fn2-machine-park)
  (w state)))
(fn2-resolve :dispatch)
