; One carrier-parameterised emitter, below columns and machines.
(in-package "ACL2")
(include-book "declare")

(defun fn2-operation-find (name rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (or (cdr (assoc-eq name (fn2-decl-get :callbacks (cdar rows))))
        (fn2-operation-find name (cdr rows)))))
(defun fn2-operation-row (name world)
  (declare (xargs :verify-guards nil))
  (fn2-operation-find name (fn2-decl-all-rows world)))
(defun fn2-operation-register (owner name row events world)
  (declare (xargs :verify-guards nil))
  (let* ((row (if (eq (fn2-decl-get :returns row) :infer)
                   (fn2-decl-set :returns (getpropc name 'stobjs-out nil world) row) row))
         (old (fn2-decl-row owner world))
         (manifest (fn2-decl-manifests events :exported world))
         (artifact (fn2-decl-find-artifact name manifest)))
    `(table ,(fn2-decl-table (car owner)) ',(cadr owner)
       ',(fn2-decl-set :generated
           (append (list (list* (car artifact) name
                          (fn2-decl-set :section (fn2-decl-get :section row) (cddr artifact))))
                   (fn2-decl-get :generated old))
           (fn2-decl-set :callbacks
             (acons name row (fn2-decl-get :callbacks old)) old)))))
(defun fn2-operation-reuse (owner name world)
  (declare (xargs :verify-guards nil))
  (let ((row (fn2-decl-row owner world)))
    `(table ,(fn2-decl-table (car owner)) ',(cadr owner)
       ',(fn2-decl-set :reuse (cons (list :callback name) (fn2-decl-get :reuse row)) row))))
(defun fn2-operation-events (owner name carrier args returns row-vars section declaration body laws contracts)
  (declare (xargs :verify-guards nil))
  (let* ((formals (append args row-vars (list carrier)))
         (events `((defun ,name ,formals ,declaration ,@body) ,@laws))
         (row (list :args args :declared-returns returns :returns returns :row-bindings row-vars
                    :calling-convention formals :carrier carrier :owner owner
                    :writes (or (fn2-decl-get :writes contracts) :unchecked)
                    :cost (or (fn2-decl-get :cost contracts) :unchecked)
                    :refusal (or (fn2-decl-get :refusal contracts) :unchecked)
                    :contract (fn2-decl-get :contract contracts)
                    :cost-values (fn2-decl-get :cost-values contracts)
                    :section section :definition events)))
    `(make-event
      (let ((old (fn2-operation-row ',name (w state))))
        (cond ((not (fn2-decl-row ',owner (w state)))
               (er soft 'fn2-operation "Missing operation owner ~x0 for ~x1." ',owner ',name))
              (old (if (equal (fn2-decl-set :returns ',returns old) ',row) (value (fn2-operation-reuse ',owner ',name (w state)))
                     (er soft 'fn2-operation "Conflicting callback ~x0." ',name)))
              ((fn2-decl-conflicts ',events (fn2-decl-all-rows (w state)) (w state))
               (er soft 'fn2-operation "Conflicting definition ~x0." ',name))
              (t (value '(progn ,@events
                   (make-event
                    (value (fn2-operation-register ',owner ',name ',row ',events (w state))))))))))))
(defmacro fn2-defoperation (owner section returns definition)
  (let* ((formals (caddr definition)) (carrier (car (last formals))))
    (fn2-operation-events owner (cadr definition) carrier (butlast formals 1)
      returns nil section (cadddr definition) (cddddr definition) nil nil)))

; Shared guard-status check for declared exports.
(defun fn2-assert-compliant-p (names world)
  (declare (xargs :guard (and (symbol-listp names) (plist-worldp world))))
  (if (endp names) t
    (and (eq (symbol-class (car names) world) :common-lisp-compliant)
         (fn2-assert-compliant-p (cdr names) world))))

; Semantic code families have no resident table. Explicit values preserve sparse
; ABI tags and flag masks; every generated constant belongs to this manifest.
(defun fn2-code-constants (prefix entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons `(defconst ,(intern-in-package-of-symbol
                        (concatenate 'string "*" (symbol-name prefix) "-"
                                     (symbol-name (caar entries)) "*") prefix)
             ,(cadar entries))
          (fn2-code-constants prefix (cdr entries)))))
(defun fn2-code-families (families)
  (declare (xargs :verify-guards nil))
  (if (atom families) nil
    (append (fn2-code-constants (caar families) (cdar families))
            (fn2-code-families (cdr families)))))
(defun fn2-code-enums (families)
  (declare (xargs :verify-guards nil))
  (if (atom families) nil
    (cons (cons (caar families) (remove-assoc-equal :count (cdar families)))
          (fn2-code-enums (cdr families)))))
(make-event
 (let ((families
        '((fn2-trace-kind (:mailbox 0) (:machine 1) (:service 2) (:clock 3) (:signal 4)
                           (:machine-start 5) (:enqueue 6) (:count 7))
          (fn2-visit (:principal 0) (:commit 1) (:timer 2) (:notification 3) (:maintenance 4) (:none 255))
          (fn2-clock-flag (:realtime-valid 1) (:realtime-negative 2) (:backward 4) (:malformed 8) (:input-mask 3) (:error-mask 12))
          (fn2-work (:empty 1) (:poll 2) (:state 4) (:refusal 6) (:mailbox 8) (:small 12) (:advance 16) (:release 20) (:transition 24) (:stage 32))
          (fn2-calendar (:principals-per-group 16) (:services 4) (:group-size 20))
          (fn2-format (:sector-bytes 4096) (:magic 843990611) (:version-offset 4) (:address-offset 8)
            (:sequence-offset 12) (:checksum-offset 16) (:payload-offset 20) (:word-bytes 4))
          (fn2-scribe (:chunk-bytes 16))
          (fn2-fnv (:offset-basis 2166136261) (:prime 16777619))
          (fn2-record (:clock 256) (:advance 257) (:client-drain 258) (:wake 259) (:death 260)))))
   (value (fn2-declare '(:operation-set fn2-codes) (list :enums (fn2-code-enums families)) nil
                      (fn2-code-families families)))))
(defconst *fn2-none* 4294967295)
(defconst *fn2-u60-max* 1152921504606846975)
(defconst *fn2-no-deadline* *fn2-u60-max*)

; ----------------------------------------------------------------------
; Logical transport over a common finite domain (pointwise-contracts). These
; traversals are proof machinery, not allocations on a served path. Functional
; instances discharge locality; the constrained functions introduce no system
; assumption.
(encapsulate
 (((fn2-pw-point * * *) => *)
  ((fn2-pw-step * * * * *) => *)
  ((fn2-pw-affected * * * * * *) => *))
 (local (defun fn2-pw-point (key g c) (declare (ignore key g c)) t))
 (local (defun fn2-pw-step (delta g a h b)
          (declare (ignore delta g a h b)) t))
 (local (defun fn2-pw-affected (key delta g a h b)
          (declare (ignore key delta g a h b)) nil))
 (defthm fn2-pw-off-footprint
   (implies (and (fn2-pw-step delta g a h b)
                 (not (fn2-pw-affected key delta g a h b))
                 (fn2-pw-point key g a))
            (fn2-pw-point key h b))
   :rule-classes nil))

(defun fn2-pw-all (keys g c)
  (if (atom keys) t
    (and (fn2-pw-point (car keys) g c) (fn2-pw-all (cdr keys) g c))))
(defun fn2-pw-repaired (keys delta g a h b)
  (if (atom keys) t
    (and (or (not (fn2-pw-affected (car keys) delta g a h b))
             (fn2-pw-point (car keys) h b))
         (fn2-pw-repaired (cdr keys) delta g a h b))))
(defthm fn2-pw-transport
  (implies (and (fn2-pw-all keys g a)
                (fn2-pw-step delta g a h b)
                (fn2-pw-repaired keys delta g a h b))
           (fn2-pw-all keys h b))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-pw-all keys g a))
          ("Subgoal *1/2" :use ((:instance fn2-pw-off-footprint (key (car keys)))))))

; The bounded range is [start,start+count). No proper-list or duplicate-free
; hypothesis is needed: all traversals use exactly the same domain.
(defun fn2-pw-range (start count g c)
  (declare (xargs :measure (nfix count)))
  (if (zp count) t
    (and (fn2-pw-point start g c)
         (fn2-pw-range (+ 1 start) (- count 1) g c))))
(defun fn2-pw-range-repaired (start count delta g a h b)
  (declare (xargs :measure (nfix count)))
  (if (zp count) t
    (and (or (not (fn2-pw-affected start delta g a h b))
             (fn2-pw-point start h b))
         (fn2-pw-range-repaired (+ 1 start) (- count 1) delta g a h b))))
(defthm fn2-pw-range-transport
  (implies (and (fn2-pw-range start count g a)
                (fn2-pw-step delta g a h b)
                (fn2-pw-range-repaired start count delta g a h b))
           (fn2-pw-range start count h b))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-pw-range start count g a))
          ("Subgoal *1/2" :use ((:instance fn2-pw-off-footprint (key start))))))

; Independent constraints: predicate instances need not prove a fold law.
; The affected set is evaluated with BOTH endpoints and held fixed for the
; two sums. This also permits transitions which change ghost context.
(encapsulate
 (((fn2-fold-value * * *) => *)
  ((fn2-fold-step * * * * *) => *)
  ((fn2-fold-affected * * * * * *) => *))
 (local (defun fn2-fold-value (key g c) (declare (ignore key g c)) 0))
 (local (defun fn2-fold-step (delta g a h b)
          (declare (ignore delta g a h b)) t))
 (local (defun fn2-fold-affected (key delta g a h b)
          (declare (ignore key delta g a h b)) nil))
 (defthm fn2-fold-value-numberp
   (acl2-numberp (fn2-fold-value key g c)) :rule-classes :type-prescription)
 (defthm fn2-fold-off-footprint
   (implies (and (fn2-fold-step delta g a h b)
                 (not (fn2-fold-affected key delta g a h b)))
            (equal (fn2-fold-value key h b) (fn2-fold-value key g a)))
   :rule-classes nil))
(defun fn2-fold-all (keys g c)
  (if (atom keys) 0
    (+ (fn2-fold-value (car keys) g c) (fn2-fold-all (cdr keys) g c))))
(defun fn2-fold-touched (keys delta g a h b context core)
  (if (atom keys) 0
    (+ (if (fn2-fold-affected (car keys) delta g a h b)
           (fn2-fold-value (car keys) context core) 0)
       (fn2-fold-touched (cdr keys) delta g a h b context core))))
(defthm fn2-fold-replacement
  (implies (fn2-fold-step delta g a h b)
           (equal (+ (fn2-fold-all keys h b)
                     (fn2-fold-touched keys delta g a h b g a))
                  (+ (fn2-fold-all keys g a)
                     (fn2-fold-touched keys delta g a h b h b))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-fold-all keys g a))
          ("Subgoal *1/2" :use ((:instance fn2-fold-off-footprint (key (car keys)))))))
(defun fn2-fold-range (start count g c)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (fn2-fold-value start g c) (fn2-fold-range (+ 1 start) (- count 1) g c))))
(defun fn2-fold-range-touched (start count delta g a h b context core)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (if (fn2-fold-affected start delta g a h b)
           (fn2-fold-value start context core) 0)
       (fn2-fold-range-touched (+ 1 start) (- count 1) delta g a h b context core))))
(defthm fn2-fold-range-replacement
  (implies (fn2-fold-step delta g a h b)
           (equal (+ (fn2-fold-range start count h b)
                     (fn2-fold-range-touched start count delta g a h b g a))
                  (+ (fn2-fold-range start count g a)
                     (fn2-fold-range-touched start count delta g a h b h b))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-fold-range start count g a))
          ("Subgoal *1/2" :use ((:instance fn2-fold-off-footprint (key start))))))

; A semantic locality law may already cover every key (including affected
; keys repaired by the transition). Declare its conjunction lift without
; repeating functional-instantiation plumbing. LOCALITY is a theorem or
; instance using KEY, DELTA, G, A, H, B; OPEN contains only point adapters.
(defmacro fn2-pw-lift-locality (name &key point all step locality open)
  `(defthm ,name
     (implies (and (,all keys g a) (,step delta g a h b))
              (,all keys h b))
     :rule-classes nil
     :hints (("Goal"
              :use ((:functional-instance fn2-pw-transport
                      (fn2-pw-point ,point) (fn2-pw-all ,all) (fn2-pw-step ,step)
                      (fn2-pw-affected (lambda (key delta g a h b) nil))
                      (fn2-pw-repaired (lambda (keys delta g a h b) t))))
              :in-theory '(,all ,@open) :do-not-induct t)
             ; ACL2 omits previously discharged functional constraints.
             ("Subgoal 2" :use ,locality)
             ("Subgoal 1" :use ,locality))))
