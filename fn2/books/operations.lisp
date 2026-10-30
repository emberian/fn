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
        '((fn2-trace-kind (:mailbox 0) (:machine 1) (:service 2) (:clock 3) (:signal 4) (:count 5))
          (fn2-visit (:principal 0) (:commit 1) (:timer 2) (:notification 3) (:maintenance 4) (:none 255))
          (fn2-clock-flag (:realtime-valid 1) (:realtime-negative 2) (:backward 4) (:malformed 8) (:input-mask 3) (:error-mask 12))
          (fn2-work (:empty 1) (:poll 2) (:state 4) (:refusal 6) (:mailbox 8) (:small 12) (:advance 16) (:release 20) (:transition 24) (:stage 32))
          (fn2-calendar (:principals-per-group 16) (:services 4) (:group-size 20))
          (fn2-format (:sector-bytes 4096) (:magic 843990611) (:version-offset 4) (:address-offset 8)
            (:sequence-offset 12) (:checksum-offset 16) (:payload-offset 20) (:word-bytes 4))
          (fn2-scribe (:chunk-bytes 16))
          (fn2-fnv (:offset-basis 2166136261) (:prime 16777619))
          (fn2-record (:clock 256) (:advance 257) (:client-drain 258) (:wake 259) (:death 260))
          (fn2-fault (:fragment 0) (:short-send 1) (:delay 2) (:reset 3) (:half-open 4) (:nonreading 5)
            (:read-io 6) (:bitrot 7) (:misread 8) (:miswrite 9) (:lying-flush 10) (:tear 11)
            (:no-space 12) (:dead 13) (:fail-slow 14) (:crash 15) (:monotonic-jump 16)
            (:realtime-back 17) (:duplicate 18) (:stale 19) (:forged 20) (:overcount 21)
            (:malformed 22) (:flush-io 23) (:short-write 24) (:release-order 25) (:none 26) (:count 26)))))
   (value (fn2-declare '(:operation-set fn2-codes) (list :enums (fn2-code-enums families)) nil
                      (fn2-code-families families)))))
(defconst *fn2-none* 4294967295)
(defconst *fn2-u60-max* 1152921504606846975)
(defconst *fn2-no-deadline* *fn2-u60-max*)
