; Layer C: DEFRUNSCHEMA compiles one ordered-run schema: its entry, index-entry
; and run-descriptor layouts through B's DEFLAYOUT and its key order. The
; schema registers through fn2-declare. Nothing else is per schema: the run
; assembly (runs-assemble.lisp) dispatches over every registered schema's
; codecs, and the append, seek, build and lookup are written once over it.
(in-package "ACL2")
(include-book "runs-page")
(fn2-book-layer :c)

(defun fn2-rs-sym (name suffix) (declare (xargs :verify-guards nil)) (fn2-columns-sym name suffix))
(defun fn2-rs-octetsp (kind)
 (declare (xargs :verify-guards nil))
 (or (eq kind :digest)
     (and (consp kind) (eq (car kind) :octets) (natp (cadr kind)) (<= (cadr kind) *fn2-run-key-octets-max*))))
(defun fn2-rs-key-kindp (kind)
 (declare (xargs :verify-guards nil))
 (or (fn2-rs-octetsp kind)
     (member-eq kind '(:u8 :u16 :u32 :u60 :u64 :varint :bool))
     (and (consp kind) (member-eq (car kind) '(:id :enum)))))
(defun fn2-rs-keyp (key)
 (declare (xargs :verify-guards nil))
 (if (atom key) (null key)
  (and (consp (car key)) (fn2-rs-key-kindp (cadar key)) (fn2-rs-keyp (cdr key)))))
(defun fn2-rs-index-layout (key)
 (declare (xargs :verify-guards nil))
 (append key (fn2-format-prefix "CHILD-" *fn2-format-ref*) '((child-entries :varint))))
(defun fn2-rs-run-layout (key)
 (declare (xargs :verify-guards nil))
 (append '((run :varint) (height :u8) (pages :varint) (entries :varint))
         (fn2-format-prefix "MIN-" key) (fn2-format-prefix "MAX-" key)
         (fn2-format-prefix "ROOT-" *fn2-format-ref*) (fn2-format-prefix "FILTER-" *fn2-format-ref*)))

; Key order over two field ranges whose key fields start at ABASE and BBASE,
; read under owners A and B. The entry layout's field indexes are used for
; every layout of the schema, which all start with the key fields.
(defun fn2-rs-compare-body (layout key)
 (declare (xargs :verify-guards nil))
 (if (atom key) '(mv :ok :eq)
  (let ((c (fn2-codec-field layout (caar key))) (rest (fn2-rs-compare-body layout (cdr key))))
   (if (fn2-rs-octetsp (cadar key))
       `(mv-let (code order)
          (fn2-run-octets-field-compare (+ abase ,c) (+ bbase ,c) ak as ag bk bs bg fn2-fields fn2-pool)
          (if (or (not (eq code :ok)) (not (eq order :eq))) (mv code order) ,rest))
     `(let ((order (fn2-run-value-compare (+ abase ,c) (+ bbase ,c) fn2-fields)))
        (if (eq order :eq) ,rest (mv :ok order)))))))

(defun fn2-rs-compare-event (name layout key)
 (declare (xargs :verify-guards nil))
 (let ((n (len key)))
 `(defun ,(fn2-rs-sym name "-COMPARE") (abase bbase ak as ag bk bs bg fn2-fields fn2-pool)
   (declare (ignorable ak as ag bk bs bg fn2-pool))
   (declare (xargs :stobjs (fn2-fields fn2-pool)
    :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp abase) (natp bbase)
                (<= (+ abase ,n) (fn2-fields-rows fn2-fields)) (<= (+ bbase ,n) (fn2-fields-rows fn2-fields)))))
   ,(fn2-rs-compare-body layout key))))

;; The CHILD- fields of an index layout sit right after the key fields, in the
;; ref layout's order, and child-entries follows them; the generic promotion
;; and lookup address them from the key count. Asserted per schema.
(defun fn2-rs-child (index field)
 (declare (xargs :verify-guards nil))
 (fn2-codec-field index (intern-in-package-of-symbol (concatenate 'string "CHILD-" field) 'fn2-rs-child)))
(defun fn2-rs-child-equalities (index nkeys fields)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (cons `(equal ,(fn2-rs-child index (symbol-name (car fields)))
                (+ ,nkeys ,(fn2-codec-field 'fn2-format-ref (car fields))))
        (fn2-rs-child-equalities index nkeys (cdr fields)))))
(defun fn2-rs-shape-assertion (name nkeys)
 (declare (xargs :verify-guards nil))
 (let ((entry (fn2-rs-sym name "-ENTRY")) (index (fn2-rs-sym name "-INDEX")))
 `(assert-event
   (and ,@(fn2-rs-child-equalities index nkeys
            '(storage-domain physical-unit writer-epoch allocation page-kind encoded-length expected-hash))
        (equal ,(fn2-codec-field index 'child-entries) (+ ,nkeys *fn2-format-ref-num-fields*))
        (<= ,(fn2-codec-constant entry "-NUM-FIELDS") *fn2-run-entry-rows*)
        (<= ,(fn2-codec-constant index "-NUM-FIELDS") *fn2-run-entry-rows*)))))

(defun fn2-defrunschema (name id key value merge page-kind)
 (declare (xargs :verify-guards nil))
 (let* ((entry (fn2-rs-sym name "-ENTRY")) (index (fn2-rs-sym name "-INDEX")) (run (fn2-rs-sym name "-RUN"))
        (cmp (fn2-rs-sym name "-COMPARE")) (layout (append key value)))
  (cond ((not (and (symbolp name) (natp id) (consp key) (fn2-rs-keyp key) (fn2-layoutp layout)
                   (<= (len layout) *fn2-run-key-fields-max*)
                   (member-eq merge '(:union :latest :unique))
                   (member-eq page-kind '(:run-data :manifest))))
         `(make-event (er soft 'defrunschema "Malformed run schema ~x0." ',name)))
        (t
         `(progn
           (deflayout ,entry ',layout)
           (deflayout ,index ',(fn2-rs-index-layout key))
           (deflayout ,run ',(fn2-rs-run-layout key))
           ,(fn2-rs-shape-assertion name (len key))
           ,(fn2-declare (list :schema name)
              (list :id id :key key :value value :merge merge :page-kind page-kind
                    :layouts (list entry index run) :compare cmp)
              nil
              (list (fn2-rs-compare-event name entry key))))))))

;; A schema declared after the run assembly would never be dispatched: refused.
(defun fn2-rs-assembled (world)
 (declare (xargs :verify-guards nil))
 (cdr (assoc-eq :schemas (table-alist 'fn2-run-assembly world))))
(defmacro defrunschema (name &key id key value merge (page-kind ':run-data))
 `(progn
   (make-event
    (if (fn2-rs-assembled (w state))
        (er soft 'defrunschema "Schema ~x0 is declared after the run assembly." ',name)
      (value '(value-triple :unassembled))))
   ,(fn2-defrunschema name id key value merge page-kind)))
