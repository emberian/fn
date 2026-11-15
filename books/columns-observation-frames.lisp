; Requested public getter/setter frames, without a quadratic field matrix.
(in-package "ACL2")
(include-book "columns-guard-hints")
(fn2-book-layer :b)

(defun fn2-columns-observation-frame-event (name table read-field write-field world)
 (declare (xargs :verify-guards nil))
 (let* ((columns (fn2-decl-get :columns
                  (fn2-decl-row (list :columns table) world)))
        (reader (fn2-columns-col-name table read-field))
        (raw (fn2-columns-sym reader "$AI"))
        (writer (fn2-columns-col-name table (fn2-columns-pre "SET-" write-field)))
        (frame (fn2-columns-sym writer "-NTH")))
  (if (not (and (symbolp name) name
                (assoc-eq read-field columns) (assoc-eq write-field columns)
                (not (eq read-field write-field))
                (getpropc reader 'unnormalized-body nil world)
                (getpropc writer 'unnormalized-body nil world)
                (not (eq (getpropc reader 'symbol-class nil world) :program))
                (not (eq (getpropc writer 'symbol-class nil world) :program))
                (equal (getpropc reader 'stobjs-in :missing world) (list nil table))
                (equal (getpropc reader 'stobjs-out :missing world) '(nil))
                (equal (getpropc writer 'stobjs-in :missing world) (list nil nil table))
                (equal (getpropc writer 'stobjs-out :missing world) (list table))
                (getpropc frame 'theorem nil world)))
      (er hard 'fn2-columns-observation-frame-event
          "No distinct logical column observation interface for ~x0 / ~x1 in ~x2."
          read-field write-field table)
   ; Different outer fields are unchanged even for malformed tables and
   ; out-of-range row indices. No row, type or enum-cardinality premise.
   `(defthm ,name
      (equal (,reader i (,writer j v ,table)) (,reader i ,table))
      :hints (("Goal" :in-theory (e/d (,reader ,raw ,frame) (,writer nth))))))))

(defmacro defcolumns-observation-frame (name table read-field write-field)
 `(make-event
   (value (fn2-columns-observation-frame-event
           ',name ',table ',read-field ',write-field (w state)))))
