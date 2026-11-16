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

; A requested extra-array LENGTH observer across this table's column setters.
; This is one linear family for the requested observer, not a field matrix.
(defun fn2-columns-array-length-column-frames (table observer columns world)
 (declare (xargs :verify-guards nil))
 (if (atom columns) nil
  (let* ((writer (fn2-columns-col-name table (fn2-columns-pre "SET-" (caar columns))))
         (frame (fn2-columns-sym writer "-NTH"))
         (name (fn2-columns-sym observer
                 (concatenate 'string "-AFTER-" (symbol-name writer)))))
   (if (not (and (getpropc writer 'unnormalized-body nil world)
                 (not (eq (getpropc writer 'symbol-class nil world) :program))
                 (equal (getpropc writer 'stobjs-in :missing world) (list nil nil table))
                 (equal (getpropc writer 'stobjs-out :missing world) (list table))
                 (getpropc frame 'theorem nil world)))
       (er hard 'fn2-columns-array-length-column-frames
           "Missing actual setter-NTH interface for ~x0." writer)
    (cons
     `(defthm ,name
       (equal (,observer (,writer i v ,table)) (,observer ,table))
       :hints (("Goal" :in-theory (e/d (,observer ,frame) (,writer nth)))))
     (fn2-columns-array-length-column-frames table observer (cdr columns) world))))))

(defun fn2-columns-array-length-frame-events (table field world)
 (declare (xargs :verify-guards nil))
 (let* ((row (fn2-decl-row (list :columns table) world))
        (extra (assoc-eq field (fn2-decl-get :extra-fields row)))
        (observer (fn2-columns-sym field "-LENGTH")))
  (if (not (and extra (fn2-columns-arrayp extra)
                (not (assoc-eq field (fn2-decl-get :columns row)))
                (getpropc observer 'unnormalized-body nil world)
                (not (eq (getpropc observer 'symbol-class nil world) :program))
                (equal (getpropc observer 'stobjs-in :missing world) (list table))
                (equal (getpropc observer 'stobjs-out :missing world) '(nil))))
      (er hard 'fn2-columns-array-length-frame-events
          "No actual extra-array LENGTH observer for ~x0 in ~x1." field table)
   `(progn ,@(fn2-columns-array-length-column-frames
               table observer (fn2-decl-get :columns row) world)))))

(defmacro defcolumns-array-length-frames (table field)
 `(make-event
   (value (fn2-columns-array-length-frame-events ',table ',field (w state)))))
