; One evaluator for both generated families, over every declared B layout.
(in-package "ACL2")
(include-book "format-roundtrip")
(include-book "layout-roundtrip")

(make-event
 (value `(progn ,@(fn2-layout-test-dispatch-events
                  'fn2-layout-teeth-codec (table-alist 'fn2-layouts (w state))
                  '(:encode :decode :roundtrip-hyps)))))
(defun fn2-layout-teeth-layouts (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (cadr (member-eq :layout (cdar entries)))
          (fn2-layout-teeth-layouts (cdr entries)))))
(make-event
 (value `(defconst *fn2-layout-teeth-layouts*
           ',(fn2-layout-teeth-layouts (table-alist 'fn2-layouts (w state))))))

(defun fn2-layout-teeth-values (layout)
  (declare (xargs :verify-guards nil))
  (if (atom layout) nil
    (let ((kind (cadar layout)))
      (cons (cond ((eq kind :digest) (cons 1 (make-list 32 :initial-element 42)))
                  ((eq kind :bool) 1)
                  ((and (consp kind) (eq (car kind) :enum)) 0)
                  ((and (consp kind) (eq (car kind) :zero)) nil)
                  ((and (consp kind) (member-eq (car kind) '(:octets :octets16 :octets32)))
                   (make-list (min 3 (cadr kind)) :initial-element 42))
                  (t 42))
            (fn2-layout-teeth-values (cdr layout))))))

(defun fn2-layout-teeth-one (layout fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
  (b* ((values (fn2-layout-teeth-values layout))
       ((mv fn2-fields fn2-pool) (fn2-layout-test-put layout values 0 0 fn2-fields fn2-pool))
       (hyp (fn2-layout-teeth-codec-roundtrip-hyps layout 0 0 1 0 1 0 1 fn2-fields fn2-pool))
       ((mv ec end fn2-pool) (fn2-layout-teeth-codec-encode layout 0 0 1 0 1 0 1 fn2-fields fn2-pool))
       ; Save the canonical premise before decoding, exactly as registered.
       (shape (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
                   (fn2-pool-semanticp fn2-pool) (natp 0)
                   (<= (len layout) (fn2-fields-rows fn2-fields))))
       ((mv code next fn2-fields) (fn2-layout-teeth-codec-decode layout 0 0 1 0 end 1 0 1 fn2-fields fn2-pool))
       (after (fn2-layout-test-values layout 0 fn2-fields fn2-pool))
       (bytes (fn2-layout-test-read next 0 0 fn2-pool)))
    (mv (and hyp (eq ec :ok)
             (fn2-layout-roundtrip-resultp layout values code next end after bytes)
             shape (eq code :ok) (fn2-layout-canonical-resultp layout after bytes))
        fn2-fields fn2-pool)))
(defun fn2-layout-teeth-all (layouts fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
  (if (atom layouts) (mv t fn2-fields fn2-pool)
    (mv-let (ok fn2-fields fn2-pool) (fn2-layout-teeth-one (car layouts) fn2-fields fn2-pool)
      (if (not ok) (mv nil fn2-fields fn2-pool)
        (fn2-layout-teeth-all (cdr layouts) fn2-fields fn2-pool)))))
(defun fn2-layout-generated-teeth ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (ok fn2-fields)
      (with-local-stobj fn2-pool
        (mv-let (ok fn2-fields fn2-pool)
          (b* (((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool))
               (fn2-fields (fn2-fields-init 128 fn2-fields))
               ((mv all fn2-fields fn2-pool) (fn2-layout-teeth-all *fn2-layout-teeth-layouts* fn2-fields fn2-pool))
               ; Family hypothesis removals call the generated exports too.
               ((mv rt fn2-fields fn2-pool) (fn2-layout-test-roundtrip-tooth 256 nil fn2-fields fn2-pool))
               ((mv canon fn2-fields fn2-pool) (fn2-layout-test-canonical-tooth '(170 0) nil fn2-fields fn2-pool)))
            (mv (and all rt canon) fn2-fields fn2-pool))
          (mv ok fn2-fields)))
      ok)))

; Resolve every obligation by its declaration name, never a table position.
(defun fn2-layout-teeth-obligations (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (fn2-codec-symbol (caar entries) "-ROUNDTRIP")
          (cons (fn2-codec-symbol (caar entries) "-CANONICAL")
                (fn2-layout-teeth-obligations (cdr entries))))))
(make-event
 (value `(fn2-assert-owed-teeth
          ,@(fn2-layout-teeth-obligations (table-alist 'fn2-layouts (w state))))))
