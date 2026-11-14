; Observation payloads cannot create operation incarnations.
(in-package "ACL2")
(include-book "ops-issued-lifecycle")

; Derive the writer theory from the column declaration. The common footprint
; lemmas inspect only generation/phase; no per-reader/per-writer matrix is needed.
(defun fn2-issued-payload-column-writers (cols)
 (declare (xargs :verify-guards nil))
 (if (atom cols) nil
  (let* ((field (caar cols)) (reader (fn2-columns-col-name 'fn2-ops field)))
   (append
    (and (not (member-eq field '(gen phase)))
         (list (fn2-columns-col-name 'fn2-ops (fn2-columns-pre "SET-" field))
               (fn2-columns-pre "UPDATE-" (fn2-columns-sym reader "$AI"))))
    (fn2-issued-payload-column-writers (cdr cols))))))
(defun fn2-issued-extra-writers (fields)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (cons (fn2-columns-pre "UPDATE-"
          (if (fn2-columns-arrayp (car fields))
              (fn2-columns-sym (caar fields) "I") (caar fields)))
        (fn2-issued-extra-writers (cdr fields)))))
(defun fn2-issued-payload-frame-events (entries writers world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((fn (caar entries)) (position (cadar entries))
         (call (cons fn (getpropc fn 'formals nil world)))
         (out (if position `(mv-nth ,position ,call) call)))
   (append
    `((defthm ,(fn2-columns-sym fn "-ISSUED-COUNT")
      (equal (fn2-ops-issued-count n ,out) (fn2-ops-issued-count n fn2-ops))
      :hints (("Goal" :in-theory (e/d (,fn ,@writers)
       (fn2-ops-issued-count fn2-op-issued-weight update-nth update-nth-array
        fn2-ops-rows fn2-opsp fn2-ops-wfp fn2-post-eligiblep fn2-post-payloadp
        fn2-op-handle-code fn2-op-slotp binary-logior binary-logand)))))
      (defthm ,(fn2-columns-sym fn "-ISSUED-TOTAL")
       ,(fn2-run-issued-claim 0 'fn2-ops out)
       :hints (("Goal" :in-theory (disable ,fn fn2-ops-issued-count fn2-ops-rows)))))
    (fn2-issued-payload-frame-events (cdr entries) writers world)))))
(make-event
 (let* ((schema (cdr (assoc-eq 'fn2-ops (fn2-decl-rows :columns (w state)))))
        (writers (append (fn2-issued-payload-column-writers (fn2-decl-get :columns schema))
                         (fn2-issued-extra-writers (fn2-decl-get :extra-fields schema)))))
  (value (cons 'progn (fn2-issued-payload-frame-events
   '((fn2-count-stray nil) (fn2-post-result nil) (fn2-post-accept-result nil)
     (fn2-op-request-cancel 1) (fn2-post-clock nil) (fn2-take-clock 4)
     (fn2-post-signal nil) (fn2-take-signal 1) (fn2-ops-latch-peer nil))
   writers (w state))))))
