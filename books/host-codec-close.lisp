; One live-core closure/cancellation implementation for codec carriers.
(in-package "ACL2")
(include-book "codec-close")
(fn2-book-layer :a)
(defun fn2-codec-host-closure-events (stem transport operation)
 (declare (xargs :verify-guards nil))
 `(progn
  (defcodec-record-closure ,operation ,transport)
(defun ,(fn2-columns-sym stem "-MARK-CLOSED") (op gen ,transport ,operation fn2-core)
 (declare (xargs :stobjs (,transport ,operation fn2-core) :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core) (,(fn2-columns-sym transport "-WFP") ,transport)
              (,(fn2-columns-sym operation "-WFP") ,operation))))
 (mv-let (code kind cap nonce address length) (fn2-host-codec-op op gen fn2-core)
  (declare (ignore kind address))
  (cond ((not (eq code :ok)) (mv code ,operation))
        ((not (,(fn2-columns-sym transport "-RETIRED-P") cap nonce ,transport))
         (mv :live ,operation))
        ((and (= (,(fn2-columns-sym operation "-ROWS") ,operation) 1)
              (< 0 (,(fn2-columns-sym operation "-PARENT-SERIAL") 0 ,operation)))
         (mv :child ,operation))
        (t
         (mv-let (bound ,operation)
          (,(fn2-columns-sym operation "-BIND") cap nonce op gen length ,operation)
          (if (not (eq bound :ok)) (mv bound ,operation)
           (,(fn2-columns-sym operation "-MARK-CARRIER-CLOSED") cap nonce op gen length
            ,transport ,operation)))))))

(defun ,(fn2-columns-sym stem "-CANCEL-RESULT") (cancel gen ,operation fn2-core)
 (declare (xargs :stobjs (,operation fn2-core) :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core) (,(fn2-columns-sym operation "-WFP") ,operation))))
 (mv-let (authorized target target-gen) (fn2-host-codec-cancel-target cancel gen fn2-core)
  (if (not (eq authorized :ok)) (mv authorized 0 nil 0 nil 0 ,operation)
   (mv-let (code kind cap nonce address length) (fn2-host-codec-op target target-gen fn2-core)
    (cond ((not (eq code :ok)) (mv code target nil 0 nil 0 ,operation))
          ((not (= (,(fn2-columns-sym operation "-ROWS") ,operation) 1))
           (mv :unbound target nil 0 nil address ,operation))
          (t
           (mv-let (bound ,operation)
            (,(fn2-columns-sym operation "-BIND") cap nonce target target-gen length ,operation)
            (if (not (eq bound :ok)) (mv bound target nil 0 nil address ,operation)
             (mv-let (decision terminal-code count won ,operation)
              (,(fn2-columns-sym operation "-CANCEL") (equal kind *fn2-action-receive*) ,operation)
              (mv decision target terminal-code count won address ,operation)))))))))

)))
; Generated host handlers use the same concrete-ledger abstraction as their
; pure consumers; verification belongs to the actual instantiated functions.
(defun fn2-codec-host-closure-guard-events (stem transport operation world)
 (declare (xargs :verify-guards nil))
 (let ((readers
        (append
         (list (fn2-columns-sym transport "-ROWS") (fn2-columns-sym operation "-ROWS")
               (fn2-columns-sym operation "-BIND")
               (fn2-columns-sym operation "-MARK-CARRIER-CLOSED")
               (fn2-columns-sym operation "-CANCEL"))
         (fn2-columns-projection-readers transport
          (fn2-decl-get :columns (fn2-decl-row (list :columns transport) world)))
         (fn2-columns-projection-readers operation
          (fn2-decl-get :columns (fn2-decl-row (list :columns operation) world))))))
  `((verify-guards ,(fn2-columns-sym stem "-MARK-CLOSED")
      :hints (("Goal" :in-theory (disable ,@readers))))
    (verify-guards ,(fn2-columns-sym stem "-CANCEL-RESULT")
      :hints (("Goal" :in-theory (disable ,@readers)))))))

(defmacro defcodec-host-closure (stem transport operation)
 `(make-event
   (value (cons 'progn
     (append (cdr (fn2-codec-host-closure-events ',stem ',transport ',operation))
             (fn2-codec-host-closure-guard-events ',stem ',transport ',operation (w state)))))))
