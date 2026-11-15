; A deferred cancellation carries proof that its codec handle was reclaimed.
(in-package "ACL2")
(include-book "codec-transport")
(fn2-book-layer :a)

(defun fn2-codec-record-closure-events (operation transport world)
 (declare (xargs :verify-guards nil))
 (let ((close (fn2-columns-sym operation "-MARK-CARRIER-CLOSED"))
       (op-wfp (fn2-columns-sym operation "-WFP"))
       (op-rows (fn2-columns-sym operation "-ROWS"))
       (tr-wfp (fn2-columns-sym transport "-WFP"))
       (tr-rows (fn2-columns-sym transport "-ROWS"))
       (readers (append
        (fn2-columns-projection-readers operation
         (fn2-decl-get :columns (fn2-decl-row (list :columns operation) world)))
        (fn2-columns-projection-readers transport
         (fn2-decl-get :columns (fn2-decl-row (list :columns transport) world)))
        (list (fn2-columns-sym operation "-ROWS") (fn2-columns-sym transport "-ROWS")))))
  `(progn
   (defun ,close (cap nonce slot generation extent ,transport ,operation)
    (declare (xargs :stobjs (,transport ,operation) :verify-guards nil
     :guard (and (,tr-wfp ,transport) (,op-wfp ,operation))))
    (cond
     ; Carrier identity alone cannot authorize an arbitrary sibling loan.
     ; The live-core caller must bind the public operation before closure.
     ((not (= (,op-rows ,operation) 1)) (mv :unbound ,operation))
     ((not (= (,tr-rows ,transport) 1)) (mv :stale ,operation))
     ((not (and (equal cap (,(fn2-columns-sym transport "-CAP") 0 ,transport))
                 (equal nonce (,(fn2-columns-sym transport "-NONCE") 0 ,transport))))
      (mv :stale ,operation))
     ((or (not (= (,(fn2-columns-sym transport "-PENDING") 0 ,transport) 0))
          (and (= (,op-rows ,operation) 1)
               (not (= (,(fn2-columns-sym operation "-PENDING-SERIAL") 0 ,operation) 0))))
      (mv :pending ,operation))
     ((not (,(fn2-columns-sym transport "-RETIRED-P") cap nonce ,transport))
      (mv :live ,operation))
     ((and (= (,op-rows ,operation) 1) (= (,(fn2-columns-sym operation "-TERMINAL") 0 ,operation) 1))
      (mv :too-late ,operation))
     (t
      (mv-let (bound ,operation)
       (,(fn2-columns-sym operation "-BIND") cap nonce slot generation extent ,operation)
       (if (not (eq bound :ok)) (mv bound ,operation)
        (let ((,operation (,(fn2-columns-sym operation "-PUT") 0 (carrier-closed 1))))
         ; The operation is still unresolved. CANCEL, not carrier Close,
         ; decides its terminal outcome from its retained application prefix.
         (mv :ok ,operation)))))))
   (verify-guards ,close :hints (("Goal" :in-theory (disable ,@readers))))
   (defthm ,(fn2-columns-sym close "-WFP")
    (implies (and (,(fn2-columns-sym operation "P") ,operation) (,op-wfp ,operation)
                  (,(fn2-columns-sym transport "P") ,transport) (,tr-wfp ,transport))
     (,op-wfp (mv-nth 1 (,close cap nonce slot generation extent ,transport ,operation))))
    :hints (("Goal" :in-theory (disable ,@readers)))))))

(defmacro defcodec-record-closure (operation transport)
 `(make-event (value (fn2-codec-record-closure-events ',operation ',transport (w state)))))
