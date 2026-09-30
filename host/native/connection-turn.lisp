;;; Native transport for the connection operation's one-use core ticket.
;;; INTERNAL until the actual installer and operation source allowance join.
;;; The caller holds owner exclusion; all callbacks additionally take extent.
(in-package "ACL2")

(defstruct (fnn-connection-turn-binding
            (:constructor %make-fnn-connection-turn-binding) (:copier nil))
  pool slots slot prepare finish fault)

(defun fnn-connection-turn-binding-make (pool slots slot)
  "Funded installation only: bind the actual pool, worker slots and endpoint."
  (%make-fnn-connection-turn-binding
   :pool pool :slots slots :slot slot
   :prepare (fnn-fixed-raw-callback 'fn-owner-index-connection-prepare)
   :finish (fnn-fixed-raw-callback 'fn-owner-index-connection-finish)
   :fault (fnn-fixed-raw-callback 'fn-owner-index-connection-fault)))

(defun fnn-connection-turn-fault-locked (binding)
  "Retain ticket/receipt roots and fence; never consume a turn on raw escape."
  (multiple-value-bind (erp word slots pool state)
      (fnn-core-mv 'fn-owner-index-connection-fault
        (funcall (fnn-connection-turn-binding-fault binding)
                 (fnn-connection-turn-binding-slots binding)
                 (fnn-connection-turn-binding-pool binding) *the-live-state*))
    (declare (ignore slots pool state))
    (when erp
      (fnn-fixed-callback-fail 'fn-owner-index-connection-fault :core-error erp))
    word))

(defun fnn-connection-turn-fault (binding)
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (fnn-connection-turn-fault-locked binding)))

(defun fnn-connection-turn-prepare (binding kind family address peer mio)
  "Enter the actual operation, prepay its body and retain its core ticket.
Return the core word, shared nonce and MIO without an argument/result list.
Only a successful core preparation licenses the matching connection start."
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (let ((returned nil))
      (unwind-protect
          (multiple-value-prog1
              (multiple-value-bind (erp word nonce slots mio1 pool state)
                  (fnn-core-mv 'fn-owner-index-connection-prepare
                    (funcall (fnn-connection-turn-binding-prepare binding)
                             kind family address peer
                             (fnn-connection-turn-binding-slot binding)
                             (fnn-connection-turn-binding-slots binding)
                             mio (fnn-connection-turn-binding-pool binding)
                             *the-live-state*))
                (declare (ignore slots pool state))
                (when erp
                  (fnn-fixed-callback-fail
                   'fn-owner-index-connection-prepare :core-error erp))
                (values word nonce mio1))
            (setf returned t))
        (unless returned (fnn-connection-turn-fault-locked binding))))))

(defun fnn-connection-turn-finish (binding nonce)
  "Consume the core operation ticket and owned slot at the actual outer return."
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (let ((returned nil))
      (unwind-protect
          (multiple-value-prog1
              (multiple-value-bind (erp word slots pool state)
                  (fnn-core-mv 'fn-owner-index-connection-finish
                    (funcall (fnn-connection-turn-binding-finish binding)
                             (fnn-connection-turn-binding-slot binding) nonce
                             (fnn-connection-turn-binding-slots binding)
                             (fnn-connection-turn-binding-pool binding)
                             *the-live-state*))
                (declare (ignore slots pool state))
                (when erp
                  (fnn-fixed-callback-fail
                   'fn-owner-index-connection-finish :core-error erp))
                (unless (eq word :left)
                  (fnn-fixed-callback-fail
                   'fn-owner-index-connection-finish :receipt-not-consumed word))
                word)
            (setf returned t))
        ;; A finish may already have touched the count. Fence BEFORE unlock,
        ;; not later in the caller, where a collector could run in the gap.
        (unless returned (fnn-connection-turn-fault-locked binding))))))

(defmacro fnn-with-prepaid-connection-turn ((binding nonce) &body body)
  "Retain an already prepaid receipt through BODY and its allocating epilogue.
This macro grants no authority and performs no entry/prepayment. Its caller
must include every allocating cleanup before normal completion. Nonlocal exits
retain the core ticket/receipt in recovery; they never run ordinary finish."
  (let ((b (gensym "BINDING")) (n (gensym "NONCE"))
        (returned (gensym "RETURNED")))
    `(let ((,b ,binding) (,n ,nonce) (,returned nil))
       (unwind-protect
           (multiple-value-prog1 (progn ,@body)
             (fnn-connection-turn-finish ,b ,n)
             (setf ,returned t))
         ;; FINISH fences its partial updates before extent unlock. Fence here
         ;; too: an interruption can precede entry into FINISH. Fault only
         ;; retains/fences, so a finish failure can call it twice; both calls
         ;; belong to the prepaid epilogue. Never retry ordinary completion.
         (unless ,returned
           (fnn-connection-turn-fault ,b))))))

(defmacro fnn-with-connection-operation
    (((nonce current-mio) binding kind family address peer mio) &body body)
  "Prepare and complete one connection operation under continuous exclusion.
The caller already holds owner exclusion. BODY runs only after :prepared,
with the returned NONCE and CURRENT-MIO, and includes all allocating cleanup.
Its complete multiple-value result is preserved. Definite nonprepared outcomes
return (values WORD NIL CURRENT-MIO) without running BODY or ordinary FINISH.
This transport does not establish the installer's resource allowance."
  (let ((b (gensym "BINDING")) (word (gensym "WORD"))
        (returned (gensym "RETURNED")))
    `(let ((,b ,binding))
       (sb-thread:with-recursive-lock (*fnn-extent-lock*)
         ;; Establish this unwind before PREPARE: even the interval after its
         ;; acknowledgment and before BODY belongs to the retained operation.
         (let ((,returned nil))
           (unwind-protect
               (multiple-value-prog1
                   (multiple-value-bind (,word ,nonce ,current-mio)
                       (fnn-connection-turn-prepare
                        ,b ,kind ,family ,address ,peer ,mio)
                     (if (eq ,word :prepared)
                         (multiple-value-prog1 (progn ,@body)
                           (fnn-connection-turn-finish ,b ,nonce))
                       (values ,word nil ,current-mio)))
                 (setf ,returned t))
             ;; Do not nest the prepaid-only macro: PREPARE/FINISH already
             ;; fence their own failures, making this at most the second
             ;; fault callback. Neither raw escape nor refusal consumes a
             ;; ticket here. Fault remains inside the continuous extent span.
             (unless ,returned
               (fnn-connection-turn-fault-locked ,b))))))))
