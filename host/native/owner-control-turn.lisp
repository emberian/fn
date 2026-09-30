;;; Internal owner scheduler control turn. Installation must qualify the
;;; complete entry/wait/cleanup closure before any served caller selects it.
(in-package "ACL2")

(defstruct (fnn-owner-control-binding
            (:constructor %make-fnn-owner-control-binding) (:copier nil))
  pool slots slot enter finish fault)

(defun fnn-owner-control-binding-make (pool slots slot)
  "Funded installation only; SLOT is the core-installed :owner-control slot."
  (%make-fnn-owner-control-binding
   :pool pool :slots slots :slot slot
   :enter (fnn-fixed-raw-callback 'fn-ats-enter-internal)
   :finish (fnn-fixed-raw-callback 'fn-ats-finish-owned)
   :fault (fnn-fixed-raw-callback 'fn-ats-uncertain-internal)))

(defun fnn-owner-control-fault-locked (binding)
  (multiple-value-bind (word slots pool)
      (fnn-core-mv 'fn-ats-uncertain-internal
        (funcall (fnn-owner-control-binding-fault binding)
                 (fnn-owner-control-binding-slots binding)
                 (fnn-owner-control-binding-pool binding)))
    (declare (ignore slots pool))
    word))

(defun fnn-owner-control-fault (binding)
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (fnn-owner-control-fault-locked binding)))

(defun fnn-owner-control-enter (binding)
  "Retain a control receipt before scheduler entry, including its cleanup."
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (let ((returned nil))
      (unwind-protect
          (multiple-value-prog1
              (multiple-value-bind (word nonce slots pool)
                  (fnn-core-mv 'fn-ats-enter-internal
                    (funcall (fnn-owner-control-binding-enter binding)
                             (fnn-owner-control-binding-slot binding) :owner-control
                             (fnn-owner-control-binding-slots binding)
                             (fnn-owner-control-binding-pool binding)))
                (declare (ignore slots pool))
                (values word nonce))
            (setf returned t))
        (unless returned (fnn-owner-control-fault-locked binding))))))

(defun fnn-owner-control-finish (binding nonce)
  "Called only after the actual scheduler cleanup has definitely returned."
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (let ((returned nil))
      (unwind-protect
          (multiple-value-prog1
              (multiple-value-bind (word slots pool)
                  (fnn-core-mv 'fn-ats-finish-owned
                    (funcall (fnn-owner-control-binding-finish binding)
                             (fnn-owner-control-binding-slot binding) nonce
                             (fnn-owner-control-binding-slots binding)
                             (fnn-owner-control-binding-pool binding)))
                (declare (ignore slots pool))
                (unless (eq word :left)
                  (fnn-fixed-callback-fail 'fn-ats-finish-owned :control-receipt-not-consumed word))
                word)
            (setf returned t))
        (unless returned (fnn-owner-control-fault-locked binding))))))

(defmacro fnn-with-owner-control-turn ((binding) &body body)
  "Keep control entry and cleanup owned independently of an operation BODY.
Only :gate-owned enters BODY. Other entry results return WORD and NONCE without
starting scheduler work. BODY includes the actual gate's allocating cleanup.
No extent lock spans the wait: the retained receipt prevents collection from
passing quiescence, while other admitted workers can reach their cleanup."
  (let ((b (gensym "BINDING")) (word (gensym "WORD"))
        (nonce (gensym "NONCE")) (returned (gensym "RETURNED")))
    `(let ((,b ,binding) (,returned nil))
       (unwind-protect
           (multiple-value-prog1
               (multiple-value-bind (,word ,nonce) (fnn-owner-control-enter ,b)
                 (if (eq ,word :gate-owned)
                     (multiple-value-prog1 (progn ,@body)
                       (fnn-owner-control-finish ,b ,nonce))
                   (values ,word ,nonce)))
             (setf ,returned t))
         ;; Ambiguous exit retains the control receipt; never unconditional
         ;; FINISH. The entry/finish callback can also fence, at most twice.
         (unless ,returned (fnn-owner-control-fault ,b))))))
