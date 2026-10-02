(defpackage "ACL2" (:use "COMMON-LISP"))
(defpackage "ACL2_INVISIBLE" (:use))
(defpackage "ACL2_*1*_ACL2" (:use))
(load "/Users/ember/dev/fn/build/lanes/gpt61-extracted-product/tools/extract/clruntime.lisp")
(multiple-value-bind (o w f)(compile-file "/Users/ember/dev/fn/build/lanes/gpt61-extracted-product/build/incoming-controller-export/build/incoming-controller-test.lisp" :output-file "/Users/ember/dev/fn/build/lanes/gpt61-extracted-product/build/incoming-controller-export/build/incoming-controller-test.fasl")(declare(ignore w))(assert(not f))(load o))
(in-package "ACL2")
(define-condition fnn-store-fault(error)())
(defun fnn-fault(&rest ignored)(declare(ignore ignored))(error 'fnn-store-fault))
(deftype fnn-octets()'(simple-array(unsigned-byte 8)(*)))
(defvar *fnn-raw-dispatch* (make-hash-table :test 'eq))
(defvar *fnn-dispatch-counterpart* nil)
(defun fnn-fixed-raw-callback (name)
  "Return the selected compiled raw entry; refuse an unprepared hot callback."
  (when *fnn-dispatch-counterpart*
    (fnn-fault "fixed callback ~(~a~) requires raw dispatch" name))
  (let ((raw (gethash name *fnn-raw-dispatch*)))
    (unless (and raw (fboundp raw))
      (fnn-fault "fixed callback ~(~a~) is missing verified raw dispatch" name))
    (let ((function (symbol-function raw)))
      (unless (compiled-function-p function)
        (fnn-fault "fixed callback ~(~a~) is not compiled" name))
      function)))
(defvar *octets*)
(defun fnn-live-octets()*octets*)
(defstruct fnn-owner-admission-job input-token source-vector)
(defun faultp(f)(handler-case(progn(funcall f)nil)(error()t)))
(defmacro fnn-core-mv (name call)
  "Preserve fixed CALL's scalar MVs without an argument or result container.
NAME names the actual ACL2 subject. CALL uses its startup-selected callback;
its own scalar refusals remain results, while execution escapes are faults."
  (let ((outcome (gensym "OUTCOME")) (condition (gensym "CONDITION")))
    `(let ((,outcome :thrown))
       (multiple-value-prog1
           (catch 'raw-ev-fncall
             (handler-case
                 (multiple-value-prog1 ,call (setq ,outcome :ok))
               (serious-condition (,condition)
                 (setq ,outcome ,condition)
                 nil)))
         (case ,outcome
           (:ok nil)
           (:thrown (fnn-fault "ACL2 raw evaluation escaped in ~(~a~)" ,name))
           (otherwise (fnn-fault "ACL2 error in ~(~a~): ~a" ,name ,outcome)))))))
(defun fnn-owner-incoming-copy-step
    (job next-callback ack-callback controller pool)
  (multiple-value-bind (word start count end controller1 pool1)
      (fnn-core-mv 'fn-owner-incoming-copy-next
        (funcall next-callback (fnn-owner-admission-job-input-token job)
                 controller pool))
    (case word
      (:copy
       (handler-case
           ;; Capacity was installed under retained charge before START.
           ;; This quantum replaces bytes only; it never reserves/resizes.
           (replace (the fnn-octets (svref (fnn-live-octets) 0))
                    (fnn-owner-admission-job-source-vector job)
                    :start1 start :end1 end :start2 start :end2 end)
         (serious-condition (cause)
           ;; A partial replacement is ambiguous. The core cancels mechanics,
           ;; retaining holder/charge; no catch/unwind releases aliases.
           (fnn-core-mv 'fn-owner-incoming-copy-ack
             (funcall ack-callback
                      (fnn-owner-admission-job-input-token job)
                      start count end :uncertain controller1 pool1))
           (error cause)))
       ;; The core acknowledgement has its own execution fault boundary.
       ;; Never retry it after a callback mutated state and then escaped.
       (fnn-core-mv 'fn-owner-incoming-copy-ack
         (funcall ack-callback (fnn-owner-admission-job-input-token job)
                  start count end :copied controller1 pool1)))
      ((:complete :setup-unavailable) (values word controller1 pool1))
      (t (fnn-fault "incoming copy returned an unknown core word ~a" word)))))

(dolist(name '(create-fn-input-copy create-fn-page-read-pool fn-owner-incoming-copy-start
                fn-owner-incoming-copy-next fn-owner-incoming-copy-ack fn-owner-incoming-copy-stop))
 (setf(gethash name *fnn-raw-dispatch*)name)
 (assert(eq(fnn-fixed-raw-callback name)(symbol-function name))))
(defun setup(c p)
 (fn-owner-page-read-install '(8192 0 0 0 8)0 0 0 8 p)
 (iohp-install-backing p)
 (multiple-value-bind(w tok p1)(fn-owner-incoming-reserve '(256 0 0 0 1)p)
  (assert(and(eq w :admitted)(eq p p1)))
  (fn-owner-incoming-copy-start tok 20 nil c p) tok))
(dolist(escape '(:throw :error))
 (dolist(stage '(:next :ack))
  (let*((c(create-fn-input-copy))(p(create-fn-page-read-pool))(tok(setup c p))
       (ledger(copy-tree(fn-owner-page-read-ledger p)))
       (*octets*(vector(make-array 64 :element-type '(unsigned-byte 8) :initial-element 0)0))
       (src(make-array 20 :element-type '(unsigned-byte 8) :initial-element 7))
       (job(make-fnn-owner-admission-job :input-token tok :source-vector src))(acks 0))
   (flet((die()(if(eq escape :throw)(throw 'raw-ev-fncall :escaped)(error "after actual mutation"))))
    (assert(faultp(lambda()
     (fnn-owner-incoming-copy-step job
      (lambda(tok c p)(multiple-value-prog1(fn-owner-incoming-copy-next tok c p)
        (when(eq stage :next)(die))))
      (lambda(tok s n e outcome c p)(incf acks)(assert(eq outcome :copied))
       (multiple-value-prog1(fn-owner-incoming-copy-ack tok s n e outcome c p)
        (when(eq stage :ack)(die)))) c p))))
    (assert(equal ledger(fn-owner-page-read-ledger p)))
    (assert(equal tok(fn-input-copy-token c)))
    (assert(eq(fn-prl-nth 1(fn-owner-incoming-row p)):setup))
    (if(eq stage :next)
     (assert(and(zerop acks)(fn-icc-pending c)(zerop(fn-icc-offset c))))
     (assert(and(= acks 1)(not(fn-icc-pending c))(= (fn-icc-offset c)20)
       (every(lambda(b)(= b 7))(subseq(svref *octets* 0)0 20)))))))))
(format t "PASS actual paid paired mutation then escape: held ledger/token, no ACK retry~%")
;; Corrupted native source-length fixture: replacement bounds fault.
(let*((c(create-fn-input-copy))(p(create-fn-page-read-pool))(tok(setup c p))
      (ledger(copy-tree(fn-owner-page-read-ledger p)))
      (*octets*(vector(make-array 64 :element-type '(unsigned-byte 8) :initial-element 0)0))
      (job(make-fnn-owner-admission-job :input-token tok :source-vector #(1)))(acks 0))
 (assert(faultp(lambda()(fnn-owner-incoming-copy-step job (fnn-fixed-raw-callback 'fn-owner-incoming-copy-next)
  (lambda(tok s n e outcome c p)(incf acks)(assert(eq outcome :uncertain))
   (fn-owner-incoming-copy-ack tok s n e outcome c p)) c p))))
 (assert(= acks 1))
 (assert(equal ledger(fn-owner-page-read-ledger p)))
 (assert(eq(fn-prl-nth 1(fn-owner-incoming-row p)):cancelled))
 (assert(eq(fn-icc-phase c):cancelled)))
(format t "PASS corrupted native source bounds: uncertain ACK once, cancelled mechanics, held charge~%")
