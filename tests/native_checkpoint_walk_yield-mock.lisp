;;; The checkpoint walk's yield names the batch it stopped before by a batch
;;; counter, not by the length of the accumulated row list (host/native/io.lisp
;;; fnn-checkpoint-walk, ledger r72-F9): (length (second walk)) is O(rows
;;; walked so far) at every batch boundary, so a walk of N batches did
;;; quadratic work in N just to name its position.  The owner's stop test
;;; ends the publication at the third boundary; the refusal names that batch.
;;;
;;; The seam is ACL2's fn-scka-srcs-n (fnn-core), which consumes a batch of
;;; rows and extends the accumulators; fnn-checkpoint-walk and
;;; fnn-checkpoint-yield are the deployed io.lisp.  The stub makes this a
;;; -mock fixture: it is cited by no claim.

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defun f-get-global (name state) (declare (ignore name state)) nil)
(load "tests/native_io_prelude.lisp")
(load "host/native/io.lisp")

(defun fnn-core (name &rest args)
  (case name
    (fn-scka-srcs-n
     (destructuring-bind (records n lacc sacc arena) args
       (declare (ignore arena))
       (let ((taken (subseq records 0 (min n (length records)))))
         (list (nthcdr n records) (append lacc taken) sacc))))
    (otherwise (error "unexpected ACL2 call ~s" name))))

(defun check (test what)
  (unless test
    (format t "native_checkpoint_walk_yield: FAIL ~a~%" what)
    (finish-output)
    (sb-ext:exit :code 1 :abort t)))

(let* ((rows (loop for i below (* 5 +fnn-checkpoint-batch-rows+) collect i))
       (calls 0)
       (message
         (handler-case
             (let ((*fnn-checkpoint-stop-test* (lambda () (>= (incf calls) 3))))
               (fnn-checkpoint-walk rows nil)
               nil)
           (serious-condition (c) (princ-to-string c)))))
  (check message "the stop test did not end the walk")
  (check (= calls 3) (format nil "the walk asked the stop test ~d times, not 3" calls))
  (check (search "walk batch 2;" message)
         (format nil "the walk's yield named its position by the accumulated row count, not the batch ordinal: ~a" message)))

;; An uninterrupted walk consumes every row.
(let ((walk (let ((*fnn-checkpoint-stop-test* nil))
              (fnn-checkpoint-walk (loop for i below 3000 collect i) nil))))
  (check (null (first walk)) "the walk did not consume every row")
  (check (= (length (second walk)) 3000) "the walk lost rows"))

(format t "native_checkpoint_walk_yield passed (2 paths)~%")
