;;; host/adapter.lisp's per-turn reuse, on the real forms read from the file:
;;; fn2-nop-reset!, the per-capability scratch vectors and the boundary fast path.
;;; Two tiers. Under `sbcl --script` the TLS record is a stand-in table (the
;;; stobj needs the certified books); under ACL2 raw mode with
;;; books/tls-record-state included (FN2_ALLOC_REAL_STOBJ=1) it is the real
;;; fn2-tls-record and its generated init.
(unless (find-package "ACL2") (defpackage "ACL2" (:use "COMMON-LISP")))
(in-package "ACL2")

(defvar *fn2-alloc-real* (equal (sb-ext:posix-getenv "FN2_ALLOC_REAL_STOBJ") "1"))

(defun fn2-alloc-adapter-forms ()
  (with-open-file (source "host/adapter.lisp")
    (let ((*package* (find-package "ACL2")))
      (loop for form = (read source nil nil) while form collect form))))

(defun fn2-alloc-named (forms head name)
  (let ((hits (remove-if-not (lambda (f) (and (consp f) (eq (car f) head)
                                              (eq (if (consp (cadr f)) (caadr f) (cadr f)) name)))
                             forms)))
    (assert (= (length hits) 1) () "host/adapter.lisp: expected one ~a ~a" head name)
    (car hits)))

(unless *fn2-alloc-real*
  ;; Stand-in with the raw-stobj contract the reset relies on: init N updates
  ;; the table in place and returns it.
  (defstruct (fn2-alloc-table (:constructor create-fn2-tls-record))
    (column (make-array 0 :element-type '(unsigned-byte 32))) (rows 0))
  (defun fn2-tls-record-rows (table) (fn2-alloc-table-rows table))
  (defun fn2-tls-record-init (n table)
    (setf (fn2-alloc-table-column table)
          (make-array n :element-type '(unsigned-byte 32) :initial-element 0)
          (fn2-alloc-table-rows table) n)
    table))

(defvar *fn2-alloc-forms* (fn2-alloc-adapter-forms))
(dolist (spec '((defstruct fn2-nop) (defun fn2-nop-reset!) (defstruct fn2-nhost)
                (defun fn2-n-interest-masks) (defun fn2-n-ready-used)
                (defvar *fn2-n-boundary-observer*) (defun fn2-n-boundary)))
  (eval (fn2-alloc-named *fn2-alloc-forms* (first spec) (second spec))))

;;; (a) reset returns every slot to the defstruct defaults, the TLS record included.
(defun fn2-alloc-dirty-record (op)
  ;; A bound row, as fn2-tls-record-start leaves it.
  (setf (fn2-nop-tls-record op)
        (if *fn2-alloc-real*
            (nth-value 1 (fn2-tls-record-init-epoch 7 9 3 5 11 0 0 (fn2-nop-tls-record op)))
          (fn2-tls-record-init 1 (fn2-nop-tls-record op)))))

(defun fn2-alloc-dirty-op ()
  (let ((op (make-fn2-nop)))
    (setf (fn2-nop-state op) 3 (fn2-nop-gen op) 41 (fn2-nop-kind op) 6 (fn2-nop-cap op) 2
          (fn2-nop-nonce op) 77 (fn2-nop-address op) 4096 (fn2-nop-len op) 512 (fn2-nop-target op) 1
          (fn2-nop-target-gen op) 8 (fn2-nop-outcome op) 1 (fn2-nop-reason op) 2 (fn2-nop-count op) 99
          (fn2-nop-aux0 op) 5 (fn2-nop-aux1 op) 6 (fn2-nop-connect-fd op) 12 (fn2-nop-entropy-offset op) 3
          (fn2-nop-tls-started op) t (fn2-nop-compress-record op) (list :record)
          (fn2-nop-family op) :inet6 (fn2-nop-port op) 119 (fn2-nop-w0 op) 1 (fn2-nop-w1 op) 2
          (fn2-nop-w2 op) 3 (fn2-nop-w3 op) 4 (fn2-nop-octets op) (list 1 2 3) (fn2-nop-offset op) 64
          (fn2-nop-fua op) 1)
    (fn2-alloc-dirty-record op)
    op))

(defun fn2-alloc-slot-count ()
  (length (sb-mop:class-slots (find-class 'fn2-nop))))

(let ((op (fn2-alloc-dirty-op)))
  (assert (= (fn2-alloc-slot-count) 28))
  (assert (not (equalp op (make-fn2-nop))))
  (assert (not (equalp (fn2-nop-tls-record op) (create-fn2-tls-record))))
  (let ((record (fn2-nop-tls-record op)))
    (assert (eq (fn2-nop-reset! op) op))
    (assert (equalp op (make-fn2-nop)))
    (assert (equalp (fn2-nop-tls-record op) (create-fn2-tls-record)))
    ;; the stobj is cleared in place, not replaced
    (assert (eq (fn2-nop-tls-record op) record))
    ;; a reset of a fresh op keeps it fresh and keeps its record
    (fn2-nop-reset! op)
    (assert (equalp op (make-fn2-nop)))
    (assert (eq (fn2-nop-tls-record op) record))))

;;; Tooth: the real reset with any one of its 28 slot resets removed leaves a
;;; dirty op that is not equalp to a fresh one.
(let* ((reset (fn2-alloc-named *fn2-alloc-forms* 'defun 'fn2-nop-reset!))
       (setf-form (find-if (lambda (f) (and (consp f) (eq (car f) 'setf))) (cdddr reset)))
       (pairs (loop for (place value) on (cdr setf-form) by #'cddr collect (list place value))))
  (assert (= (length pairs) 28))
  (dotimes (k (length pairs))
    (let ((planted (append (subseq reset 0 3)
                           (substitute `(setf ,@(loop for pair in pairs for i from 0
                                                      unless (= i k) append pair))
                                       setf-form (cdddr reset) :test #'eq))))
      (eval (subst 'fn2-alloc-planted-reset 'fn2-nop-reset! planted))
      (let ((op (fn2-alloc-dirty-op)))
        (funcall 'fn2-alloc-planted-reset op)
        (assert (not (equalp op (make-fn2-nop))) ()
                "omitting reset of ~s still equalp" (first (nth k pairs)))))))
(format t "ALLOC-RESET-OK ~a~%" (if *fn2-alloc-real* "real-stobj" "stand-in-record"))

;;; (b) the scratch vectors are the host's own, cleared in place each turn.
(let* ((host (make-fn2-nhost :caps (vector :a :b :c)
                             :interest-masks (make-array 3 :initial-element 0)
                             :ready-used (make-array 3 :initial-element nil)))
       (masks (fn2-n-interest-masks host)) (used (fn2-n-ready-used host)))
  (assert (eq masks (fn2-nhost-interest-masks host)))
  (assert (eq used (fn2-nhost-ready-used host)))
  (fill masks 5) (fill used t)
  (assert (eq (fn2-n-interest-masks host) masks))
  (assert (eq (fn2-n-ready-used host) used))
  (assert (every #'zerop masks))
  (assert (every #'null used))
  ;; a host built without them, or whose capability table changed, gets fresh ones
  (setf (fn2-nhost-caps host) (vector :a :b :c :d))
  (assert (= (length (fn2-n-interest-masks host)) 4))
  (assert (not (eq (fn2-nhost-interest-masks host) masks)))
  (let ((bare (make-fn2-nhost :caps (vector :a :b))))
    (assert (equalp (fn2-n-interest-masks bare) #(0 0)))
    (assert (equalp (fn2-n-ready-used bare) #(nil nil)))
    (assert (eq (fn2-n-ready-used bare) (fn2-n-ready-used bare)))))
(format t "ALLOC-SCRATCH-OK~%")

;;; (c) the observer sees ordinals 1, 2, 3 inside the lock; with no cut armed
;;; and no observer the boundary returns without taking the lock.
(let ((host (make-fn2-nhost)) (seen nil))
  (let ((*fn2-n-boundary-observer*
          (lambda (h ordinal label slot generation selected)
            (assert (eq h host))
            (assert (sb-thread:holding-mutex-p (fn2-nhost-boundary-lock h)))
            (push (list ordinal label slot generation selected) seen))))
    (fn2-n-boundary host "take")
    (fn2-n-boundary host "ack")
    (fn2-n-boundary host "post" 4 9))
  (assert (equal (reverse seen) '((1 "take" nil nil nil) (2 "ack" nil nil nil) (3 "post" 4 9 nil))))
  (assert (= (fn2-nhost-boundaries host) 3))
  ;; Holding the lock here: the slow path would be a recursive lock attempt.
  (sb-thread:with-mutex ((fn2-nhost-boundary-lock host))
    (assert (null (fn2-n-boundary host "post" 4 9)))
    (let ((*fn2-n-boundary-observer* (lambda (&rest args) (declare (ignore args)))))
      (assert (handler-case (progn (fn2-n-boundary host "post") nil) (error () t)))))
  (assert (= (fn2-nhost-boundaries host) 3)))
(format t "ALLOC-BOUNDARY-OK~%")
