;;; The BP listener drive runs after the owner mutex is released; a failure of
;;; it is re-signalled inside a settle quantum, where the one envelope classifies
;;; and fences it with the mutex held.  Shipped bodies: fnn-bpnc-execute,
;;; fnn-bpnc-drive-after, def-section fnn-quantum-bp (the lock is the stubbed
;;; fnn-section-run).
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-rc-begin (run reserve)
  (declare (ignorable run reserve))
  (harness-stub-reached 'fnn-rc-begin "host/native/admin.lisp"))
;;; ---- derived stubs: END ----

(define-condition fnn-store-indeterminate (error) ())
(defstruct fnn-bpnc owner listeners)
(defvar *fnn-section-step* nil)
(defvar *fnn-bplc-test-change* nil)
(defvar *held* nil)
(defvar *trace* nil)
(defvar *drive-failure* nil)
(defun note (what) (push (list what *held*) *trace*))

(defun fnn-section-run (owner class cid admits classes name thunk)
  (declare (ignore owner class cid admits classes name))
  (note :section-enter)
  (let ((*held* t))
    (handler-bind ((serious-condition
                     ;; The envelope: classified and fenced while held.
                     (lambda (c) (declare (ignore c)) (note :fence))))
      (funcall thunk))))
(defun fnn-owner-disk-admit (owner) (declare (ignore owner)) :ok)
(defun fnn-owner-result (&rest arguments) (declare (ignore arguments)) :result)
;; The quanta of a live reconfiguration (host/native/admin.lisp
;; fnn-owner-live-reconfigure) collapse here to one section whose published
;; answer is :accepted; the caller's CONTINUE runs inside it, as it does in
;; the quantum that decides the answer.
(defmacro fnn-owner-live-reconfigure
    ((run drive section service cid &rest class) (word reason)
     &key before stage reserve convert release continue)
  (declare (ignore run drive before stage reserve convert release))
  `(,section ,service ,cid
             (lambda ()
               (note :publish)
               (let ((,word :accepted) (,reason nil))
                 (declare (ignorable ,word ,reason))
                 ,continue))
             ,@class))
(defun fnn-fault (&rest arguments) (error "fault ~s" arguments))
(defun fnn-bplc-begin-locked (node) (declare (ignore node)) (note :begin))
(defun fnn-bplc-reconfigure (node)   ; the pre-split entry, if still shipped
  (declare (ignore node)) (note :drive))
(defun fnn-bplc-cut (node cut) (declare (ignore node cut)) (note :cut))
(defun fnn-bplc-drive (node &optional service)
  (declare (ignore node service))
  (note :drive)
  (when *drive-failure* (error 'fnn-store-indeterminate)))

(defun load-shipped (path kinds names)
  (with-open-file (stream path)
    (dolist (wanted names)
      (file-position stream 0)
      (let ((found nil))
        (loop for form = (read stream nil :eof) until (eq form :eof)
              when (and (consp form) (member (car form) kinds)
                        (eq (cadr form) wanted))
                do (eval form) (setq found t) (return))
        (unless found (error "~a: ~s not found" path wanted))))))

(defun fn-fs-section-declp (actors classes admits)
  (declare (ignore actors classes admits)) t)
(load-shipped "host/native/owner.lisp" '(defvar) '(*fnn-sections*))
(load-shipped "host/native/owner.lisp" '(defun) '(fnn-section-declare))
(load-shipped "host/native/owner.lisp" '(defmacro) '(def-section))
(load-shipped "host/native/owner.lisp" '(def-section) '(fnn-quantum-bp))
(load-shipped "host/native/bp-control.lisp" '(defun) '(fnn-bpnc-execute))
(with-open-file (s "host/native/bp-control.lisp")
  (loop for form = (read s nil :eof) until (eq form :eof)
        when (and (consp form) (eq (car form) 'defun)
                  (eq (cadr form) 'fnn-bpnc-drive-after))
          do (eval form)))

(defun run (failure)
  (setq *trace* nil *drive-failure* failure)
  (let ((node (make-fnn-bpnc :owner :owner :listeners :listeners))
        (outcome nil))
    (handler-case (setq outcome (fnn-bpnc-execute node '(:execute :plan)))
      (fnn-store-indeterminate () (setq outcome :raised)))
    (values outcome (reverse *trace*))))

;; Success: the drive and the cut run with the mutex free; only publish and
;; begin run under it.
(multiple-value-bind (outcome trace) (run nil)
  (unless (eq outcome :accepted) (error "outcome ~s" outcome))
  (dolist (what '(:drive :cut))
    (let ((row (find what trace :key #'first)))
      (unless row (error "~s never ran: ~s" what trace))
      (when (second row) (error "~s ran while the owner mutex was held: ~s" what trace))))
  (dolist (what '(:publish))
    (unless (second (find what trace :key #'first))
      (error "~s ran outside the owner mutex: ~s" what trace))))

;; Failure: the condition is fenced by a section that holds the mutex, after the
;; drive left the first one, and the caller sees the same condition.
(multiple-value-bind (outcome trace) (run t)
  (unless (eq outcome :raised) (error "the failure was swallowed: ~s" outcome))
  (let ((fence (find :fence trace :key #'first :from-end t)))
    (unless (and fence (second fence))
      (error "the failure was not fenced under the mutex: ~s" trace))
    (unless (> (position fence trace) (position :drive trace :key #'first))
      (error "the fence precedes the drive: ~s" trace))
    (unless (= 2 (count :section-enter trace :key #'first))
      (error "no settle section: ~s" trace))))

(format t "native BP listener off lock: PASS~%")
