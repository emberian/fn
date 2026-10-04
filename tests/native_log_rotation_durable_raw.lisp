;;; A failed rotate-durable barrier is the log's uncertainty, never retried
;;; (host/native/io.lisp fnn-log-make-durable).  The rotated-to segment's
;;; name and head are fenced off the owner mutex by whichever comes first:
;;; the checkpoint publication (host/native/owner.lisp
;;; fnn-owner-publish-captured, whose thread boundary classifies an OS
;;; error with no step of its own as a job failure: serving continues) or
;;; the new segment's first batch fence (fnn-log-fence).  A barrier that
;;; failed must not be asked again and believed: on Linux a second fsync
;;; after a failed one can answer 0 with the directory entry not durable
;;; (the error is reported once), and the batch behind it would be
;;; acknowledged in a segment whose name may not survive.  The first failure
;;; must fence the log kernel and answer uncertain; every later call must
;;; answer uncertain without touching the disk.
;;;
;;; This loads the deployed io.lisp; the kernel transition the failure takes
;;; is books/store-log-kernel-concrete.lisp's own fn-lgc-fence-failed, read
;;; from the book.  Only the two barrier syscalls are recorded seams.

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defun f-get-global (name state)
  (declare (ignore name state))
  nil)
(load "tests/native_io_prelude.lisp")
(load "host/native/io.lisp")

(book-defuns "books/store-log-kernel-concrete.lisp"
             '(fn-lgc-make fn-lgc-count fn-lgc-last fn-lgc-frontier fn-lgc-next-txid
               fn-lgc-batch fn-lgc-inflight fn-lgc-acked fn-lgc-phase fn-lgc-fence-failed))
;; ACL2's NFIX, which the book's accessors call.
(defun nfix (x) (if (and (integerp x) (>= x 0)) x 0))
;; The dispatcher answers the book's function itself (no guard table here).
(defun fnn-call (name &rest args) (list (apply name args)))
;; Unarmed developer cut: no selector in this process.
(defun fnn-log-at (point) (declare (ignore point)) nil)

(defvar *barriers* nil)
(defvar *dir-answers* nil)
(defun fnn-fsync-file (fd) (push (list :file fd) *barriers*) nil)
(defun fnn-fsync-dir (path)
  (push (list :dir path) *barriers*)
  (let ((answer (pop *dir-answers*)))
    (when (eq answer :eio) (fnn-os-fail 5 path)))
  (setq *fnn-section-step* nil))

(defun check (test what)
  (unless test
    (format t "native_log_rotation_durable: FAIL ~a~%" what)
    (finish-output)
    (sb-ext:exit :code 1 :abort t)))

(defun outcome (thunk)
  (handler-case (progn (funcall thunk) :returned)
    (fnn-store-indeterminate () :uncertain)
    (fnn-os-error () :os-error)
    (serious-condition (c) (list :other (class-name (class-of c))))))

;; 1. A clean barrier: the name is durable, nothing pending, the kernel as it was.
(let* ((kernel (fn-lgc-make 3 '(1 2) 8192 9 nil nil 3 :fenced))
       (log (%make-fnn-log :fd 77 :kernel kernel :dir-pending "/store/journal"))
       (*barriers* nil) (*dir-answers* (list :ok)))
  (check (eq (outcome (lambda () (fnn-log-make-durable log))) :returned) "clean barrier returns")
  (check (null (fnn-log-dir-pending log)) "clean barrier clears the pending name")
  (check (equal (fnn-log-kernel log) kernel) "clean barrier leaves the kernel")
  (check (eq (outcome (lambda () (fnn-log-make-durable log))) :returned) "a durable name is a no-op")
  (check (= (length *barriers*) 2) "a durable name takes no second barrier"))

;; 2. The directory barrier fails once.  The first call is the log's
;; uncertainty (the kernel fenced), and the next caller -- the batch fence
;; that would acknowledge members of the new segment -- is answered
;; uncertain again with no barrier asked, even though the disk would now
;; answer success.
(let* ((kernel (fn-lgc-make 0 '(7 7) 4096 12 nil nil 0 :fenced))
       (log (%make-fnn-log :fd 78 :kernel kernel :dir-pending "/store/journal"))
       (*barriers* nil) (*dir-answers* (list :eio :ok :ok)))
  (check (eq (outcome (lambda () (fnn-log-make-durable log))) :uncertain)
         "a failed rotate-durable barrier is uncertain, not an OS error a job boundary drops")
  (check (eq (fn-lgc-phase (fnn-log-kernel log)) :fault)
         "a failed rotate-durable barrier fences the log kernel")
  (let ((before (length *barriers*)))
    (check (eq (outcome (lambda () (fnn-log-make-durable log))) :uncertain)
           "a failed rotate-durable barrier is never retried and believed")
    (check (= (length *barriers*) before) "the retry asked the disk again"))
  (check (fnn-log-dir-pending log) "the name is still not durable"))

;; 3. The file barrier (the head) fails: the same verdict.
(let* ((kernel (fn-lgc-make 0 '(7 7) 4096 12 nil nil 0 :fenced))
       (log (%make-fnn-log :fd 79 :kernel kernel :dir-pending "/store/journal"))
       (*barriers* nil) (*dir-answers* nil))
  (let ((old (fdefinition 'fnn-fsync-file)))
    (setf (fdefinition 'fnn-fsync-file) (lambda (fd) (declare (ignore fd)) (fnn-os-fail 5)))
    (unwind-protect
         (check (eq (outcome (lambda () (fnn-log-make-durable log))) :uncertain)
                "a failed head barrier is uncertain")
      (setf (fdefinition 'fnn-fsync-file) old)))
  (check (eq (outcome (lambda () (fnn-log-make-durable log))) :uncertain)
         "a failed head barrier is never retried"))

;; 4. The batch fence behind the failed name: uncertain, the members in
;; flight no longer in flight, and no data barrier asked (the kernel is
;; fenced; nothing in the new segment is ever acknowledged).
(let* ((kernel (fn-lgc-make 0 '(7 7) 4096 12 nil '((r1)) 0 :fenced))
       (log (%make-fnn-log :fd 80 :kernel kernel :dir-pending "/store/journal"
                           :inflight (list (list 1 2 3 4))))
       (*barriers* nil) (*dir-answers* (list :eio))
       (datasyncs 0))
  (check (eq (outcome (lambda () (fnn-log-make-durable log))) :uncertain) "publication's barrier fails")
  (let ((old (fdefinition 'fnn-log-fdatasync)))
    (setf (fdefinition 'fnn-log-fdatasync) (lambda (fd) (declare (ignore fd)) (incf datasyncs) nil))
    (unwind-protect
         (check (eq (outcome (lambda () (fnn-log-fence log))) :uncertain)
                "the batch fence behind a failed rotate-durable barrier is uncertain")
      (setf (fdefinition 'fnn-log-fdatasync) old)))
  (check (zerop datasyncs) "the batch fence asked the data barrier behind a failed name")
  (check (null (fnn-log-inflight log)) "the failed fence left members in flight")
  (check (eq (fn-lgc-phase (fnn-log-kernel log)) :fault) "the failed fence left the kernel unfenced"))

(format t "native_log_rotation_durable: PASS~%")
