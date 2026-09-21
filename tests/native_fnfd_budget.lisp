;;; Raw-native FNFD recovery observation test.  It loads the production
;;; directory reader and owner traversal; only the ACL2 wrapper seam has a
;;; small test policy so two v1 sibling trees must share one counter.

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defun f-get-global (name state)
  (declare (ignore name state))
  nil)
(load "host/native/io.lisp")

(defvar *nfb-observations* nil)

(defun nfb-check (test control &rest args)
  (unless test (error (apply #'format nil control args))))

;; This is a test-only ACL2-wrapper stand-in.  Production calls the wrappers
;; loaded from host/feed-filename-host.lisp; the stand-in makes the budget four
;; so the executable raw walk reaches a sibling after the first child drains it.
(defun fnn-core (name &rest args)
  (case name
    (fn-feed-filename-host-max-v1-chunks 5)
    (fn-feed-filename-host-observation-limit 4)
    (fn-feed-filename-host-observation-remaining
     (destructuring-bind (remaining observed) args
       (push (list remaining observed) *nfb-observations*)
       (if (and (integerp remaining) (>= remaining 0)
                (integerp observed) (>= observed 0) (<= observed remaining))
           (- remaining observed)
         :bad)))
    ;; The test faults before the second leaf needs a decode.  This accepted
    ;; peer lets the first sibling take the same production decode path.
    (fn-feed-filename-host-decode '(112 101 101 114))
    (otherwise (error "unexpected ACL2 FNFD wrapper: ~a" name))))

(load "host/native/feed-filename.lisp")
;; The traversal needs only the store root accessor.  A pathname string is the
;; minimal fake store for this raw filesystem test.
(defun fnn-store-root (store) store)
(load "host/native/owner.lisp")

(defun nfb-mkdir (path)
  (fnn-safe-directory path t)
  path)

(defun nfb-touch (path)
  (with-open-file (out path :direction :output :if-does-not-exist :create
                            :if-exists :error)
    (declare (ignore out)))
  path)

(defun nfb-remove-tree (path)
  (ignore-errors
    (sb-ext:run-program "/bin/rm" (list "-rf" path)
                        :search nil :output nil :error nil)))

(defun nfb-shared-budget-exhausts-across-siblings ()
  (let* ((root (format nil "/tmp/fn-fnfd-budget-~d" (sb-posix:getpid)))
         (feed (fnn-join root "feed"))
         (v1 (fnn-join feed "v1"))
         (left (fnn-join v1 "aa"))
         (right (fnn-join v1 "bb"))
         (left-journal (fnn-join left "journal.fnfd"))
         (right-journal (fnn-join right "journal.fnfd")))
    (nfb-remove-tree root)
    (unwind-protect
         (progn
           (nfb-mkdir root)
           (nfb-mkdir feed)
           (nfb-mkdir v1)
           (nfb-mkdir left)
           (nfb-mkdir right)
           (nfb-touch left-journal)
           (nfb-touch right-journal)
           (setq *nfb-observations* nil)
           (let ((faulted nil))
             (handler-case
                 (fnn-owner-feed-existing-peers root)
               (fnn-store-fault (e)
                 (setq faulted t)
                 (nfb-check (search "FNFD v1 namespace exceeds ACL2 observation bound"
                                    (fnn-message e))
                            "wrong shared-budget fault: ~a" e)))
             (nfb-check faulted "sibling v1 traversal did not exhaust shared budget"))
           ;; Root consumes v1, the v1 directory consumes both children, and
           ;; the first child consumes its leaf.  The second sibling receives
           ;; zero, and the real bounded reader faults before it retains that
           ;; journal name or calls the ACL2 transition again.
           (nfb-check (equal (nreverse *nfb-observations*)
                             '((4 1) (3 2) (1 1)))
                      "raw traversal used per-directory rather than shared budget: ~s"
                      (nreverse *nfb-observations*))
           (nfb-check (and (probe-file left-journal) (probe-file right-journal))
                      "budget fault removed retained FNFD evidence"))
      (nfb-remove-tree root))))

(nfb-shared-budget-exhausts-across-siblings)
(format t "native FNFD shared-budget tests passed~%")
