;;; SCN1137 actual guarded BP projection and actual heap profile consumer.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "COMMON-LISP"))
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
(defun fnn-heap-history-observation (root profile)
  (declare (ignorable root profile))
  (harness-stub-reached 'fnn-heap-history-observation "host/native/heap.lisp"))
(defun fnn-heap-operator-profile (config-path words)
  (declare (ignorable config-path words))
  (harness-stub-reached 'fnn-heap-operator-profile "host/native/heap.lisp"))
;;; ---- derived stubs: END ----
(declaim (declaration xargs))
(defun posp (x) (and (integerp x) (< 0 x)))
(defun source-functions (path names)
 (with-open-file (in path)
  (loop for form = (read in nil :eof) until (eq form :eof)
   when (and (consp form) (eq (car form) 'defun) (member (second form) names))
   do (progn (eval form) (setf names (remove (second form) names)))
   finally (assert (null names)))))
(source-functions "books/bp-heap-command.lisp"
 '(fn-bph-decimal-characters fn-bph-connections fn-bph-command-plan fn-bph-refusal-line
   fn-bph-before-control fn-bph-node-serve-p fn-bph-node-journal fn-bph-node-transfer))
(defvar *events* nil)
(define-condition fixture-refused (error) ())
(defun fnn-core (name &rest args) (apply name args))
(defun fnn-absolute (root) (concatenate 'string "/captured/" root))
(defun fnn-heap-store-profile (root)
 (push (list :profile root) *events*) (list :profile root))
(defun fnn-refuse (&rest args) (declare (ignore args)) (error 'fixture-refused))
(source-functions "books/peer-flight-startup.lisp" '(fn-pfr-operation-observes-p))
;; A served run observes its peer authority file (fnn-peer-flight-profile,
;; host/native/heap.lisp): recorded here, the store root it is read under.
(defun fnn-peer-flight-profile (root)
 (push (list :peer root) *events*) (list :peer root))
(source-functions "host/native/heap.lisp" '(fnn-heap-command-profile-base fnn-heap-command-profile))
(dolist (entry
 '((("bp-node" "serve" "0" "journal" "store" "receipts" "workflow" "node" "peer" "dest" "policy" "issuer" "host" "4556") 1)
   (("bp-app" "receive" "0" "spool" "store" "receipts" "node" "peer" "dest" "policy" "issuer" "1" "02") 2)))
 (let ((*events* nil))
  (assert (equal (multiple-value-list (fnn-heap-command-profile (first entry)))
                 (list '(:profile "/captured/store") (second entry) :run nil nil nil "/captured/store"
                       '(:peer "/captured/store") nil)))
  (assert (equal *events* '((:peer "/captured/store") (:profile "/captured/store"))))))
(dolist (argv
 '(("bp-node" "serve")
   ("bp-node" "serve" "0" "journal" "store")
   ("bp-app" "receive" "0" "spool" "store" "receipts" "node" "peer" "dest" "policy" "issuer" "1" "0")
   ("bp-app" "receive" "0" "spool" "store" "receipts" "node" "peer" "dest" "policy" "issuer" "1" "18446744073709551616")))
 (let ((*events* nil) (refused nil))
  (handler-case (fnn-heap-command-profile argv) (fixture-refused () (setq refused t)))
  (assert refused) (assert (null *events*))))
(let ((*events* nil))
 (assert (equal (multiple-value-list
                 (fnn-heap-command-profile '("bp-node" "dispatch" "journal" "store")))
                '(nil 0 nil nil nil nil nil nil nil)))
 (assert (null *events*)))
;; The probe's BP terms (fnn-heap-bp-terms): the two profiles read under the
;; command's journal root with the node's own readers, the transfer argument
;; (default when absent) and the segment MRU; nothing for any other command.
(defconstant +fnn-tcl-transfer-mru+ 1048576)
(defconstant +fnn-tcl-segment-mru+ 1024)
(defun fnn-bp-session-profile (root) (push (list :session root) *events*) (list :session root))
(defun fnn-bps-read-profile (root) (push (list :node root) *events*) (list :node root))
(source-functions "host/native/bp-node.lisp" '(fnn-heap-bp-terms))
(let ((*events* nil))
 (assert (equal (fnn-heap-bp-terms '("bp-node" "serve" "0" "journal" "store" "receipts" "workflow" "node" "peer"
                                     "dest" "policy" "issuer" "host" "4556" "1" "3600000" "2" "32" "65536"))
                '((:session "journal") (:node "journal") 65536 1024)))
 (assert (equal (fnn-heap-bp-terms '("bp-node" "serve" "0" "journal" "store" "receipts" "workflow" "node" "peer"
                                     "dest" "policy" "issuer" "host" "4556"))
                '((:session "journal") (:node "journal") 1048576 1024))))
(let ((*events* nil))
 (assert (null (fnn-heap-bp-terms '("bp-app" "receive" "0" "spool" "store" "receipts" "node" "peer" "dest"
                                    "policy" "issuer" "1" "02"))))
 (assert (null (fnn-heap-bp-terms '("bp-node" "dispatch" "journal" "store"))))
 (assert (null *events*)))
(let ((refused nil))
 (handler-case (fnn-heap-bp-terms '("bp-node" "serve" "0" "journal" "store" "receipts" "workflow" "node" "peer"
                                    "dest" "policy" "issuer" "host" "4556" "1" "3600000" "2" "32" "0"))
  (fixture-refused () (setq refused t)))
 (assert refused))
(format t "PASS actual BP heap source root and connection propagation~%")
