(in-package "ACL2")
(include-book "../../books/paged-checkpoint-root-extend")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)
(defun pck-root-test-record (s)
  (fn-store-retention-event-make :undertake s (+ 1 s) 0 "o" "s" "e" 1))
(defconst *pck-root-test-prefix* (list (pck-root-test-record 0)))
(defconst *pck-root-test-delta* (list (pck-root-test-record 1)))
(defconst *pck-root-test-c* (fn-sco-capture nil *pck-root-test-prefix*))
(defconst *pck-root-test-roots*
  (list (fn-sco-cpr *pck-root-test-c*) (fn-sco-identity *pck-root-test-c*)
        (fn-sco-consumer *pck-root-test-c*) (fn-sco-topic *pck-root-test-c*)))
(assert-event
 (and (equal *pck-root-test-roots*
             (list (fn-sco-cpr *pck-root-test-c*) (fn-sco-identity *pck-root-test-c*)
                   (fn-sco-consumer *pck-root-test-c*) (fn-sco-topic *pck-root-test-c*)))
      (equal 1 (len (fn-sco-records *pck-root-test-c*)))
      (consp *pck-root-test-delta*)
      (equal (fn-pck-root-extend *pck-root-test-roots* 1 nil *pck-root-test-delta* :f 140)
             (fn-pck-root-tree-of-capture
              (fn-sco-extend *pck-root-test-c* nil *pck-root-test-delta*) :f 140))))
(assert-event
 (not (equal (fn-pck-root-extend *pck-root-test-roots* 0 nil *pck-root-test-delta* :f 140)
             (fn-pck-root-tree-of-capture
              (fn-sco-extend *pck-root-test-c* nil *pck-root-test-delta*) :f 140))))
(must-fail-checked
 (assert-event
  (equal (fn-pck-root-extend *pck-root-test-roots* 0 nil *pck-root-test-delta* :f 140)
         (fn-pck-root-tree-of-capture
          (fn-sco-extend *pck-root-test-c* nil *pck-root-test-delta*) :f 140))))
