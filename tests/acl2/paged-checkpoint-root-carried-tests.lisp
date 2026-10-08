(in-package "ACL2")
(include-book "../../books/paged-checkpoint-root-carried")
(include-book "paged-checkpoint-cursor-tests")

(defconst *pckrc-roots*
  (list (fn-sco-cpr *pckc-base*) (fn-sco-identity *pckc-base*)
        (fn-sco-consumer *pckc-base*) (fn-sco-topic *pckc-base*)))

; Raw execution uses the carried tries. The entry is guard verified.
(defun pckrc-raw (roots ix rest s delta f plen)
  (declare (xargs :mode :program))
  (fn-pck-root-extend-carried roots ix rest s delta f plen))

(defthm pckrc-whole-antecedent
  (and (equal *pckrc-roots*
              (list (fn-sco-cpr *pckc-base*) (fn-sco-identity *pckc-base*)
                    (fn-sco-consumer *pckc-base*) (fn-sco-topic *pckc-base*)))
       (equal 2 (len (fn-sco-records *pckc-base*)))
       (fn-pck-cpr-cursorp (fn-sco-cpr *pckc-base*) *pckc-ix*
                           *pckc-rest* *sfi-t-configs*))
  :rule-classes nil
  :hints (("Goal" :use pckc-positive-has-the-whole-cursor-invariant
           :in-theory (disable fn-pck-cpr-cursorp))))

(assert-event
 (let ((out (pckrc-raw *pckrc-roots* *pckc-ix* *pckc-rest* 2
                        *pckc-delta* '(:position 3) 39)))
   (and (equal (car out)
                (fn-pck-root-tree-of-capture
                 (fn-sco-extend *pckc-base* *sfi-t-configs* *pckc-delta*)
                 '(:position 3) 39))
        (equal (car out)
                (fn-pck-root-tree-of-capture *sfi-t-base* '(:position 3) 39))
        (equal (cdr out) (cdr *pckc-out*))
        (fn-sco-pausedp (caar out)))))

(assert-event
 (not (equal (car (pckrc-raw *pckrc-roots* *pckc-ix* *pckc-rest* 3
                             *pckc-delta* nil 39))
              (fn-pck-root-tree-of-capture *sfi-t-base* nil 39))))
(must-fail-checked
 (assert-event
  (equal (car (pckrc-raw *pckrc-roots* *pckc-ix* *pckc-rest* 3
                         *pckc-delta* nil 39))
         (fn-pck-root-tree-of-capture *sfi-t-base* nil 39))))

(assert-event
 (let ((calls (sfi-t-exec-closure '(fn-pck-root-extend-carried) nil (w state))))
   (not (intersection-eq
          '(fn-cnode-statep fn-rii-ix-of fn-sco-drop fn-sco-nthcdr
            fn-sco-extend fn-rii-sco-extend fn-cei-build-aux fn-cei-branch-get)
          calls))))
