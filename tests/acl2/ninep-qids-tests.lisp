; Internal metadata fixtures only; no installed family claim.
(in-package "ACL2")

(include-book "../../books/ninep-qids")

(defconst *n9q-session*
 '(:base 0 nil (:internal-mount 0) (nil) (:idle) (nil) (0)
   (nil) (:idle) (nil) (nil) (nil) :held nil 0 nil))

(defconst *n9q-empty*
 (list '(nil nil nil) 0 '(:internal-mount 0)))

(defconst *n9q-root-key* '(:ninep-node :root 0 nil 0))

(defconst *n9q-root-lookup* '(:ninep-qid (:ninep-node :root 0 nil 0) 0 :lookup nil nil 0))

(defconst *n9q-with-root*
 (list (list *n9q-root-key* nil nil) 1 '(:internal-mount 0)))

(defthm n9q-complete-literal-1
(and (fn-ninep-sessionp *n9q-session*) (fn-ninep-qidsp *n9q-empty*)
      (equal (fn-9pq-step *n9q-root-lookup* *n9q-session* *n9q-empty*)
             (list :qid '(128 0 0) *n9q-root-lookup*
                   (list (list *n9q-root-key* nil nil) 1 '(:internal-mount 0)))))
 :rule-classes nil)

(defconst *n9q-root-compare*
 '(:ninep-qid (:ninep-node :root 0 nil 0) 0 :compare nil nil 0))

(defthm n9q-complete-literal-2
(and (equal (fn-9pq-step *n9q-root-lookup* *n9q-session* *n9q-with-root*)
             (list :yield nil '(:ninep-qid (:ninep-node :root 0 nil 0) 0 :compare nil nil 0)
                   *n9q-with-root*))
      (equal (fn-9pq-step *n9q-root-compare* *n9q-session* *n9q-with-root*)
             (list :qid '(128 0 0) *n9q-root-compare* *n9q-with-root*)))
 :rule-classes nil)

(defconst *n9q-groups* '(:ninep-qid (:ninep-node :groups 0 nil 0) 0 :lookup nil nil 0))

(defconst *n9q-groups-next*
 '(:ninep-qid (:ninep-node :groups 0 nil 0) 1 :lookup nil nil 0))

(defthm n9q-complete-literal-3
(and (equal (mv-nth 0 (fn-9pq-step *n9q-groups* *n9q-session* *n9q-with-root*)) :yield)
      (equal (fn-9pq-step *n9q-groups-next* *n9q-session* *n9q-with-root*)
        (list :qid '(128 0 1) *n9q-groups-next*
          (list (list *n9q-root-key* '(:ninep-node :groups 0 nil 0) nil)
                2 '(:internal-mount 0)))))
 :rule-classes nil)

(defthm n9q-complete-literal-4
(and (natp 0) (fn-ninep-sessionp *n9q-session*) (fn-ninep-qidsp *n9q-with-root*)
      (not (equal (nth 13 *n9q-session*) :returned))
      (equal (fn-9pq-retire-step 0 *n9q-session* *n9q-with-root*)
             (list :await-return 0 *n9q-with-root*)))
 :rule-classes nil)

(defthm n9q-complete-literal-5
(and (not (equal (nth 2 *n9q-with-root*) '(:other-mount 1)))
      (equal (fn-9pq-step *n9q-root-lookup*
                (update-nth 3 '(:other-mount 1) *n9q-session*) *n9q-with-root*)
        (list :stale nil *n9q-root-lookup* *n9q-with-root*)))
 :rule-classes nil)

(defthm n9q-complete-literal-6
(equal (fn-9pq-step (fn-9pq-begin '(:ninep-node :group 2 (1) 0))
                    *n9q-session* *n9q-with-root*)
        (list :yield nil '(:ninep-qid (:ninep-node :group 2 (1) 0) 0 :validate nil nil 1)
              *n9q-with-root*))
 :rule-classes nil)

(defthm n9q-complete-literal-7
(equal (fn-9pq-step '(:ninep-qid (:ninep-node :group 2 (1) 0) 0 :validate nil nil 1)
                    *n9q-session* *n9q-with-root*)
        (list :invalid nil '(:ninep-qid (:ninep-node :group 2 (1) 0) 0 :validate nil nil 1)
              *n9q-with-root*))
 :rule-classes nil)
