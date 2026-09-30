; Shared exact proof-only models of the public borrowed history feed.
; These are not host loops or node validators. One definition is shared by
; the inverse refinement and the actual cold-source carry proof.
(in-package "ACL2")
(include-book "history-decode-stream")

(defun-nx fn-hdc-model-run (fuel s pool)
  (if (or (zp fuel) (member-eq (nth 0 s) '(:done :refused))) s
    (fn-hdc-model-run (1- fuel) (fn-hdc-feed (nth (nth 7 s) pool) s) pool)))

(defthm fn-hdc-model-run-preserves-source-end
  (equal (nth 8 (fn-hdc-model-run fuel s pool)) (nth 8 s))
  :hints (("Goal" :induct (fn-hdc-model-run fuel s pool)
           :in-theory (e/d (fn-hdc-model-run) (fn-hdc-feed)))))

(defun-nx fn-hdc-node-in-poolp (node end)
 (declare (xargs :measure (acl2-count node)))
 (and (true-listp node)
      (cond ((eq (car node) :atom) (equal (len node) 2))
            ((eq (car node) :pair)
             (and (equal (len node) 3)
                  (fn-hdc-node-in-poolp (cadr node) end)
                  (fn-hdc-node-in-poolp (caddr node) end)))
            ((eq (car node) :span)
             (and (equal (len node) 5) (member-equal (cadr node) '(3 4 6))
                  (natp (caddr node)) (< (caddr node) 3)
                  (natp (nth 3 node)) (natp (nth 4 node))
                  (<= (+ (nth 3 node) (nth 4 node)) end)))
            (t nil))))

(defun-nx fn-hdc-stack-in-poolp (stack end)
 (if (consp stack)
     (and (fn-hdc-node-in-poolp (car stack) end)
          (fn-hdc-stack-in-poolp (cdr stack) end))
   (null stack)))

(in-theory (disable fn-hdc-model-run fn-hdc-node-in-poolp fn-hdc-stack-in-poolp))
