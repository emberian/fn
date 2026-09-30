(in-package "ACL2")
(include-book "../../books/group-number-source-lookup")
; Logical fixture rows in this leaf's unchanged held-record coordinate.
(defun fn-tgnq-held (groups) (declare (xargs :guard t))
  (list 0 0 0 "<a@x>" 0 groups nil nil nil 0 0 nil nil nil nil))
(defun fn-tgnq-run (fuel c)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (fn-gns-stage-cursorp c))
         (member-eq (fn-gns-at 0 c) '(:done :refused))) c
   (fn-tgnq-run (1- fuel) (fn-gns-stage-step c))))
(defun fn-tgnq-old-match (g n root cat) (declare (xargs :guard (stringp g)))
 (equal (fn-gnix-get n (fn-gns-group-value-root (fn-gns-group-get g 0 0 root)))
        (fn-gns-ordinal-option (fn-cat-number-seq g n cat 0))))
(defun fn-tgnq-conclusion (g n c h cat) (declare (xargs :guard (and (stringp g) (true-listp cat))))
 (equal (fn-gnix-get n (fn-gns-group-value-root
                       (fn-gns-group-get g 0 0 (fn-gns-at 1 (fn-gns-stage-result c)))))
        (fn-gns-ordinal-option
          (fn-cat-number-seq g n (append cat (list (fn-cat-assign h cat))) 0))))
(defun fn-tgnq-denotation (c h cat root) (declare (xargs :guard (and (true-listp cat) (fn-gns-stage-cursorp c))))
 (equal (fn-gns-stage-denotation c)
        (fn-gns-memberships-root (fn-cat-assign-numbers (fn-record-groups h) cat)
                                (len cat) root)))
(defconst *tgnq-h* (fn-tgnq-held '("a")))
(defconst *tgnq-c* (fn-tgnq-run 100 (fn-gns-stage-begin
                   (fn-cat-assign-numbers (fn-record-groups *tgnq-h*) nil) 0 nil)))
; Reachable positive: all five hypotheses, actual terminal result and ordinal0.
(assert-event (and (fn-gns-stage-cursorp *tgnq-c*)
 (eq (fn-gns-at 0 *tgnq-c*) :done) (fn-tgnq-denotation *tgnq-c* *tgnq-h* nil nil)
 (posp 1) (fn-gns-membershipsp (fn-cat-assign-numbers (fn-record-groups *tgnq-h*) nil))
 (fn-tgnq-old-match "a" 1 nil nil) (fn-tgnq-conclusion "a" 1 *tgnq-c* *tgnq-h* nil)
 (equal (fn-cat-number-seq "a" 1 (list (fn-cat-assign *tgnq-h* nil)) 0) 0)))
; Removal: completion phase only.
(assert-event (let ((c (fn-gns-stage-begin (fn-cat-assign-numbers '("a") nil) 0 nil)))
 (and (not (eq (fn-gns-at 0 c) :done)) (fn-tgnq-denotation c *tgnq-h* nil nil)
      (posp 1) (fn-gns-membershipsp (fn-cat-assign-numbers '("a") nil))
      (fn-tgnq-old-match "a" 1 nil nil) (not (fn-tgnq-conclusion "a" 1 c *tgnq-h* nil)))))
; Corrupted schedule: remove exact carried stage denotation only.
(assert-event (let ((c (fn-tgnq-run 4 (fn-gns-stage-begin nil 0 nil))))
 (and (eq (fn-gns-at 0 c) :done) (not (fn-tgnq-denotation c *tgnq-h* nil nil))
      (posp 1) (fn-gns-membershipsp (fn-cat-assign-numbers '("a") nil))
      (fn-tgnq-old-match "a" 1 nil nil) (not (fn-tgnq-conclusion "a" 1 c *tgnq-h* nil)))))
; Guard-external query: number0 aliases generic trie root1, not local number1.
(assert-event (and (eq (fn-gns-at 0 *tgnq-c*) :done)
 (fn-tgnq-denotation *tgnq-c* *tgnq-h* nil nil) (not (posp 0))
 (fn-gns-membershipsp (fn-cat-assign-numbers '("a") nil))
 (fn-tgnq-old-match "a" 0 nil nil) (not (fn-tgnq-conclusion "a" 0 *tgnq-c* *tgnq-h* nil))))
; Corrupted row: malformed earlier membership prevents supported fold.
(assert-event (let* ((h (fn-tgnq-held '(7 "a")))
                     (c (fn-tgnq-run 4 (fn-gns-stage-begin nil 0 nil))))
 (and (eq (fn-gns-at 0 c) :done) (fn-tgnq-denotation c h nil nil) (posp 1)
      (not (fn-gns-membershipsp (fn-cat-assign-numbers (fn-record-groups h) nil)))
      (fn-tgnq-old-match "a" 1 nil nil) (not (fn-tgnq-conclusion "a" 1 c h nil)))))
; Corrupted old root: new row has no groups, retained catalog lookup is lost.
(assert-event (let* ((h (fn-tgnq-held nil)) (cat (list (fn-cat-assign *tgnq-h* nil)))
                     (c (fn-tgnq-run 4 (fn-gns-stage-begin nil 1 nil))))
 (and (eq (fn-gns-at 0 c) :done) (fn-tgnq-denotation c h cat nil) (posp 1)
      (fn-gns-membershipsp (fn-cat-assign-numbers (fn-record-groups h) cat))
      (not (fn-tgnq-old-match "a" 1 nil cat)) (not (fn-tgnq-conclusion "a" 1 c h cat)))))
