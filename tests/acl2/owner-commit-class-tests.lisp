; Witnesses and teeth for books/owner-commit-class.lisp (lane
; commit-onto-log, 2026-09-27; PKT-688 (4)).
;
; The keystone `fn-ocm-commit-waits-at-most-the-bound' has no hypothesis: its
; bound is BOUND less the passes already made.  Here: reachable witnesses (a
; reader storm delays a waiting commit by exactly the bound, four quanta; with
; nobody else waiting the commit is admitted at once and batches everything
; queued); the pick's facts (a commit pick keeps the four classes' cursor and
; resets the count; every other pick is fn-osch-next's); the conclusion
; failing when the commit class does NOT wait (the delay then counts every
; quantum of the sequence: must-fail against the bound); and the admission
; rule's hypothesis (idle or due) failing for a non-idle, not-yet-due pick.
(in-package "ACL2")
(include-book "../../books/owner-commit-class")
(include-book "std/testing/must-fail" :dir :system)

; The pick's two values, for assertions outside a logic function.
(defun ocmt-class (s w c)
  (mv-let (class s2) (fn-ocm-next s w c) (declare (ignore s2)) class))
(defun ocmt-state (s w c)
  (mv-let (class s2) (fn-ocm-next s w c) (declare (ignore class)) s2))
(defun ocmt-osch-class (s w)
  (mv-let (class s2) (fn-osch-next s w) (declare (ignore s2)) class))

(defconst *ocm-storm* '((0 3 0 0) (0 3 0 0) (0 3 0 0) (0 3 0 0) (0 3 0 0) (0 3 0 0)))
(defconst *ocm-idle* '((0 0 0 0)))

; A reader storm: the commit waits exactly the bound, then is admitted.
(assert-event (equal (fn-ocm-commit-delay (fn-ocm-init) *ocm-storm*) *fn-ocm-bound*))
(assert-event (equal (fn-ocm-commit-delay (fn-ocm-init) *ocm-storm*) 4))
; Nobody else waits: the commit is admitted at the first pick.
(assert-event (equal (fn-ocm-commit-delay (fn-ocm-init) *ocm-idle*) 0))
(assert-event (equal (ocmt-class (fn-ocm-init) '(0 0 0 0) t) :commit))
; A commit that has been passed over the bound is due even under the storm.
(assert-event (equal (ocmt-class (list (fn-osch-init) 4) '(0 3 0 0) t) :commit))
; Not due and not idle: the four classes' pick, and the pass is counted.
(assert-event (equal (ocmt-class (list (fn-osch-init) 1) '(0 3 0 0) t) :reader))
(assert-event (equal (fn-ocm-skipped (ocmt-state (list (fn-osch-init) 1) '(0 3 0 0) t)) 2))
; No commit waits: exactly fn-osch-next, and nothing is counted.
(assert-event (equal (ocmt-class (fn-ocm-init) '(1 3 0 0) nil)
                     (ocmt-osch-class (fn-osch-init) '(1 3 0 0))))
(assert-event (equal (fn-ocm-skipped (ocmt-state (fn-ocm-init) '(1 3 0 0) nil)) 0))
; A commit pick keeps the cursor and resets the count.
(assert-event (equal (fn-ocm-sched (ocmt-state (list '(2 x) 4) '(0 3 0 0) t)) '(2 x)))
(assert-event (equal (fn-ocm-skipped (ocmt-state (list '(2 x) 4) '(0 3 0 0) t)) 0))
; The fold ignores a commit quantum and folds the others.
(assert-event (equal (fn-ocm-observe (fn-ocm-init) :commit 5 5) (fn-ocm-init)))
(assert-event (not (equal (fn-ocm-observe (fn-ocm-init) :reader 5 5) (fn-ocm-init))))
; The slots: :commit is slot 4, the others the four classes'.
(assert-event (and (fn-ocm-classp :commit) (equal (fn-ocm-class-index :commit) 4)
                   (equal (fn-ocm-class-index :poster) 2) (not (fn-ocm-classp :other))))

; Tooth: the keystone's shape fails for a delay that is not the commit's --
; the reader storm with the commit NOT waiting runs every quantum, six, past
; the bound.  (fn-ocm-commit-delay asks with the commit waiting; the sequence
; of the four classes' own picks is what a non-waiting commit sees.)
(defun ocmt-plain-delay (s ws)
  (declare (xargs :measure (len ws)))
  (if (consp ws)
      (mv-let (class s2) (fn-ocm-next s (car ws) nil)
        (if class (+ 1 (ocmt-plain-delay s2 (cdr ws))) (ocmt-plain-delay s2 (cdr ws))))
    0))
(assert-event (equal (ocmt-plain-delay (fn-ocm-init) *ocm-storm*) 6))
(must-fail
 (assert-event (<= (ocmt-plain-delay (fn-ocm-init) *ocm-storm*) *fn-ocm-bound*)))

; Tooth: the admission rule's hypothesis.  Not idle and not due, a waiting
; commit is NOT picked.
(assert-event (not (equal (ocmt-class (list (fn-osch-init) 3) '(0 3 0 0) t) :commit)))
(must-fail
 (assert-event (equal (ocmt-class (list (fn-osch-init) 3) '(0 3 0 0) t) :commit)))
