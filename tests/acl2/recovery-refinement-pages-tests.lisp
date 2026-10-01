; Teeth for books/recovery-refinement-pages (lane recovery-refinement-2,
; 2026-10-01; PRF-1215): the generation bound on the ground page store of
; tests/acl2/pagestore-tests.lisp (re-made here under its own prefix, the
; digest seam attached to the same toy structural hash): the plan of one
; dirty page writes 3 pages, within the generation 3; the plan of two dirty
; pages writes 5, within 5; two such commits fit the reserve for K = 1,
; D = 2; the hypothesis removal (a dirty set past K * D: the reserve is
; exceeded) and the MUTATION (a commit that writes its pages twice is past
; its generation).
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/recovery-refinement-pages")

(defun rrp-t-toy-h (x)
  ; A digest that separates every pair of contents the witnesses compare.
  ; Not a hash.
  (declare (xargs :guard t))
  (acl2-count x))
(defattach pgs-digest rrp-t-toy-h)

(defun rrp-t-tab () (list (list 2 1 (pgs-digest "alpha")) (list 3 1 (pgs-digest "beta"))))
(defun rrp-t-dir () (list (list 1 1 (pgs-digest (rrp-t-tab)))))
(defun rrp-t-rec () (pgs-make-rec 1 6 2 (pgs-digest (rrp-t-dir))))
(defun rrp-t-pages ()
  (list (cons 6 (rrp-t-dir)) (cons 1 (rrp-t-tab)) (cons 2 "alpha") (cons 3 "beta")
        (cons 4 "stale")))
(defun rrp-t-d0 () (cons (rrp-t-pages) (list (cons :main (cons (rrp-t-rec) nil)))))
(defun rrp-t-alloc () (list (list 5 4) 7))
(defun rrp-t-plan (dirty) (pgs-plan-commit (rrp-t-d0) :main :eager dirty (rrp-t-alloc)))

; Reachable: the store opens, the plan of one dirty page is a plan of three
; writes (the data page, its table page, the directory), within the
; generation of one; the plan of two dirty pages (one grown) writes five,
; within the generation of two; the reserve for K = 1 record of D = 2
; pages holds two such commits.
(assert-event
 (and (equal (pgs-view (pgs-open (rrp-t-d0) :main :eager)) '(1 ("alpha" "beta")))
      (equal (car (rrp-t-plan (list (cons 1 "new")))) :plan)
      (equal (len (second (rrp-t-plan (list (cons 1 "new"))))) 3)
      (<= (len (second (rrp-t-plan (list (cons 1 "new")))))
          (fn-rrp-generation-pages 1))
      (equal (car (rrp-t-plan (list (cons 1 "new") (cons 2 "grown")))) :plan)
      (equal (len (second (rrp-t-plan (list (cons 1 "new") (cons 2 "grown"))))) 4)
      (<= (len (second (rrp-t-plan (list (cons 1 "new") (cons 2 "grown")))))
          (fn-rrp-generation-pages 2))
      (equal (fn-rrp-reserve-pages 1 2) 10)
      (<= (+ (len (second (rrp-t-plan (list (cons 1 "new") (cons 2 "grown")))))
             (len (second (rrp-t-plan (list (cons 1 "new") (cons 2 "grown"))))))
          (fn-rrp-reserve-pages 1 2))))

; The bound is not slack by more than the table sharing: one dirty page
; writes exactly its generation.
(assert-event
 (equal (len (second (rrp-t-plan (list (cons 1 "new"))))) (fn-rrp-generation-pages 1)))

; Hypothesis removal: a dirty set past K * D (two dirty pages against
; K = 1, D = 1) is not within the reserve for two commits: 4 + 4 > 6; the
; plan itself is still a plan (every retained hypothesis holds).
(assert-event
 (and (equal (car (rrp-t-plan (list (cons 1 "new") (cons 2 "grown")))) :plan)
      (not (<= (len (list (cons 1 "new") (cons 2 "grown"))) (* 1 1)))
      (equal (fn-rrp-reserve-pages 1 1) 6)))
(must-fail-checked
 (defthm rrp-t-past-the-dirty-bound
   (<= (+ (len (second (rrp-t-plan (list (cons 1 "new") (cons 2 "grown")))))
          (len (second (rrp-t-plan (list (cons 1 "new") (cons 2 "grown"))))))
       (fn-rrp-reserve-pages 1 1))))

; MUTATION: a commit that writes its pages twice (the plan's writes
; appended to themselves) is past its generation.
(defun rrp-t-doubled-writes (dirty)
  (let ((w (second (rrp-t-plan dirty)))) (append w w)))
(assert-event (equal (len (rrp-t-doubled-writes (list (cons 1 "new")))) 6))
(must-fail-checked
 (defthm rrp-t-doubled-commit-within-the-generation
   (<= (len (rrp-t-doubled-writes (list (cons 1 "new")))) (fn-rrp-generation-pages 1))))
