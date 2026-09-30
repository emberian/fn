(in-package "ACL2")
(include-book "../../books/history-page-cursor")

(defconst *hpc-plan* '(:plan root (4 5) (0) (6) 1 2 allocation))
(defconst *hpc-c0* (fn-hpc-begin '(0 2) *hpc-plan* '(capture 7) '(lease 9)))
(defconst *hpc-c1* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c0*))))
(defconst *hpc-c2* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c1*))))
(defconst *hpc-c3* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c2*))))
(defconst *hpc-c4* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c3*))))
(defconst *hpc-c5* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c4*))))
(defconst *hpc-c6* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c5*))))
(defconst *hpc-c7* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c6*))))
(defconst *hpc-c8* (nth 2 (mv-list 3 (fn-hpc-tick *hpc-c7*))))

; Full literal begin antecedent and result, nonempty data/table/directory.
(assert-event
 (and (true-listp '(0 2)) (fn-his-plan-okp *hpc-plan*)
      (equal (fn-hpc-remaining *hpc-c0*)
             (fn-his-plan-writes '(0 2) *hpc-plan*))
      (equal (fn-hpc-remaining *hpc-c0*)
             '((4 0 0) (5 0 4096) (6 2 0) (1 1 1024) (2 1 3072)))))

; Each reachable phase asserts the complete residual theorem, not just status.
(defun hpc-literal-tooth (c)
  (and (fn-hpc-cursorp c)
       (equal (fn-hpc-remaining c)
              (append (if (equal (nth 0 (mv-list 3 (fn-hpc-tick c))) :emit)
                          (list (nth 1 (mv-list 3 (fn-hpc-tick c)))) nil)
                      (fn-hpc-remaining (nth 2 (mv-list 3 (fn-hpc-tick c))))))
       (fn-hpc-cursorp (nth 2 (mv-list 3 (fn-hpc-tick c))))
       (equal (fn-hpc-at 8 (nth 2 (mv-list 3 (fn-hpc-tick c)))) (fn-hpc-at 8 c))
       (equal (fn-hpc-at 9 (nth 2 (mv-list 3 (fn-hpc-tick c)))) (fn-hpc-at 9 c))))
(assert-event (hpc-literal-tooth *hpc-c0*))
(assert-event (hpc-literal-tooth *hpc-c1*))
(assert-event (hpc-literal-tooth *hpc-c2*))
(assert-event (hpc-literal-tooth *hpc-c3*))
(assert-event (hpc-literal-tooth *hpc-c4*))
(assert-event (hpc-literal-tooth *hpc-c5*))
(assert-event (hpc-literal-tooth *hpc-c6*))
(assert-event (hpc-literal-tooth *hpc-c7*))
(assert-event (hpc-literal-tooth *hpc-c8*))
(assert-event
 (and (fn-hpc-cursorp *hpc-c8*)
      (equal (nth 0 (mv-list 3 (fn-hpc-tick *hpc-c8*))) :done)
      (equal (fn-hpc-remaining *hpc-c8*) nil)))

; Corrupted-state hypothesis removal: the theorem has just cursorp as its
; hypothesis. Negative directory position violates it and the conclusion.
; Logical evaluation bypasses guards deliberately for this invalid state.
(assert-event
 (with-guard-checking :none
  (let ((c '(2 nil nil nil nil 1 -1 0 (capture 7) (lease 9))))
   (and (not (fn-hpc-cursorp c))
        (not (equal (fn-hpc-remaining c)
                    (append (if (equal (nth 0 (mv-list 3 (fn-hpc-tick c))) :emit)
                                (list (nth 1 (mv-list 3 (fn-hpc-tick c)))) nil)
                            (fn-hpc-remaining (nth 2 (mv-list 3 (fn-hpc-tick c))))))))))
)
; Mutation witness: swapping an emitted selector changes the promised plan.
(assert-event
 (and (fn-hpc-cursorp *hpc-c0*)
      (equal (nth 0 (mv-list 3 (fn-hpc-tick *hpc-c0*))) :emit)
      (not (equal (fn-hpc-remaining *hpc-c0*)
                  (cons '(4 2 0) (fn-hpc-remaining *hpc-c1*))))))

; Reachability witness through the actual image build and page-store commit.
; The earlier two-page-directory fixture tests a phase shape without claiming
; that a tiny production image would require a two-page directory.
(defun hpc-production-plan-tooth ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hrecs$c
    (mv-let (out fn-hrecs$c)
      (mv-let (verdict fn-hrecs$c) (fn-his-build '(t) 7 fn-hrecs$c)
        (let ((lpages (fn-his-lpages fn-hrecs$c)))
          (mv-let (plan fn-hrecs$c) (fn-his-commit fn-hrecs$c)
            (let ((c (fn-hpc-begin lpages plan '(capture 7) '(lease 9))))
              (mv (and (equal verdict :ok) (consp lpages)
                       (true-listp lpages) (fn-his-plan-okp plan)
                       (equal (fn-hpc-remaining c) (fn-his-plan-writes lpages plan))
                       (equal (nth 0 (mv-list 3 (fn-hpc-tick c))) :emit)
                       (hpc-literal-tooth c))
                  fn-hrecs$c)))))
      out)))
(assert-event (hpc-production-plan-tooth))
