(in-package "ACL2")
(include-book "../../books/history-census-controller")

; Only the fixture driver reads a logical pool; real supply is authenticated
; by the outer source/pin/read serial boundary.
(defun fn-hct-test-drive (fuel c pool)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (list :fuel c)
    (mv-let (v result next) (fn-hct-tick c)
      (cond ((member-eq v '(:prepared :row-done)) (list v result next))
            ((eq v :continue) (fn-hct-test-drive (1- fuel) next pool))
            ((fn-hsrcb-demandp v)
             (mv-let (sv supplied)
               (fn-hct-supply c (fn-hrcur-field 1 v)
                              (nth (fn-hrcur-field 1 v) pool))
               (if (eq sv :continue) (fn-hct-test-drive (1- fuel) supplied pool)
                 (list sv supplied))))
            (t (list v result next))))))


(assert-event
 (mv-let (v offered)
   (fn-hct-offer (fn-hct-begin 1 :capture :lease) 0 '(:decoded (:span 3 0 1 3)))
   (let ((done (fn-hct-test-drive 100 offered '(0 65 66 67))))
     (mv-let (terminal census final) (fn-hct-tick (caddr done))
       (and (eq v :started) (equal (car done) :row-done)
            (equal (cadr done) (len (fn-scc-encode "ABC")))
            (eq terminal :prepared)
            (equal census (list 1 (+ (len (fn-scc-encode "ABC")) (fn-hp-pad8-count (len (fn-scc-encode "ABC"))))))
            (equal final (caddr done)))))))

(assert-event
 (mv-let (v offered)
   (fn-hct-offer (fn-hct-begin 1 :capture :lease) 0 '(:resident "ABC"))
   (let ((done (fn-hct-test-drive 100 offered nil)))
     (and (eq v :started) (equal (car done) :row-done)
          (equal (cadr done) (len (fn-scc-encode "ABC")))
          (equal (fn-hrcur-field 3 (caddr done))
                 (+ (len (fn-scc-encode "ABC")) (fn-hp-pad8-count (len (fn-scc-encode "ABC")))))))))

; Opaque-span supply emits directly: account it exactly once before tick.
(assert-event
 (let* ((child (list :cold (list :opaque-span nil 1 nil :capture :lease nil
                                   '(:span 6 0 1 1) 1)))
        (c (list :codec 1 0 0 (list :active child 0) :capture :lease)))
   (mv-let (demand ignored held) (fn-hct-tick c)
     (declare (ignore ignored))
     (mv-let (bad-word bad-c) (fn-hct-supply c 2 65)
       (mv-let (word next) (fn-hct-supply c 1 65)
         (and (equal demand '(:need-byte 1 :opaque-span 1))
              (equal held c)
              (equal bad-word '(:refused :cold-demand-position))
              (equal bad-c c) (eq word :continue)
              (equal (fn-hrcur-field 2 (fn-hrcur-field 4 next)) 1)
              (equal (fn-hrcur-field 5 next) :capture)
              (equal (fn-hrcur-field 6 next) :lease)))))))
