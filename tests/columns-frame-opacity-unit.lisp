; Default frame hints preserve the public observation and every claim.
(in-package "ACL2")
(include-book "../books/columns")

; All result ABIs and a conditional non-frame facet in one expansion.
; Frame equalities remain unconditional, independently of supplied H.
(assert-event
 (equal
  (fn2-columns-preservation-facts 'sample '(sample x)
   '(("-DIRECT" observe nil :frame x)
     ("-FIRST" observe 0 :frame x :hyps ((irrelevant x)))
     ("-THIRD" observe 2 :frame x :rule-classes nil)
     ("-TYPE" valid 1 :hyps ((selected x))))
   '((outer-hyp x)) nil)
  '((defthm sample-direct (equal (observe (sample x)) (observe x))
     :hints (("Goal" :in-theory (disable observe))))
    (defthm sample-first (equal (observe (car (sample x))) (observe x))
     :hints (("Goal" :in-theory (disable observe))))
    (defthm sample-third (equal (observe (mv-nth 2 (sample x))) (observe x))
     :hints (("Goal" :in-theory (disable observe))) :rule-classes nil)
    (defthm sample-type (implies (and (selected x)) (valid (mv-nth 1 (sample x))))))))

; Caller hints retain their old precedence; per-spec hints override them.
; Explicit per-spec NIL opts out rather than silently acquiring the default.
(assert-event
 (equal
  (fn2-columns-preservation-facts 'sample '(sample x)
   '(("-CALLER" observe nil :frame x)
     ("-SPEC" observe nil :frame x :hints (("Goal" :use exact-local-fact)))
     ("-NONE" observe nil :frame x :hints nil))
   nil '(("Goal" :in-theory (enable observe))))
  '((defthm sample-caller (equal (observe (sample x)) (observe x))
     :hints (("Goal" :in-theory (enable observe))))
    (defthm sample-spec (equal (observe (sample x)) (observe x))
     :hints (("Goal" :use exact-local-fact)))
    (defthm sample-none (equal (observe (sample x)) (observe x))))))
(assert-event
 (equal
  (fn2-columns-preservation-facts 'sample '(sample x)
   '(("-NONE" observe nil :frame x :hints nil)) nil nil)
  '((defthm sample-none (equal (observe (sample x)) (observe x))))))

; Actual opaque-callee composition, not only a comparison of generated text.
(defcolumns fn2-frame-cell ((value :u8)))
(defun fn2-frame-leaf (i value fn2-frame-cell)
 (declare (xargs :stobjs fn2-frame-cell
  :guard (and (fn2-frame-cell-wfp fn2-frame-cell)
              (natp i) (< i (fn2-frame-cell-rows fn2-frame-cell))
              (unsigned-byte-p 8 value))))
 (fn2-frame-cell-set-value i value fn2-frame-cell))
(fn2-frame-cell-preserves fn2-frame-leaf (i value fn2-frame-cell)
 :specs (("-ROWS" fn2-frame-cell-rows nil :frame fn2-frame-cell)))
(defun fn2-frame-wrapper (i value fn2-frame-cell)
 (declare (xargs :stobjs fn2-frame-cell
  :guard (and (fn2-frame-cell-wfp fn2-frame-cell)
              (natp i) (< i (fn2-frame-cell-rows fn2-frame-cell))
              (unsigned-byte-p 8 value))))
 (fn2-frame-leaf i value fn2-frame-cell))
(fn2-frame-cell-preserves fn2-frame-wrapper (i value fn2-frame-cell)
 :specs (("-ROWS" fn2-frame-cell-rows nil :frame fn2-frame-cell)))
(assert-event (eq (symbol-class 'fn2-frame-wrapper (w state)) :common-lisp-compliant))
