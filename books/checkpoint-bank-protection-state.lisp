; Canonical readonly cold evidence/receipt definitions, shared by boot
; and terminal disposal. No capture, selection, mutation or readiness input.
(in-package "ACL2")
(include-book "checkpoint-bank-closure-state")
(fn2-book-layer :b)

(defcolumns fn2-checkpoint-bank-protection
 ((phase (:enum fn2-checkpoint-bank-protection-phase (:idle :walking :protected :uncertain)))
  (cursor :u32) (total :u32) (bound-mask :u8) (tag :u60) (generation :u60)
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (edge-total :u32) (ops-rows :u32) (candidate-rows :u32))
 :extra-fields ((fn2-checkpoint-bank-protection-sources :type (array (unsigned-byte 60) (72)) :initially 0
  :why "All four exact retained generations/tags/full descriptor+anchor identities; masked by row phase after owner init.")))

(defun fn2-checkpoint-bank-protection-source-word (i fn2-checkpoint-bank-closures)
 (declare (xargs :stobjs fn2-checkpoint-bank-closures :guard (and (fn2-checkpoint-bank-closures-wfp fn2-checkpoint-bank-closures) (natp i) (< i 72))))
 (let ((slot (floor i 18)) (word (mod i 18)))
  (cond ((= word 0) (fn2-checkpoint-bank-closures-capture-generationi slot fn2-checkpoint-bank-closures))
        ((= word 1) (fn2-checkpoint-bank-closures-capture-tagi slot fn2-checkpoint-bank-closures))
        (t (fn2-checkpoint-bank-closures-identityi (+ (* slot 16) (- word 2)) fn2-checkpoint-bank-closures)))))

(defun fn2-checkpoint-bank-protection-sources-p (i fn2-checkpoint-bank-closures fn2-checkpoint-bank-protection)
 (declare (xargs :stobjs (fn2-checkpoint-bank-closures fn2-checkpoint-bank-protection)
  :measure (nfix (- 72 (nfix i))) :guard (and (fn2-checkpoint-bank-closures-wfp fn2-checkpoint-bank-closures) (fn2-checkpoint-bank-protection-wfp fn2-checkpoint-bank-protection) (natp i) (<= i 72))))
 (or (>= (nfix i) 72)
  (and (= (fn2-checkpoint-bank-protection-sourcesi i fn2-checkpoint-bank-protection) (fn2-checkpoint-bank-protection-source-word i fn2-checkpoint-bank-closures))
       (fn2-checkpoint-bank-protection-sources-p (+ 1 (nfix i)) fn2-checkpoint-bank-closures fn2-checkpoint-bank-protection))))
