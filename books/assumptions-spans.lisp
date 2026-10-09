; fn: the execution assumptions of books/def-span-scan.lisp, as constrained
; functions (AGENTS.md: a named assumption is an encapsulate with a local
; witness, and the theorems that use it mention it).
;
; Every def-span-scan instance proves a work bound about its CHARGE MODEL,
; NAME-WORK: each examined octet costs 1 plus the instance's :cost term.  No
; equation ties that term to the compiled code.  The two assumptions below
; say what the compiled code must satisfy for the charge to bound the real
; work; every instance also proves NAME-EXEC-WORK-BOUND, the same bound over
; the REAL-COST model NAME-EXEC-WORK, whose per-octet cost is
; `fn-assume-span-exec-cost', so the theorem mentions the assumption.
;
; Qualification is by functional instance: a profile supplies concrete
; functions for `fn-assume-span-exec-cost' and `fn-assume-span-cost-bound'
; with the cost bound of instance NAME equal to its :cost-max (:final-cost-max
; for a stream's final), and discharges the constraint from the disassembly
; and allocation evidence of the landing that ships NAME (the compiled body,
; read, does at most that much work and allocates nothing).  Until a profile
; exists the bound is in terms of `fn-assume-span-cost-bound'.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; A-BODY-COST.  "One execution of the compiled body of def-span-scan instance
; NAME -- KIND :body for BODY, NORM, MAP or STEP, :final for a stream's FINAL
; -- on arguments ARGS does natural work at most a bound fixed per instance and
; kind, and allocates nothing."
;
; Theorems that take it: every NAME-EXEC-WORK-BOUND, through the functional
; instance of its shape's library work bound in which the cost function is
; `(lambda (..) (fn-assume-span-exec-cost 'NAME KIND (list ..)))' and the cost
; maximum is `(fn-assume-span-cost-bound 'NAME KIND)'.

(encapsulate
  (((fn-assume-span-exec-cost * * *) => *)
   ((fn-assume-span-cost-bound * *) => *))

  (local (defun fn-assume-span-exec-cost (name kind args)
           (declare (ignore name kind args))
           0))

  (local (defun fn-assume-span-cost-bound (name kind)
           (declare (ignore name kind))
           0))

  (defthm fn-assume-span-exec-cost-bounded
    (and (natp (fn-assume-span-cost-bound name kind))
         (natp (fn-assume-span-exec-cost name kind args))
         (<= (fn-assume-span-exec-cost name kind args)
             (fn-assume-span-cost-bound name kind)))
    :rule-classes
    ((:type-prescription :corollary (natp (fn-assume-span-cost-bound name kind)))
     (:type-prescription :corollary (natp (fn-assume-span-exec-cost name kind args)))
     (:linear :corollary (<= (fn-assume-span-exec-cost name kind args)
                             (fn-assume-span-cost-bound name kind))))))

; -----------------------------------------------------------------------------
; A-RESERVED.  "The output instance a :copy or :stream call of NAME writes was
; reserved, when allocated, to at least the call's CAP, so a call that leaves
; the output's fill at most CAP neither grows nor copies the array."
;
; `(fn-assume-span-growth name cap nfill)' is the work of growing the output
; during one call of NAME with capacity CAP that ends with NFILL octets.
;
; Theorems that take it: every :copy and :stream NAME-EXEC-WORK-BOUND, which
; adds the growth term to the real-cost model and bounds the sum.

(encapsulate
  (((fn-assume-span-growth * * *) => *))

  (local (defun fn-assume-span-growth (name cap nfill)
           (declare (ignore name cap nfill))
           0))

  (defthm fn-assume-span-growth-within-cap
    (and (natp (fn-assume-span-growth name cap nfill))
         (implies (and (natp cap) (natp nfill) (<= nfill cap))
                  (equal (fn-assume-span-growth name cap nfill) 0)))
    :rule-classes
    ((:type-prescription :corollary (natp (fn-assume-span-growth name cap nfill)))
     (:rewrite :corollary (implies (and (natp cap) (natp nfill) (<= nfill cap))
                                   (equal (fn-assume-span-growth name cap nfill) 0))))))
