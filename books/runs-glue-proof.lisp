; Discharges owed obligations for runs-glue.
;
; fn2-run-glue-verified is emitted by the macro (fn2-run-assemble), which
; runs-assemble.lisp defines and runs-served.lisp invokes; the row and
; fn2-run-glue-assembled exist only in a world that includes runs-served.
; Scope: the theorem is a ground evaluation of fn2-run-glue-check over the
; symbol-class snapshot runs-served froze at its certification (19 schemas),
; not a statement about any other assembly or a later world.
(in-package "ACL2")
(include-book "runs-served")
(include-book "owed-discharge")
(fn2-book-layer :c)

(defthm fn2-run-glue-verified-proved
  (fn2-run-glue-verified$owed)
  :hints (("Goal" :in-theory (enable fn2-run-glue-verified$owed)))
  :rule-classes nil)

(fn2-owed-discharge fn2-run-glue-verified fn2-run-glue-verified-proved)
