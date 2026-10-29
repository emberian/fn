; M1: a declaration defect, not a runtime mutation.
; Original runtime locus: fn2/books/machines-a-run.lisp:82-98 (admission)
; and :126-146 (reclamation) at 137695dfc. Both use the shared allocator.
; A different capability does not imply independent admission/reclamation.
(in-package "ACL2")
(defconst *fn2-e1-independence-declaration* :different-capability)
