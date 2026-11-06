; The served authority keystone's evidence (books/owed-authority.lisp):
; the positive trace asserting the whole antecedent and conclusion and the
; branches it exercised, and one hypothesis-removal witness per hypothesis,
; each an unauthorized commit on the served path.
(in-package "ACL2")
(include-book "../books/owed-authority")
(include-book "std/testing/assert-bang" :dir :system)

(assert-event (fn2-authority-served-enforced-positive))
(assert-event (fn2-authority-served-binding-removed))
(assert-event (fn2-authority-served-current-removed))
(assert-event (fn2-authority-served-publication-removed))
