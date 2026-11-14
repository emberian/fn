; UNEXECUTED arithmetic controls only. These are not physical construction,
; held-cut, resource admission or whole maintenance witnesses.
(in-package "ACL2")
(include-book "../books/checkpoint-master-abort")
(assert-event (and (equal (fn2-checkpoint-directory-budget 16) 2)
                   (equal (fn2-checkpoint-directory-budget 50) 3)
                   (< (+ 14 (fn2-checkpoint-directory-budget 16)) 17)
                   (not (< (+ 15 (fn2-checkpoint-directory-budget 16)) 17))))
; Removing the actual distinct-extent bound loses the claimed budget: 26
; allocation records cannot be covered by the 16-extent arena's two commits.
(assert-event (< (fn2-checkpoint-directory-budget 16)
                  (+ 1 (ceiling 26 *fn2-checkpoint-allocation-records-per-ticket*))))
