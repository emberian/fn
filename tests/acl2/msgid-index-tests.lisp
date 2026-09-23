(in-package "ACL2")
(include-book "../../books/msgid-index")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-midx-a*
  (fn-make-article "<a@example.invalid>" '(1 2) '("fn.test")
                   '(("fn.test" . 1)) t 841000000))
(defconst *fn-midx-b*
  (fn-make-article "<b@example.invalid>" '(3 4) '("fn.test")
                   '(("fn.test" . 2)) t 841000000))
(defconst *fn-midx-a-conflict*
  (fn-make-article "<a@example.invalid>" '(9 9) '("fn.test")
                   '(("fn.test" . 3)) t 841000000))

(assert-event
 (equal (fn-midx-lookup "<b@example.invalid>"
                        (fn-midx-build (list *fn-midx-a* *fn-midx-b*)))
        *fn-midx-b*))

; Persistent extension leaves the older pinned root observable unchanged.
(defconst *fn-midx-old* (fn-midx-build (list *fn-midx-a*)))
(defconst *fn-midx-new* (fn-midx-extend *fn-midx-b* *fn-midx-old*))
(assert-event (equal (fn-midx-lookup "<a@example.invalid>" *fn-midx-old*)
                     *fn-midx-a*))
(assert-event (equal (fn-midx-lookup "<b@example.invalid>" *fn-midx-old*) nil))
(assert-event (equal (fn-midx-lookup "<b@example.invalid>" *fn-midx-new*)
                     *fn-midx-b*))

; Ordered duplicate behavior is deliberate: the same article the canonical
; scan selects wins in the derived index.
(assert-event
 (equal (fn-midx-lookup "<a@example.invalid>"
                        (fn-midx-build
                         (list *fn-midx-a-conflict* *fn-midx-a*)))
        *fn-midx-a-conflict*))

(must-fail
 (defthm fn-midx-false-last-duplicate-wins
   (equal (fn-midx-lookup "<a@example.invalid>"
                          (fn-midx-build
                           (list *fn-midx-a-conflict* *fn-midx-a*)))
          *fn-midx-a*)))

(must-fail
 (defthm fn-midx-false-lookup-without-matching-key
   (equal (fn-midx-lookup "<missing@example.invalid>"
                          (fn-midx-build (list *fn-midx-a*)))
          *fn-midx-a*)))

(assert-event
 (fn-midx-unique-branchesp
  (fn-midx-build
   (list *fn-midx-a* *fn-midx-b* *fn-midx-a-conflict*))))

; A malformed alist with repeated character branches demonstrates why the
; builder-produced uniqueness hypothesis is load-bearing for the fanout bound.
(assert-event
 (not (fn-midx-unique-branchesp
       (list (cons #\a nil) (cons #\a nil)))))
