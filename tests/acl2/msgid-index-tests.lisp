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

; The served Message-ID form is nonempty.  A malformed article identifier
; cannot shadow its character path, so the correspondence needs no scan of
; the entire article list to establish a string-list recognizer per command.
(defconst *fn-midx-malformed*
  (fn-make-article nil '(7) '("fn.test")
                   '(("fn.test" . 4)) t 841000000))
(assert-event
 (equal (fn-midx-lookup "<a@example.invalid>"
                        (fn-midx-build
                         (list *fn-midx-malformed* *fn-midx-a*)))
        *fn-midx-a*))

; Dropping either query hypothesis changes the result for malformed input.
(must-fail
 (defthm fn-midx-false-empty-query-correspondence
   (equal (fn-midx-lookup "" (fn-midx-build (list *fn-midx-malformed*)))
          (fn-find-article "" (list *fn-midx-malformed*)))))
(must-fail
 (defthm fn-midx-false-nonstring-query-correspondence
   (equal (fn-midx-lookup nil (fn-midx-build (list *fn-midx-malformed*)))
          (fn-find-article nil (list *fn-midx-malformed*)))))

; A retention/configuration-only refresh reuses the pinned root; a single
; acceptance extends it; a recovered discontinuity rebuilds the new view.
(assert-event
 (equal (fn-midx-refresh *fn-midx-old* (list *fn-midx-a*)
                         (list *fn-midx-a*))
        *fn-midx-old*))
(assert-event
 (equal (fn-midx-refresh *fn-midx-old* (list *fn-midx-a*)
                         (list *fn-midx-b* *fn-midx-a*))
        *fn-midx-new*))
(assert-event
 (equal (fn-midx-refresh *fn-midx-old* (list *fn-midx-a*)
                         (list *fn-midx-b*))
        (fn-midx-build (list *fn-midx-b*))))

; A stale root is observably wrong for the new accepted article: refresh's
; premise must relate the old root to the old list.
(must-fail
 (defthm fn-midx-false-refresh-with-stale-root
   (fn-midx-correspondencep
    (fn-midx-refresh nil (list *fn-midx-a*)
                     (list *fn-midx-b* *fn-midx-a*))
    (list *fn-midx-b* *fn-midx-a*))))
