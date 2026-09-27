; Witnesses and teeth for books/catalog-load-index (PRF-240's load by extents).
(in-package "ACL2")
(include-book "../../books/catalog-load-index")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

; One article whose payload is the buffer's cells [2, 5), beside a
; non-article row (skipped by both loads), over a buffer with two leading
; cells that belong to no payload.
(defconst *obi-rec*
  (fn-record-make 0 0 0 "<obi@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3 841000000))
(defconst *obi-buf* '(7 7 65 13 10))
(defconst *obi-rows* (list *obi-rec* 'not-a-record))
(defconst *obi-extents* '((2 . 5) (0 . 0)))

; The reachable witness: the agreement holds, the load by extents is the
; fold, and the fold interned the article (one row, one sealed payload,
; whose bytes are the extent's).
(defthm obi-witness-agrees
  (fn-obi-extents-agreep *obi-rows* *obi-extents* *obi-buf*))
(defthm obi-witness-load-is-cat-load
  (equal (fn-obi-load *obi-rows* *obi-extents* *obi-buf* nil 0 nil nil)
         (fn-cat-load *obi-rows* nil 0 nil nil)))
(defthm obi-witness-load-seals-the-extent
  (equal (mv-nth 0 (fn-obi-load *obi-rows* *obi-extents* *obi-buf* nil 0 nil nil))
         (list '(65 13 10))))
(defthm obi-witness-load-commits-one-row
  (equal (len (mv-nth 1 (fn-obi-load *obi-rows* *obi-extents* *obi-buf* nil 0 nil nil)))
         1))

; Hypothesis removal (fn-obi-extents-agreep): the extent [1, 4) is not the
; row's payload.  The hypothesis fails, the conclusion fails (the arena
; holds the wrong bytes), and the keystone without it is false.
(defconst *obi-extents-off* '((1 . 4) (0 . 0)))
(defthm obi-off-disagrees
  (not (fn-obi-extents-agreep *obi-rows* *obi-extents-off* *obi-buf*)))
(defthm obi-off-load-differs
  (not (equal (fn-obi-load *obi-rows* *obi-extents-off* *obi-buf* nil 0 nil nil)
              (fn-cat-load *obi-rows* nil 0 nil nil))))
(local (must-fail (defthm obi-load-without-agreement
                    (equal (fn-obi-load rows extents fn-octets keyring generation fn-arena fn-cat)
                           (fn-cat-load rows keyring generation fn-arena fn-cat))
                    :hints (("Goal" :do-not-induct t
                             :in-theory (theory 'minimal-theory))))))
