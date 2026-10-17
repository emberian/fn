; Witnesses and teeth for books/catalog-load-index (PRF-240's load by extents).
(in-package "ACL2")
(include-book "must-fail-checked")
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

; Hypothesis removal (fn-obi-extents-agreep): the extent [1, 4) is not the
; row's payload.  The hypothesis fails, the conclusion fails (the arena
; holds the wrong bytes), and the keystone without it is false.
(defconst *obi-extents-off* '((1 . 4) (0 . 0)))

