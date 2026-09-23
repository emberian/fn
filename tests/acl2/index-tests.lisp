; PRF-010 executable and correspondence checks.
(in-package "ACL2")
(include-book "../../books/index")

(defconst *index-groups* '("comp.lang" "fn.test"))
(defconst *index-article-a*
  (fn-make-article "<a@example.invalid>" '(65)
                   '("comp.lang" "fn.test")
                   (list (cons "comp.lang" 1)
                         (cons "fn.test" 7))
                   t 841000000))
(defconst *index-article-b*
  (fn-make-article "<b@example.invalid>" '(66)
                   '("comp.lang")
                   (list (cons "comp.lang" 4))
                   t 841000000))
; The same local number 4 is valid in fn.test and comp.lang: group is part
; of the index key, so no global number namespace is introduced.
(defconst *index-article-c*
  (fn-make-article "<c@example.invalid>" '(67)
                   '("fn.test")
                   (list (cons "fn.test" 4))
                   t 841000000))
(defconst *index-articles*
  (list *index-article-a* *index-article-b* *index-article-c*))
(defconst *index-nexts*
  (list (cons "comp.lang" 5) (cons "fn.test" 8)))
(defconst *index-state*
  (fn-make-state *index-groups* *index-nexts*
                 *index-articles* 3 nil nil))
(defconst *index-built* (fn-index-rebuild *index-state*))
(defconst *index-empty-state* (fn-initial-state *index-groups*))
(defconst *index-omitted* (cdr *index-built*))

(assert-event (fn-statep *index-state*))
(assert-event (fn-article-listp *index-groups* *index-articles*))
(assert-event (fn-index-listp *index-built*))
(assert-event (fn-index-correspondencep
               *index-built* *index-articles*))
(assert-event (equal *index-built*
                     '(("comp.lang" 1 "<a@example.invalid>")
                       ("fn.test" 7 "<a@example.invalid>")
                       ("comp.lang" 4 "<b@example.invalid>")
                       ("fn.test" 4 "<c@example.invalid>"))))

; Sparse local numbers and cross-posts are returned from the materialized list.
(assert-event
 (equal (fn-index-query-range *index-built* "comp.lang" 1 4)
        '(("comp.lang" 1 "<a@example.invalid>")
          ("comp.lang" 4 "<b@example.invalid>"))))
(assert-event
 (equal (fn-index-query-range *index-built* "fn.test" 1 8)
        '(("fn.test" 7 "<a@example.invalid>")
          ("fn.test" 4 "<c@example.invalid>"))))
(assert-event
 (equal (fn-index-query-range *index-built* "fn.test" 4 4)
        '(("fn.test" 4 "<c@example.invalid>"))))
(assert-event (equal (fn-index-query-range *index-built* "missing" 1 9)
                     nil))
(assert-event (equal (fn-index-query-range *index-built* "comp.lang" 9 2)
                     nil))

; The query and the independent source-membership enumeration agree for all
; selected ranges, including an empty range and the sparse/cross-post ranges.
(assert-event
 (equal (fn-index-query-range *index-built* "comp.lang" 1 4)
        (fn-index-reference-range "comp.lang" 1 4 *index-articles*)))
(assert-event
 (equal (fn-index-query-range *index-built* "fn.test" 1 8)
        (fn-index-reference-range "fn.test" 1 8 *index-articles*)))
(assert-event
 (equal (fn-index-query-range *index-built* "missing" 1 9)
        (fn-index-reference-range "missing" 1 9 *index-articles*)))

; A deliberately omitted entry fails the correspondence invariant and loses a
; concrete range result.  This rejects an index that is individually well typed
; but incomplete.
(assert-event (fn-index-listp *index-omitted*))
(assert-event (not (fn-index-correspondencep
                    *index-omitted* *index-articles*)))
(assert-event (not (fn-index-completep
                    *index-omitted* *index-articles*)))
(assert-event
 (not (equal (fn-index-query-range *index-omitted* "comp.lang" 1 4)
             (fn-index-reference-range "comp.lang" 1 4 *index-articles*))))

; Empty and valid state boundaries remain guard-safe and rebuild to an empty
; materialization.  No persisted ABI or host filesystem is assumed.
(assert-event (fn-statep *index-empty-state*))
(assert-event (equal (fn-index-rebuild *index-empty-state*) nil))
(assert-event (equal (fn-index-query-range nil "comp.lang" 1 9) nil))

; The public boundary refuses malformed values without relying on a caller guard.
(assert-event (equal (fn-index-query-range '(("bad" 0)) "comp.lang" 1 9)
                     nil))
(assert-event (equal (fn-index-query-range *index-built* 17 1 9)
                     nil))
(assert-event (equal (fn-index-query-range *index-built* "comp.lang" 'low 9)
                     nil))

; Soundness and completeness are separate directions: an omitted entry remains
; sourced/sound but is incomplete, while an invented entry is rejected as
; unsourced even if the rest of the source materialization is present.
(assert-event (fn-index-entry-sourcedp
               '("comp.lang" 1 "<a@example.invalid>")
               *index-articles*))
(assert-event (fn-index-soundp *index-omitted* *index-articles*))
(assert-event (not (fn-index-completep *index-omitted* *index-articles*)))
(defconst *index-invented*
  (cons '("comp.lang" 99 "<invented@example.invalid>") *index-built*))
(assert-event (fn-index-listp *index-invented*))
(assert-event (not (fn-index-entry-sourcedp
                    '("comp.lang" 99 "<invented@example.invalid>")
                    *index-articles*)))
(assert-event (not (fn-index-soundp *index-invented* *index-articles*)))
