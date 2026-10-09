(in-package "ACL2")
(include-book "../../books/def-carried")

; The same introduction, with a legacy absolute name or the :FN sysfile.
(defconst *book-provenance-absolute-world*
  '((fn-cd-get formals x)
    (include-book-path global-value "/tree/books/def-carried.lisp")
    (project-dir-alist global-value (:fn . "/tree/"))))
(defconst *book-provenance-project-world*
  '((fn-cd-get formals x)
    (include-book-path global-value (:fn . "books/def-carried.lisp"))
    (project-dir-alist global-value (:fn . "/tree/"))))
(defconst *book-provenance-legacy-world*
  (append (butlast *book-provenance-absolute-world* 1)
          '((project-dir-alist global-value))))

(assert-event (fn-cd-assumptions-bookp "/tree/books/assumptions.lisp"
                                      *book-provenance-absolute-world*))
(assert-event (fn-cd-assumptions-bookp '(:fn . "books/assumptions-recovery.lisp")
                                      *book-provenance-project-world*))
(assert-event (fn-cd-assumptions-bookp '(:fn . "books/assumptions-recovery.lisp")
                                      *book-provenance-absolute-world*))
(assert-event (fn-cd-assumptions-bookp "/tree/books/assumptions-recovery.lisp"
                                      *book-provenance-project-world*))
(assert-event (not (fn-cd-assumptions-bookp "/other/books/assumptions.lisp"
                                           *book-provenance-project-world*)))
(assert-event (not (fn-cd-assumptions-bookp '(:system . "books/assumptions.lisp")
                                           *book-provenance-project-world*)))
(assert-event (not (fn-cd-assumptions-bookp '(:other . "books/assumptions.lisp")
                                           *book-provenance-project-world*)))
(assert-event (not (fn-cd-assumptions-bookp '(:fn . "books/sub/assumptions.lisp")
                                           *book-provenance-project-world*)))
(assert-event (not (fn-cd-assumptions-bookp '(:fn . "books/not-assumptions.lisp")
                                           *book-provenance-project-world*)))
; Preserve legacy worlds without any project mapping and source-load fallback.
(assert-event (fn-cd-assumptions-bookp "/tree/books/assumptions.lisp"
                                      *book-provenance-legacy-world*))
(assert-event (not (fn-cd-assumptions-bookp "/other/books/assumptions.lisp"
                                           *book-provenance-legacy-world*)))
(assert-event (fn-cd-assumptions-bookp '(:fn . "books/assumptions.lisp")
                                      '((project-dir-alist global-value))))
(assert-event (not (fn-cd-assumptions-bookp '(:system . "books/assumptions.lisp")
                                           '((project-dir-alist global-value)))))
