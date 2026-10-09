(in-package "ACL2")
(include-book "../../books/book-name-relative")

(defconst *book-name-test-projects*
  '((:system . "/acl2/books/") (:fn . "/tree/")))

(assert-event (equal (book-name-relative '(:fn . "books/assumptions.lisp") nil)
                     "books/assumptions.lisp"))
(assert-event (equal (book-name-relative "/tree/books/assumptions.lisp"
                                        *book-name-test-projects*)
                     "books/assumptions.lisp"))
(assert-event (equal (book-name-relative '(:fn . "host/interfaces.lisp") nil)
                     "host/interfaces.lisp"))
(assert-event (equal (book-name-relative '(:system . "books/assumptions.lisp") nil)
                     ":system/books/assumptions.lisp"))
(assert-event (equal (book-name-relative '(:other . "books/assumptions.lisp") nil)
                     ":other/books/assumptions.lisp"))
(assert-event (equal (book-name-relative "/acl2/books/std/lists.lisp"
                                        *book-name-test-projects*)
                     ":system/std/lists.lisp"))
(assert-event (equal (book-name-relative "/other/books/assumptions.lisp"
                                        *book-name-test-projects*)
                     "/other/books/assumptions.lisp"))
(assert-event (equal (book-name-relative "/tree-impostor/books/assumptions.lisp"
                                        *book-name-test-projects*)
                     "/tree-impostor/books/assumptions.lisp"))
(assert-event (equal (book-name-relative "books/local.lisp" nil) "books/local.lisp"))
(assert-event (not (book-name-relative nil nil)))
(assert-event (not (book-name-relative '(:fn books/x.lisp) nil)))
(assert-event (not (book-name-relative '(fn . "books/x.lisp") nil)))
