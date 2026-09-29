; Teeth for books/owner-inspect-group.lisp (row S3d, lane operability-5).
(in-package "ACL2")
(include-book "../../books/owner-inspect-group")

(defun oig-art (id groups memberships)
  (fn-make-article id nil groups memberships t 841000000))

; Four articles, posted out of number order; one in two groups.
(defconst *oig-articles*
  (list (oig-art "<b@x.invalid>" '("fn.test") '(("fn.test" . 2)))
        (oig-art "<a@x.invalid>" '("fn.test") '(("fn.test" . 1)))
        (oig-art "<c@x.invalid>" '("fn.other") '(("fn.other" . 7)))
        (oig-art "<d@x.invalid>" '("fn.test" "fn.other")
                 '(("fn.test" . 3) ("fn.other" . 8)))))

(defconst *oig-all* *fn-nntp-max-article-number*)

; The rows: number order, each number to its article's Message-ID.
(assert-event (equal (fn-oig-rows "fn.test" 1 *oig-all* *oig-articles*)
                     '((1 . "<a@x.invalid>") (2 . "<b@x.invalid>") (3 . "<d@x.invalid>"))))
(assert-event (equal (fn-oig-rows "fn.other" 1 *oig-all* *oig-articles*)
                     '((7 . "<c@x.invalid>") (8 . "<d@x.invalid>"))))
; The range is honoured.
(assert-event (equal (fn-oig-rows "fn.test" 2 2 *oig-articles*)
                     '((2 . "<b@x.invalid>"))))
; A group with no article: no row.
(assert-event (null (fn-oig-rows "fn.none" 1 *oig-all* *oig-articles*)))

; KEYSTONE fn-oig-rows-number-the-listgroup-numbers, positive witnesses: the
; complete conclusion (no hypothesis) on both groups and on a sub-range.
(assert-event (equal (strip-cars (fn-oig-rows "fn.test" 1 *oig-all* *oig-articles*))
                     (fn-nntp-group-range-numbers "fn.test" 1 *oig-all* *oig-articles*)))
(assert-event (equal (fn-nntp-group-range-numbers "fn.test" 1 *oig-all* *oig-articles*)
                     '(1 2 3)))
(assert-event (equal (strip-cars (fn-oig-rows "fn.other" 1 *oig-all* *oig-articles*))
                     (fn-nntp-group-range-numbers "fn.other" 1 *oig-all* *oig-articles*)))
(assert-event (equal (strip-cars (fn-oig-rows "fn.test" 2 3 *oig-articles*))
                     (fn-nntp-group-range-numbers "fn.test" 2 3 *oig-articles*)))
(assert-event (equal (fn-nntp-group-range-numbers "fn.test" 2 3 *oig-articles*) '(2 3)))

; The report over an archive carrying both groups.
(defconst *oig-archive*
  (fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 9))
                 *oig-articles* 5 nil nil))

(assert-event
 (equal (fn-oig-report "fn.test" *oig-archive*)
        (fn-oig-text (concatenate 'string
                                  "inspect group=fn.test members=3" (string #\Newline)
                                  "1 <a@x.invalid>" (string #\Newline)
                                  "2 <b@x.invalid>" (string #\Newline)
                                  "3 <d@x.invalid>" (string #\Newline)))))
(assert-event
 (equal (fn-oig-report "fn.other" *oig-archive*)
        (fn-oig-text (concatenate 'string
                                  "inspect group=fn.other members=2" (string #\Newline)
                                  "7 <c@x.invalid>" (string #\Newline)
                                  "8 <d@x.invalid>" (string #\Newline)))))
; A group the archive does not carry: refused by name, with what it would take.
(assert-event
 (fn-oig-prefixp (fn-oig-text "refused unknown-group group=fn.none this node carries no such group; what it would take: ")
                 (fn-oig-report "fn.none" *oig-archive*)))

; fn-oig-report-exit-is-the-membership, both arms.
(assert-event (equal (fn-oig-report-exit (fn-oig-report "fn.test" *oig-archive*)) 0))
(assert-event (equal (fn-oig-report-exit (fn-oig-report "fn.other" *oig-archive*)) 0))
(assert-event (equal (fn-oig-report-exit (fn-oig-report "fn.none" *oig-archive*)) 1))
; A configured group with no article yet: the members line alone, exit 0.
(assert-event
 (equal (fn-oig-report "fn.empty"
                       (fn-make-state '("fn.empty") '(("fn.empty" . 1)) nil 0 nil nil))
        (fn-oig-text (concatenate 'string "inspect group=fn.empty members=0" (string #\Newline)))))
(assert-event
 (equal (fn-oig-report-exit
         (fn-oig-report "fn.empty" (fn-make-state '("fn.empty") '(("fn.empty" . 1)) nil 0 nil nil)))
        0))

; The kind the request carries.
(assert-event (fn-oig-kindp '(:inspect-group . "fn.test")))
(assert-event (not (fn-oig-kindp '(:inspect-group . ""))))
(assert-event (not (fn-oig-kindp '(:moderation-list . "fn.test"))))
(assert-event (not (fn-oig-kindp :inspect-group)))

; The digits: 0, a small count, a count past ten digits.
(assert-event (equal (fn-oig-nat 0) '(48)))
(assert-event (equal (fn-oig-nat 305) (fn-oig-text "305")))
(assert-event (equal (fn-oig-nat 12345678901234) (fn-oig-text "12345678901234")))
