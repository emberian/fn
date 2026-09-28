; Witnesses for the served reads' loop twins (PKT-877, lane serve-depth).
;
; Each walk below is (mbe :logic <its recursion, unchanged> :exec <a loop>),
; and its verify-guards event proves the two equal on every input satisfying
; the guard.  These run the executable -- the loop -- in order, on the edge
; cases, and over 50,000 elements: a group of 50,000 committed articles (the
; walks LIST ACTIVE, GROUP, NEXT, LAST and LISTGROUP make), 50,000 configured
; groups (LIST ACTIVE's line walk), a number list sorted from an order that
; is not descending (the insertion loop), 100,000 characters and octets (the
; syntax conversions) and 50,000 reply pieces.  Before, each recursed once per
; element, and at a node thread's 1,024 KiB the owner died past ~30,000
; articles (native-sd1, planning/evidence/serve-depth-2026-09-28.md).

(in-package "ACL2")
(include-book "../../books/nntp-index")

(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary)))

; -----------------------------------------------------------------------------
; A group of N articles: article I (from 1) is <aI@example.invalid> at number I.

(defun sdt-msgid (i)
  (declare (xargs :mode :program))
  (concatenate 'string "<a" (coerce (fn-nntp-octets-chars (fn-nntp-decimal-field i)) 'string) "@example.invalid>"))

(defun sdt-articles (i acc)
  ; Articles I down to 1 consed onto ACC: the list comes out 1..N, oldest first.
  (declare (xargs :mode :program))
  (if (zp i)
      acc
    (sdt-articles (1- i)
                  (cons (fn-make-article (sdt-msgid i) i '("fn.test")
                                         (list (cons "fn.test" i)) t 841000000)
                        acc))))

(defconst *sdt-n* 50000)
(defconst *sdt-articles* (sdt-articles *sdt-n* nil))

(assert-event (equal (len *sdt-articles*) 50000))

; The count and the water marks (GROUP's 211, LIST ACTIVE's line).
(assert-event (equal (fn-nntp-group-count "fn.test" *sdt-articles*) 50000))
(assert-event (equal (fn-nntp-group-low "fn.test" *sdt-articles*) 1))
(assert-event (equal (fn-nntp-group-high "fn.test" *sdt-articles*) 50000))
(assert-event (equal (fn-nntp-group-count "fn.other" *sdt-articles*) 0))
(assert-event (equal (fn-nntp-group-low "fn.other" *sdt-articles*) 0))
(assert-event (equal (fn-nntp-group-high nil nil) 0))

; NEXT and LAST: the neighbours of a number, and the ends.
(assert-event (equal (fn-nntp-group-next-number "fn.test" 100 *sdt-articles*) 101))
(assert-event (equal (fn-nntp-group-last-number "fn.test" 100 *sdt-articles*) 99))
(assert-event (equal (fn-nntp-group-next-number "fn.test" 50000 *sdt-articles*) 0))
(assert-event (equal (fn-nntp-group-last-number "fn.test" 1 *sdt-articles*) 0))

; LISTGROUP's numbers, in order, and its lines.
(defconst *sdt-range* (fn-nntp-group-range-numbers "fn.test" 1 50000 *sdt-articles*))
(assert-event (equal (len *sdt-range*) 50000))
(assert-event (and (equal (car *sdt-range*) 1)
                   (equal (car (last *sdt-range*)) 50000)
                   (fn-nntp-orderedp *sdt-range*)))
(assert-event (equal (fn-nntp-group-range-numbers "fn.test" 7 9 *sdt-articles*) '(7 8 9)))
(assert-event (equal (fn-nntp-group-range-numbers "fn.test" 9 7 *sdt-articles*) nil))
(defconst *sdt-lines* (fn-nntp-number-lines *sdt-range*))
(assert-event (and (equal (len *sdt-lines*) 50000)
                   (equal (car *sdt-lines*) (fn-nntp-decimal-field 1))
                   (equal (car (last *sdt-lines*)) (fn-nntp-decimal-field 50000))))

; The index-backed numbers: count, min, max, the neighbours, and the sort of
; an order that is not descending (ascending, then one out of place), which
; takes the insertion loop and not the descending fast path.
(defconst *sdt-nums* (cons 25000 (fn-nntp-index-numbers (fn-index-build *sdt-articles*))))
(assert-event (equal (fn-nntp-numbers-count *sdt-nums*) 50001))
(assert-event (equal (fn-nntp-numbers-min *sdt-nums*) 1))
(assert-event (equal (fn-nntp-numbers-max *sdt-nums*) 50000))
(assert-event (equal (fn-nntp-numbers-min-above 49998 *sdt-nums*) 49999))
(assert-event (equal (fn-nntp-numbers-max-below 3 *sdt-nums*) 2))
(assert-event (not (fn-nntp-descending-integersp *sdt-nums*)))
(defconst *sdt-sorted* (fn-nntp-numbers-sort *sdt-nums*))
(assert-event (and (equal (len *sdt-sorted*) 50001)
                   (fn-nntp-orderedp *sdt-sorted*)
                   (equal (car *sdt-sorted*) 1)
                   (equal (car (last *sdt-sorted*)) 50000)))
(assert-event (equal (fn-nntp-numbers-sort '(3 1 2)) '(1 2 3)))
(assert-event (equal (fn-nntp-insert-number 5 '(1 3 7 9)) '(1 3 5 7 9)))
(assert-event (equal (fn-nntp-insert-number 10 '(1 3)) '(1 3 10)))

; -----------------------------------------------------------------------------
; LIST ACTIVE over 50,000 configured groups, none holding an article: one
; line each, in the configured order.

(defun sdt-groups (i acc)
  (declare (xargs :mode :program))
  (if (zp i)
      acc
    (sdt-groups (1- i) (cons (concatenate 'string "fn.g" (coerce (fn-nntp-octets-chars (fn-nntp-decimal-field i)) 'string))
                             acc))))

(defconst *sdt-groups* (sdt-groups 50000 nil))
(defconst *sdt-empty* (fn-make-state *sdt-groups* nil nil 0 nil nil))
(defconst *sdt-active* (fn-nntp-active-lines *sdt-empty* *sdt-groups*))
(assert-event (and (equal (len *sdt-active*) 50000)
                   (equal (car *sdt-active*) (fn-nntp-active-line *sdt-empty* "fn.g1"))
                   (equal (car (last *sdt-active*))
                          (fn-nntp-active-line *sdt-empty* "fn.g50000"))))
(assert-event (equal (len (fn-nntp-newsgroup-lines *sdt-groups*)) 50000))
(assert-event (equal (len (fn-nntp-counts-lines *sdt-empty* *sdt-groups*)) 50000))

; -----------------------------------------------------------------------------
; The syntax conversions and the reply's pieces: 100,000 characters and
; octets round-trip, and 50,000 pieces concatenate in order.

(defconst *sdt-text* (coerce (make-list 100000 :initial-element #\x) 'string))
(assert-event (equal (len (fn-nntp-string-octets *sdt-text*)) 100000))
(assert-event (equal (fn-nntp-octets-chars (fn-nntp-string-octets *sdt-text*))
                     (coerce *sdt-text* 'list)))
(assert-event (equal (fn-nntp-string-octets "AB") '(65 66)))
(assert-event (equal (fn-nntp-octets-chars nil) nil))

(defconst *sdt-pieces* (make-list 50000 :initial-element '(97 98)))
(assert-event (equal (len (fn-nntp-append-pieces *sdt-pieces*)) 100000))
(assert-event (equal (fn-nntp-append-pieces '((1 2) nil (3))) '(1 2 3)))
