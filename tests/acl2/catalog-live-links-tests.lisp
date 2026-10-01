; Teeth for the live-links keystones of books/catalog-live-links.lisp
; (fn-cpl-okp-of-withdraw, fn-cpl-okp-of-commit): per keystone a reachable
; positive witness asserting the complete antecedent and the conclusion,
; and an okp-removal witness (Codex review r27 F3): every retained
; hypothesis holds, `fn-cpl-okp' of the input fails, and the conclusion
; fails.  `fn-cpl-okp' is a defun-sk; the witnesses evaluate it through
; fn-cpl-okp-is-all-goodp (an equality, proved in the book).
;
; Open: the withdrawal keystone's hypothesis (null (fn-held-withdrawn (nth
; r c))) has no counterexample -- a withdrawn row has no live number, so the
; plan is empty and the table and rows are unchanged; removing it waits on a
; proof of the weakened theorem, not on a failed search.

(in-package "ACL2")
(include-book "../../books/catalog-live-links")

; Three held records (the shape books/catalog-paged.lisp's *cp-w1* uses).
(defun cllt-held (seq msgid groups)
  (declare (xargs :guard t :verify-guards nil))
  (let ((art (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10))))
    (fn-held-plain (fn-record-make seq (+ 1 seq) 0 msgid art groups "o" "s" "e" 1 5
                                   (fn-ab-for-received :post-d25 art))
                   seq)))

(defconst *cat-h0* (cllt-held 0 "<a@x>" '("fn.test")))
(defconst *cat-h1* (cllt-held 1 "<b@x>" '("fn.test")))
(defconst *cat-h2* (cllt-held 2 "<c@x>" '("fn.test" "fn.other")))
(assert-event (and (fn-held-p *cat-h0*) (fn-held-p *cat-h1*) (fn-held-p *cat-h2*)))

(defmacro cllt-okp (dir tab c)
  `(fn-cpl-all-goodp ,dir ,tab ,tab ,c))

; The reading the witnesses use is `fn-cpl-okp' itself.
(defthm cllt-okp-is-okp
  (equal (fn-cpl-okp dir tab c) (cllt-okp dir tab c))
  :rule-classes nil
  :hints (("Goal" :by fn-cpl-okp-is-all-goodp)))

; The rows: three commits, "fn.test" numbers 1 2 3 (h2 also "fn.other" 1).
(defconst *cllt-c2* (fn-cat$a-commit *cat-h1* (fn-cat$a-commit *cat-h0* nil)))
(defconst *cllt-c3* (fn-cat$a-commit *cat-h2* *cllt-c2*))

(defconst *cllt-next3* '((("fn.test" . 1) . 2) (("fn.test" . 2) . 3) (("fn.test" . 3) . 0)))
(defconst *cllt-prev3* '((("fn.test" . 1) . 0) (("fn.test" . 2) . 1) (("fn.test" . 3) . 2)))

; --- fn-cpl-okp-of-withdraw, positive: withdraw row 1 (number 2) at 3 by 7.
(defconst *cllt-w-next*
  (fn-cpl-unlink t (fn-cpl-wplan (fn-held-numbers (nth 1 *cllt-c3*)) 1 *cllt-c3*) *cllt-next3*))
(defconst *cllt-w-prev*
  (fn-cpl-unlink nil (fn-cpl-wplan (fn-held-numbers (nth 1 *cllt-c3*)) 1 *cllt-c3*) *cllt-prev3*))
(defconst *cllt-w-rows* (fn-cat-mark-withdrawn 1 3 7 *cllt-c3*))

(assert-event
 (and (fn-cat-rowsp *cllt-c3*) (natp 1) (< 1 (len *cllt-c3*))
      (null (fn-held-withdrawn (nth 1 *cllt-c3*)))
      (cllt-okp t *cllt-next3* *cllt-c3*) (cllt-okp nil *cllt-prev3* *cllt-c3*)
      ;; the conclusion, both tables
      (cllt-okp t *cllt-w-next* *cllt-w-rows*) (cllt-okp nil *cllt-w-prev* *cllt-w-rows*)
      ;; and what it means: 2 is gone, 1 and 3 are each other's neighbours
      (equal (hons-assoc-equal '("fn.test" . 2) *cllt-w-next*) nil)
      (equal (cdr (hons-assoc-equal '("fn.test" . 1) *cllt-w-next*)) 3)
      (equal (cdr (hons-assoc-equal '("fn.test" . 3) *cllt-w-next*)) 0)
      (equal (hons-assoc-equal '("fn.test" . 2) *cllt-w-prev*) nil)
      (equal (cdr (hons-assoc-equal '("fn.test" . 1) *cllt-w-prev*)) 0)
      (equal (cdr (hons-assoc-equal '("fn.test" . 3) *cllt-w-prev*)) 1)))

; --- fn-cpl-okp-of-withdraw without (fn-cpl-okp dir tab c): 3's NEXT is 1.
(defconst *cllt-bad-next3* '((("fn.test" . 1) . 2) (("fn.test" . 2) . 3) (("fn.test" . 3) . 1)))

(assert-event
 (and (fn-cat-rowsp *cllt-c3*) (natp 1) (< 1 (len *cllt-c3*))
      (null (fn-held-withdrawn (nth 1 *cllt-c3*)))
      (not (cllt-okp t *cllt-bad-next3* *cllt-c3*))
      (not (cllt-okp t (fn-cpl-unlink t (fn-cpl-wplan (fn-held-numbers (nth 1 *cllt-c3*)) 1 *cllt-c3*)
                                      *cllt-bad-next3*)
                     *cllt-w-rows*))))

; --- fn-cpl-okp-of-commit, positive: commit h2 over rows 1 2 of "fn.test".
(defconst *cllt-next2* '((("fn.test" . 1) . 2) (("fn.test" . 2) . 0)))
(defconst *cllt-prev2* '((("fn.test" . 1) . 0) (("fn.test" . 2) . 1)))
(defconst *cllt-cplan*
  (fn-cpl-cplan (fn-record-groups *cat-h2*)
                (and (null (fn-held-withdrawn *cat-h2*)) (fn-scat-msgid-idp (fn-record-msgid *cat-h2*)))
                *cllt-c2*))
(defconst *cllt-c-next* (fn-cpl-link t *cllt-cplan* *cllt-next2*))
(defconst *cllt-c-prev* (fn-cpl-link nil *cllt-cplan* *cllt-prev2*))

(assert-event
 (and (fn-cat-rowsp *cllt-c2*)
      (cllt-okp t *cllt-next2* *cllt-c2*) (cllt-okp nil *cllt-prev2* *cllt-c2*)
      (equal (append *cllt-c2* (list (fn-cat-assign *cat-h2* *cllt-c2*))) *cllt-c3*)
      (cllt-okp t *cllt-c-next* *cllt-c3*) (cllt-okp nil *cllt-c-prev* *cllt-c3*)
      ;; 3 joins after 2; "fn.other" 1 is alone
      (equal (cdr (hons-assoc-equal '("fn.test" . 2) *cllt-c-next*)) 3)
      (equal (cdr (hons-assoc-equal '("fn.test" . 3) *cllt-c-next*)) 0)
      (equal (cdr (hons-assoc-equal '("fn.test" . 3) *cllt-c-prev*)) 2)
      (equal (cdr (hons-assoc-equal '("fn.other" . 1) *cllt-c-next*)) 0)
      (equal (cdr (hons-assoc-equal '("fn.other" . 1) *cllt-c-prev*)) 0)))

; --- fn-cpl-okp-of-commit without (fn-cpl-okp dir tab c): 1's NEXT is 5.
(defconst *cllt-bad-next2* '((("fn.test" . 1) . 5) (("fn.test" . 2) . 0)))

(assert-event
 (and (fn-cat-rowsp *cllt-c2*)
      (not (cllt-okp t *cllt-bad-next2* *cllt-c2*))
      (not (cllt-okp t (fn-cpl-link t *cllt-cplan* *cllt-bad-next2*) *cllt-c3*))))

; --- a keyed clear empties the rows: a table kept across it is not good
; (Codex r27 F2); the cleared table is (fn-cpl-okp-nil).
(assert-event
 (and (cllt-okp t *cllt-next3* *cllt-c3*)
      (not (cllt-okp t *cllt-next3* (fn-cat$a-clear-keyed '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32) *cllt-c3*)))
      (cllt-okp t nil (fn-cat$a-clear-keyed '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32) *cllt-c3*))))
