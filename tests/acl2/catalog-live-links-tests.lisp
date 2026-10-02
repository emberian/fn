; Teeth for the live-links keystones of books/catalog-live-links.lisp
; (fn-cpl-okp-of-withdraw, fn-cpl-okp-of-commit): per keystone a reachable
; positive witness asserting the complete antecedent and the conclusion,
; and an okp-removal witness (Codex review r27 F3): every retained
; hypothesis holds, `fn-cpl-okp' of the input fails, and the conclusion
; fails.  `fn-cpl-okp' is a defun-sk; the witnesses evaluate it through
; fn-cpl-okp-is-all-goodp (an equality, proved in the book).  The tables
; are the ones the commits generate (Codex r30 F2).  Coverage (sec. 6,
; fn-cpl-coverp-of-commit/-of-withdraw): positive and coverage-removal
; witnesses, proved over the constants (a defun-sk).  Codex r30 F4: the
; natp-r removal witness; the r < len c weakening is proved.  Codex r33 F2:
; fn-cpl-probe-of-live positive + coverage/okp/liveness removals,
; coverage-of-redecide positive + removal, the clear asserts coverage; the
; hypotheses with no removal witness are listed at the end with the reason.
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
    (fn-held-plain (fn-record-make seq (+ 1 seq) 0 msgid art groups "o" "s" "e" 1 5)
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
(defconst *cllt-c1* (fn-cat$a-commit *cat-h0* nil))
(defconst *cllt-c2* (fn-cat$a-commit *cat-h1* *cllt-c1*))
(defconst *cllt-c3* (fn-cat$a-commit *cat-h2* *cllt-c2*))

; The tables the three commits GENERATE from empty ones (Codex r30 F2): the
; links each commit's plan installs, "fn.other" 1 included (the shadowed
; entries stay in the alist, as the hash table's puts replace them).
(defmacro cllt-livep (h) `(and (null (fn-held-withdrawn ,h)) (fn-scat-msgid-idp (fn-record-msgid ,h))))
(defmacro cllt-gen (dir)
  `(fn-cpl-link ,dir (fn-cpl-cplan (fn-record-groups *cat-h2*) (cllt-livep *cat-h2*) *cllt-c2*)
     (fn-cpl-link ,dir (fn-cpl-cplan (fn-record-groups *cat-h1*) (cllt-livep *cat-h1*) *cllt-c1*)
       (fn-cpl-link ,dir (fn-cpl-cplan (fn-record-groups *cat-h0*) (cllt-livep *cat-h0*) nil) nil))))
(defconst *cllt-next3* (cllt-gen t))
(defconst *cllt-prev3* (cllt-gen nil))

(assert-event
 (and (equal (cdr (hons-assoc-equal '("fn.test" . 1) *cllt-next3*)) 2)
      (equal (cdr (hons-assoc-equal '("fn.test" . 2) *cllt-next3*)) 3)
      (equal (cdr (hons-assoc-equal '("fn.test" . 3) *cllt-next3*)) 0)
      (equal (cdr (hons-assoc-equal '("fn.other" . 1) *cllt-next3*)) 0)
      (equal (cdr (hons-assoc-equal '("fn.test" . 3) *cllt-prev3*)) 2)
      (equal (cdr (hons-assoc-equal '("fn.other" . 1) *cllt-prev3*)) 0)))

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

; --- fn-cpl-okp-of-withdraw without (natp r) (Codex r30 F4): r = -1 reads
; and marks row 0 (nth/update-nth of a non-natural), the plan is empty
; (no number's row is -1), so the table keeps "fn.test" 1, which died.
; Run on the definitions (guard checking :none): -1 is outside nth's guard.
(with-guard-checking-event
 :none
 (assert-event
  (and (fn-cat-rowsp *cllt-c3*) (not (natp -1)) (< -1 (len *cllt-c3*))
       (null (fn-held-withdrawn (nth -1 *cllt-c3*)))
       (cllt-okp t *cllt-next3* *cllt-c3*)
       (not (cllt-okp t (fn-cpl-unlink t (fn-cpl-wplan (fn-held-numbers (nth -1 *cllt-c3*)) -1 *cllt-c3*)
                                       *cllt-next3*)
                      (fn-cat-mark-withdrawn -1 3 7 *cllt-c3*))))))

; --- without (< r (len c)): no counterexample -- the weakened theorem is
; proved (fn-cpl-okp-of-withdraw-any-r).  Without (fn-cat-rowsp c): open
; (the proof uses it, fn-cpl-live-below-high; no counterexample is known,
; and a failed search is not one).

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

; --- fn-cpl-coverp-of-commit / -of-withdraw (sec. 6), positive: the
; generated tables cover every live number before and after.
(defthm cllt-cover-commit-positive
  (and (fn-cat-rowsp *cllt-c2*)
       (fn-cpl-coverp (fn-cpl-link t (fn-cpl-cplan (fn-record-groups *cat-h1*) (cllt-livep *cat-h1*) *cllt-c1*)
                                   (fn-cpl-link t (fn-cpl-cplan (fn-record-groups *cat-h0*) (cllt-livep *cat-h0*) nil) nil))
                      *cllt-c2*)
       (fn-cpl-coverp *cllt-next3* *cllt-c3*)
       (fn-cpl-coverp *cllt-prev3* *cllt-c3*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cpl-coverp fn-cat-live-numberp))))

(defthm cllt-cover-withdraw-positive
  (and (fn-cat-rowsp *cllt-c3*) (natp 1) (< 1 (len *cllt-c3*))
       (null (fn-held-withdrawn (nth 1 *cllt-c3*)))
       (fn-cpl-coverp *cllt-next3* *cllt-c3*)
       (fn-cpl-coverp *cllt-w-next* *cllt-w-rows*)
       (fn-cpl-coverp *cllt-w-prev* *cllt-w-rows*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cpl-coverp fn-cat-live-numberp))))

; --- coverage removed: a NEXT table missing "fn.test" 1 before the third
; commit misses it after (it is live in both).
(defconst *cllt-hole-next2* '((("fn.test" . 2) . 0)))

(defthm cllt-cover-commit-removal
  (and (fn-cat-rowsp *cllt-c2*)
       (not (fn-cpl-coverp *cllt-hole-next2* *cllt-c2*))
       (not (fn-cpl-coverp (fn-cpl-link t (fn-cpl-cplan (fn-record-groups *cat-h2*) (cllt-livep *cat-h2*) *cllt-c2*)
                                        *cllt-hole-next2*)
                           *cllt-c3*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpl-coverp-necc (x '("fn.test" . 1)) (tab *cllt-hole-next2*) (c *cllt-c2*))
                        (:instance fn-cpl-coverp-necc (x '("fn.test" . 1)) (c *cllt-c3*)
                                   (tab (fn-cpl-link t (fn-cpl-cplan (fn-record-groups *cat-h2*) (cllt-livep *cat-h2*) *cllt-c2*)
                                                     *cllt-hole-next2*)))))))

; --- the withdrawal with coverage removed: a NEXT table missing "fn.test" 3
; (live, and not the withdrawn number 2) misses it after.  (A hole at 1
; would be filled: the unlink puts 1's NEXT.)
(defconst *cllt-hole-next3* '((("fn.test" . 1) . 2) (("fn.test" . 2) . 3)))

(defthm cllt-cover-withdraw-removal
  (and (fn-cat-rowsp *cllt-c3*) (natp 1) (< 1 (len *cllt-c3*))
       (null (fn-held-withdrawn (nth 1 *cllt-c3*)))
       (not (fn-cpl-coverp *cllt-hole-next3* *cllt-c3*))
       (not (fn-cpl-coverp (fn-cpl-unlink t (fn-cpl-wplan (fn-held-numbers (nth 1 *cllt-c3*)) 1 *cllt-c3*)
                                          *cllt-hole-next3*)
                           *cllt-w-rows*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpl-coverp-necc (x '("fn.test" . 3)) (tab *cllt-hole-next3*) (c *cllt-c3*))
                        (:instance fn-cpl-coverp-necc (x '("fn.test" . 3)) (c *cllt-w-rows*)
                                   (tab (fn-cpl-unlink t (fn-cpl-wplan (fn-held-numbers (nth 1 *cllt-c3*)) 1 *cllt-c3*)
                                                       *cllt-hole-next3*)))))))

; --- Codex r33 F2.  fn-cpl-probe-of-live: positive (every hypothesis and
; the conclusion), then each hypothesis removed alone with the other two
; affirmed and the conclusion failing.
(defthm cllt-probe-positive
  (and (fn-cpl-coverp *cllt-next3* *cllt-c3*)
       (fn-cpl-okp t *cllt-next3* *cllt-c3*)
       (fn-cat-live-numberp "fn.test" 2 *cllt-c3*)
       (consp (hons-assoc-equal '("fn.test" . 2) *cllt-next3*))
       (equal (cdr (hons-assoc-equal '("fn.test" . 2) *cllt-next3*)) (fn-cpl-next-of "fn.test" 2 *cllt-c3*))
       (equal (fn-cpl-next-of "fn.test" 2 *cllt-c3*) 3))
  :rule-classes nil
  :hints (("Goal" :use ((:instance cllt-okp-is-okp (dir t) (tab *cllt-next3*) (c *cllt-c3*)))
           :in-theory (enable fn-cpl-coverp fn-cat-live-numberp))))

; coverage removed: "fn.test" 3 live and unbound (the other entries good).
(defthm cllt-probe-coverage-removal
  (and (not (fn-cpl-coverp *cllt-hole-next3* *cllt-c3*))
       (fn-cpl-okp t *cllt-hole-next3* *cllt-c3*)
       (fn-cat-live-numberp "fn.test" 3 *cllt-c3*)
       (not (consp (hons-assoc-equal '("fn.test" . 3) *cllt-hole-next3*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpl-coverp-necc (x '("fn.test" . 3)) (tab *cllt-hole-next3*) (c *cllt-c3*))
                        (:instance cllt-okp-is-okp (dir t) (tab *cllt-hole-next3*) (c *cllt-c3*))))))

; goodness removed: every live number bound, but 3's NEXT says 1 (it is 0).
(defconst *cllt-wrong-next3* (cons '(("fn.test" . 3) . 1) *cllt-next3*))

(defthm cllt-probe-okp-removal
  (and (fn-cpl-coverp *cllt-wrong-next3* *cllt-c3*)
       (not (fn-cpl-okp t *cllt-wrong-next3* *cllt-c3*))
       (fn-cat-live-numberp "fn.test" 3 *cllt-c3*)
       (not (equal (cdr (hons-assoc-equal '("fn.test" . 3) *cllt-wrong-next3*))
                   (fn-cpl-next-of "fn.test" 3 *cllt-c3*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance cllt-okp-is-okp (dir t) (tab *cllt-wrong-next3*) (c *cllt-c3*)))
           :in-theory (enable fn-cpl-coverp fn-cat-live-numberp))))

; liveness removed: after the withdrawal of 2 both tables are good and
; cover, 2 is not live, and its entry is gone.
(defthm cllt-probe-liveness-removal
  (and (fn-cpl-coverp *cllt-w-next* *cllt-w-rows*)
       (fn-cpl-okp t *cllt-w-next* *cllt-w-rows*)
       (not (fn-cat-live-numberp "fn.test" 2 *cllt-w-rows*))
       (not (consp (hons-assoc-equal '("fn.test" . 2) *cllt-w-next*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance cllt-okp-is-okp (dir t) (tab *cllt-w-next*) (c *cllt-w-rows*)))
           :in-theory (enable fn-cpl-coverp fn-cat-live-numberp))))

; --- fn-cpl-coverp-of-redecide: positive (redecide row 1 under the
; generated table) and coverage removed (the hole at 3 stays a hole).
(defconst *cllt-rd-rows* (update-nth 1 (fn-held-with-context (nth 1 *cllt-c3*) 9) *cllt-c3*))

(defthm cllt-cover-redecide-positive
  (and (natp 1) (< 1 (len *cllt-c3*))
       (fn-cpl-coverp *cllt-next3* *cllt-c3*)
       (fn-cpl-coverp *cllt-next3* *cllt-rd-rows*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cpl-coverp fn-cat-live-numberp))))

(defthm cllt-cover-redecide-removal
  (and (natp 1) (< 1 (len *cllt-c3*))
       (not (fn-cpl-coverp *cllt-hole-next3* *cllt-c3*))
       (not (fn-cpl-coverp *cllt-hole-next3* *cllt-rd-rows*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpl-coverp-necc (x '("fn.test" . 3)) (tab *cllt-hole-next3*) (c *cllt-c3*))
                        (:instance fn-cpl-coverp-necc (x '("fn.test" . 3)) (tab *cllt-hole-next3*) (c *cllt-rd-rows*))))))

; --- the keyed clear: the cleared rows have no live number, so the emptied
; tables cover them (fn-cpl-coverp-of-no-rows) -- and so does the stale one,
; which is not good (above): coverage alone does not make a table sound.
(defthm cllt-cover-clear
  (let ((rows (fn-cat$a-clear-keyed '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32) *cllt-c3*)))
    (and (equal rows nil)
         (fn-cpl-coverp nil rows)
         (fn-cpl-coverp *cllt-next3* rows)))
  :rule-classes nil)

; --- The hypotheses with no removal witness, and why (a failed search is
; not a counterexample; none is claimed redundant until its weakening is
; proved):
;  fn-cpl-coverp-of-withdraw (natp r), (< r (len c)), (null (fn-held-withdrawn
;   (nth r c))): each removal leaves the conclusion TRUE on every case we
;   know -- coverage needs only that the unlink drops no key that stays
;   live, and the plan names only numbers of row r, which a mark of a valid
;   r kills and an invalid or already-withdrawn r leaves dead or absent.
;  fn-cpl-coverp-of-redecide (natp r), (< r (len c)): a non-natural r
;   redecides row 0, an r past the end appends rows with no numbers; the
;   liveness of every number is unchanged.
;  fn-cpl-coverp-of-commit / -of-withdraw (fn-cat-rowsp c): open, as for
;   fn-cpl-okp-of-withdraw (the proofs use it; no counterexample is known).
