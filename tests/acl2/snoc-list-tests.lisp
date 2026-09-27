; fn: witnesses and teeth for books/snoc-list.lisp and the kernel's held
; histories (books/store-files.lisp fn-sf-records / fn-sf-successes as
; snoc-lists; the host's commit books/records-concrete.lisp
; fn-rcon-sf-record-dir-result, the prepare's candidate test
; books/owner-prepare-carried.lisp fn-pcar-files-candidatep, the finish's
; seek books/owner-commit-carried.lisp fn-ccar-seek-at).
;
; The kernel states are store-files-tests': *sf-linked* is :record-attempted
; with an empty history and one candidate; *sf-published* is its commit;
; *sf-acked* its success.  Each is evaluated (the executable branch of every
; transition, fn-sf-remake / the O(1) snoc).
(in-package "ACL2")
(include-book "../../books/owner-commit-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "store-files-tests")

; -----------------------------------------------------------------------------
; snoc-list: positive witnesses (fn-sl-list-of-fn-sl-of, fn-sl-snoc-of-fn-sl-of,
; fn-sl-list-of-fn-sl-snoc, fn-sl-count-is-len, fn-sl-last-is-last,
; fn-sl-nth-is-nth), each antecedent and conclusion asserted.
(assert-event (equal (fn-sl-of '(a b c)) '(:snoc 3 c b a)))
(assert-event (equal (fn-sl-list '(:snoc 3 c b a)) '(a b c)))
(assert-event (equal (fn-sl-of '(a . b)) '(:raw a . b)))
(assert-event (equal (fn-sl-list (fn-sl-of '(a . b))) '(a . b)))
(assert-event (equal (fn-sl-snoc (fn-sl-of '(a b)) 'c) (fn-sl-of '(a b c))))
(assert-event (equal (fn-sl-snoc (fn-sl-of '(a b)) 'c) '(:snoc 3 c b a)))
(assert-event (equal (fn-sl-snoc (fn-sl-of '(a . b)) 'c) (fn-sl-of '(a c))))
(assert-event (fn-sl-canonp '(:snoc 3 c b a)))
(assert-event (equal (fn-sl-count '(:snoc 3 c b a)) 3))
(assert-event (equal (fn-sl-last '(:snoc 3 c b a)) 'c))
(assert-event (equal (fn-sl-nth 0 '(:snoc 3 c b a)) 'a))
(assert-event (equal (fn-sl-nth 2 '(:snoc 3 c b a)) 'c))
(assert-event (equal (fn-sl-nth 3 '(:snoc 3 c b a)) nil))

; The readers hold for every value, a non-canonical one included: a snoc form
; whose REV is shorter than its count reads as padded with nil.
(defconst *sl-bad* '(:snoc 5 c b a))
(assert-event (equal (fn-sl-list *sl-bad*) '(nil nil a b c)))
(assert-event (equal (fn-sl-count *sl-bad*) (len (fn-sl-list *sl-bad*))))
(assert-event (equal (fn-sl-nth 0 *sl-bad*) (nth 0 (fn-sl-list *sl-bad*))))
(assert-event (equal (fn-sl-last *sl-bad*) (car (last (fn-sl-list *sl-bad*)))))
; HYPOTHESIS-REMOVAL (fn-sl-canonp in fn-sl-of-list-when-canonp): the
; retained conclusion's value, and canonp fails, and the conclusion fails.
(assert-event (not (fn-sl-canonp *sl-bad*)))
(assert-event (not (equal (fn-sl-of (fn-sl-list *sl-bad*)) *sl-bad*)))
; fn-sl-list-of-fn-sl-snoc has no hypothesis: it holds on the bad form too.
(assert-event (equal (fn-sl-list (fn-sl-snoc *sl-bad* 'd)) '(nil nil a b c d)))

; -----------------------------------------------------------------------------
; The kernel.  Reachable POSITIVE witnesses: the commit appends the candidate,
; held as a snoc form; the success likewise; the O(1) readers are the lists'.
(assert-event (fn-sf-statep *sf-linked*))
(assert-event (equal (fn-sf-phase *sf-linked*) :record-attempted))
(assert-event (equal (fn-sf-records *sf-published*)
                     (append (fn-sf-records *sf-linked*)
                             (list (fn-sf-record-candidate *sf-linked*)))))
(assert-event (equal (fn-sf-records-field *sf-published*)
                     (fn-sl-of (fn-sf-records *sf-published*))))
(assert-event (equal (car (fn-sf-records-field *sf-published*)) :snoc))
(assert-event (equal (fn-rcon-sf-record-dir-result *sf-linked* :ok) *sf-published*))
(assert-event (equal (fn-sf-records-count *sf-published*) 1))
(assert-event (equal (fn-sf-records-last *sf-published*)
                     (fn-sf-record-candidate *sf-linked*)))
(assert-event (equal (fn-sf-records-nth 0 *sf-published*)
                     (fn-sf-record-candidate *sf-linked*)))
(assert-event (equal (fn-sf-successes *sf-acked*) '((0 . 0))))
(assert-event (equal (fn-sf-successes-field *sf-acked*) (fn-sl-of '((0 . 0)))))
(assert-event (fn-sf-statep *sf-acked*))

; The finish's seek from the newest end finds the committed record at its
; pair (fn-ccar-seek-at-is-seek), and nothing at another pair.
(assert-event (equal (fn-ccar-seek-at '(0 . 0) *sf-published*)
                     (fn-sf-record-candidate *sf-linked*)))
(assert-event (equal (fn-ccar-seek-at '(0 . 0) *sf-published*)
                     (fn-ccar-seek '(0 . 0) (fn-sf-records *sf-published*) 0)))
(assert-event (equal (fn-ccar-seek-at '(1 . 0) *sf-published*) nil))

; HYPOTHESIS-REMOVAL (fn-sf-shapep in fn-sf-make-fields-is-make): a tuple whose
; records field is not canonical.  Copying its field is not fn-sf-make of its
; list.  (CORRUPTED state, labelled: no transition builds it.)
(defconst *sf-noncanon*
  (fn-sf-make-fields :ready 0 nil *sl-bad* nil nil (fn-sl-of nil) 5))
(assert-event (not (fn-sf-shapep *sf-noncanon*)))
(assert-event (not (equal (fn-sf-make-fields :ready 0 nil (fn-sf-records-field *sf-noncanon*)
                                             nil nil (fn-sf-successes-field *sf-noncanon*) 5)
                          (fn-sf-make :ready 0 nil (fn-sf-records *sf-noncanon*)
                                      nil nil (fn-sf-successes *sf-noncanon*) 5))))

; fn-sl-nth-is-nth's (natp i) hypothesis is redundant (audit packet G3-7,
; lane audit-fixes): the weakened theorem is proved here, so no removal
; witness exists.  Both sides fix the index (fn-sl-nth by nfix, nth by zp).
; The library statement is left as it is (snoc-list has wide fan-in).
(local (defthm sl-t-nth-of-nfix
         (equal (fn-sl-nth (nfix i) h) (fn-sl-nth i h))
         :hints (("Goal" :in-theory (e/d (fn-sl-nth fn-sl-nth-elem) (fn-sl-nth-is-nth))))))
(local (defthm sl-t-nth-nth-of-nfix (equal (nth (nfix i) x) (nth i x))))
(defthm sl-t-nth-is-nth-without-natp
  (equal (fn-sl-nth i h) (nth i (fn-sl-list h)))
  :hints (("Goal" :use ((:instance fn-sl-nth-is-nth (i (nfix i)))
                        (:instance sl-t-nth-of-nfix)
                        (:instance sl-t-nth-nth-of-nfix (x (fn-sl-list h))))
           :in-theory (union-theories '((:type-prescription nfix) natp)
                                      (theory 'minimal-theory))))
  :rule-classes nil)
; The non-natural indices the hypothesis excludes, evaluated on both forms
; (fn-sl-nth's guard asks natp, so as a ground theorem).
(defthm sl-t-nth-at-non-naturals
  (and (equal (fn-sl-nth 1/2 '(:snoc 3 c b a)) (nth 1/2 (fn-sl-list '(:snoc 3 c b a))))
       (equal (fn-sl-nth -1 '(:snoc 3 c b a)) (nth -1 (fn-sl-list '(:snoc 3 c b a))))
       (equal (fn-sl-nth 'x '(:snoc 3 c b a)) 'a)
       (equal (fn-sl-nth -1 '(a b c)) (nth -1 '(a b c))))
  :rule-classes nil)
