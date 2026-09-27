; fn: teeth for books/catalog-number-index.lisp (wave 5, lane index-stobjs).
;
; What this book is evidence FOR.  `fn-cnx-view-seq-is-walk': under the
; invariant `fn-cnx-freshp' (no number bound twice), the catalog's one-probe
; number lookup at a version is the walk of the visible rows;
; `fn-cnx-view-range-is-walk': the clamped ascending range is the walk per
; number over the unclamped range; `fn-cnx-freshp-of-*': every writer keeps
; the invariant.  The exec path runs the lookups on a live local catalog
; (with a withdrawal, a second group and the range 1..4294967295) against
; the walks.  Each keystone gets a reachable ground witness asserting its
; complete antecedent and conclusion, and for each hypothesis a witness on
; which the other hypotheses hold, the omitted one fails and the conclusion
; fails, with a `must-fail' of the conclusion at that constant.  The
; duplicate-number catalog is a CORRUPTED STATE: no sequence of the
; catalog's exports produces it (that is what the preservation theorems
; say); it is built from held records whose numbers are written by hand.

(in-package "ACL2")
(include-book "../../books/catalog-number-index")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-cnx-view-seq (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cnx-range-aux (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cnx-view-range (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cnx-freshp (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Rows: three in fn.test, one in fn.other, one in both.

(defun cnxt-held (seq msgid groups)
  (fn-held-make seq (+ 1 seq) 0 msgid seq groups "o" "s" "e" 1 5
                (fn-hf-make 100 14 2) (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0) nil nil))

(defconst *cnxt-h0* (cnxt-held 0 "<a@x>" '("fn.test")))
(defconst *cnxt-h1* (cnxt-held 1 "<b@x>" '("fn.test")))
(defconst *cnxt-h2* (cnxt-held 2 "<c@x>" '("fn.test")))
(defconst *cnxt-h3* (cnxt-held 3 "<d@x>" '("fn.other")))
(defconst *cnxt-h4* (cnxt-held 4 "<e@x>" '("fn.test" "fn.other")))

(defun cnxt-run (fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-cat-commit *cnxt-h0* fn-cat))
         (fn-cat (fn-cat-commit *cnxt-h1* fn-cat))
         (fn-cat (fn-cat-commit *cnxt-h2* fn-cat))
         (fn-cat (fn-cat-commit *cnxt-h3* fn-cat))
         ; a reader pins version 4; row 1 is withdrawn at version 4
         (fn-cat (fn-cat-withdraw 1 9 fn-cat))
         (fn-cat (fn-cat-commit *cnxt-h4* fn-cat))
         (count (fn-cat-count fn-cat)))
    (mv (list count
              (fn-cnx-view-seq "fn.test" 2 4 fn-cat)          ; row 1, visible at 4
              (fn-cnx-view-seq "fn.test" 2 5 fn-cat)          ; withdrawn at 4: gone at 5
              (fn-cnx-view-seq "fn.test" 4 5 fn-cat)          ; row 4 is fn.test's 4
              (fn-cnx-view-seq "fn.test" 4 4 fn-cat)          ; above version 4
              (fn-cnx-view-seq "fn.other" 2 5 fn-cat)         ; row 4 is fn.other's 2
              (fn-cnx-view-seq "fn.test" 9 5 fn-cat)          ; never bound
              (equal (fn-cnx-view-seq "fn.test" 2 5 fn-cat)
                     (fn-cat-view-number-find "fn.test" 2 count 5 fn-cat))
              (equal (fn-cnx-view-seq "fn.test" 4 5 fn-cat)
                     (fn-cat-view-number-find "fn.test" 4 count 5 fn-cat))
              (fn-cnx-view-range "fn.test" 1 4294967295 5 fn-cat)
              (fn-cnx-view-range "fn.test" 1 4294967295 4 fn-cat)
              (fn-cnx-view-range "fn.test" 2 3 5 fn-cat)
              (fn-cnx-view-range "fn.other" 1 4294967295 5 fn-cat)
              (fn-cnx-view-range "fn.test" 5 4294967295 5 fn-cat))
        fn-cat)))

(defun cnxt-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat
    (mv-let (result fn-cat) (cnxt-run fn-cat) result)))

(assert-event
 (equal (cnxt-exec)
        (list 5 1 nil 4 nil 4 nil t t
              '(0 2 4) '(0 1 2) '(2) '(3 4) nil)))

; -----------------------------------------------------------------------------
; The logical value the exec path built (fn-cat-commit-is-append,
; fn-cat-withdraw-is-mark).

(defconst *cnxt-c4*
  (fn-cat$a-commit *cnxt-h3*
   (fn-cat$a-commit *cnxt-h2*
    (fn-cat$a-commit *cnxt-h1*
     (fn-cat$a-commit *cnxt-h0* nil)))))
(defconst *cnxt-c* (fn-cat$a-commit *cnxt-h4* (fn-cat$a-withdraw 1 9 *cnxt-c4*)))

; Reachability: the constant is what the exports produce from the creator.
(defthm cnxt-w-reached
  (equal *cnxt-c*
         (fn-cat-commit *cnxt-h4*
          (fn-cat-withdraw 1 9
           (fn-cat-commit *cnxt-h3*
            (fn-cat-commit *cnxt-h2*
             (fn-cat-commit *cnxt-h1*
              (fn-cat-commit *cnxt-h0* (create-fn-cat))))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; KEYSTONE fn-cnx-view-seq-is-walk: the complete antecedent, then the
; conclusion, at a bound, visible, non-degenerate number.

(defthm cnxt-w-view-seq
  (and (fn-cnx-freshp *cnxt-c*)
       4
       (equal (fn-cnx-view-seq "fn.test" 4 5 *cnxt-c*) 4)
       (equal (fn-cat-view-number-find "fn.test" 4 (fn-cat-count *cnxt-c*) 5 *cnxt-c*) 4))
  :rule-classes nil)

; Hypothesis N removed: N = nil.  The invariant holds; the walk compares nil
; with each row's number in fn.test and finds row 3 (fn.other only), the
; newest such visible row; the column names no row.
(defthm cnxt-w-view-seq-without-n
  (and (fn-cnx-freshp *cnxt-c*)
       (not nil)
       (equal (fn-cat-view-number-find "fn.test" nil (fn-cat-count *cnxt-c*) 5 *cnxt-c*) 3)
       (equal (fn-cnx-view-seq "fn.test" nil 5 *cnxt-c*) nil))
  :rule-classes nil)

(must-fail
 (defthm cnxt-f-view-seq-without-n
   (equal (fn-cnx-view-seq "fn.test" nil 5 *cnxt-c*)
          (fn-cat-view-number-find "fn.test" nil (fn-cat-count *cnxt-c*) 5 *cnxt-c*))
   :rule-classes nil))

; Hypothesis fn-cnx-freshp removed: a CORRUPTED catalog, two rows numbered
; 1 in fn.test (hand-written numbers).  N = 1 holds; the walk answers the
; newer row, the column the first.
(defun cnxt-numbered (h numbers)
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) (fn-held-context h)
                numbers nil))

(defconst *cnxt-bad*
  (list (cnxt-numbered *cnxt-h0* '(("fn.test" . 1)))
        (cnxt-numbered *cnxt-h1* '(("fn.test" . 1)))))

(defthm cnxt-w-view-seq-without-freshp
  (and (fn-cat-p *cnxt-bad*)
       (not (fn-cnx-freshp *cnxt-bad*))
       1
       (equal (fn-cnx-view-seq "fn.test" 1 2 *cnxt-bad*) 0)
       (equal (fn-cat-view-number-find "fn.test" 1 (fn-cat-count *cnxt-bad*) 2 *cnxt-bad*) 1))
  :rule-classes nil)

(must-fail
 (defthm cnxt-f-view-seq-without-freshp
   (equal (fn-cnx-view-seq "fn.test" 1 2 *cnxt-bad*)
          (fn-cat-view-number-find "fn.test" 1 (fn-cat-count *cnxt-bad*) 2 *cnxt-bad*))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cnx-view-range-is-walk: the range 1..10 over fn.test at
; version 5 (clamped to 1..4: the group's high), the withdrawn row 1 absent.

(defthm cnxt-w-view-range
  (and (fn-cnx-freshp *cnxt-c*)
       (equal (fn-cat-group-next "fn.test" *cnxt-c*) 5)
       (equal (fn-cnx-view-range "fn.test" 1 10 5 *cnxt-c*) '(0 2 4))
       (equal (fn-cnx-walk-range "fn.test" 1 10 5 *cnxt-c*) '(0 2 4)))
  :rule-classes nil)

(defthm cnxt-w-view-range-without-freshp
  (and (not (fn-cnx-freshp *cnxt-bad*))
       (equal (fn-cnx-view-range "fn.test" 1 3 2 *cnxt-bad*) '(0))
       (equal (fn-cnx-walk-range "fn.test" 1 3 2 *cnxt-bad*) '(1)))
  :rule-classes nil)

(must-fail
 (defthm cnxt-f-view-range-without-freshp
   (equal (fn-cnx-view-range "fn.test" 1 3 2 *cnxt-bad*)
          (fn-cnx-walk-range "fn.test" 1 3 2 *cnxt-bad*))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; Preservation: every writer from the creator keeps the invariant (the
; reachable chain above), and the invariant is not vacuous: the corrupted
; catalog stays corrupted through a commit (the commit cannot repair an
; earlier duplicate).

(defthm cnxt-w-preserved-along-the-chain
  (and (fn-cnx-freshp (create-fn-cat$a))
       (fn-cnx-freshp (fn-cat$a-commit *cnxt-h0* nil))
       (fn-cnx-freshp *cnxt-c4*)
       (fn-cnx-freshp (fn-cat$a-withdraw 1 9 *cnxt-c4*))
       (fn-cnx-freshp *cnxt-c*)
       (fn-cnx-freshp (fn-cat$a-redecide 2 (fn-hc-make (fn-stx-make-verdict :verified nil 7) nil 7) *cnxt-c*))
       (fn-cnx-freshp (fn-cat$a-clear *cnxt-c*)))
  :rule-classes nil)

(defthm cnxt-w-corrupted-stays-corrupted
  (and (not (fn-cnx-freshp *cnxt-bad*))
       (not (fn-cnx-freshp (fn-cat$a-commit *cnxt-h2* *cnxt-bad*))))
  :rule-classes nil)
