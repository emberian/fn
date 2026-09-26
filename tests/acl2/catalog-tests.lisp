; fn: teeth for books/catalog.lisp (wave 5, lane catalog-slice).
;
; What this book is evidence FOR.  The abstraction obligations of the
; catalog (`fn-cat-commit{correspondence}' and the others) say that every
; export's executable step on the tables equals the list operation on the
; abstraction whenever the correspondence and the export's guard hold; the
; keystones say a commit keeps every row below the old count and adds one
; row whose numbers are fresh (`fn-cat-commit-keeps-rows',
; `fn-cat-commit-new-row', `fn-cat-commit-binds-fresh-numbers'), and that
; visibility is a versioned fact (`fn-cat-visible-at-withdrawn').  Each
; gets a ground positive witness asserting its complete antecedent and
; conclusion, and for each hypothesis a witness on which the retained
; hypotheses hold, the omitted one fails and the conclusion fails, with a
; `must-fail' of the conclusion.  The exec path is run on a live local
; catalog: three commits (two in one group, one in two), the lookups by
; Message-ID and by number, a withdrawal, the pinned view before and after
; it, a redecision, a clear.

(in-package "ACL2")
(include-book "../../books/catalog")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The host runs compiled code: every exec function is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-cat$c-commit (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-withdraw (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-redecide (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-visible-at (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-group-number (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-msgid-seqs (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-held-p (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Ground held records: three articles, the first two in fn.test, the third
; in fn.test and fn.other; a cancel (a row with no groups) for the first.

(defun cat-held (seq msgid groups octets)
  (fn-held-make seq (+ 1 seq) 0 msgid seq groups "o" "s" "e" 1 5
                (fn-hf-make octets 14 2) (fn-hc-make :unverified nil 0) nil nil))

(defconst *cat-h0* (cat-held 0 "<a@x>" '("fn.test") 100))
(defconst *cat-h1* (cat-held 1 "<b@x>" '("fn.test") 200))
(defconst *cat-h2* (cat-held 2 "<c@x>" '("fn.test" "fn.other") 300))
(defconst *cat-cancel* (cat-held 3 "<cancel@x>" '("fn.control") 50))

(assert-event (and (fn-held-p *cat-h0*) (fn-held-p *cat-h1*) (fn-held-p *cat-h2*)
                   (fn-held-p *cat-cancel*)))

; -----------------------------------------------------------------------------
; The executable path on a live local catalog.

(defun cat-exec-run (fn-cat)
  (declare (xargs :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (fn-cat-commit *cat-h0* fn-cat))
         (fn-cat (fn-cat-commit *cat-h1* fn-cat))
         (fn-cat (fn-cat-commit *cat-h2* fn-cat))
         (before (list (fn-cat-count fn-cat)
                       (fn-cat-msgid-seqs "<b@x>" fn-cat)
                       (fn-cat-msgid-seqs "<none@x>" fn-cat)
                       (fn-cat-group-number "fn.test" 1 fn-cat)
                       (fn-cat-group-number "fn.test" 3 fn-cat)
                       (fn-cat-group-number "fn.other" 1 fn-cat)
                       (fn-cat-group-number "fn.other" 2 fn-cat)
                       (fn-cat-group-next "fn.test" fn-cat)
                       (fn-cat-group-next "fn.nowhere" fn-cat)
                       (fn-cat-group-count "fn.test" fn-cat)
                       (fn-cat-group-count "fn.other" fn-cat)
                       (fn-cat-total-octets fn-cat)
                       (fn-held-numbers (fn-cat-at 2 fn-cat))
                       (fn-cat-visible-at 0 3 fn-cat)))
         ; a reader pins version 3; the cancel commits at sequence 3 and
         ; withdraws row 0 at version 3 (the count before the cancel).
         (fn-cat (fn-cat-withdraw 0 3 fn-cat))
         (fn-cat (fn-cat-commit *cat-cancel* fn-cat))
         (after (list (fn-held-withdrawn (fn-cat-at 0 fn-cat))
                      (fn-cat-visible-at 0 3 fn-cat)   ; the pinned reader still sees it
                      (fn-cat-visible-at 0 4 fn-cat)   ; a reader who advanced does not
                      (fn-cat-visible-at 1 4 fn-cat)
                      (fn-cat-visible-at 3 3 fn-cat)   ; the cancel is above version 3
                      (fn-cat-count fn-cat)))
         (fn-cat (fn-cat-redecide 1 (fn-hc-make :verified nil 7) fn-cat))
         (redecided (fn-hc-generation (fn-held-context (fn-cat-at 1 fn-cat))))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv (list before after redecided (fn-cat-count fn-cat)) fn-cat)))

(defun cat-exec ()
  (with-local-stobj fn-cat
    (mv-let (result fn-cat) (cat-exec-run fn-cat) result)))

(assert-event
 (equal (cat-exec)
        (list (list 3 '(1) nil 0 2 2 nil 4 1 3 1 600
                    '(("fn.test" . 3) ("fn.other" . 1)) t)
              (list '(3 . 3) t nil t nil 4)
              7
              0)))

; -----------------------------------------------------------------------------
; The abstraction on ground values: the two-row catalog the keystone
; witnesses use, and its columns by the logical functions (the exec path
; above computed the same values on the live tables).

(defconst *cat-a* (list (fn-cat-assign *cat-h0* nil)
                        (fn-cat-assign *cat-h1* (list (fn-cat-assign *cat-h0* nil)))))

(assert-event (and (fn-held-listp *cat-a*)
                   (equal (fn-cat$a-count *cat-a*) 2)
                   (equal (fn-cat$a-total-octets *cat-a*) 300)
                   (equal (fn-cat$a-group-next "fn.test" *cat-a*) 3)
                   (equal (fn-cat$a-msgid-seqs "<b@x>" *cat-a*) '(1))
                   (equal (fn-cat$a-group-number "fn.test" 2 *cat-a*) 1)))

; -----------------------------------------------------------------------------
; Keystones: the positive witness, complete antecedent and conclusion.

(defthm cat-w-fresh-numbers
  (and (fn-cat-p *cat-a*) (member-equal "fn.test" (fn-record-groups *cat-h2*))
       (equal (fn-cat-group-next "fn.test" *cat-a*) 3)
       (equal (fn-cat-group-number "fn.test" 3 (fn-cat-commit *cat-h2* *cat-a*))
              (fn-cat-count *cat-a*))
       (equal (fn-cat-count *cat-a*) 2))
  :rule-classes nil)

; Without membership: a group the row does not join binds no fresh number.
(defthm cat-w-fresh-numbers-without-member
  (and (fn-cat-p *cat-a*) (not (member-equal "fn.nowhere" (fn-record-groups *cat-h2*)))
       (not (equal (fn-cat-group-number "fn.nowhere" (fn-cat-group-next "fn.nowhere" *cat-a*)
                                        (fn-cat-commit *cat-h2* *cat-a*))
                   (fn-cat-count *cat-a*))))
  :rule-classes nil)
(must-fail
 (defthm cat-r-fresh-numbers-without-member
   (equal (fn-cat-group-number "fn.nowhere" (fn-cat-group-next "fn.nowhere" *cat-a*)
                               (fn-cat-commit *cat-h2* *cat-a*))
          (fn-cat-count *cat-a*))
   :rule-classes nil))

; The fn-cat-p hypothesis of fn-cat-commit-binds-fresh-numbers: no witness
; falsifies it (a row's non-natural number contributes 0 to the high and
; never equals the natural the commit assigns), and the weakened theorem
; was not proved within the lane's budget (PKT-585); the hypothesis stays,
; and a failed proof search is not counted as teeth.

; Visibility is a versioned fact: row 0 withdrawn at version 3 is visible
; at version 3 and not at version 4.
(defconst *cat-a-w* (fn-cat-mark-withdrawn 0 2 3 *cat-a*))   ; = (fn-cat-withdraw 0 3 *cat-a*) by fn-cat-withdraw-is-mark
(defthm cat-w-visible-withdrawn
  (and (natp 0) (natp 3) (< 0 (fn-cat-count *cat-a-w*))
       (fn-held-withdrawn (fn-cat-at 0 *cat-a-w*))
       (equal (fn-held-withdrawn (fn-cat-at 0 *cat-a-w*)) '(2 . 3))
       (equal (fn-cat-visible-at 0 2 *cat-a-w*) (and (< 0 2) (<= 2 2)))
       (equal (fn-cat-visible-at 0 3 *cat-a-w*) (and (< 0 3) (<= 3 2)))
       (fn-cat-visible-at 0 2 *cat-a-w*)
       (not (fn-cat-visible-at 0 3 *cat-a-w*)))
  :rule-classes nil)

; Without the withdrawal: the row is visible at every version above it.
(defthm cat-w-visible-without-withdrawn
  (and (natp 0) (natp 3) (< 0 (fn-cat-count *cat-a*))
       (not (fn-held-withdrawn (fn-cat-at 0 *cat-a*)))
       (not (equal (fn-cat-visible-at 0 3 *cat-a*)
                   (and (< 0 3) (<= 3 (car (fn-held-withdrawn (fn-cat-at 0 *cat-a*))))))))
  :rule-classes nil)
(must-fail
 (defthm cat-r-visible-without-withdrawn
   (equal (fn-cat-visible-at 0 3 *cat-a*)
          (and (< 0 3) (<= 3 (car (fn-held-withdrawn (fn-cat-at 0 *cat-a*))))))
   :rule-classes nil))

; A commit keeps every row below the old count, and the count grows by one.
(defthm cat-w-commit-keeps-rows
  (and (natp 1) (< 1 (fn-cat-count *cat-a*))
       (equal (fn-cat-at 1 (fn-cat-commit *cat-h2* *cat-a*)) (fn-cat-at 1 *cat-a*))
       (equal (fn-cat-count (fn-cat-commit *cat-h2* *cat-a*)) 3)
       (equal (fn-cat-at 2 (fn-cat-commit *cat-h2* *cat-a*)) (fn-cat-assign *cat-h2* *cat-a*)))
  :rule-classes nil)

; Without the bound: the row at the old count is the new one, not the old.
(defthm cat-w-commit-keeps-rows-without-bound
  (and (natp 2) (not (< 2 (fn-cat-count *cat-a*)))
       (not (equal (fn-cat-at 2 (fn-cat-commit *cat-h2* *cat-a*)) (fn-cat-at 2 *cat-a*))))
  :rule-classes nil)
(must-fail
 (defthm cat-r-commit-keeps-rows-without-bound
   (equal (fn-cat-at 2 (fn-cat-commit *cat-h2* *cat-a*)) (fn-cat-at 2 *cat-a*))
   :rule-classes nil))
