; fn: teeth for books/catalog-delta.lisp (wave 5, lane catalog-slice step 5).
;
; What this book is evidence FOR.  `fn-cat-apply-delta-step-bounded': each
; step touches at most its quantum of rows.  GROUND CHECK, not teeth of a
; theorem: that the resumable application, in steps of any positive quanta,
; to completion, is the one-shot application is OPEN in books/catalog-delta
; (withdrawn, unproved in the lane's budget); the :policy case run in two
; quanta on a live catalog over a live arena, and on ground values, agrees
; with the one-shot application by computation.
; `fn-view-cancel-after-target': a cancel committed after its target leaves
; the article visible to a reader pinned before the cancel until that
; reader advances past the cancel's version (two connections on the live
; catalog: SCN-131's ACL2 half).  Per hypothesis a witness on which the
; retained hypotheses hold, the omitted one fails and the conclusion fails.

(in-package "ACL2")
(include-book "../../books/catalog-delta")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-cat-apply-delta (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-apply-delta-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-recontext (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-recontext-range (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-view-sees (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-delta-p (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Ground fixtures: two payloads, two held rows over handles 0 and 1 with
; contexts decided under generation 0, and a third row (a cancel).

(defconst *cdt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *cdt-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10 67 13 10)))

(defun cdt-held (seq msgid handle bytes)
  (fn-held-make seq (+ 1 seq) 0 msgid handle '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of bytes) (fn-held-context-of bytes nil 0) nil nil))

(defconst *cdt-h0* (cdt-held 0 "<a@x>" 0 *cdt-p0*))
(defconst *cdt-h1* (cdt-held 1 "<b@x>" 1 *cdt-p1*))
(defconst *cdt-cancel* (cdt-held 2 "<cancel@x>" 1 *cdt-p1*))

(assert-event (and (fn-held-p *cdt-h0*) (fn-held-p *cdt-h1*) (fn-held-p *cdt-cancel*)
                   (fn-delta-p (list :policy 1 0 2))
                   (fn-delta-p (list :withdraw 0 2))
                   ; by specification: the flip types the context's verdict
                   ; (fn-hc-verdictp): the verdict value, token :verified.
                   (fn-delta-p (list :redecide 1 (fn-hc-make (fn-stx-make-verdict :verified nil 3)
                                                             nil 3)))
                   (fn-delta-p (list :withdraw-pending "<z@x>" 5))
                   (fn-delta-p (fn-delta-of-row 0 *cdt-h0*))
                   (not (fn-delta-p (list :policy 1 2 0)))
                   (not (fn-delta-p (list :retention 1)))))

; -----------------------------------------------------------------------------
; The executable path.  Build the two-row catalog over the arena; apply the
; :policy delta one-shot; rebuild; apply it in quanta (1 1); the contexts
; agree and carry generation 1.  Then the cancel-after-target case over two
; connections: A pins version 2 before the cancel, B advances after it.

(defun cdt-build (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (fn-arena (fn-arena-seal-list *cdt-p0* fn-arena))
         (fn-arena (fn-arena-seal-list *cdt-p1* fn-arena))
         (fn-cat (fn-cat-commit *cdt-h0* fn-cat))
         (fn-cat (fn-cat-commit *cdt-h1* fn-cat)))
    (mv fn-arena fn-cat)))

(defun cdt-contexts (fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (list (fn-held-context (fn-cat-at 0 fn-cat)) (fn-held-context (fn-cat-at 1 fn-cat))))

(defun cdt-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (mv-let (fn-arena fn-cat)
    (cdt-build fn-arena fn-cat)
    (let* ((before (cdt-contexts fn-cat))
           (fn-cat (fn-cat-apply-delta (list :policy 1 0 2) nil fn-arena fn-cat))
           (one-shot (cdt-contexts fn-cat)))
      (mv-let (fn-arena fn-cat)
        (cdt-build fn-arena fn-cat)
        (mv-let (cursor1 done1 fn-cat)
          (fn-cat-apply-delta-step (list :policy 1 0 2) 0 1 nil fn-arena fn-cat)
          (let ((mid (cdt-contexts fn-cat)))
            (mv-let (cursor2 done2 fn-cat)
              (fn-cat-apply-delta-step (list :policy 1 0 2) cursor1 1 nil fn-arena fn-cat)
              (let ((in-quanta (cdt-contexts fn-cat)))
                (mv-let (fn-arena fn-cat)
                  (cdt-build fn-arena fn-cat)
                  (let* ((fn-cat (fn-cat-apply-in-quanta (list :policy 1 0 2) 0 '(1) nil fn-arena fn-cat))
                         (run (cdt-contexts fn-cat))
                         ; two connections: A pins at version 2 (fn-view-advance
                         ; before the cancel); the cancel of row 0 commits: the
                         ; withdrawal at version 2, then the cancel's own row;
                         ; B advances to version 3 after it.
                         (va (fn-view-advance fn-cat))
                         (fn-cat (fn-cat-apply-delta (list :withdraw 0 2) nil fn-arena fn-cat))
                         (fn-cat (fn-cat-commit *cdt-cancel* fn-cat))
                         (vb (fn-view-advance fn-cat)))
                    (mv (list before one-shot
                              (list cursor1 done1 mid)
                              (list cursor2 done2 in-quanta)
                              run
                              (list va vb
                                    (fn-view-sees va 0 fn-cat)      ; A still sees the article
                                    (fn-view-sees vb 0 fn-cat)      ; B does not
                                    (fn-view-sees va 2 fn-cat)      ; A does not see the cancel row
                                    (fn-view-sees vb 2 fn-cat)      ; B does
                                    (fn-view-apply va (list :withdraw 0 2))
                                    (fn-held-withdrawn (fn-cat-at 0 fn-cat))))
                        fn-arena fn-cat)))))))))))

(defun cdt-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cdt-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defconst *cdt-ctx0-g1* (fn-held-context-of *cdt-p0* nil 1))
(defconst *cdt-ctx1-g1* (fn-held-context-of *cdt-p1* nil 1))

(assert-event
 (equal (cdt-exec)
        (list (list (fn-held-context *cdt-h0*) (fn-held-context *cdt-h1*))
              (list *cdt-ctx0-g1* *cdt-ctx1-g1*)
              (list 1 nil (list *cdt-ctx0-g1* (fn-held-context *cdt-h1*)))
              (list 2 t (list *cdt-ctx0-g1* *cdt-ctx1-g1*))
              (list *cdt-ctx0-g1* *cdt-ctx1-g1*)
              (list 2 3 t nil nil t 2 '(2 . 2)))))

(assert-event (and (equal (fn-hc-generation *cdt-ctx0-g1*) 1)
                   (not (equal *cdt-ctx0-g1* (fn-held-context *cdt-h0*)))))

; -----------------------------------------------------------------------------
; The keystones on ground values (the logical side: the list catalog and the
; list arena).

(defconst *cdt-a* (list *cdt-p0* *cdt-p1*))
(defconst *cdt-c* (list (fn-cat-assign *cdt-h0* nil)
                        (fn-cat-assign *cdt-h1* (list (fn-cat-assign *cdt-h0* nil)))))

(defthm cdt-w-in-quanta-is-apply
  (and (fn-delta-p (list :policy 1 0 2))
       (natp 0)
       (implies (eq (car (list :policy 1 0 2)) :policy) (<= 0 (nth 2 (list :policy 1 0 2))))
       (equal (fn-cat-apply-in-quanta (list :policy 1 0 2) 0 '(1) nil *cdt-a* *cdt-c*)
              (fn-cat-apply-delta (list :policy 1 0 2) nil *cdt-a* *cdt-c*))
       (equal (fn-cat-apply-in-quanta (list :policy 1 0 2) 0 '(2) nil *cdt-a* *cdt-c*)
              (fn-cat-apply-delta (list :policy 1 0 2) nil *cdt-a* *cdt-c*))
       ; not vacuous: the application changes both contexts
       (not (equal (fn-cat-apply-delta (list :policy 1 0 2) nil *cdt-a* *cdt-c*) *cdt-c*))
       (equal (fn-held-context (fn-cat-at 1 (fn-cat-apply-delta (list :policy 1 0 2) nil *cdt-a* *cdt-c*)))
              *cdt-ctx1-g1*))
  :rule-classes nil)

; Without the cursor at or before the range's start: the resumed run skips
; the rows below the cursor and is not the one-shot application.
(defthm cdt-w-in-quanta-without-cursor
  (and (fn-delta-p (list :policy 1 0 2)) (natp 1)
       (not (<= 1 (nth 2 (list :policy 1 0 2))))
       (not (equal (fn-cat-apply-in-quanta (list :policy 1 0 2) 1 '(1) nil *cdt-a* *cdt-c*)
                   (fn-cat-apply-delta (list :policy 1 0 2) nil *cdt-a* *cdt-c*))))
  :rule-classes nil)
(must-fail-checked
 (defthm cdt-r-in-quanta-without-cursor
   (equal (fn-cat-apply-in-quanta (list :policy 1 0 2) 1 '(1) nil *cdt-a* *cdt-c*)
          (fn-cat-apply-delta (list :policy 1 0 2) nil *cdt-a* *cdt-c*))
   :rule-classes nil))

; Without fn-delta-p (a :policy whose range is inverted): the one-shot
; application is the identity while the resumable form is refused by the
; bound; the theorem does not apply.  (A malformed delta is refused by the
; grammar before either is called.)
(defthm cdt-w-in-quanta-without-delta-p
  (and (not (fn-delta-p (list :policy 1 2 0))) (natp 0)
       (equal (fn-cat-apply-delta (list :policy 1 2 0) nil *cdt-a* *cdt-c*) *cdt-c*))
  :rule-classes nil)

; The bound on a step.
(defthm cdt-w-step-bounded
  (and (natp 0) (posp 1)
       (mv-let (cursor2 done c2)
         (fn-cat-apply-delta-step (list :policy 1 0 2) 0 1 nil *cdt-a* *cdt-c*)
         (declare (ignore done c2))
         (and (<= cursor2 (+ (max 0 (nfix 0)) 1)) (equal cursor2 1))))
  :rule-classes nil)

; The cancel-after-target case, complete antecedent and conclusion: the
; cancel commits when the count is 2; a reader at version 2 sees row 0; a
; reader at version 3 does not.
(defthm cdt-w-cancel-after-target
  (and (natp 0) (natp 2) (natp 2) (< 0 (fn-cat-count *cdt-c*))
       (null (fn-held-withdrawn (fn-cat-at 0 *cdt-c*)))
       (equal (car (fn-cat-apply-delta (list :withdraw 0 2) nil *cdt-a* *cdt-c*))
              (car (fn-cat-withdraw 0 2 *cdt-c*)))
       (let ((c2 (fn-cat-withdraw 0 2 *cdt-c*)))
         (and (equal (fn-held-withdrawn (fn-cat-at 0 c2)) (cons (fn-cat-count *cdt-c*) 2))
              (equal (fn-view-sees 2 0 c2) (and (< 0 2) (<= 2 (fn-cat-count *cdt-c*))))
              (fn-view-sees 2 0 c2)
              (not (fn-view-sees (+ 1 (fn-cat-count *cdt-c*)) 0 c2)))))
  :rule-classes nil)

; Without the target's being un-withdrawn (a second cancel of the same
; row): the first cancel's version stands, not the second's.
(defconst *cdt-c-w* (fn-cat-mark-withdrawn 0 2 1 *cdt-c*))   ; = (fn-cat-withdraw 0 1 *cdt-c*) by fn-cat-withdraw-is-mark
(defthm cdt-w-cancel-without-fresh-target
  (and (natp 0) (natp 2) (< 0 (fn-cat-count *cdt-c-w*))
       (not (null (fn-held-withdrawn (fn-cat-at 0 *cdt-c-w*))))
       (not (equal (fn-held-withdrawn (fn-cat-at 0 (fn-cat-withdraw 0 2 *cdt-c-w*)))
                   (cons (fn-cat-count *cdt-c-w*) 2))))
  :rule-classes nil)
(must-fail-checked
 (defthm cdt-r-cancel-without-fresh-target
   (equal (fn-held-withdrawn (fn-cat-at 0 (fn-cat-withdraw 0 2 *cdt-c-w*)))
          (cons (fn-cat-count *cdt-c-w*) 2))
   :rule-classes nil))

; Without the bound (a target that is not a row): nothing is withdrawn.
(defthm cdt-w-cancel-without-bound
  (and (natp 5) (not (< 5 (fn-cat-count *cdt-c*)))
       (equal (fn-cat-apply-delta (list :withdraw 5 2) nil *cdt-a* *cdt-c*) *cdt-c*))
  :rule-classes nil)
