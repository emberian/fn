; fn: `fn-deftransition' --- prove a property of a transition with the
; recognizer CLOSED, as docs/proof-style.md requires.
;
; The measurement this exists for (BOARD 2026-09-20, C2): a
; `(local (in-theory (enable fn-tcl-sessionp)))' above one theorem put the
; recognizer's eleven sub-recognizers into the clause and produced 1082
; subgoals; with the recognizer closed the same theorem took 0.30 s.  The same
; fan was diagnosed, with `accumulated-persistence :frames-a', in the
; checkpoint, reader-profile and article-exports lanes.
;
; The cure is always the same four parts, and three of them are the parts a
; lane forgets:
;
;   1. a NAMED closed theory, so the reader sees which recognizers are shut
;      for this proof instead of scanning upward for a floating
;      `(local (in-theory (disable ...)))' that some later form may widen;
;   2. one branch lemma per branch that cannot affect the property, stated
;      with the branch test as its hypothesis --- `:rule-classes nil', because
;      a restatement of a branch is not a rule (proof-style section 7);
;   3. the content proved at the transition that owns it;
;   4. the theorem lifted by `:use', with the closed theory pinned AT THE FORM
;      and the opens narrowed to the transition itself ("Never enable a
;      vocabulary book-wide").
;
; `fn-deftransition-closed' is part 1; `fn-deftransition' is parts 2 and 4 and
; wires the branch lemmas into the lift's `:use' so that a generated lemma
; cannot be left unused.  Part 3 is the caller's, and is the only part that
; carries content.
;
; This book has no `include-book' and leaves no rule enabled: its plumbing is
; `:program' mode and it defines only macros.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; fn-deftransition-closed
;
;   (fn-deftransition-closed fn-tcl-session-closed
;     (fn-tcl-sessionp fn-tcl-next fn-tcl-with-outbound))
;
; names the recognizers and helpers that stay shut for this cluster's
; transition properties and shuts them.  The `deftheory' is NOT local: a book
; above cites the name in the one hint that needs it rather than
; reconstructing the list.

(defmacro fn-deftransition-closed (name rules)
  (list 'progn
        `(deftheory ,name ',rules)
        `(local (in-theory (disable ,name)))))

; -----------------------------------------------------------------------------
; Branch lemmas

(defun fn-deftransition-branch-events (branches closed opens classes)
  (declare (xargs :mode :program))
  (if (endp branches) nil
    (let* ((branch (car branches))
           (lemma (car branch))
           (test (cadr branch))
           (claim (caddr branch)))
      (cons `(local
              (defthm ,lemma
                (implies ,test ,claim)
                :rule-classes ,classes
                :hints (("Goal" :in-theory (e/d ,opens ,closed)))))
            (fn-deftransition-branch-events (cdr branches) closed opens classes)))))

(defun fn-deftransition-branch-names (branches)
  (declare (xargs :mode :program))
  (if (endp branches) nil
    (cons (car (car branches)) (fn-deftransition-branch-names (cdr branches)))))

; -----------------------------------------------------------------------------
; fn-deftransition
;
;   (fn-deftransition fn-tcl-refuse-preserves-sessionp
;     :statement (implies (and (fn-tcl-sessionp s) (fn-clock-timep now))
;                         (fn-tcl-sessionp
;                          (fn-tcl-result-session
;                           (fn-tcl-refuse s xfer-id reason now))))
;     :closed (fn-tcl-session-closed)
;     :opens (fn-tcl-refuse))
;
; `:statement' is the theorem, unchanged and unwrapped: the macro never edits
; a keystone's statement, it only fixes the theory the proof runs in.
; `:closed' and `:opens' become one `e/d' pinned at this form.  Each
; `:branches' entry is `(<lemma-name> <branch-test> <claim>)'; the lemma is
; local, `:rule-classes nil' by default, proved in the same theory, and its
; name is appended to `:use', so a branch lemma that does not participate in
; the lift is a name the prover reports unused rather than a silent decoration.

(defmacro fn-deftransition (name &key
                                 statement
                                 closed
                                 opens
                                 branches
                                 use
                                 (branch-rule-classes 'nil)
                                 hints
                                 (rule-classes ':default))
  (let ((lifted (append use (fn-deftransition-branch-names branches))))
    (cons
     'progn
     (append
      (fn-deftransition-branch-events branches closed opens branch-rule-classes)
      (list
       `(defthm ,name
          ,statement
          :hints (("Goal" :in-theory (e/d ,opens ,closed)
                   ,@(if lifted (list :use lifted) nil))
                  ,@hints)
          ,@(if (eq rule-classes :default) nil
              (list :rule-classes rule-classes))))))))
