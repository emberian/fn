; Teeth for books/msgid-index-concrete.lisp: the Message-ID trie walked by
; string index.
(in-package "ACL2")
(include-book "../../books/msgid-index-concrete")
(include-book "std/testing/must-fail" :dir :system)
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Witness: three articles whose Message-IDs share the prefix "<a" and branch
; at depth 2 and at depth 3, one a proper prefix-sibling of another, so the
; walk descends shared nodes, takes the branch at a character, and must not
; stop at a prefix.

(defconst *mxc-t-a*
  (fn-make-article "<a@example.invalid>" '(1 2) '("fn.test")
                   '(("fn.test" . 1)) t 841000000))
(defconst *mxc-t-ab*
  (fn-make-article "<ab@example.invalid>" '(3 4) '("fn.test")
                   '(("fn.test" . 2)) t 841000000))
(defconst *mxc-t-ac*
  (fn-make-article "<ac@example.invalid>" '(5 6) '("fn.test")
                   '(("fn.test" . 3)) t 841000000))
(defconst *mxc-t-arts* (list *mxc-t-ac* *mxc-t-ab* *mxc-t-a*))
(defconst *mxc-t-trie* (fn-midx-build *mxc-t-arts*))

; The concrete build is the trie, node for node.
(assert-event (equal (fn-mxc-build *mxc-t-arts*) *mxc-t-trie*))
(assert-event (fn-midx-correspondencep (fn-mxc-build *mxc-t-arts*) *mxc-t-arts*))
; Extension and the three refresh arms.
(assert-event (equal (fn-mxc-extend *mxc-t-ac* (fn-midx-build (cdr *mxc-t-arts*)))
                     *mxc-t-trie*))
(assert-event (equal (fn-mxc-refresh *mxc-t-trie* *mxc-t-arts* *mxc-t-arts*)
                     (fn-midx-refresh *mxc-t-trie* *mxc-t-arts* *mxc-t-arts*)))
(assert-event (equal (fn-mxc-refresh (fn-midx-build (cdr *mxc-t-arts*))
                                     (cdr *mxc-t-arts*) *mxc-t-arts*)
                     *mxc-t-trie*))
(assert-event (equal (fn-mxc-refresh nil '(:other) *mxc-t-arts*) *mxc-t-trie*))

; Each held Message-ID is found, and it is the held article.
(assert-event (equal (fn-mxc-lookup "<a@example.invalid>" *mxc-t-trie*) *mxc-t-a*))
(assert-event (equal (fn-mxc-lookup "<ab@example.invalid>" *mxc-t-trie*) *mxc-t-ab*))
(assert-event (equal (fn-mxc-lookup "<ac@example.invalid>" *mxc-t-trie*) *mxc-t-ac*))

; The lookup agrees with fn-midx-lookup on hits, on a miss that shares a
; prefix, on a proper prefix of a held key (an interior node: no value), on
; an extension of a held key, on the empty string (the root's terminal
; slot), on non-strings, and on a trie that is not a builder's.
(defconst *mxc-t-queries*
  (list "<a@example.invalid>" "<ab@example.invalid>" "<ac@example.invalid>"
        "<ad@example.invalid>" "<a" "<ab@example.invalid>x" "" nil 7
        (list #\< #\a)))
(defun mxc-t-agree (qs trie)
  (if (consp qs)
      (and (equal (fn-mxc-lookup (car qs) trie) (fn-midx-lookup (car qs) trie))
           (mxc-t-agree (cdr qs) trie))
    t))
(assert-event (mxc-t-agree *mxc-t-queries* *mxc-t-trie*))
(assert-event (mxc-t-agree *mxc-t-queries* nil))
(assert-event (mxc-t-agree *mxc-t-queries* '((:fn-midx-value . 3) (#\< (#\a)) . 5)))
(assert-event (null (fn-mxc-lookup "<a" *mxc-t-trie*)))
(assert-event (null (fn-mxc-lookup "<ad@example.invalid>" *mxc-t-trie*)))

; The executed code: every concrete function is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-mxc-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-mxc-lookup (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-mxc-put (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-mxc-extend (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-mxc-build (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-mxc-refresh (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The keystones have no hypothesis.  The index lemma's (natp i) is needed:
; at i = -1 the walk reads the root's terminal slot without looking at the
; key, and the list walk (nthcdr's zp case) walks the whole key.  On a trie
; whose root holds a terminal value and the key "<a@example.invalid>" the
; two differ.

(defconst *mxc-t-rooted* (fn-midx-branch-put :fn-midx-value :root *mxc-t-trie*))
; Outside the guard, so evaluated by the prover rather than at the top level.
(defthm mxc-t-get-at-minus-one-reads-the-root
  (equal (fn-mxc-get "<a@example.invalid>" -1 *mxc-t-rooted*) :root)
  :hints (("Goal" :in-theory (enable fn-mxc-get))))
(defthm mxc-t-list-walk-at-minus-one-walks-the-key
  (equal (fn-midx-get-chars (nthcdr -1 (coerce "<a@example.invalid>" 'list))
                            *mxc-t-rooted*)
         *mxc-t-a*))
; The lemmas' instances at i = -1, (natp i) dropped, are false: the
; negation of each instance is a theorem.
(defthm mxc-t-get-lemma-false-without-natp
  (not (equal (fn-mxc-get "<a@example.invalid>" -1 *mxc-t-rooted*)
              (fn-midx-get-chars (nthcdr -1 (coerce "<a@example.invalid>" 'list))
                                 *mxc-t-rooted*)))
  :hints (("Goal" :in-theory (enable fn-mxc-get))))
(defthm mxc-t-put-lemma-false-without-natp
  (not (equal (fn-mxc-put "<a@example.invalid>" -1 :new *mxc-t-trie*)
              (fn-midx-put-chars (nthcdr -1 (coerce "<a@example.invalid>" 'list))
                                 :new *mxc-t-trie*)))
  :hints (("Goal" :in-theory (enable fn-mxc-put))))

; The guard of the walk is needed for its compiled code: with (natp i)
; dropped from the guard, the walk's own body (its mbt, the index into the
; string) is not guard-verified.
(must-fail
 (defun mxc-t-get-unguarded (msgid i trie)
   (declare (xargs :guard (stringp msgid) :verify-guards t
                   :measure (nfix (- (length msgid) (nfix i)))))
   (if (and (mbt (and (stringp msgid) (natp i)))
            (< i (length msgid)))
       (mxc-t-get-unguarded msgid (1+ i) (fn-midx-branch-get (char msgid i) trie))
     (fn-midx-branch-get *fn-midx-value-key* trie))))
