; Teeth for the index-backed NNTP enumeration keystones (C1-09).
;
; The keystones are the six FN-NNTP-INDEX-...-EQUALS-FOLD theorems in
; books/nntp-index.lisp and the three FN-NNTP-INDEX-CACHE-OPEN-ANSWERS-...
; theorems that lift them to the cache the host calls.  Every one carries the
; hypothesis (FN-ARTICLE-LISTP CONFIGURED ARTICLES); the range keystone also
; carries (NATP LOW) and (NATP HIGH).  Each hypothesis below has a concrete
; separating witness -- two different answers, not a failed proof -- and a
; MUST-FAIL, bounded by an explicit prover step limit, confirming the general
; statement does not go through without it.
(in-package "ACL2")
(include-book "../../books/nntp-index")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.  Two configured groups, three committed
; articles, one of them cross-posted.  fn.test's available numbers appear in
; descending article order (7 then 4), so an answer that merely echoed article
; order would be wrong; fn.letters and fn.test have different low, high and
; range answers, so an answer that ignored the group would be wrong too.

(defconst *nix-groups* '("fn.letters" "fn.test"))
(defconst *nix-article-a*
  (fn-make-article "<a@example.invalid>" '(65)
                   '("fn.letters" "fn.test")
                   (list (cons "fn.letters" 1) (cons "fn.test" 7))
                   t))
(defconst *nix-article-b*
  (fn-make-article "<b@example.invalid>" '(66)
                   '("fn.letters")
                   (list (cons "fn.letters" 4))
                   t))
(defconst *nix-article-c*
  (fn-make-article "<c@example.invalid>" '(67)
                   '("fn.test")
                   (list (cons "fn.test" 4))
                   t))
(defconst *nix-articles*
  (list *nix-article-a* *nix-article-b* *nix-article-c*))
(defconst *nix-nexts* (list (cons "fn.letters" 5) (cons "fn.test" 8)))
(defconst *nix-archive*
  (fn-make-state *nix-groups* *nix-nexts* *nix-articles* 3 nil nil))
(defconst *nix-index* (fn-index-build *nix-articles*))

(assert-event (fn-statep *nix-archive*))
(assert-event (fn-article-listp *nix-groups* *nix-articles*))
(assert-event (fn-nntp-projectionp *nix-archive*))
(assert-event (equal (len *nix-index*) 4))

; The fold answers this witness produces are distinct across groups and are
; not the identity on article order.
(assert-event (equal (fn-nntp-group-count "fn.letters" *nix-articles*) 2))
(assert-event (equal (fn-nntp-group-low "fn.letters" *nix-articles*) 1))
(assert-event (equal (fn-nntp-group-high "fn.letters" *nix-articles*) 4))
(assert-event (equal (fn-nntp-group-low "fn.test" *nix-articles*) 4))
(assert-event (equal (fn-nntp-group-high "fn.test" *nix-articles*) 7))
(assert-event (equal (fn-nntp-group-range-numbers "fn.test" 1 9 *nix-articles*)
                     '(4 7)))
(assert-event (equal (fn-nntp-group-next-number "fn.letters" 1 *nix-articles*) 4))
(assert-event (equal (fn-nntp-group-last-number "fn.test" 7 *nix-articles*) 4))

; The index-backed variants agree, command by command.
(assert-event (equal (fn-nntp-index-group-count *nix-index* "fn.letters") 2))
(assert-event (equal (fn-nntp-index-group-low *nix-index* "fn.letters") 1))
(assert-event (equal (fn-nntp-index-group-high *nix-index* "fn.letters") 4))
(assert-event (equal (fn-nntp-index-group-low *nix-index* "fn.test") 4))
(assert-event (equal (fn-nntp-index-group-high *nix-index* "fn.test") 7))
(assert-event (equal (fn-nntp-index-group-range-numbers *nix-index* "fn.test" 1 9)
                     '(4 7)))
(assert-event (equal (fn-nntp-index-group-next-number *nix-index* "fn.letters" 1) 4))
(assert-event (equal (fn-nntp-index-group-last-number *nix-index* "fn.test" 7) 4))

; A group with no committed article, and a group that is not configured at
; all, both answer with the empty projection rather than with another group's
; numbers.
(assert-event (equal (fn-nntp-index-group-count *nix-index* "fn.absent") 0))
(assert-event (equal (fn-nntp-index-group-low *nix-index* "fn.absent") 0))
(assert-event (equal (fn-nntp-index-group-range-numbers *nix-index* "fn.absent" 1 9)
                     nil))

; -----------------------------------------------------------------------------
; The cache the host calls.  FN-INDEX-HOST-QUERY (host/index-host.lisp) calls
; FN-NNTP-INDEX-CACHE-QUERY and nothing else.

(defconst *nix-generation* 3)
(defconst *nix-digest* (fn-nntp-index-config-digest *nix-archive*))
(defconst *nix-cache* (fn-nntp-index-cache-open *nix-generation* *nix-archive*))

(assert-event (fn-nntp-index-cache-freshp *nix-cache* *nix-generation* *nix-digest*))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* *nix-generation* *nix-digest*
                      :count "fn.letters" 1 9 nil)
                     '(:ok . 2)))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* *nix-generation* *nix-digest*
                      :range "fn.test" 1 9 nil)
                     '(:ok 4 7)))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* *nix-generation* *nix-digest*
                      :next "fn.letters" 1 9 1)
                     '(:ok . 4)))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* *nix-generation* *nix-digest*
                      :capabilities "fn.letters" 1 9 nil)
                     '(:unknown)))

; A forged generation is refused, in both directions, and so is a forged
; configuration digest.  The refusal is a distinct result, not a wrong answer.
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* 4 *nix-digest* :count "fn.letters" 1 9 nil)
                     '(:stale)))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* 2 *nix-digest* :count "fn.letters" 1 9 nil)
                     '(:stale)))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* *nix-generation* '(:forged)
                      :count "fn.letters" 1 9 nil)
                     '(:stale)))
; A generation that is not a natural number is not a generation.
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* "3" *nix-digest* :count "fn.letters" 1 9 nil)
                     '(:stale)))

; -----------------------------------------------------------------------------
; The generation test is load bearing: a cache built before a post answers
; differently from the truth after it.  Without the refusal above, this is the
; wrong answer the reader would have served.

(defconst *nix-article-d*
  (fn-make-article "<d@example.invalid>" '(68)
                   '("fn.letters")
                   (list (cons "fn.letters" 5))
                   t))
(defconst *nix-posted-articles* (append *nix-articles* (list *nix-article-d*)))
(defconst *nix-posted-archive*
  (fn-make-state *nix-groups* (list (cons "fn.letters" 6) (cons "fn.test" 8))
                 *nix-posted-articles* 4 nil nil))
(defconst *nix-posted-digest*
  (fn-nntp-index-config-digest *nix-posted-archive*))

(assert-event (fn-statep *nix-posted-archive*))
(assert-event (equal (fn-nntp-group-count "fn.letters" *nix-posted-articles*) 3))
(assert-event (equal (fn-nntp-group-high "fn.letters" *nix-posted-articles*) 5))
; The pre-post cache would have answered 2 and 4.  It is refused instead.
(assert-event (equal (fn-nntp-index-group-count *nix-index* "fn.letters") 2))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-cache* 4 *nix-posted-digest*
                      :count "fn.letters" 1 9 nil)
                     '(:stale)))
; Re-opened at the new generation, the cache carries the post-generation truth.
(defconst *nix-posted-cache*
  (fn-nntp-index-cache-open 4 *nix-posted-archive*))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-posted-cache* 4 *nix-posted-digest*
                      :count "fn.letters" 1 9 nil)
                     '(:ok . 3)))
(assert-event (equal (fn-nntp-index-cache-query
                      *nix-posted-cache* 4 *nix-posted-digest*
                      :high "fn.letters" 1 9 nil)
                     '(:ok . 5)))

; -----------------------------------------------------------------------------
; Hypothesis 1: (FN-ARTICLE-LISTP CONFIGURED ARTICLES).
;
; It is the consistency of the article list that makes one group contribute at
; most one membership.  An article whose group list repeats a group is
; materialized twice by FN-INDEX-BUILD while FN-NNTP-MEMBERSHIP-NUMBER reads
; only the first match, so the two answers separate.

(defconst *nix-duplicate-article*
  (fn-make-article "<dup@example.invalid>" '(68)
                   '("fn.letters" "fn.letters")
                   (list (cons "fn.letters" 1) (cons "fn.letters" 2))
                   t))
(defconst *nix-duplicate-articles* (list *nix-duplicate-article*))

(assert-event (not (fn-article-listp *nix-groups* *nix-duplicate-articles*)))
(assert-event (equal (fn-nntp-group-range-numbers
                      "fn.letters" 1 9 *nix-duplicate-articles*)
                     '(1)))
(assert-event (equal (fn-nntp-index-group-range-numbers
                      (fn-index-build *nix-duplicate-articles*) "fn.letters" 1 9)
                     '(1 2)))
(assert-event (equal (fn-nntp-group-count "fn.letters" *nix-duplicate-articles*) 1))
(assert-event (equal (fn-nntp-index-group-count
                      (fn-index-build *nix-duplicate-articles*) "fn.letters")
                     2))

(with-prover-step-limit 500000
 (must-fail
  (thm (implies (and (stringp group) (natp low) (natp high))
                (equal (fn-nntp-index-group-range-numbers
                        (fn-index-build articles) group low high)
                       (fn-nntp-group-range-numbers group low high articles))))))

(with-prover-step-limit 500000
 (must-fail
  (thm (implies (stringp group)
                (equal (fn-nntp-index-group-count (fn-index-build articles) group)
                       (fn-nntp-group-count group articles))))))

; -----------------------------------------------------------------------------
; Hypothesis 2: (NATP LOW), and hypothesis 3: (NATP HIGH).
;
; FN-INDEX-QUERY-RANGE is total: a malformed bound refuses with NIL.  The fold
; has no such test -- FN-NG-LESS-EQUAL completes a non-number to zero -- so on
; a non-natural bound the two disagree rather than both refusing.

(assert-event (equal (fn-nntp-group-range-numbers "fn.letters" 1/2 9 *nix-articles*)
                     '(1 4)))
(assert-event (equal (fn-nntp-index-group-range-numbers *nix-index* "fn.letters" 1/2 9)
                     nil))
(assert-event (equal (fn-nntp-group-range-numbers "fn.letters" 1 9/2 *nix-articles*)
                     '(1 4)))
(assert-event (equal (fn-nntp-index-group-range-numbers *nix-index* "fn.letters" 1 9/2)
                     nil))

(with-prover-step-limit 500000
 (must-fail
  (thm (implies (and (fn-article-listp configured articles)
                     (stringp group)
                     (natp high))
                (equal (fn-nntp-index-group-range-numbers
                        (fn-index-build articles) group low high)
                       (fn-nntp-group-range-numbers group low high articles))))))

(with-prover-step-limit 500000
 (must-fail
  (thm (implies (and (fn-article-listp configured articles)
                     (stringp group)
                     (natp low))
                (equal (fn-nntp-index-group-range-numbers
                        (fn-index-build articles) group low high)
                       (fn-nntp-group-range-numbers group low high articles))))))

; -----------------------------------------------------------------------------
; Hypothesis 4: (STRINGP GROUP).  This one does not separate, and is recorded
; as what it is: FN-INDEX-QUERY-RANGE's totality guard.  Under
; FN-ARTICLE-LISTP every membership key is a string, so a non-string group
; selects nothing on either side and both answers are the empty projection.
; It is carried in the keystones because the query is total, not because it
; rejects a reachable case.
(assert-event (equal (fn-nntp-group-range-numbers :fn.letters 1 9 *nix-articles*)
                     nil))
(assert-event (equal (fn-nntp-index-group-range-numbers *nix-index* :fn.letters 1 9)
                     nil))
