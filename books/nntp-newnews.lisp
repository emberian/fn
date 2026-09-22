; NEWNEWS (RFC 3977 section 7.4): what the answer contains, and what it costs.
;
; The renderer and the scan are defined in books/nntp-responses.lisp, beside
; the other reader commands; this book proves the five facts that make the
; command an answer rather than a hope.  Each is stated of
; `fn-nntp-newnews-scan' or of `fn-nntp-step', and `fn-nntp-step' is what the
; served path reaches: books/served.lisp's `fn-served-dispatch' calls
; `fn-auth-step' (books/nntp-auth.lisp), which delegates through
; `fn-peer-step' (books/peer-inbound.lisp) and `fn-nntp-post-step'
; (books/nntp-post.lisp) to `fn-nntp-step', whose `fn-nntp-archive-command'
; arm for NEWNEWS calls `fn-nntp-newnews-response', which calls the scan.
; The last of the five theorems below is that arm, as an equation.
;
;   fn-nntp-newnews-lines-are-clean
;       every rendered line is a stored identifier and carries no CR, LF or
;       NUL, so books/nntp-effects.lisp can read the block back as a
;       well-formed multi-line response.
;   fn-nntp-newnews-scan-reports-only-witnessed-lines
;       nothing is reported that is not the identifier of a committed article
;       available at a number in a group the wildmat matched, whose own
;       injection stamp is at or after the requested instant.  This is the
;       scoping property: a NEWNEWS cannot name an article of a group its
;       wildmat did not match.
;   fn-nntp-newnews-scan-answers-exactly-within-the-budget
;       the refusal is decided by the candidate count against the fuel, and
;       by nothing else.  The count is an independent fold over the same
;       article list, not the scan's own recursion read back.
;   fn-nntp-newnews-scan-reports-at-most-the-budget
;       an answered NEWNEWS renders at most `fuel' lines.
;   fn-nntp-newnews-refusal-is-the-only-other-outcome
;       the scan's outcomes are exactly (:ok lines) and (:over-budget): there
;       is no third value and no truncated answer that could read as complete.
(in-package "ACL2")
(include-book "nntp-legacy")

; The five books of the nntp cluster, books/nntp-overview.lisp and
; books/nntp-legacy.lisp withdraw their definitions at their export events;
; this book reasons about the scan itself, so it re-enables exactly them,
; locally.  No includer inherits them.
(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary
                          fn-nov-vocabulary)))

; The article parser, the syntax recognizer and the date-time decoder stay
; closed for the whole book, for the reason books/nntp-overview.lisp records
; for the first two: opened, they if-split every goal that mentions an
; article thousands of ways.  No theorem here looks inside a stamp; the stamp
; is an opaque (:ok ms) or (:error reason) whose only use is the two tests in
; the scan.
(local (in-theory (disable fn-article-parse fn-article-syntax-p
                           fn-nntp-dt-parse fn-nntp-newnews-stamp)))

; -----------------------------------------------------------------------------
; A candidate is projectable
;
; `fn-nntp-newnews-candidatep' asks for a positive available number in one of
; the matched groups, and `fn-nntp-article-number`
; (books/nntp-projection.lisp) answers a positive number only for an article
; whose stored identifier this profile can render -- the identifier test is
; literally a conjunct of the branch that returns the number.  So the scan
; can only ever render an identifier it can render, with no hypothesis on
; the archive at all.

; Forward chaining, not only rewriting: the hypothesis carries `groups`, which
; the conclusion does not, so a rewrite rule would have to guess it.  Chaining
; from the candidate test itself needs no search.
(defthm fn-nntp-newnews-candidate-is-projectable
  (implies (fn-nntp-newnews-candidatep groups article)
           (fn-nntp-article-idp article))
  :rule-classes
  ((:rewrite)
   (:forward-chaining
    :trigger-terms ((fn-nntp-newnews-candidatep groups article))))
  ; The identifier test stays closed and the availability test opens: the
  ; conclusion is then literally a conjunct of the branch the hypothesis
  ; selects, and no lemma about the projection is spent.
  :hints (("Goal" :induct (fn-nntp-newnews-candidatep groups article)
           :in-theory (disable fn-nntp-article-idp))))

(local
 (defthm fn-nntp-newnews-string-octets-true-listp
   (true-listp (fn-nntp-string-octets text))))

(local
 (defthm fn-nntp-newnews-id-octets-are-a-clean-field
   (implies (fn-nntp-article-idp article)
            (fn-nov-clean-fieldp
             (fn-nntp-string-octets (fn-article-msgid article))))
   :hints (("Goal"
            :use ((:instance fn-nntp-printable-token-is-a-clean-field
                             (token (fn-nntp-string-octets
                                     (fn-article-msgid article)))))
            :in-theory (disable fn-nov-clean-fieldp)))))

; RFC 3977 section 7.4.2's block: one message-id per line, and a line that
; carried CR, LF or NUL would split the response.
(defthm fn-nntp-newnews-lines-are-clean
  (fn-nov-clean-line-listp
   (fn-nntp-parse-1 (fn-nntp-newnews-scan groups threshold articles fuel)))
  :hints (("Goal"
           :induct (fn-nntp-newnews-scan groups threshold articles fuel)
           ; The candidate test, the identifier test and the rendering all
           ; stay closed, so the two lemmas above chain over them instead of
           ; the goal reopening the whole projection.
           :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-idp
                               fn-nntp-string-octets fn-article-msgid))))

; -----------------------------------------------------------------------------
; Nothing is reported that the request did not ask for
;
; The witness predicate is an independent scan of the same article list: it
; asks, for one rendered line, whether SOME committed article is a candidate
; for these groups, carries a readable stamp at or after the threshold, and
; renders to that line.  It is a specification, never called by a served
; path, and it is withdrawn at the export event below.

(defun fn-nntp-newnews-witnessedp (line groups threshold articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (or (and (fn-nntp-newnews-candidatep groups (car articles))
               (fn-nntp-parse-okp (fn-nntp-newnews-stamp (car articles)))
               (fn-ng-less-equal
                threshold (fn-nntp-parse-1 (fn-nntp-newnews-stamp (car articles))))
               (equal line (fn-nntp-string-octets
                            (fn-article-msgid (car articles)))))
          (fn-nntp-newnews-witnessedp line groups threshold (cdr articles)))
    nil))

(defthm fn-nntp-newnews-scan-reports-only-witnessed-lines
  (implies (member-equal
            line
            (fn-nntp-parse-1 (fn-nntp-newnews-scan groups threshold articles fuel)))
           (fn-nntp-newnews-witnessedp line groups threshold articles))
  :hints (("Goal"
           :induct (fn-nntp-newnews-scan groups threshold articles fuel)
           :in-theory (disable fn-nntp-newnews-candidatep
                               fn-nntp-string-octets fn-article-msgid))))

; -----------------------------------------------------------------------------
; The work bound
;
; The candidate count is the second independent fold: it walks the same
; article list and counts the articles the scan would have to parse.  The
; theorem is that the scan answers exactly when that count fits in the fuel,
; so the refusal is a property of the request and the store and not of the
; order in which the scan happened to meet them.

(defun fn-nntp-newnews-candidate-count (groups articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (if (fn-nntp-newnews-candidatep groups (car articles))
          (+ 1 (fn-nntp-newnews-candidate-count groups (cdr articles)))
        (fn-nntp-newnews-candidate-count groups (cdr articles)))
    0))

(defthm fn-nntp-newnews-candidate-count-natural
  (natp (fn-nntp-newnews-candidate-count groups articles))
  :rule-classes :type-prescription)

(defthm fn-nntp-newnews-scan-answers-exactly-within-the-budget
  (equal (fn-nntp-parse-okp (fn-nntp-newnews-scan groups threshold articles fuel))
         (<= (fn-nntp-newnews-candidate-count groups articles) (nfix fuel)))
  :hints (("Goal"
           :induct (fn-nntp-newnews-scan groups threshold articles fuel)
           :in-theory (disable fn-nntp-newnews-candidatep
                               fn-nntp-string-octets fn-article-msgid))))

(defthm fn-nntp-newnews-scan-reports-at-most-the-budget
  (<= (len (fn-nntp-parse-1
            (fn-nntp-newnews-scan groups threshold articles fuel)))
      (nfix fuel))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
           :induct (fn-nntp-newnews-scan groups threshold articles fuel)
           :in-theory (disable fn-nntp-newnews-candidatep
                               fn-nntp-string-octets fn-article-msgid))))

; Two outcomes, and no third.  A scan that is not an answer is the one
; refusal value, so a caller that tests `fn-nntp-parse-okp' has tested
; everything there is to test, and no partial list can reach a 230 block.
(defthm fn-nntp-newnews-refusal-is-the-only-other-outcome
  (implies (not (fn-nntp-parse-okp
                 (fn-nntp-newnews-scan groups threshold articles fuel)))
           (equal (fn-nntp-newnews-scan groups threshold articles fuel)
                  (list :over-budget)))
  :hints (("Goal"
           :induct (fn-nntp-newnews-scan groups threshold articles fuel)
           :in-theory (disable fn-nntp-newnews-candidatep
                               fn-nntp-string-octets fn-article-msgid))))

; -----------------------------------------------------------------------------
; The dispatcher arm
;
; The subject of the theorems above is the function the reader dispatcher
; calls for NEWNEWS.  This is that sentence as an equation: a well-formed
; NEWNEWS command line on an open, projected session is answered by
; `fn-nntp-newnews-response' over the line's own argument tokens, and by
; nothing else.

; The arm itself, over the token list, so that the step-level statement is
; one unfolding of `fn-nntp-step` on top of it rather than the whole
; dispatcher at once.
(local
 (defthm fn-nntp-newnews-command-arm
   (implies (and (fn-nntp-session-projected session)
                 (fn-nntp-keyword-tokenp (car tokens))
                 (fn-nntp-keywordp (car tokens) "NEWNEWS"))
            (equal (fn-nntp-command session archive env tokens)
                   (fn-nntp-newnews-response session archive env (cdr tokens))))
   :hints (("Goal" :in-theory (disable fn-nntp-newnews-response
                                       fn-nntp-retrieval fn-nntp-group-result
                                       fn-nntp-listgroup-command
                                       fn-nntp-list-command
                                       fn-nntp-next-or-last
                                       fn-nntp-over-response
                                       fn-nntp-xover-response
                                       fn-nntp-hdr-response
                                       fn-nntp-xhdr-response
                                       fn-nntp-xpat-response
                                       fn-nntp-newgroups-response)))))

; Three of `fn-nntp-step`'s own tests are kept as hypotheses although the
; others already imply them: a token that upcases to "NEWNEWS" is seven
; letters, so it is an RFC 3977 section 9.8 keyword and the token list it
; heads is a cons; and a NEWNEWS line inside section 3.1's 510-octet limit
; cannot carry a 498-octet argument, because the keyword and the other two
; mandatory arguments take 25 octets of it.  Those three have no `must-fail`
; case in the test book, and that is deliberate: dropping any of them leaves
; a statement that is TRUE and that this book cannot prove, which would
; record a proof difficulty rather than a tooth.  The five hypotheses that do
; change the answer each have one, grounded in a concrete session or line.
(defthm fn-nntp-step-dispatches-newnews-to-the-newnews-response
  (implies (and (fn-nntp-sessionp session)
                (equal (fn-nntp-session-openp session) t)
                (fn-nntp-session-projected session)
                (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "NEWNEWS"))
           (equal (fn-nntp-step session archive env (list :command line))
                  (fn-nntp-newnews-response session archive env
                                            (cdr (fn-nntp-tokenize line)))))
  :hints (("Goal" :in-theory (disable fn-nntp-newnews-response
                                      fn-nntp-command fn-nntp-tokenize
                                      fn-nntp-command-inputp
                                      fn-nntp-keyword-tokenp
                                      fn-nntp-keywordp))))

(verify-guards fn-nntp-newnews-witnessedp)
(verify-guards fn-nntp-newnews-candidate-count)

; -----------------------------------------------------------------------------
; Export.  The six keystones stay enabled.  The two specification functions
; are proof vocabulary -- nothing on a served path calls either -- so they are
; withdrawn under one name, as the books below this one withdraw theirs.

(deftheory fn-nntp-newnews-vocabulary
  '(fn-nntp-newnews-witnessedp fn-nntp-newnews-candidate-count))

(in-theory (disable fn-nntp-newnews-vocabulary))
