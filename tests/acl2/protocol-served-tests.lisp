; protocol-served-tests.lisp -- teeth for books/protocol-served.lisp (lane
; def-command, 2026-10-03).
;
; GEN: defteeth -- these teeth are written by hand in the shape of the teeth
; contract v1 (build/coordinator/lanedumps/generators-2.md: the positive
; witness asserts every labelled hypothesis and the conclusion; one removal
; per hypothesis affirms every retained hypothesis, the failure of the
; removed one and of the conclusion, or is recorded :deferred; a mutation is
; a checked edit of the claim) and become (defteeth K ...) forms when that
; generator lands; the owed rows are in the source book.
;
; What is asserted:
;  (1) fn-proto-archive-command-cat-is-pinned on every declared row's :teeth
;      lines, on the served-catalog fixture (three articles in fn.test /
;      fn.other, the pinned archive = the view at 3, its index the pin built
;      from it): the hypotheses conjunct by conjunct and the conclusion on
;      both components, with and without an Xref server named; the lines
;      answer (221, 211, 411, 224; OVER's cursor arm answers a cursor only
;      with no Xref server named: c07's spot-check); and the composed subject
;      on BOTH routes reaches each declared row (fn-scr-command, the
;      unrestricted route's command layer; fn-pix-command-pinned, the
;      restricted route's dispatcher): a reply, never the 500 of an
;      unrecognized command (the HELP closure's converse, by evaluation).
;  (2) removal witnesses: view-articles (the pinned archive served at a view
;      the pin does not name: reachable); trie-correspondence (an index whose
;      trie is the build of another view: logical); statep, pin-correspondence,
;      fresh and columns :deferred (no ground state outside each is built
;      here; the weakened theorems are registered as must-fails, which is not
;      a counterexample).
;  (3) a mutation (:conclusion): the sessions compared for the effects fails
;      on a line whose reply moves the current article.
;  (4) fn-proto-advance-eventp-is-served-advance-eventp and
;      fn-proto-archive-keywordp-is-nntp-archive-keywordp witnessed on every
;      served keyword, with a mutation: a table whose :view :select rows are
;      GROUP alone differs from the machine on LISTGROUP.
;  (5) the fail-closed checks of the served table: the real one passes; a
;      served command with no served row, a served row no protocol row
;      names, a served row without :view, forms without :cost, a :pinned row whose
;      arm mentions the live formal, a :view-decided without a registry id,
;      two forms of one name and a form list whose last test is not t are
;      refused.
;  (6) the generated dispatcher and the policy sites are guard-verified.

(in-package "ACL2")
(include-book "../../books/protocol-served")
(include-book "../../books/served-catalog-chain")   ; fn-scr-command: the unrestricted route
(include-book "must-fail-checked")

;; The served-catalog fixture (tests/acl2/served-catalog-tests.lisp).
(defconst *pst-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *pst-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *pst-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))

(defun pst-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defun pst-catalog (ws handle c)
  (if (consp ws)
      (pst-catalog (cdr ws) (+ 1 handle)
                   (append c (list (fn-cat-assign (pst-held (car ws) handle nil) c))))
    c))

(defconst *pst-w0* (fn-record-make 0 1 1 "<a@x>" *pst-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *pst-w1* (fn-record-make 1 2 2 "<b@x>" *pst-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *pst-w2* (fn-record-make 2 3 3 "<c@x>" *pst-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *pst-a* (list *pst-p0* *pst-p1* *pst-p2*))
(defconst *pst-c* (pst-catalog (list *pst-w0* *pst-w1* *pst-w2*) 0 nil))

;; Macros: a theorem may name the arena's and the catalog's logical values
;; where the stobjs are required; a function may not (so the helpers below
;; take the archive, the index and the stobjs as formals).
(defmacro pst-arch (v)
  `(fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                  (fn-cat-view-articles ,v *pst-a* *pst-c*) 0 nil nil))

(defmacro pst-index (v)
  `(fn-gidx-pin (fn-midx-build (fn-cat-view-articles ,v *pst-a* *pst-c*))
                (fn-gidx-build (fn-cat-view-articles ,v *pst-a* *pst-c*))))

(defconst *pst-session* (fn-nntp-make-session t "fn.test" 1 t))
(defmacro pst-tokens (line) `(fn-nntp-tokenize (fn-nntp-string-octets ,line)))

;; The served environment names an Xref server (books/protocol-table.lisp's
;; :live column: it always does), so the Xref prelude and the compatibility
;; arms answer; and one that names none, so OVER's cursor arm answers.
(defconst *pst-env-x*
  (fn-nntp-env-listed nil nil nil (list nil nil (fn-nntp-string-octets "news.example.invalid"))))
(defconst *pst-env-0* (fn-nntp-env-listed nil nil nil nil))

;; The conclusion of fn-proto-archive-command-cat-is-pinned at one line: the
;; sessions equal, the expanded effects equal.
(defun pst-agree (env line arch index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line)))
         (cat (fn-proto-archive-command-cat *pst-session* arch index nil env
                                            (car tokens) (cdr tokens) 3 fn-arena fn-cat))
         (pinned (fn-nntp-archive-command-pinned *pst-session* arch index nil env
                                                 (car tokens) (cdr tokens) fn-arena)))
    (and (equal (fn-nntp-result-session cat) (fn-nntp-result-session pinned))
         (equal (fn-ovw-expand (fn-nntp-result-effects cat) fn-arena fn-cat)
                (fn-ovw-expand (fn-nntp-result-effects pinned) fn-arena fn-cat)))))

(defun pst-agree-all (env lines arch index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (consp lines)
      (and (pst-agree env (car lines) arch index fn-arena fn-cat)
           (pst-agree-all env (cdr lines) arch index fn-arena fn-cat))
    t))

;; The declared rows' :teeth lines, from the table.
(defun pst-teeth-lines (names rows)
  (declare (xargs :verify-guards nil))
  (if (consp names)
      (append (fn-proto-plist-get :teeth (fn-proto-row-plist (fn-proto-row (car names) rows)))
              (pst-teeth-lines (cdr names) rows))
    nil))

(defconst *pst-lines* (pst-teeth-lines *fn-proto-cat-rows* *fn-proto-served-table*))

;; (1) The positive witness: every hypothesis (fn-scol-okp is a defun-nx:
;; its definition is opened so the fixture evaluates it), then the
;; conclusion on every declared line, with and without an Xref server.
(defthm pst-keystone-witness
  (let ((arch (pst-arch 3)) (index (pst-index 3)))
    (and ;; view-articles
         (equal (fn-state-articles arch) (fn-cat-view-articles 3 *pst-a* *pst-c*))
         ;; statep
         (fn-statep arch)
         ;; pin-correspondence
         (fn-gidx-pin-correspondencep index arch)
         ;; trie-correspondence
         (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles arch))
         ;; fresh
         (fn-cnx-freshp *pst-c*)
         ;; columns
         (fn-scol-okp *pst-a* *pst-c*)
         ;; the conclusion, on every declared line
         (<= 20 (len *pst-lines*))
         (pst-agree-all *pst-env-x* *pst-lines* arch index *pst-a* *pst-c*)
         (pst-agree-all *pst-env-0* *pst-lines* arch index *pst-a* *pst-c*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

;; The lines are not trivial: a 221 (XPAT), a 211 (GROUP) and a 224 (OVER)
;; answered; GROUP of an unknown group 411; and OVER's cursor arm answers
;; the range as a cursor with either Xref environment.
(defun pst-code (env line arch index fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (take 3 (cadr (car (fn-nntp-result-effects
                        (fn-nntp-archive-command-pinned *pst-session* arch index nil env
                                                        (car tokens) (cdr tokens) fn-arena)))))))

(defun pst-cursorp (env line arch index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (fn-ovw-cursor-effectp
     (car (fn-nntp-result-effects
           (fn-proto-archive-command-cat *pst-session* arch index nil env
                                         (car tokens) (cdr tokens) 3 fn-arena fn-cat))))))

(defthm pst-lines-answer
  (let ((arch (pst-arch 3)) (index (pst-index 3)))
    (and (equal (pst-code *pst-env-x* "XPAT Subject 1-3 *" arch index *pst-a*) (list 50 50 49))
         (equal (pst-code *pst-env-x* "GROUP fn.test" arch index *pst-a*) (list 50 49 49))
         (equal (pst-code *pst-env-x* "GROUP fn.none" arch index *pst-a*) (list 52 49 49))
         (equal (pst-code *pst-env-x* "OVER 1-3" arch index *pst-a*) (list 50 50 52))
         (pst-cursorp *pst-env-0* "OVER 1-3" arch index *pst-a* *pst-c*)
         (pst-cursorp *pst-env-x* "OVER 1-3" arch index *pst-a* *pst-c*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ovw-cursor-effectp))))

;; Composed reachability on BOTH routes: each declared row's first :teeth
;; line draws a reply other than 500 from the unrestricted route's command
;; layer (fn-scr-command) and from the restricted route's dispatcher
;; (fn-pix-command-pinned).
(defun pst-first-lines (names rows)
  (declare (xargs :verify-guards nil))
  (if (consp names)
      (let ((teeth (fn-proto-plist-get :teeth (fn-proto-row-plist (fn-proto-row (car names) rows)))))
        (if (consp teeth)
            (cons (car teeth) (pst-first-lines (cdr names) rows))
          (pst-first-lines (cdr names) rows)))
    nil))

(defun pst-not-500 (effects)
  (declare (xargs :verify-guards nil))
  (and (consp effects)
       (or (and (fn-ovw-cursor-effectp (car effects))
                (fn-ovw-cursorp (cadr (car effects))))
           (and (fn-nnw-meta-effectp (car effects))
                (fn-nnw-meta-livep (cadr (car effects))))
           (and (consp (car effects)) (equal (car (car effects)) :reply)
                (not (equal (take 3 (cadr (car effects))) (list 53 48 48)))))))

(defun pst-reaches (lines arch index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (consp lines)
      (and (pst-not-500
            (fn-nntp-result-effects
             (fn-scr-command *pst-session* arch index nil *pst-env-x*
                             (fn-nntp-tokenize (fn-nntp-string-octets (car lines)))
                             3 fn-arena fn-cat)))
           (pst-not-500
            (fn-nntp-result-effects
             (fn-pix-command-pinned *pst-session* arch index nil *pst-env-x*
                                    (fn-nntp-tokenize (fn-nntp-string-octets (car lines)))
                                    fn-arena)))
           (pst-reaches (cdr lines) arch index fn-arena fn-cat))
    t))

(defthm pst-rows-reach-both-routes
  (and (equal (len (pst-first-lines *fn-proto-cat-rows* *fn-proto-served-table*))
              (len *fn-proto-cat-rows*))
       (pst-reaches (pst-first-lines *fn-proto-cat-rows* *fn-proto-served-table*)
                    (pst-arch 3) (pst-index 3) *pst-a* *pst-c*))
  :rule-classes nil)

;; DC03: these reachable successes distinguish the number/current forms,
;; cursor movement and LISTGROUP selection from a recognized command that
;; merely returns an error.  The literal boundary antecedent is asserted
;; together with both components of its conclusion (pst-agree-all).
(defun pst-command-at-session (session env line arch index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (fn-proto-archive-command-cat session arch index nil env
                                  (car tokens) (cdr tokens) 3 fn-arena fn-cat)))

(defun pst-pinned-at-session (session env line arch index fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (fn-nntp-archive-command-pinned session arch index nil env
                                     (car tokens) (cdr tokens) fn-arena)))

(defun pst-reaches-at-session (session env line arch index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (and (pst-not-500 (fn-nntp-result-effects
                       (fn-scr-command session arch index nil env tokens 3 fn-arena fn-cat)))
         (pst-not-500 (fn-nntp-result-effects
                       (fn-pix-command-pinned session arch index nil env tokens fn-arena))))))

(defun pst-result-code (result)
  (declare (xargs :verify-guards nil))
  (take 3 (cadr (car (fn-nntp-result-effects result)))))

(defconst *pst-dc03-success-lines*
  '("NEXT" "LISTGROUP fn.test" "LISTGROUP fn.test 2-3"
    "ARTICLE" "ARTICLE 2" "HEAD" "HEAD 2"
    "BODY" "BODY 2" "STAT" "STAT 2"))

(defthm pst-dc03-reachable-positive
  (let* ((arch (pst-arch 3)) (index (pst-index 3))
         (next (pst-command-at-session *pst-session* *pst-env-x* "NEXT" arch index *pst-a* *pst-c*))
         (last (pst-command-at-session (fn-nntp-make-session t "fn.test" 2 t)
                                       *pst-env-x* "LAST" arch index *pst-a* *pst-c*)))
    (and (equal (fn-state-articles arch) (fn-cat-view-articles 3 *pst-a* *pst-c*))
         (fn-statep arch)
         (fn-gidx-pin-correspondencep index arch)
         (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles arch))
         (fn-cnx-freshp *pst-c*)
         (fn-scol-okp *pst-a* *pst-c*)
         (pst-agree-all *pst-env-x* *pst-dc03-success-lines* arch index *pst-a* *pst-c*)
         (pst-agree-all *pst-env-0* *pst-dc03-success-lines* arch index *pst-a* *pst-c*)
         (pst-reaches *pst-dc03-success-lines* arch index *pst-a* *pst-c*)
         (equal (pst-result-code next) '(50 50 51))
         (equal (fn-nntp-session-current (fn-nntp-result-session next)) 2)
         (equal (fn-nntp-result-session last)
                (fn-nntp-result-session (pst-pinned-at-session
                  (fn-nntp-make-session t "fn.test" 2 t) *pst-env-x* "LAST" arch index *pst-a*)))
         (equal (fn-ovw-expand (fn-nntp-result-effects last) *pst-a* *pst-c*)
                (fn-ovw-expand (fn-nntp-result-effects (pst-pinned-at-session
                  (fn-nntp-make-session t "fn.test" 2 t) *pst-env-x* "LAST" arch index *pst-a*))
                  *pst-a* *pst-c*))
         (pst-reaches-at-session (fn-nntp-make-session t "fn.test" 2 t)
                                 *pst-env-x* "LAST" arch index *pst-a* *pst-c*)
         (equal (pst-result-code last) '(50 50 51))
         (equal (fn-nntp-session-current (fn-nntp-result-session last)) 1)
         (equal (pst-result-code (pst-command-at-session *pst-session* *pst-env-x*
                                  "LISTGROUP fn.test" arch index *pst-a* *pst-c*)) '(50 49 49))
         (equal (pst-result-code (pst-command-at-session *pst-session* *pst-env-x*
                                  "ARTICLE 2" arch index *pst-a* *pst-c*)) '(50 50 48))
         (equal (pst-result-code (pst-command-at-session *pst-session* *pst-env-x*
                                  "HEAD 2" arch index *pst-a* *pst-c*)) '(50 50 49))
         (equal (pst-result-code (pst-command-at-session *pst-session* *pst-env-x*
                                  "BODY 2" arch index *pst-a* *pst-c*)) '(50 50 50))
         (equal (pst-result-code (pst-command-at-session *pst-session* *pst-env-x*
                                  "STAT 2" arch index *pst-a* *pst-c*)) '(50 50 51))
         (equal (fn-nntp-session-current (fn-nntp-result-session
                 (pst-command-at-session *pst-session* *pst-env-x* "STAT 2"
                                         arch index *pst-a* *pst-c*))) 2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

;; The withdrawal preludes remain ahead of compatibility and retrieval.
;; A control pin retains the target while the catalog's view hides it;
;; both the number and Message-ID forms therefore reach their literal
;; withdrawn tests, even with an Xref server configured.
(defconst *pst-c-withdrawn*
  (fn-cat$a-commit (pst-held *pst-w2* 2 nil)
                   (fn-cat$a-withdraw 1 2 (take 2 *pst-c*))))
(defmacro pst-withdrawn-arch ()
  `(fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                  (fn-cat-view-articles 3 *pst-a* *pst-c-withdrawn*) 0 nil nil))
(defmacro pst-withdrawn-index ()
  `(fn-gidx-pin-with-control
     (fn-midx-build (fn-cat-view-articles 3 *pst-a* *pst-c-withdrawn*))
     (fn-gidx-build (fn-cat-view-articles 3 *pst-a* *pst-c-withdrawn*))
     (fn-ctl-pin (list (cadr (fn-cat-view-articles 3 *pst-a* *pst-c*))) nil)))
(defconst *pst-withdrawn-lines*
  '("ARTICLE 2" "ARTICLE <b@x>" "HEAD 2" "HEAD <b@x>"
    "BODY 2" "BODY <b@x>" "STAT 2" "STAT <b@x>"))

(defthm pst-dc03-withdrawn-positive
  (let ((arch (pst-withdrawn-arch)) (index (pst-withdrawn-index)))
    (and (equal (fn-state-articles arch) (fn-cat-view-articles 3 *pst-a* *pst-c-withdrawn*))
         (fn-statep arch)
         (fn-gidx-pin-correspondencep index arch)
         (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles arch))
         (fn-cnx-freshp *pst-c-withdrawn*)
         (fn-scol-okp *pst-a* *pst-c-withdrawn*)
         (fn-nntp-number-withdrawn-p-cat *pst-session* index (fn-nntp-string-octets "2")
                                         3 *pst-a* *pst-c-withdrawn*)
         (fn-nntp-message-id-tokenp (fn-nntp-string-octets "<b@x>"))
         (fn-nntp-msgid-withdrawn-p-cat index (fn-nntp-string-octets "<b@x>")
                                        3 *pst-a* *pst-c-withdrawn*)
         (pst-agree-all *pst-env-x* *pst-withdrawn-lines* arch index *pst-a* *pst-c-withdrawn*)
         (pst-agree-all *pst-env-0* *pst-withdrawn-lines* arch index *pst-a* *pst-c-withdrawn*)
         (pst-reaches *pst-withdrawn-lines* arch index *pst-a* *pst-c-withdrawn*)
         (equal (pst-code *pst-env-x* "ARTICLE 2" arch index *pst-a*) '(52 50 51))
         (equal (pst-code *pst-env-x* "ARTICLE <b@x>" arch index *pst-a*) '(52 51 48))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

;; (2) Removal witnesses.
;; view-articles, reachable: the pinned archive served at view 2 (the third
;; row invisible) answers XPAT (a declared row) differently from the pinned
;; reference.
(defun pst-cat-at (env line v arch index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (fn-proto-archive-command-cat *pst-session* arch index nil env
                                  (car tokens) (cdr tokens) v fn-arena fn-cat)))

(defun pst-pinned-of (env line arch index fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (fn-nntp-archive-command-pinned *pst-session* arch index nil env
                                    (car tokens) (cdr tokens) fn-arena)))

(defthm pst-without-view-articles
  (let ((arch (pst-arch 3)) (index (pst-index 3)))
    (and ;; retained
         (fn-statep arch)
         (fn-gidx-pin-correspondencep index arch)
         (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles arch))
         (fn-cnx-freshp *pst-c*)
         (fn-scol-okp *pst-a* *pst-c*)
         ;; removed: served at view 2, which the pin does not name
         (not (equal (fn-state-articles arch) (fn-cat-view-articles 2 *pst-a* *pst-c*)))
         ;; the conclusion fails
         (not (equal (fn-ovw-expand
                      (fn-nntp-result-effects
                       (pst-cat-at *pst-env-x* "XPAT Subject 1-3 *" 2 arch index *pst-a* *pst-c*))
                      *pst-a* *pst-c*)
                     (fn-ovw-expand
                      (fn-nntp-result-effects
                       (pst-pinned-of *pst-env-x* "XPAT Subject 1-3 *" arch index *pst-a*))
                      *pst-a* *pst-c*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

(local (must-fail-checked
        (defthm fn-proto-archive-command-cat-is-pinned-without-view-articles
          (implies (and (fn-statep archive)
                        (fn-gidx-pin-correspondencep index archive)
                        (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                                 (fn-state-articles archive))
                        (fn-cnx-freshp fn-cat)
                        (fn-scol-okp fn-arena fn-cat))
                   (equal (fn-nntp-result-session
                           (fn-proto-archive-command-cat
                            session archive index verdicts env keyword args v fn-arena fn-cat))
                          (fn-nntp-result-session
                           (fn-nntp-archive-command-pinned
                            session archive index verdicts env keyword args fn-arena))))
          :hints (("Goal" :by fn-proto-archive-command-cat-is-pinned-by-rows)))))

;; trie-correspondence, logical: an index whose trie is the build of view 2
;; (no row for <c@x>) with the buckets of view 3; STAT <c@x> (an undeclared
;; row, served by the fallthrough's catalog arm) is found by the catalog and
;; not by the pin's trie.
(defthm pst-without-trie-correspondence
  (let ((arch (pst-arch 3))
        (index (fn-gidx-pin (fn-midx-build (fn-cat-view-articles 2 *pst-a* *pst-c*))
                            (fn-gidx-build (fn-cat-view-articles 3 *pst-a* *pst-c*)))))
    (and ;; retained
         (equal (fn-state-articles arch) (fn-cat-view-articles 3 *pst-a* *pst-c*))
         (fn-statep arch)
         (fn-gidx-pin-correspondencep index arch)
         (fn-cnx-freshp *pst-c*)
         (fn-scol-okp *pst-a* *pst-c*)
         ;; removed
         (not (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles arch)))
         ;; the conclusion fails
         (not (equal (fn-nntp-result-effects
                      (pst-cat-at *pst-env-x* "STAT <c@x>" 3 arch index *pst-a* *pst-c*))
                     (fn-nntp-result-effects
                      (pst-pinned-of *pst-env-x* "STAT <c@x>" arch index *pst-a*))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp fn-midx-correspondencep))))

;; statep, pin-correspondence, fresh, columns: :deferred.
(local (must-fail-checked
        (defthm fn-proto-archive-command-cat-is-pinned-without-pin-correspondence
          (implies (and (equal (fn-state-articles archive)
                               (fn-cat-view-articles v fn-arena fn-cat))
                        (fn-statep archive)
                        (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                                 (fn-state-articles archive))
                        (fn-cnx-freshp fn-cat)
                        (fn-scol-okp fn-arena fn-cat))
                   (equal (fn-ovw-expand
                           (fn-nntp-result-effects
                            (fn-proto-archive-command-cat
                             session archive index verdicts env keyword args v fn-arena fn-cat))
                           fn-arena fn-cat)
                          (fn-ovw-expand
                           (fn-nntp-result-effects
                            (fn-nntp-archive-command-pinned
                             session archive index verdicts env keyword args fn-arena))
                           fn-arena fn-cat)))
          :hints (("Goal" :by fn-proto-archive-command-cat-is-pinned-by-rows)))))

;; (3) Mutation (:conclusion): the sessions compared for the effects.  On
;; STAT 2 the catalog's reply moves the current article: the session is not
;; the effects.
(defthm pst-mutant-conclusion
  (let ((arch (pst-arch 3)) (index (pst-index 3)))
    (and (pst-agree *pst-env-x* "STAT 2" arch index *pst-a* *pst-c*)
         (not (equal (fn-nntp-result-session
                      (pst-cat-at *pst-env-x* "STAT 2" 3 arch index *pst-a* *pst-c*))
                     (fn-ovw-expand
                      (fn-nntp-result-effects
                       (pst-cat-at *pst-env-x* "STAT 2" 3 arch index *pst-a* *pst-c*))
                      *pst-a* *pst-c*)))))
  :rule-classes nil)

;; (4) The :view column's executable sites, on every served keyword.
(defun pst-advance-lines (names)
  (declare (xargs :verify-guards nil))
  (if (consp names)
      (cons (list :command (fn-nntp-string-octets (concatenate 'string (car names) " x")))
            (pst-advance-lines (cdr names)))
    nil))

(defun pst-advance-agree (events)
  (declare (xargs :verify-guards nil))
  (if (consp events)
      (and (equal (fn-proto-advance-eventp (car events))
                  (fn-served-advance-eventp (car events)))
           (pst-advance-agree (cdr events)))
    t))

(defun pst-archive-agree (names)
  (declare (xargs :verify-guards nil))
  (if (consp names)
      (and (equal (fn-proto-archive-keywordp (fn-nntp-string-octets (car names)))
                  (fn-nntp-archive-keywordp (fn-nntp-string-octets (car names))))
           (pst-archive-agree (cdr names)))
    t))

(defthm pst-view-sites-agree
  (and (pst-advance-agree (pst-advance-lines *fn-proto-served-names*))
       (fn-proto-advance-eventp (list :command (fn-nntp-string-octets "GROUP fn.test")))
       (fn-proto-advance-eventp (list :command (fn-nntp-string-octets "listgroup")))
       (not (fn-proto-advance-eventp (list :command (fn-nntp-string-octets "LIST"))))
       (not (fn-proto-advance-eventp (list :article (fn-nntp-string-octets "GROUP fn.test"))))
       (pst-archive-agree *fn-proto-served-names*)
       (equal (len *fn-proto-archive-names*) 16))
  :rule-classes nil)

;; Mutation: a table whose only :select row is GROUP disagrees with the
;; machine on a LISTGROUP line.
(defthm pst-mutant-select-rows
  (let ((event (list :command (fn-nntp-string-octets "LISTGROUP fn.test"))))
    (and (fn-served-advance-eventp event)
         (not (fn-proto-keyword-in-listp (fn-nntp-string-octets "LISTGROUP") '("GROUP")))))
  :rule-classes nil)

;; (5) Fail closed: the served columns' checks, on edits of the real table.
(defun pst-drop (key plist)
  (declare (xargs :verify-guards nil))
  (cond ((or (atom plist) (atom (cdr plist))) nil)
        ((equal (car plist) key) (cddr plist))
        (t (cons (car plist) (cons (cadr plist) (pst-drop key (cddr plist)))))))

(defun pst-edit (name key value rows)
  ; the row NAME with KEY set to VALUE (:drop removes it)
  (declare (xargs :verify-guards nil))
  (if (atom rows)
      nil
    (cons (if (and (consp (car rows)) (equal (car (car rows)) name) (true-listp (cdr (car rows))))
              (cons name (if (eq value :drop)
                             (pst-drop key (cdr (car rows)))
                           (list* key value (pst-drop key (cdr (car rows))))))
            (car rows))
          (pst-edit name key value (cdr rows)))))

(defthm pst-table-fails-closed
  (and (fn-proto-tablep *fn-proto-table*)
       (fn-proto-served-tablep *fn-proto-served-table* *fn-proto-table*)
       ;; a served command with no served row
       (not (fn-proto-served-tablep (cdr *fn-proto-served-table*) *fn-proto-table*))
       ;; a served row for a command no protocol row names
       (not (fn-proto-served-tablep (cons '("FROBNICATE" :view :none :effect :none :view-rfc "none")
                                          *fn-proto-served-table*)
                                    *fn-proto-table*))
       ;; a served row without a view
       (not (fn-proto-served-tablep (pst-edit "GROUP" :view :drop *fn-proto-served-table*) *fn-proto-table*))
       ;; forms without a cost
       (not (fn-proto-served-tablep (pst-edit "XPAT" :cost :drop *fn-proto-served-table*) *fn-proto-table*))
       ;; a pinned row whose arm reads the live view (the lint)
       (not (fn-proto-served-tablep
             (pst-edit "XPAT" :forms
                       '(("any" :test t :cat (fn-nntp-xpat-response-cat session args live fn-arena fn-cat)
                          :by (fn-nntp-xpat-response-cat-is-archive)))
                       *fn-proto-served-table*)
             *fn-proto-table*))
       ;; a ruling without its registry row
       (not (fn-proto-served-tablep (pst-edit "LIST" :view-decided :completed *fn-proto-served-table*)
                                    *fn-proto-table*))
       ;; two forms of one name
       (not (fn-proto-served-tablep
             (pst-edit "XPAT" :forms
                       '(("any" :test (null args) :cat (fn-nntp-single session "501 syntax error"))
                         ("any" :test t :cat (fn-nntp-xpat-response-cat session args v fn-arena fn-cat)))
                       *fn-proto-served-table*)
             *fn-proto-table*))
       ;; a form list whose last test is not t
       (not (fn-proto-served-tablep
             (pst-edit "XPAT" :forms
                       '(("any" :test (consp args) :cat (fn-nntp-xpat-response-cat session args v fn-arena fn-cat)))
                       *fn-proto-served-table*)
             *fn-proto-table*))
       ;; a row that no HELP line lists is refused by the served book's
       ;; assertion, not here: the set check reads two declarations
       (equal (len *fn-proto-served-names*) 31))
  :rule-classes nil)

;; (6) The generated dispatcher and the policy sites are guard-verified.
(assert-event
 (equal (list (symbol-class 'fn-proto-archive-command-cat (w state))
              (symbol-class 'fn-proto-advance-eventp (w state))
              (symbol-class 'fn-proto-archive-keywordp (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant)))
