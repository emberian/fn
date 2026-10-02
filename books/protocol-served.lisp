; protocol-served.lisp -- the served (catalog) dispatcher GENERATED from the
; protocol table's served columns, each FORM's view contract as a generated
; theorem, the pinned-boundary theorem as the generated case split over the
; rows, and the view policy's executable sites pinned to the :view column
; (lane def-command, 2026-10-03; consultation c07's shape).
;
; books/served-catalog-dispatch.lisp hand-writes fn-nntp-archive-command-cat,
; one cond over every command's arms, and proves it equal to the pinned
; reference fn-nntp-archive-command-pinned by one theorem whose hints name
; every arm (fn-nntp-archive-command-cat-is-pinned).  books/served.lisp
; hand-writes which keywords move the pin (fn-served-advance-eventp) and
; books/nntp.lisp which read the archive (fn-nntp-archive-keywordp);
; books/nntp-help.lisp hand-keeps the table HELP prints.  Each of those is
; one column of books/protocol-table.lisp now, and this book is where the
; column meets the code:
;
;   fn-proto-archive-command-cat    one flat cond, a clause per row with :forms
;                                   in table order (the forms' arms in order),
;                                   falling through to the hand dispatcher for
;                                   a row not yet declared (the fallthrough
;                                   goes at the switch, with the hand cond);
;   fn-proto-cat-row-NAME-is-cat    per row: under that keyword the generated
;                                   dispatcher IS the hand one (the row's text
;                                   says what the dispatcher does; local);
;   fn-proto-form-NAME-FORM-is-pinned  per FORM: the form's view CONTRACT
;                                   (today every declared form is :pinned,
;                                   :select or :none): under the keystone's
;                                   hypotheses, the form's test and NO EARLIER
;                                   form's (first match), the result equals
;                                   the pinned reference's; proved from the
;                                   form's :by with the hand keystone CLOSED
;                                   (local);
;   fn-proto-cat-row-NAME-is-pinned per row: the forms' cases (local);
;   fn-proto-archive-command-cat-is-pinned  KEYSTONE: the generated dispatcher
;                                   is the pinned reference (the case split);
;                                   ONE context today -- the first form that
;                                   reads a second context (a :completed or
;                                   :pin-or-completed form, PRF-1237/1238)
;                                   REPLACES this statement by the two-context
;                                   refinement (c07 C4/G5); the single-context
;                                   specialization keeps a separate name then;
;   fn-proto-advance-eventp-is-served-advance-eventp   the :view :select rows
;                                   are exactly the keywords the served machine
;                                   re-pins on;
;   fn-proto-archive-keywordp-is-nntp-archive-keywordp the :dispatch :archive
;                                   rows are exactly the archive keywords;
;   (assert-event ...)              HELP's table is set-equal to the served
;                                   names: a drift check (fail closed), not the
;                                   closure proof; the closure is PRF-194's
;                                   theorem (books/nntp-help.lisp) and the
;                                   reachability teeth on both routes
;                                   (tests/acl2/protocol-served-tests.lisp).
; Each keystone is followed by its fn-teeth-owed row (the teeth contract v1,
; build/coordinator/lanedumps/generators-2.md): what the teeth must say.

(in-package "ACL2")
(include-book "served-catalog-dispatch")
(include-book "served")       ; fn-served-advance-eventp
(include-book "nntp-help")    ; *fn-nntp-served-command-table*
(include-book "protocol-table")

(local (in-theory (disable (tau-system))))

;; The served dispatcher's formals, in order (the hand one's).
(defconst *fn-proto-cat-formals*
  '(session archive index verdicts env keyword args v fn-arena fn-cat))

;; The boundary theorem's labelled hypotheses (fn-nntp-archive-command-cat-is-
;; pinned's), the teeth contract's :claim shape.
(defconst *fn-proto-cat-claim-hyps*
  '((view-articles (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat)))
    (statep (fn-statep archive))
    (pin-correspondence (fn-gidx-pin-correspondencep index archive))
    (trie-correspondence (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                                  (fn-state-articles archive)))
    (fresh (fn-cnx-freshp fn-cat))
    (columns (fn-scol-okp fn-arena fn-cat))))

(defun fn-proto-hyp-terms (labelled)
  (declare (xargs :guard t))
  (if (consp labelled)
      (cons (if (consp (car labelled)) (cadr (car labelled)) nil)
            (fn-proto-hyp-terms (cdr labelled)))
    nil))

(defconst *fn-proto-cat-hyps* (fn-proto-hyp-terms *fn-proto-cat-claim-hyps*))

;; The keystone's conclusion over the dispatcher CAT (a function name).
(defun fn-proto-cat-conclusion (cat)
  (declare (xargs :guard t))
  `(and (equal (fn-nntp-result-session (,cat ,@*fn-proto-cat-formals*))
               (fn-nntp-result-session
                (fn-nntp-archive-command-pinned
                 session archive index verdicts env keyword args fn-arena)))
        (equal (fn-ovw-expand (fn-nntp-result-effects (,cat ,@*fn-proto-cat-formals*))
                              fn-arena fn-cat)
               (fn-ovw-expand (fn-nntp-result-effects
                               (fn-nntp-archive-command-pinned
                                session archive index verdicts env keyword args fn-arena))
                              fn-arena fn-cat))))

; -----------------------------------------------------------------------------
; The generated dispatcher

(make-event
 `(defun fn-proto-archive-command-cat ,*fn-proto-cat-formals*
    (declare (xargs :stobjs (fn-arena fn-cat)
                    :guard (and (natp v)
                                (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                    :verify-guards nil))
    (cond
     ,@(fn-proto-cat-flat-clauses *fn-proto-table*)
     (t (fn-nntp-archive-command-cat ,@*fn-proto-cat-formals*)))))

; -----------------------------------------------------------------------------
; Keyword exclusivity (books/protocol-dispatch.lisp's, restated locally), the
; two preludes vanish outside their rows, and books/served-catalog-dispatch.
; lisp's local lemmas restated: the pin's buckets and trie are the builds
; under the correspondences, and a state's articles are an article list of
; its groups.

(local
 (defthm fn-proto-served-keywordp-exclusive
   (implies (and (fn-nntp-keywordp keyword a)
                 (syntaxp (quotep b))
                 (not (equal (fn-nntp-string-octets a) (fn-nntp-string-octets b))))
            (not (fn-nntp-keywordp keyword b)))
   :hints (("Goal" :in-theory (enable fn-nntp-keywordp)))))

(local
 (defthm fn-proto-xref-reply-cat-only-for-its-commands
   (implies (and (not (fn-nntp-keywordp keyword "OVER"))
                 (not (fn-nntp-keywordp keyword "XOVER"))
                 (not (fn-nntp-keywordp keyword "LIST")))
            (not (fn-nntp-xref-reply-cat session archive index env keyword args v fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-xref-reply-cat)
                                   (fn-nntp-keywordp fn-nntp-xref-server fn-gidx-pinp
                                    fn-nntp-parse-range fn-nntp-range-okp fn-nntp-keyword-tokenp
                                    fn-nntp-message-id-tokenp
                                    fn-nntp-over-range-served-cat fn-nntp-over-current-served-cat
                                    fn-nntp-over-msgid-served-cat fn-nntp-list-overview-fmt-served))))))

(local
 (defthm fn-proto-rcompat-reply-cat-only-for-its-commands
   (implies (and (not (fn-nntp-keywordp keyword "NEWGROUPS"))
                 (not (fn-nntp-keywordp keyword "LIST"))
                 (not (fn-nntp-keywordp keyword "ARTICLE"))
                 (not (fn-nntp-keywordp keyword "HEAD"))
                 (not (fn-nntp-keywordp keyword "HDR"))
                 (not (fn-nntp-keywordp keyword "XHDR")))
            (not (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-rcompat-reply-cat)
                                   (fn-nntp-keywordp fn-nntp-xref-server fn-gidx-pinp
                                    fn-rcompat-retrieval-cat fn-rcompat-hdr-cat
                                    fn-rcompat-retrieval-kind fn-gidx-pin-trie fn-rcompat-reply))))))

(local
 (defthm fn-proto-pin-buckets-are-built
   (implies (and (fn-gidx-pin-correspondencep index archive) (fn-gidx-pinp index))
            (equal (fn-gidx-pin-buckets index)
                   (fn-gidx-build (fn-state-articles archive))))
   :hints (("Goal" :in-theory (enable fn-gidx-pin-correspondencep)))))

(local
 (defthm fn-proto-pin-trie-is-built
   (implies (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive))
            (equal (fn-gidx-pin-trie index)
                   (fn-midx-build (fn-state-articles archive))))
   :hints (("Goal" :in-theory (enable fn-midx-correspondencep)))))

(local
 (defthm fn-proto-built-trie-corresponds
   (fn-midx-correspondencep (fn-midx-build articles) articles)
   :hints (("Goal" :in-theory (enable fn-midx-correspondencep)))))

(local
 (defthm fn-proto-statep-article-listp
   (implies (fn-statep archive)
            (fn-article-listp (fn-state-groups archive) (fn-state-articles archive)))
   :hints (("Goal" :in-theory (enable fn-statep)))))

;; Closed in every generated proof: the token recognizers (an arm for another
;; command falls away by exclusivity, never by computing) and every arm, on
;; both sides (the hand keystone's list, books/served-catalog-dispatch.lisp).
(defconst *fn-proto-cat-closed*
  '(fn-nntp-keywordp fn-nntp-keyword-tokenp fn-nntp-upcase-keyword
    fn-nntp-parse-range fn-nntp-range-okp fn-nntp-xref-server fn-gidx-pinp
    fn-rcompat-list-keywordp fn-nntp-message-id-tokenp fn-nntp-number-tokenp
    fn-nntp-printable-tokenp fn-nntp-token-string fn-gidx-pin-buckets fn-gidx-pin-trie
    fn-rcompat-reply fn-nntp-xref-reply fn-gidx-list-counts-command
    fn-rcompat-reply-cat fn-nntp-number-withdrawn-p-cat
    fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p
    fn-nntp-withdrawn-reply fn-gidx-listgroup-command
    fn-nntp-over-range-indexed fn-nntp-verdict-hdr-response
    fn-nntp-verdict-hdr-response-cat
    fn-nntp-control-hdr-response fn-nntp-enrollment-hdr-response
    fn-nntp-msgid-retrieval-cat fn-nntp-number-retrieval-cat
    fn-nntp-msgid-retrieval-indexed fn-nntp-msgid-retrieval fn-nntp-number-retrieval
    fn-cat-view-articles fn-midx-correspondencep fn-gidx-pin-correspondencep
    fn-nntp-list-counts-command-cat fn-nntp-list-counts-command
    fn-nntp-listgroup-command-cat fn-nntp-listgroup-command
    fn-nntp-over-range-cat fn-nntp-over-range fn-nntp-xover-range
    fn-nntp-group-result-cat fn-nntp-group-result
    fn-nntp-hdr-command-cat fn-nntp-hdr-command
    fn-nntp-xpat-response-cat fn-nntp-xpat-response
    fn-nntp-current-retrieval fn-nntp-over-current fn-nntp-over-msgid
    fn-nntp-list-response fn-nntp-list-active-times
    fn-nntp-list-newsgroups-described fn-nntp-list-motd fn-nntp-list-command
    fn-nntp-single fn-gidx-build fn-midx-build fn-statep
    fn-nntp-xref-reply-cat fn-nntp-msgid-withdrawn-p-cat
    fn-nntp-control-hdr-response-cat fn-nntp-enrollment-hdr-response-cat
    fn-nntp-over-range-ovw fn-ovw-expand fn-ovw-start fn-ovw-cursor-effect
    fn-nntp-multi fn-nntp-multi-octets fn-nntp-reply-effect fn-nntp-make-result
    fn-nntp-list-active-cat fn-nntp-next-or-last-cat
    fn-nntp-current-retrieval-cat fn-nntp-next-or-last fn-scat-list-active-formp
    fn-nntp-retrieval fn-nntp-hdr-response fn-nntp-xhdr-response
    fn-nntp-over-response fn-nntp-xover-response fn-nntp-newgroups-response
    fn-nntp-newnews-response fn-scol-okp fn-cnx-freshp
    ;; the cursor arm's spec form (fn-ovw-over-range-cat-is-spec) would
    ;; rewrite a form's :by instance away from the walk it names
    fn-ovw-over-range-cat-is-spec))

; -----------------------------------------------------------------------------
; Names

(defun fn-proto-dash-name (name)
  ; a form name as a theorem-name part: upper case, spaces to dashes
  (declare (xargs :guard (stringp name)))
  (string-upcase (substitute #\- #\Space name)))

(defun fn-proto-cat-thm-name (name suffix)
  (declare (xargs :guard (and (stringp name) (stringp suffix))))
  (intern-in-package-of-symbol
   (concatenate 'string "FN-PROTO-CAT-ROW-" (fn-proto-dash-name name) suffix)
   'fn-proto-archive-command-cat))

(defun fn-proto-form-thm-name (row form)
  (declare (xargs :guard (and (stringp row) (stringp form))))
  (intern-in-package-of-symbol
   (concatenate 'string "FN-PROTO-FORM-" (fn-proto-dash-name row) "-"
                (fn-proto-dash-name form) "-IS-PINNED")
   'fn-proto-archive-command-cat))

(defun fn-proto-cat-thm-names (names suffix)
  (declare (xargs :guard (stringp suffix) :verify-guards nil))
  (if (consp names)
      (cons (fn-proto-cat-thm-name (car names) suffix)
            (fn-proto-cat-thm-names (cdr names) suffix))
    nil))

; -----------------------------------------------------------------------------
; Per row: the generated dispatcher is the hand one under the row's keyword.

(defun fn-proto-cat-row-is-cat-events (names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons `(local
              (defthm ,(fn-proto-cat-thm-name (car names) "-IS-CAT")
                (implies (fn-nntp-keywordp keyword ,(car names))
                         (equal (fn-proto-archive-command-cat ,@*fn-proto-cat-formals*)
                                (fn-nntp-archive-command-cat ,@*fn-proto-cat-formals*)))
                :hints (("Goal" :do-not-induct t
                         :in-theory (e/d (fn-proto-archive-command-cat fn-nntp-archive-command-cat)
                                         ,*fn-proto-cat-closed*)))))
            (fn-proto-cat-row-is-cat-events (cdr names)))
    nil))

(make-event (cons 'progn (fn-proto-cat-row-is-cat-events *fn-proto-cat-rows*)))

; -----------------------------------------------------------------------------
; Per FORM: its view contract, from its :by.  The form applies when its test
; holds and no earlier form's does (first match: the premises below), so a
; form's test may overlap a later form's.  The hand keystone and the row's
; -is-cat lemma stay closed: the case is proved from the declaration, as it
; will be once the hand dispatcher is gone.

(defun fn-proto-form-test (form)
  (declare (xargs :guard t))
  (and (consp form) (true-listp (cdr form)) (fn-proto-plist-get :test (cdr form))))

(defun fn-proto-form-get (key form)
  (declare (xargs :guard t))
  (and (consp form) (true-listp (cdr form)) (fn-proto-plist-get key (cdr form))))

(defun fn-proto-negate-all (tests)
  (declare (xargs :guard t))
  (if (consp tests)
      (cons `(not ,(car tests)) (fn-proto-negate-all (cdr tests)))
    nil))

;; The condition under which FORM (after the forms whose tests are PRIOR)
;; answers: no earlier test, then its own.
(defun fn-proto-form-condition (prior form)
  (declare (xargs :guard t))
  `(and ,@(fn-proto-negate-all prior) ,(fn-proto-form-test form)))

(defun fn-proto-form-events (row forms prior)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp forms)
      (let ((form (car forms)))
        (cons `(local
                (defthm ,(fn-proto-form-thm-name row (car form))
                  (implies (and ,@*fn-proto-cat-hyps*
                                (fn-nntp-keywordp keyword ,row)
                                ,(fn-proto-form-condition prior form))
                           ,(fn-proto-cat-conclusion 'fn-proto-archive-command-cat))
                  :hints (("Goal" :do-not-induct t
                           :in-theory (e/d (fn-proto-archive-command-cat
                                            fn-nntp-archive-command-pinned fn-nntp-archive-command
                                            ,@(fn-proto-form-get :open form))
                                           ,(append
                                             (list 'fn-nntp-archive-command-cat-is-pinned
                                                   (fn-proto-cat-thm-name row "-IS-CAT"))
                                             (set-difference-equal
                                              *fn-proto-cat-closed*
                                              (fn-proto-form-get :open form))))
                           :use ,(fn-proto-form-get :by form)))))
              (fn-proto-form-events row (cdr forms)
                                    (append prior (list (fn-proto-form-test form))))))
    nil))

;; The forms' conditions, a partition of the row's argument shapes (the last
;; test is t), for the row's case split.
(defun fn-proto-form-conditions (forms prior)
  (declare (xargs :guard t))
  (if (consp forms)
      (cons (fn-proto-form-condition prior (car forms))
            (fn-proto-form-conditions (cdr forms)
                                      (append prior (list (fn-proto-form-test (car forms))))))
    nil))

(defun fn-proto-form-thm-names (row forms)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp forms)
      (cons (fn-proto-form-thm-name row (car (car forms)))
            (fn-proto-form-thm-names row (cdr forms)))
    nil))

; Per row: the forms' cases.
(defun fn-proto-cat-row-is-pinned-events (names rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (let ((forms (fn-proto-row-forms (fn-proto-row (car names) rows))))
        (append
         (fn-proto-form-events (car names) forms nil)
         (cons `(local
                 (defthm ,(fn-proto-cat-thm-name (car names) "-IS-PINNED")
                   (implies (and ,@*fn-proto-cat-hyps*
                                 (fn-nntp-keywordp keyword ,(car names)))
                            ,(fn-proto-cat-conclusion 'fn-proto-archive-command-cat))
                   :hints (("Goal" :do-not-induct t
                            :cases ,(fn-proto-form-conditions forms nil)
                            :in-theory (union-theories
                                        ',(fn-proto-form-thm-names (car names) forms)
                                        (theory 'minimal-theory))))))
               (fn-proto-cat-row-is-pinned-events (cdr names) rows))))
    nil))

(make-event (cons 'progn (fn-proto-cat-row-is-pinned-events *fn-proto-cat-rows* *fn-proto-table*)))

; -----------------------------------------------------------------------------
; The case split: a declared row by its generated case, an undeclared one by
; the fallthrough (the hand dispatcher under its keystone, until the switch).

(defun fn-proto-cat-not-any (names term)
  (declare (xargs :guard t))
  (if (consp names)
      (cons `(not (fn-nntp-keywordp ,term ,(car names)))
            (fn-proto-cat-not-any (cdr names) term))
    nil))

(defun fn-proto-cat-cases (names term)
  (declare (xargs :guard t))
  (if (consp names)
      (cons `(fn-nntp-keywordp ,term ,(car names))
            (fn-proto-cat-cases (cdr names) term))
    nil))

(make-event
 `(local
   (defthm fn-proto-cat-row-none-is-cat
     (implies (and ,@(fn-proto-cat-not-any *fn-proto-cat-rows* 'keyword))
              (equal (fn-proto-archive-command-cat ,@*fn-proto-cat-formals*)
                     (fn-nntp-archive-command-cat ,@*fn-proto-cat-formals*)))
     :hints (("Goal" :in-theory (union-theories '(fn-proto-archive-command-cat)
                                                (theory 'minimal-theory)))))))

(make-event
 `(local
   (defthm fn-proto-archive-command-cat-is-pinned-by-rows
     (implies (and ,@*fn-proto-cat-hyps*)
              ,(fn-proto-cat-conclusion 'fn-proto-archive-command-cat))
     :hints (("Goal" :do-not-induct t
              :cases ,(fn-proto-cat-cases *fn-proto-cat-rows* 'keyword)
              :in-theory (union-theories
                          '(fn-proto-cat-row-none-is-cat fn-nntp-archive-command-cat-is-pinned
                            ,@(fn-proto-cat-thm-names *fn-proto-cat-rows* "-IS-PINNED"))
                          (theory 'minimal-theory)))))))

; KEYSTONE.  The dispatcher generated from the table's served columns is the
; pinned reference: the results' sessions are equal and their effects are
; equal once expanded (fn-ovw-expand; the OVER/XOVER range arm answers a
; cursor), under the hand keystone's hypotheses.  The subject is
; fn-nntp-archive-command-cat's role (host/owner-host.lisp fn-owner-chunk-span
; -> books/served-catalog-chain.lisp fn-scr-command), which this dispatcher
; takes at the switch.  One context: see the header.
(defthm fn-proto-archive-command-cat-is-pinned
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-statep archive)
                (fn-gidx-pin-correspondencep index archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-cnx-freshp fn-cat)
                (fn-scol-okp fn-arena fn-cat))
           (and (equal (fn-nntp-result-session
                        (fn-proto-archive-command-cat
                         session archive index verdicts env keyword args v fn-arena fn-cat))
                       (fn-nntp-result-session
                        (fn-nntp-archive-command-pinned
                         session archive index verdicts env keyword args fn-arena)))
                (equal (fn-ovw-expand
                        (fn-nntp-result-effects
                         (fn-proto-archive-command-cat
                          session archive index verdicts env keyword args v fn-arena fn-cat))
                        fn-arena fn-cat)
                       (fn-ovw-expand
                        (fn-nntp-result-effects
                         (fn-nntp-archive-command-pinned
                          session archive index verdicts env keyword args fn-arena))
                        fn-arena fn-cat))))
  :hints (("Goal" :by fn-proto-archive-command-cat-is-pinned-by-rows)))

(make-event
 `(table fn-teeth-owed 'fn-proto-archive-command-cat-is-pinned
         '(:by defprotocol
           :claim (,*fn-proto-cat-claim-hyps*
                   ,(fn-proto-cat-conclusion 'fn-proto-archive-command-cat))
           :subject fn-nntp-archive-command-cat)))

; Guards: every arm is guard-verified in books/served-catalog.lisp.
(verify-guards fn-proto-archive-command-cat
  :hints (("Goal" :in-theory (enable (tau-system)))))

; -----------------------------------------------------------------------------
; The :view column's executable sites.

;; A keyword in a list of command names (books/nntp-help.lisp's
;; fn-nntp-keyword-in-rowp over one row).
(defun fn-proto-keyword-in-listp (keyword names)
  (declare (xargs :guard t))
  (fn-nntp-keyword-in-rowp keyword names))

;; The event fn-served-dispatch re-pins on: a framed command line whose
;; keyword is a :view :select row's.
(defun fn-proto-advance-eventp (event)
  (declare (xargs :guard t))
  (and (consp event)
       (equal (car event) :command)
       (consp (cdr event))
       (null (cdr (cdr event)))
       (fn-nntp-command-inputp (car (cdr event)))
       (let ((tokens (fn-nntp-tokenize (car (cdr event)))))
         (and (consp tokens)
              (fn-nntp-keyword-tokenp (car tokens))
              (fn-proto-keyword-in-listp (car tokens) *fn-proto-select-names*)))))

; KEYSTONE.  The :view :select rows are exactly the keywords the served
; machine re-pins on (books/served.lisp fn-served-advance-eventp, the one
; executable site of NNT-042's view policy).  A row declared :select that the
; machine does not re-pin on, or a re-pin the table does not declare, refuses
; this theorem.
(defthm fn-proto-advance-eventp-is-served-advance-eventp
  (equal (fn-proto-advance-eventp event)
         (fn-served-advance-eventp event))
  :hints (("Goal" :in-theory (e/d (fn-proto-advance-eventp fn-served-advance-eventp
                                   fn-proto-keyword-in-listp fn-nntp-keyword-in-rowp)
                                  (fn-nntp-keywordp fn-nntp-keyword-tokenp
                                   fn-nntp-command-inputp fn-nntp-tokenize)))))

(table fn-teeth-owed 'fn-proto-advance-eventp-is-served-advance-eventp
       '(:by defprotocol
         :claim (() (equal (fn-proto-advance-eventp event) (fn-served-advance-eventp event)))
         :subject fn-served-advance-eventp))

;; The keywords that read the archive: the :dispatch :archive rows.
(defun fn-proto-archive-keywordp (keyword)
  (declare (xargs :guard t))
  (fn-proto-keyword-in-listp keyword *fn-proto-archive-names*))

; KEYSTONE.  The :dispatch :archive rows are exactly books/nntp.lisp's
; archive keywords (fn-nntp-archive-keywordp, the split between the session
; and archive dispatchers).
(defthm fn-proto-archive-keywordp-is-nntp-archive-keywordp
  (equal (fn-proto-archive-keywordp keyword)
         (fn-nntp-archive-keywordp keyword))
  :hints (("Goal" :in-theory (e/d (fn-proto-archive-keywordp fn-nntp-archive-keywordp
                                   fn-proto-keyword-in-listp fn-nntp-keyword-in-rowp)
                                  (fn-nntp-keywordp)))))

(table fn-teeth-owed 'fn-proto-archive-keywordp-is-nntp-archive-keywordp
       '(:by defprotocol
         :claim (() (equal (fn-proto-archive-keywordp keyword) (fn-nntp-archive-keywordp keyword)))
         :subject fn-nntp-archive-keywordp))

; -----------------------------------------------------------------------------
; HELP's table is the table's served names: a keyword the served step answers
; with no row, or a row HELP does not list, refuses certification.  A DRIFT
; check between two declarations; the closure itself is PRF-194's theorem
; (an unlisted keyword is answered 500) and the reachability teeth.

(defun fn-proto-flatten-rows (table)
  (declare (xargs :guard t))
  (if (consp table)
      (append (if (true-listp (car table)) (car table) nil)
              (fn-proto-flatten-rows (cdr table)))
    nil))

(assert-event
 (and (subsetp-equal (fn-proto-flatten-rows *fn-nntp-served-command-table*)
                     *fn-proto-served-names*)
      (subsetp-equal *fn-proto-served-names*
                     (fn-proto-flatten-rows *fn-nntp-served-command-table*)))
 :msg "HELP's served command table and the protocol table's served rows differ")
