; NEWNEWS from the durable article stamp, through the served dispatcher.
(in-package "ACL2")
(include-book "nntp-legacy")

(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary
                          fn-nov-vocabulary)))

; The article parser is deliberately absent from this book and from the scan.
(defthm fn-nntp-newnews-candidate-is-projectable
  (implies (fn-nntp-newnews-candidatep groups article)
           (fn-nntp-article-idp article))
  :rule-classes
  ((:rewrite)
   (:forward-chaining
    :trigger-terms ((fn-nntp-newnews-candidatep groups article))))
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

(defthm fn-nntp-newnews-lines-are-clean
  (fn-nov-clean-line-listp
   (fn-nntp-newnews-scan groups threshold articles horizon))
  :hints (("Goal"
           :induct (fn-nntp-newnews-scan groups threshold articles horizon)
           :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-idp
                               fn-nntp-string-octets fn-article-msgid))))

; Independent, quadratic specification.  NEWER is the prefix accepted after
; the article being tested; unlike the served scan, this walks that prefix
; again to find its nearest usable stamp.
(defun fn-nntp-newnews-prefix-horizon (newer horizon)
  (declare (xargs :guard t))
  (if (consp newer)
      (fn-nntp-newnews-prefix-horizon
       (cdr newer)
       (let ((stamp (fn-article-stamp (car newer))))
         (if (natp stamp) stamp horizon)))
    horizon))

(defthm fn-nntp-newnews-prefix-horizon-append-one
  (equal (fn-nntp-newnews-prefix-horizon
          (append newer (list article)) horizon)
         (let ((stamp (fn-article-stamp article)))
           (if (natp stamp) stamp
             (fn-nntp-newnews-prefix-horizon newer horizon))))
  :hints (("Goal" :induct (fn-nntp-newnews-prefix-horizon newer horizon))))

(defun fn-nntp-newnews-accepted-since
    (groups threshold articles newer horizon)
  (declare (xargs :guard (true-listp newer)
                  :measure (acl2-count articles)))
  (if (consp articles)
      (let* ((article (car articles))
             (current (fn-nntp-newnews-prefix-horizon newer horizon))
             (rest (fn-nntp-newnews-accepted-since
                    groups threshold (cdr articles)
                    (append newer (list article)) horizon)))
        (if (and (fn-nntp-newnews-candidatep groups article)
                 (fn-nntp-newnews-newp
                  threshold (fn-article-stamp article) current))
            (cons (fn-nntp-string-octets (fn-article-msgid article)) rest)
          rest))
    nil))

(local
 (defthm fn-nntp-newnews-scan-is-filter-with-prefix
   (equal (fn-nntp-newnews-scan
           groups threshold articles
           (fn-nntp-newnews-prefix-horizon newer horizon))
          (fn-nntp-newnews-accepted-since
           groups threshold articles newer horizon))
   :hints (("Goal"
            :induct (fn-nntp-newnews-accepted-since
                     groups threshold articles newer horizon)
            :in-theory (disable fn-nntp-newnews-candidatep
                                fn-nntp-newnews-newp
                                fn-nntp-string-octets fn-article-msgid)))))

(defthm fn-nntp-newnews-scan-is-the-acceptance-filter
  (equal (fn-nntp-newnews-scan groups threshold articles horizon)
         (fn-nntp-newnews-accepted-since
          groups threshold articles nil horizon))
  :hints (("Goal" :use ((:instance fn-nntp-newnews-scan-is-filter-with-prefix
                                  (newer nil)))
           :in-theory (disable fn-nntp-newnews-scan-is-filter-with-prefix
                               fn-nntp-newnews-accepted-since
                               fn-nntp-newnews-scan))))

; Erase only payload octets; all identifiers, memberships and stamps persist.
(defun fn-nntp-newnews-without-payload (articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (let ((a (car articles)))
        (cons (fn-make-article
               (fn-article-msgid a) nil (fn-article-groups a)
               (fn-article-memberships a) (fn-article-pin a)
               (fn-article-stamp a))
              (fn-nntp-newnews-without-payload (cdr articles))))
    nil))

(defthm fn-nntp-newnews-scan-reads-no-payload
  (equal (fn-nntp-newnews-scan
          groups threshold (fn-nntp-newnews-without-payload articles)
          horizon)
         (fn-nntp-newnews-scan groups threshold articles horizon))
  :hints (("Goal" :induct (fn-nntp-newnews-scan
                           groups threshold articles horizon)
           :in-theory (disable fn-nntp-newnews-candidatep
                               fn-nntp-newnews-newp fn-nntp-string-octets))))

(defun fn-nntp-newnews-candidate-count (groups articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (+ (if (fn-nntp-newnews-candidatep groups (car articles)) 1 0)
         (fn-nntp-newnews-candidate-count groups (cdr articles)))
    0))

(defthm fn-nntp-newnews-scan-lines-at-most-candidates
  (<= (len (fn-nntp-newnews-scan groups threshold articles horizon))
      (fn-nntp-newnews-candidate-count groups articles))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-nntp-newnews-scan
                           groups threshold articles horizon)
           :in-theory (disable fn-nntp-newnews-candidatep
                               fn-nntp-newnews-newp fn-nntp-string-octets))))

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

(verify-guards fn-nntp-newnews-prefix-horizon)
(verify-guards fn-nntp-newnews-accepted-since)
(verify-guards fn-nntp-newnews-without-payload)
(verify-guards fn-nntp-newnews-candidate-count)

(deftheory fn-nntp-newnews-vocabulary
  '(fn-nntp-newnews-prefix-horizon
    fn-nntp-newnews-accepted-since
    fn-nntp-newnews-without-payload
    fn-nntp-newnews-candidate-count))

(in-theory (disable fn-nntp-newnews-vocabulary))
