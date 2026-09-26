; fn: HELP lists the served command table (PRF-194, NNT-038).
;
; RFC 3977 section 7.2: HELP is "a short summary of the commands that are
; understood by this implementation".  The implementation a client meets is
; the served dispatcher, and the host calls it through
;
;   host/native/owner.lisp fnn-owner-serve-client (the socket read)
;     -> fn-own-read (books/owner.lisp) -> fn-served-step (books/served.lisp)
;       -> fn-served-feed -> fn-served-dispatch -> fn-auth-step-pinned
;
; so the subject here is fn-auth-step-pinned, the function
; fn-served-dispatch calls for every framed command line.  Until 2026-09-26
; HELP listed only books/nntp.lisp's reader verbs and omitted AUTHINFO,
; STARTTLS and XREDEEM, which the authentication layer above it serves, and
; IHAVE, CHECK and TAKETHIS, which the peer layer serves (the NNTP gap
; inventory's R4).
;
; WHAT IS PROVED.
;
;   fn-nntp-help-renders-the-served-command-table-by-definition: HELP's
;     reply is the multi-line block whose lines are the rows of
;     *fn-nntp-served-command-table*, each row's
;     keywords joined by one space.
;
;   KEYSTONE fn-auth-step-pinned-answers-500-to-a-keyword-help-does-not-list:
;     on a served session in command mode (not handshaking TLS, no transit
;     article or POST body awaited, the reader session open), a well-formed
;     command line whose keyword is not in the table is answered exactly
;     "500 command not recognized" (RFC 3977 section 3.2.1), submits
;     nothing, and leaves the session as it was.  So every keyword the
;     served step does anything with is one HELP lists.
;
; NOT PROVED (PKT-571).  The converse -- every listed keyword draws some
; reply other than 500 for EVERY argument list and session -- would need a
; fact about every reply builder.  tests/acl2/nntp-help-tests.lisp checks it
; by evaluation, on a served session, for each of the 28 keywords.

(in-package "ACL2")
(include-book "nntp-auth")

; The served command table: every keyword the served dispatcher
; (fn-auth-step-pinned, books/nntp-auth.lisp, which books/served.lisp
; fn-served-dispatch calls) recognizes, one row per HELP line.  The layers
; answer them: CAPABILITIES, POST, AUTHINFO, XREDEEM and STARTTLS the
; authentication layer; IHAVE, CHECK, TAKETHIS and MODE STREAM the peer
; layer on a peer connection (a reader connection answers the three transit
; verbs 502, RFC 3977 section 3.2.1, which is "understood" and not 500); the
; rest books/nntp.lisp's two dispatchers.  PRF-194 (below):
; a keyword outside this table is answered 500 by the served step, and
; HELP's lines are this table's rows.
(defconst *fn-nntp-served-command-table*
  '(("CAPABILITIES" "HELP" "QUIT" "MODE" "DATE" "POST")
    ("AUTHINFO" "STARTTLS" "XREDEEM")
    ("GROUP" "LISTGROUP" "LIST" "NEXT" "LAST" "NEWGROUPS" "NEWNEWS")
    ("ARTICLE" "HEAD" "BODY" "STAT")
    ("OVER" "XOVER" "HDR" "XHDR" "XPAT")
    ("IHAVE" "CHECK" "TAKETHIS")))

(defun fn-nntp-keyword-in-rowp (keyword row)
  (declare (xargs :guard t))
  (if (consp row)
      (or (and (stringp (car row)) (fn-nntp-keywordp keyword (car row)))
          (fn-nntp-keyword-in-rowp keyword (cdr row)))
    nil))

(defun fn-nntp-keyword-in-tablep (keyword table)
  (declare (xargs :guard t))
  (if (consp table)
      (or (fn-nntp-keyword-in-rowp keyword (car table))
          (fn-nntp-keyword-in-tablep keyword (cdr table)))
    nil))

(defun fn-nntp-served-keywordp (keyword)
  (declare (xargs :guard t))
  (fn-nntp-keyword-in-tablep keyword *fn-nntp-served-command-table*))

; One HELP line from one row: the keywords' octets, one space between each
; two.
(defun fn-nntp-help-row-octets (row)
  (declare (xargs :guard t))
  (if (consp row)
      (append (fn-nntp-string-octets (car row))
              (if (consp (cdr row))
                  (cons 32 (fn-nntp-help-row-octets (cdr row)))
                nil))
    nil))

(defun fn-nntp-help-table-lines (table)
  (declare (xargs :guard t))
  (if (consp table)
      (cons (fn-nntp-help-row-octets (car table))
            (fn-nntp-help-table-lines (cdr table)))
    nil))

(defthm fn-nntp-help-renders-the-served-command-table-by-definition
  (equal (fn-nntp-help session)
         (fn-nntp-multi session "100 help text follows"
                        (fn-nntp-help-table-lines
                         *fn-nntp-served-command-table*)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-help) (fn-nntp-multi)))))

; The table, written out as the disjunction of keyword tests the dispatchers
; themselves make, so the keystone's proof reads each arm off its branch.
(defthm fn-nntp-served-keywordp-unfolds
  (equal (fn-nntp-served-keywordp k)
         (or (fn-nntp-keywordp k "CAPABILITIES") (fn-nntp-keywordp k "HELP")
             (fn-nntp-keywordp k "QUIT") (fn-nntp-keywordp k "MODE")
             (fn-nntp-keywordp k "DATE") (fn-nntp-keywordp k "POST")
             (fn-nntp-keywordp k "AUTHINFO") (fn-nntp-keywordp k "STARTTLS")
             (fn-nntp-keywordp k "XREDEEM")
             (fn-nntp-keywordp k "GROUP") (fn-nntp-keywordp k "LISTGROUP")
             (fn-nntp-keywordp k "LIST") (fn-nntp-keywordp k "NEXT")
             (fn-nntp-keywordp k "LAST") (fn-nntp-keywordp k "NEWGROUPS")
             (fn-nntp-keywordp k "NEWNEWS")
             (fn-nntp-keywordp k "ARTICLE") (fn-nntp-keywordp k "HEAD")
             (fn-nntp-keywordp k "BODY") (fn-nntp-keywordp k "STAT")
             (fn-nntp-keywordp k "OVER") (fn-nntp-keywordp k "XOVER")
             (fn-nntp-keywordp k "HDR") (fn-nntp-keywordp k "XHDR")
             (fn-nntp-keywordp k "XPAT")
             (fn-nntp-keywordp k "IHAVE") (fn-nntp-keywordp k "CHECK")
             (fn-nntp-keywordp k "TAKETHIS")))
  :hints (("Goal" :in-theory (e/d (fn-nntp-served-keywordp
                                   fn-nntp-keyword-in-tablep
                                   fn-nntp-keyword-in-rowp)
                                  (fn-nntp-keywordp)))))

(in-theory (disable fn-nntp-served-keywordp))

; -----------------------------------------------------------------------------
; The keystone
;
; Reconstruction facts: a session layer rebuilt from its own base is that
; layer, which is what "the session is the one the command arrived on" needs
; at each of the three wrappers the unlisted keyword passes through.  They
; are disabled after the keystone; the teeth enable them by name.

(defthm fn-help-inj-nth-is-nth
  (equal (fn-inj-nth k xs) (nth k xs))
  :hints (("Goal" :in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr))))

(defthm fn-help-six-list-rebuild
  (implies (and (true-listp x) (equal (len x) 6))
           (equal (list (car x) (cadr x) (caddr x) (cadddr x)
                        (car (cddddr x)) (cadr (cddddr x)))
                  x))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x))
                           (len (cdddr x)) (len (cddddr x))
                           (len (cdr (cddddr x))) (len (cddr (cddddr x)))
                           (true-listp (cddr (cddddr x)))))))

(defthm fn-help-nth-of-a-constant
  (implies (and (syntaxp (quotep n)) (posp n))
           (equal (nth n x) (nth (- n 1) (cdr x))))
  :hints (("Goal" :in-theory (enable))))

(defthm fn-help-nth-0
  (equal (nth 0 x) (car x))
  :hints (("Goal" :in-theory (enable))))

(defthm fn-help-rebuild-post
  (implies (and (fn-post-session-shapep x) (not (fn-post-session-awaiting x)))
           (equal (fn-post-make-session (fn-post-session-base x) nil) x))
  :hints (("Goal" :in-theory (enable fn-post-session-shapep fn-post-session-base
                                     fn-post-session-awaiting fn-post-make-session
                                     fn-inj-nth fn-inj-car fn-inj-cdr)
           :expand ((len x) (len (cdr x)) (len (cddr x))))))

(defthm fn-help-rebuild-peer
  (implies (fn-peer-session-shapep ps)
           (equal (fn-peer-with-base ps (fn-peer-session-base ps)) ps))
  :hints (("Goal" :in-theory (enable fn-peer-session-shapep fn-peer-session-base
                                     fn-peer-session-peer fn-peer-session-transfer
                                     fn-peer-session-inflight fn-peer-session-node
                                     fn-peer-session-cfg fn-peer-with-base
                                     fn-peer-make-session
                                     fn-inj-nth fn-inj-car fn-inj-cdr)
           :expand ((len (cdr (cddddr ps))) (len (cddr (cddddr ps)))))))

(defthm fn-help-rebuild-auth
  (implies (fn-auth-session-shapep as)
           (equal (fn-auth-with-base as (fn-auth-session-base as)) as))
  :hints (("Goal" :in-theory (enable fn-auth-session-shapep fn-auth-session-base
                                     fn-auth-session-config fn-auth-session-pending
                                     fn-auth-session-subject fn-auth-session-tlsp
                                     fn-auth-session-handshakingp fn-auth-with-base
                                     fn-auth-make-session
                                     fn-inj-nth fn-inj-car fn-inj-cdr)
           :expand ((len (cdr (cddddr as))) (len (cddr (cddddr as)))))))

; KEYSTONE (PRF-194).  A keyword HELP does not list is not served: the
; served step answers it exactly RFC 3977 section 3.2.1's "500 command not
; recognized", submits nothing and changes nothing.  Each hypothesis is a
; mode the step can be in and each is needed (tests/acl2/nntp-help-tests
; .lisp): a handshaking connection serves nothing; a transit article or a
; POST body awaited takes the line as article data; a closed reader session
; answers nothing; a line that is not a command line, not a keyword, or
; with too many arguments is 501.  The unauthenticated gate needs no
; hypothesis: it refuses only restricted keywords, all of which are listed.
(defthm fn-auth-step-pinned-answers-500-to-a-keyword-help-does-not-list
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line)))))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp))
           :use ((:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as)))))))

; The reconstruction facts are general rewrites; they leave the theory here.
(in-theory (disable fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth))
