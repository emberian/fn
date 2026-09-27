; Teeth for the served reader's compatibility arms (PRF-243, NNT-052;
; books/nntp-reader-compat.lisp, books/owner-agent.lisp `fn-oag-group-facts',
; books/config.lisp code 25).  Reachable witnesses through the pinned
; dispatcher with a server name; each keystone's hypotheses fail by name.
(in-package "ACL2")
(include-book "../../books/owner-xref-read")
(include-book "../../books/nntp-pinned-msgid")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-rct-payload (id subject)
  (append (fn-nntp-string-octets "Message-ID: ")
          (fn-nntp-string-octets id) '(13 10)
          (fn-nntp-string-octets "Subject: ")
          (fn-nntp-string-octets subject) '(13 10 13 10 88 13 10)))

(defconst *rct-groups* '("fn.one" "fn.two"))
; A: cross-posted to fn.one (2) and fn.two (7).
(defconst *rct-a*
  (fn-make-article "<rct-a@example.invalid>"
                   (fn-rct-payload "<rct-a@example.invalid>" "A")
                   '("fn.one" "fn.two")
                   (list (cons "fn.one" 2) (cons "fn.two" 7))
                   t 841000000))
(defconst *rct-articles* (list *rct-a*))
(defconst *rct-state*
  (fn-make-state *rct-groups* (list (cons "fn.one" 3) (cons "fn.two" 8))
                 *rct-articles* 1 nil nil))
(defconst *rct-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *rct-state*) "fn.two" 7))
(defconst *rct-pin*
  (fn-gidx-pin (fn-midx-build *rct-articles*) (fn-gidx-build *rct-articles*)))
(defconst *rct-server* (fn-nntp-string-octets "news.example.org"))
; Clock observations (DTN milliseconds): the facts' provenance and "now".
(defconst *rct-obs* (fn-clock-observation 5000 841000000000 1000 t))
; fn.one created at 840000000000, fn.gone at 840000500000 (not a group of
; the view: retired, or excluded by a restricted view), fn.two at
; 841100000000.
(defconst *rct-facts*
  (list (fn-nntp-group-fact "fn.one" 840000000000 *rct-obs*)
        (fn-nntp-group-fact "fn.gone" 840000500000 *rct-obs*)
        (fn-nntp-group-fact "fn.two" 841100000000 *rct-obs*)))
(defun fn-rct-env (subs)
  (fn-nntp-env-full *rct-obs* *rct-facts* nil
                    (list nil nil *rct-server* nil *rct-facts* subs) nil))
(defconst *rct-blind*
  (fn-nntp-env-full *rct-obs* *rct-facts* nil nil nil))

(defun fn-nntp-string-list-octets (xs)
  (if (consp xs)
      (cons (fn-nntp-string-octets (car xs))
            (fn-nntp-string-list-octets (cdr xs)))
    nil))

(defun fn-rct-cmd (env keyword args)
  (fn-nntp-archive-command-pinned
   *rct-session* *rct-state* *rct-pin* nil env
   (fn-nntp-string-octets keyword)
   (fn-nntp-string-list-octets args)))

(assert-event (and (fn-statep *rct-state*) (fn-nntp-sessionp *rct-session*)
                   (fn-gidx-pinp *rct-pin*)
                   (equal (fn-nntp-xref-server (fn-rct-env nil)) *rct-server*)
                   (null (fn-nntp-xref-server *rct-blind*))
                   (fn-nntp-group-fact-listp *rct-facts*)))

; -----------------------------------------------------------------------------
; PKT-665: NEWGROUPS and LIST ACTIVE.TIMES list the view's groups created
; since the date, and never fn.gone.

; 2026-08-26 00:00:00 is DTN 841017600000 ms: fn.two only.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "NEWGROUPS" '("20260826" "000000"))
        (fn-nntp-multi *rct-session* "231 list of new newsgroups follows"
                       (fn-nntp-active-lines *rct-state* '("fn.two")))))
; From 2000: both groups of the view, not fn.gone.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "NEWGROUPS" '("20000101" "000000" "GMT"))
        (fn-nntp-multi *rct-session* "231 list of new newsgroups follows"
                       (fn-nntp-active-lines *rct-state* '("fn.one" "fn.two")))))
; The generic (blind) reply names fn.gone: the held filter is what drops it.
(assert-event
 (equal (fn-nntp-newgroups-response *rct-session* *rct-state* *rct-blind*
                                    (fn-nntp-string-list-octets
                                     '("20000101" "000000")))
        (fn-nntp-multi *rct-session* "231 list of new newsgroups follows"
                       (fn-nntp-active-lines *rct-state*
                                             '("fn.one" "fn.gone" "fn.two")))))
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "LIST" '("ACTIVE.TIMES"))
        (fn-nntp-list-active-times
         *rct-session*
         (fn-nntp-env-full *rct-obs*
                           (list (car *rct-facts*) (caddr *rct-facts*))
                           nil (list nil nil *rct-server* nil *rct-facts* nil)
                           nil)
         nil)))

; fn-rcompat-newgroups-names-member, reachable: fn.two is listed for the
; 2026-08-26 threshold; fn.one (too early) and fn.gone (not held) are not.
(defconst *rct-threshold* 841017600000)
(assert-event
 (and (member-equal "fn.two" (fn-rcompat-newgroups-names
                              *rct-threshold* *rct-groups* *rct-facts*))
      (member-equal "fn.two" *rct-groups*)
      (fn-rcompat-created-since-p "fn.two" *rct-threshold* *rct-facts*)
      (not (member-equal "fn.one" (fn-rcompat-newgroups-names
                                   *rct-threshold* *rct-groups* *rct-facts*)))
      (not (fn-rcompat-created-since-p "fn.one" *rct-threshold* *rct-facts*))
      (not (member-equal "fn.gone" (fn-rcompat-newgroups-names
                                    0 *rct-groups* *rct-facts*)))
      (fn-rcompat-created-since-p "fn.gone" 0 *rct-facts*)
      (not (member-equal "fn.gone" *rct-groups*))))
; The keystone has no hypothesis (a first draft required a rational
; threshold; the weakened statement was proved, so it went).  Its two
; conjuncts fail separately above (fn.one: not created since; fn.gone: not
; held).

; -----------------------------------------------------------------------------
; PKT-666: LIST SUBSCRIPTIONS

; Nothing configured: the view's groups.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "LIST" '("SUBSCRIPTIONS"))
        (fn-nntp-multi *rct-session* "215 list of recommended newsgroups follows"
                       (list (fn-nntp-string-octets "fn.one")
                             (fn-nntp-string-octets "fn.two")))))
; Configured (fn.two, fn.gone, fn.one): in that order, fn.gone dropped.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env '("fn.two" "fn.gone" "fn.one")) "LIST"
                    '("SUBSCRIPTIONS"))
        (fn-nntp-multi *rct-session* "215 list of recommended newsgroups follows"
                       (list (fn-nntp-string-octets "fn.two")
                             (fn-nntp-string-octets "fn.one")))))
; With a wildmat (RFC 6048 section 2.6.3).
(assert-event
 (equal (fn-rct-cmd (fn-rct-env '("fn.two" "fn.one")) "LIST"
                    '("SUBSCRIPTIONS" "*.one"))
        (fn-nntp-multi *rct-session* "215 list of recommended newsgroups follows"
                       (list (fn-nntp-string-octets "fn.one")))))
; A blind environment keeps the unmaintained 503.
(assert-event
 (equal (fn-rct-cmd *rct-blind* "LIST" '("SUBSCRIPTIONS"))
        (fn-nntp-single *rct-session* "503 data item not stored")))
; fn-rcompat-subscription-names-keep-the-configured-order: its hypothesis.
(assert-event
 (and (not (consp nil))
      (not (equal (fn-rcompat-subscription-names nil *rct-groups*)
                  (fn-rcompat-names-held *rct-groups* nil)))))
(must-fail
 (thm (equal (fn-rcompat-subscription-names configured groups)
             (fn-rcompat-names-held groups configured))))

; -----------------------------------------------------------------------------
; PKT-667: the served OVERVIEW.FMT is the compatibility form.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "LIST" '("OVERVIEW.FMT"))
        (fn-nntp-multi-octets
         *rct-session*
         (fn-nntp-string-octets "215 order of fields in overview database")
         (fn-nov-fmt-octet-lines
          '("Subject:" "From:" "Date:" "Message-ID:" "References:" "Bytes:"
            "Lines:" "Xref:full")))))

; -----------------------------------------------------------------------------
; PKT-668: HEAD/ARTICLE carry this node's Xref; HDR/XHDR Xref return it.

(defconst *rct-xref* "Xref: news.example.org fn.one:2 fn.two:7")
(defconst *rct-served-payload*
  (append (fn-nntp-string-octets "Message-ID: <rct-a@example.invalid>")
          '(13 10) (fn-nntp-string-octets "Subject: A") '(13 10)
          (fn-nntp-string-octets *rct-xref*) '(13 10 13 10 88 13 10)))
(assert-event
 (equal (fn-rcompat-served-payload *rct-server* *rct-a*) *rct-served-payload*))
; HEAD 7 in fn.two: the stored header lines, then the Xref line.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "HEAD" '("7"))
        (fn-nntp-article-response
         *rct-session*
         (fn-make-article "<rct-a@example.invalid>" *rct-served-payload*
                          '("fn.one" "fn.two")
                          (list (cons "fn.one" 2) (cons "fn.two" 7))
                          t 841000000)
         7 :head t "fn.two")))
(assert-event
 (let ((reply (fn-rct-cmd (fn-rct-env nil) "ARTICLE"
                          '("<rct-a@example.invalid>"))))
   (equal (fn-nntp-result-effects reply)
          (list (fn-nntp-reply-effect
                 (append (fn-nntp-string-octets
                          "220 7 <rct-a@example.invalid> article follows")
                         '(13 10) *rct-served-payload*
                         '(46 13 10)))))))
; BODY is unchanged, and the blind environment serves the stored octets.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "BODY" '("7"))
        (fn-rct-cmd *rct-blind* "BODY" '("7"))))
(assert-event
 (equal (fn-rct-cmd *rct-blind* "HEAD" '("7"))
        (fn-nntp-article-response *rct-session* *rct-a* 7 :head t "fn.two")))
; XHDR Xref 1-10 and HDR Xref <msgid>: the field's value.
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "XHDR" '("Xref" "1-10"))
        (fn-nntp-multi *rct-session* "221 header follows"
                       (list (fn-nntp-string-octets
                              "7 news.example.org fn.one:2 fn.two:7")))))
(assert-event
 (equal (fn-rct-cmd (fn-rct-env nil) "HDR" '("XREF" "<rct-a@example.invalid>"))
        (fn-nntp-multi *rct-session* "225 headers follow"
                       (list (fn-nntp-string-octets
                              "0 news.example.org fn.one:2 fn.two:7")))))

; fn-rcompat-served-payload-inserts-one-line, reachable in its first branch.
(assert-event
 (let ((split (fn-nntp-split-article (fn-article-payload *rct-a*))))
   (and (consp (fn-xref-pairs *rct-a*))
        (not (fn-rcl-tombstonep (fn-article-payload *rct-a*)))
        (fn-nntp-split-okp split)
        (equal (fn-rcompat-served-payload *rct-server* *rct-a*)
               (append (fn-nntp-split-head split)
                       (fn-xref-field *rct-server* (fn-xref-pairs *rct-a*))
                       (list 13 10) (list 13 10)
                       (fn-nntp-split-body split))))))
; Its second branch: an article numbered nowhere is served as stored.
(defconst *rct-unnumbered*
  (fn-make-article "<rct-u@example.invalid>"
                   (fn-rct-payload "<rct-u@example.invalid>" "U") nil nil t 0))
(assert-event
 (and (not (consp (fn-xref-pairs *rct-unnumbered*)))
      (equal (fn-rcompat-served-payload *rct-server* *rct-unnumbered*)
             (fn-article-payload *rct-unnumbered*))))

; The session of a served retrieval is the generic one (cursor to 7 in
; fn.two), and the hypothesis on the argument list is needed: with two
; arguments the generic retrieval answers 501, the served one reads the
; first.
(assert-event
 (equal (fn-nntp-result-session
         (fn-rcompat-retrieval *rct-session* *rct-state*
                               (fn-gidx-pin-trie *rct-pin*) :head
                               (fn-nntp-string-list-octets '("2")) *rct-server*))
        (fn-nntp-result-session
         (fn-nntp-retrieval *rct-session* *rct-state* :head
                            (fn-nntp-string-list-octets '("2"))))))
(defconst *rct-no-cursor*
  (fn-nntp-set-cursor (fn-nntp-open-session *rct-state*) "fn.two" nil))
(assert-event
 (not (equal (fn-nntp-result-session
              (fn-rcompat-retrieval *rct-no-cursor* *rct-state*
                                    (fn-gidx-pin-trie *rct-pin*) :head
                                    (fn-nntp-string-list-octets '("7" "x"))
                                    *rct-server*))
             (fn-nntp-result-session
              (fn-nntp-retrieval *rct-no-cursor* *rct-state* :head
                                 (fn-nntp-string-list-octets '("7" "x")))))))
(must-fail
 (thm (equal (fn-nntp-result-session
              (fn-rcompat-retrieval session archive trie kind args server))
             (fn-nntp-result-session
              (fn-nntp-retrieval session archive kind args)))))

; The owner's projection (PKT-665): a live entry whose stamp has a wall
; reading yields its fact; the zero stamp of an old `init' yields none.
(defconst *rct-stamp* (fn-clock-observation 5 841000000 1 t))
(assert-event
 (equal (fn-oag-group-facts
         (list (fn-cfg-group-make "fn.one" 1 *rct-stamp* nil
                                  *fn-cfg-default-policy-id* 0)
               (fn-cfg-group-make "fn.old" 1 *fn-cfg-default-stamp* nil
                                  *fn-cfg-default-policy-id* 0)
               (fn-cfg-group-make "fn.retired" 1 *rct-stamp* 2
                                  *fn-cfg-default-policy-id* 0))
         2)
        (list (fn-nntp-group-fact "fn.one" 841000000000
                                  (fn-clock-observation 5000 841000000000
                                                        1000 t)))))
; The configured list (code 25): admitted for live groups named once.
(defconst *rct-cfg-v*
  (fn-cfg-apply (fn-cfg-empty-value) 1 *rct-stamp*
                (list (fn-cfg-create-group "fn.one" *fn-cfg-default-policy-id*)
                      (fn-cfg-create-group "fn.two" *fn-cfg-default-policy-id*))))
(assert-event
 (and (null (fn-cfg-set-default-subscriptions-reason
             *rct-cfg-v* 1 (fn-cfg-set-default-subscriptions '("fn.two" "fn.one"))))
      (equal (fn-cfg-set-default-subscriptions-reason
              *rct-cfg-v* 1 (fn-cfg-set-default-subscriptions '("fn.two" "fn.two")))
             :subscription-row)
      (equal (fn-cfg-set-default-subscriptions-reason
              *rct-cfg-v* 1 (fn-cfg-set-default-subscriptions '("fn.none")))
             :subscription-row)
      (equal (fn-cfg-default-subscriptions
              (fn-cfg-apply-delta *rct-cfg-v* 2 *rct-stamp*
                                  (fn-cfg-set-default-subscriptions
                                   '("fn.two" "fn.one"))))
             '("fn.two" "fn.one"))
      (equal (fn-cfg-kind-code :set-default-subscriptions) 25)
      (equal (fn-cfg-code-kind 25) :set-default-subscriptions)))
