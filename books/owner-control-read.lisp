;; Packet C3 (control-c3e, PRF-084): the served withdrawal answers stated
;; over the function the host calls.
;;
;; Host path (reader), as for HDR :fn-verified (books/owner-verdict-read):
;; host/native/owner.lisp calls fn-owner-chunk (host/owner-host.lisp), which
;; runs fn-ocfg-read-tls-prefix, equal to fn-ocfg-read by
;; fn-ocfg-read-tls-prefix-is-full-read (books/owner-tls-prefix), which is
;; fn-own-read on the connection.  fn-own-read builds the served connection
;; from the owner connection -- its archive, its index, its buckets and its
;; control pin (`fn-own-conn-control', set from `fn-own-view-control' at
;; open and advance) -- and runs the byte fold fn-served-step, which hands
;; each framed event to fn-served-dispatch and so to the pinned dispatcher
;; fn-nntp-archive-command-pinned (books/nntp.lisp).
;;
;; `fn-own-read-archive-command-is-the-pinned-dispatcher' says that for one
;; read framing exactly one archive command line, the reply is the pinned
;; dispatcher's over the connection's pinned archive and its group pin with
;; the connection's control pin in the fourth slot, whenever that reply
;; offers no article.  The three keystones below instantiate it with the
;; arms of books/nntp-control.lisp; `fn-own-conn-okp' (books/owner-
;; invariants.lisp, carried by fn-own-relation) gives every connection's
;; control pin the meaning those arms need (`fn-own-related-conn-control').
;;
;; Framing is a hypothesis here, as in owner-verdict-read.
(in-package "ACL2")
(include-book "owner-verdict-read")
(include-book "nntp-control")
(include-book "owner-invariants")

;; The pinned dispatcher's reply to one command line, over connection CONN.
(defun fn-octl-reply (conn line)
  (declare (xargs :verify-guards nil))
  (let* ((ns (fn-post-session-base
              (fn-peer-session-base
               (fn-auth-session-base (fn-served-conn-session conn)))))
         (tokens (fn-nntp-tokenize line)))
    (fn-nntp-archive-command-pinned
     ns (fn-served-conn-archive conn) (fn-served-conn-pinned-index conn)
     (fn-served-conn-verdicts conn)
     (fn-nntp-env (fn-served-conn-observation conn) nil
                  (and (fn-inj-config-allow (fn-served-conn-config conn)) t))
     (car tokens) (cdr tokens))))

(defthm fn-octl-reply-of-with-wire
  (equal (fn-octl-reply (fn-ovr-with-wire conn w) line)
         (fn-octl-reply conn line)))

(defmacro fn-octl-reader-hyps (as tokens line)
  `(let* ((ps (fn-auth-session-base ,as))
          (pst (fn-peer-session-base ps))
          (ns (fn-post-session-base pst)))
     (and (fn-auth-sessionp ,as)
          (not (fn-auth-session-handshakingp ,as))
          (not (fn-auth-gatedp ,as (car ,tokens)))
          (fn-peer-sessionp ps)
          (null (fn-peer-session-peer ps))
          (fn-post-sessionp pst)
          (not (fn-post-session-awaiting pst))
          (fn-nntp-sessionp ns)
          (equal (fn-nntp-session-openp ns) t)
          (fn-nntp-session-projected ns)
          (fn-nntp-command-inputp ,line)
          (fn-nntp-command-arguments-at-mostp ,tokens)
          (consp ,tokens)
          (fn-nntp-keyword-tokenp (car ,tokens))
          (fn-nntp-archive-keywordp (car ,tokens)))))

;; The pinned dispatcher's effects are a true list on every arm (the served
;; chain appends the submission effect after them).  Proved per response
;; function, with each callee closed.
(local
 (defthm fn-octl-result-effects-of-cons
   (equal (fn-nntp-result-effects (cons session effects)) effects)
   :hints (("Goal" :in-theory (enable fn-nntp-result-effects)))))

(local
 (defthm fn-octl-article-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-article-response session article number kind updatep group)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-article-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-msgid-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-msgid-retrieval session archive kind token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-msgid-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-number-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-number-retrieval session archive kind token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-number-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-current-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-current-retrieval session archive kind)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-current-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-retrieval session archive kind args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-current-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-current session archive field legacyp)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-current fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-range session archive field token legacyp)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-msgid-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-msgid session archive field token legacyp)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-msgid fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-command session archive args legacyp)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-response session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-active-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-active session archive groups)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-active fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-newsgroups-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-newsgroups session groups)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-newsgroups fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-filtered-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-filtered-response session archive kind wildmat)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-filtered-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-active-or-newsgroups-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-active-or-newsgroups session archive kind args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-active-or-newsgroups fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-overview-fmt-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-overview-fmt session)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-overview-fmt fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-headers-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-headers session)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-headers fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-unmaintained-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-unmaintained-response session keyword args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-unmaintained-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-response session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-active-times-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-active-times session env args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-active-times fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-counts-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-counts session archive groups)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-counts fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-counts-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-counts-command session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-counts-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-command session archive env args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-listgroup-result-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-listgroup-result session archive group range)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-listgroup-result fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-listgroup-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-listgroup-command session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-listgroup-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-next-or-last-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-next-or-last session archive direction)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-next-or-last fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-current-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-current session archive)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-current fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-range session archive token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-msgid-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-msgid session archive token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-msgid fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-response session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xhdr-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xhdr-response session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xhdr-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xover-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xover-range session archive token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xover-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xover-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xover-response session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xover-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xpat-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xpat-range session archive field patterns token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xpat-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xpat-msgid-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xpat-msgid session archive field patterns token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xpat-msgid fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xpat-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xpat-response session archive args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xpat-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-gidx-list-counts-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-gidx-list-counts-command session archive buckets args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-gidx-list-counts-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-withdrawn-reply-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-withdrawn-reply session msgidp)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-withdrawn-reply fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-verdict-hdr-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-verdict-hdr-response session archive verdicts args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-verdict-hdr-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-range-indexed-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-range-indexed session buckets trie token legacyp)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-range-indexed fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-gidx-listgroup-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-gidx-listgroup-command session archive buckets args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-gidx-listgroup-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-msgid-retrieval-indexed-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-msgid-retrieval-indexed session archive index kind token)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-msgid-retrieval-indexed fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-newgroups-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-newgroups-response session archive env args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-newgroups-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-newnews-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-newnews-response session archive env args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-newnews-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-group-result-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-group-result session archive group)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-group-result fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-archive-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-archive-command session archive env keyword args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-archive-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-control-hdr-response-effects-true-listp
   (true-listp (fn-nntp-result-effects
                (fn-nntp-control-hdr-response session archive index verdicts args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-control-hdr-response fn-nntp-single
                                    fn-nntp-multi fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-nntp-control-cleanp
                                    fn-ctl-served-held fn-ctl-control-item
                                    fn-ctl-served-status fn-nntp-hdr-line
                                    fn-nntp-string-octets fn-nntp-hdr-initial
                                    fn-nntp-stuff-lines fn-nntp-crlf
                                    fn-ctl-target-octets fn-nntp-decimal-field))))))

(defthm fn-octl-archive-command-pinned-effects-true-listp
  (true-listp (fn-nntp-result-effects
               (fn-nntp-archive-command-pinned session archive index verdicts
                                               env keyword args)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-nntp-archive-command-pinned)
                                  (fn-nntp-result-effects fn-nntp-archive-command
                                   fn-nntp-withdrawn-reply fn-gidx-list-counts-command
                                   fn-nntp-msgid-retrieval-indexed fn-gidx-listgroup-command
                                   fn-nntp-over-range-indexed fn-nntp-verdict-hdr-response
                                   fn-nntp-control-hdr-response fn-nntp-keywordp
                                   fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p)))))

;; One framed archive command line through the pinned chain: the dispatch's
;; effects are the pinned dispatcher's reply, and the wire is kept, when the
;; reply offers no article.
(defthm fn-octl-dispatch-archive-command
  (let ((tokens (fn-nntp-tokenize line)))
    (implies (and (fn-octl-reader-hyps (fn-served-conn-session conn) tokens line)
                  (not (fn-post-offeredp
                        (fn-nntp-result-effects (fn-octl-reply conn line)))))
             (and (equal (fn-served-result-effects
                          (fn-served-dispatch conn (list :command line)))
                         (fn-nntp-result-effects (fn-octl-reply conn line)))
                  (equal (fn-served-conn-wire
                          (fn-served-result-conn
                           (fn-served-dispatch conn (list :command line))))
                         (fn-served-conn-wire conn)))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-auth-step-pinned
                                   fn-auth-command fn-auth-delegate-pinned
                                   fn-peer-step-pinned fn-peer-delegate-pinned
                                   fn-nntp-post-step-pinned fn-nntp-step-pinned
                                   fn-nntp-command-pinned
                                   fn-auth-tls-eventp fn-nntp-keywordp
                                   fn-nntp-archive-keywordp)
                                  (fn-nntp-archive-command-pinned fn-nntp-upcase-keyword
                                   fn-served-conn-pinned-index
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp
                                   fn-nntp-keyword-tokenp fn-nntp-command-inputp
                                   fn-nntp-command-arguments-at-mostp)))))

;; The served step: one read framing that one line answers the reply.
(defthm fn-octl-served-step-archive-command
  (let* ((w0 (fn-served-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (tokens (fn-nntp-tokenize line)))
    (implies (and (fn-served-conn-shapep conn)
                  (fn-wire-statep w0)
                  (not (equal (fn-wire-state-mode w0) :closed))
                  (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
                  (equal (fn-wire-result-events (fn-wire-feed-byte w1 byte))
                         (list (list :command line)))
                  (not (equal (fn-wire-state-mode w2) :closed))
                  (fn-octl-reader-hyps (fn-served-conn-session conn) tokens line)
                  (not (fn-post-offeredp
                        (fn-nntp-result-effects (fn-octl-reply conn line)))))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-nntp-result-effects (fn-octl-reply conn line)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-of-one-framed-event
                  (event (list :command line)))
                 (:instance fn-octl-dispatch-archive-command
                  (conn (fn-ovr-with-wire
                         conn
                         (fn-wire-result-state
                          (fn-wire-feed-byte
                           (fn-wire-result-state
                            (fn-wire-feed-proper (fn-served-conn-wire conn) prefix))
                           byte))))))
           :in-theory (e/d (fn-served-closed-wirep fn-served-tls-handshakingp)
                           (fn-served-step-of-one-framed-event
                            fn-octl-dispatch-archive-command fn-octl-reply
                            fn-served-step fn-served-dispatch
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-tokenize fn-auth-gatedp
                            fn-nntp-archive-keywordp
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp)))))

;; The served connection fn-own-read builds for connection CONN of O.
(defun fn-octl-served-conn (o conn)
  (declare (xargs :verify-guards nil))
  (fn-served-make-conn-group-indexed
   (fn-own-conn-wire conn) (fn-own-conn-live-session o conn)
   (fn-own-conn-archive conn) (fn-own-conn-config conn)
   (fn-own-conn-observation conn) (fn-own-clock o)
   (fn-own-conn-verdicts conn) (fn-own-conn-index conn)
   (fn-own-conn-group-index conn) (fn-own-conn-control conn)))

;; KEYSTONE (the host-called read).  One read of connection ID framing one
;; archive command line answers the pinned dispatcher's reply over that
;; connection's pinned archive, index, buckets and control pin.
(defthm fn-own-read-archive-command-is-the-pinned-dispatcher
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (tokens (fn-nntp-tokenize line))
         (reply (fn-octl-reply (fn-octl-served-conn o conn) line)))
    (implies (and conn
                  (fn-wire-statep w0)
                  (not (equal (fn-wire-state-mode w0) :closed))
                  (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
                  (equal (fn-wire-result-events (fn-wire-feed-byte w1 byte))
                         (list (list :command line)))
                  (not (equal (fn-wire-state-mode w2) :closed))
                  (fn-octl-reader-hyps (fn-own-conn-live-session o conn) tokens line)
                  (not (fn-post-offeredp (fn-nntp-result-effects reply))))
             (equal (car (fn-own-read o id (append prefix (list byte))))
                    (fn-nntp-result-effects reply))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-octl-served-step-archive-command
                  (conn (fn-octl-served-conn o (fn-own-find-conn id (fn-own-conns o))))))
           :in-theory (e/d (fn-own-read fn-own-finish-read)
                           (fn-octl-served-step-archive-command fn-octl-reply
                            fn-served-step fn-own-conn-live-session
                            fn-own-conn-wire fn-own-conn-archive fn-own-conn-config
                            fn-own-conn-observation fn-own-conn-verdicts
                            fn-own-conn-index fn-own-conn-group-index
                            fn-own-conn-control
                            fn-own-conn-session fn-own-find-conn
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-tokenize fn-auth-gatedp
                            fn-nntp-archive-keywordp
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-own-conn-boundedp fn-own-set-conns fn-own-enqueue
                            fn-own-replace-conn fn-own-remove-conn)))))

;; The pinned index of that served connection carries the owner connection's
;; control pin whenever the connection has buckets.
(defthm fn-octl-pinned-index-of-served-conn
  (implies (fn-own-conn-group-index conn)
           (and (equal (fn-gidx-pin-control
                        (fn-served-conn-pinned-index (fn-octl-served-conn o conn)))
                       (fn-own-conn-control conn))
                (equal (fn-gidx-pin-trie
                        (fn-served-conn-pinned-index (fn-octl-served-conn o conn)))
                       (fn-own-conn-index conn))))
  :hints (("Goal" :in-theory (enable fn-served-conn-pinned-index))))

;; What the relation says of a connection's control pin: its W is the
;; withdrawn list of the connection's pinned prefix, whose visible list the
;; connection serves.
(defthm fn-own-related-conn-control
  (let* ((s (fn-own-store o))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (raw (fn-state-articles
               (fn-own-prefix-archive (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-sf-records (fn-sn-files s))
                                      (fn-own-conn-version conn)
                                      (fn-own-conn-frontier conn))))
         (control (fn-own-conn-control conn))
         (ws (fn-ctl-pin-ws control)))
    (implies (and (fn-own-relation o) conn control)
             (and (equal (fn-state-articles (fn-own-conn-archive conn))
                         (fn-ctl-visible-articles raw ws (fn-own-conn-verdicts conn)))
                  (equal (fn-ctl-pin-withdrawn control)
                         (fn-ctl-withdrawn-articles raw ws (fn-own-conn-verdicts conn)))
                  (fn-midx-correspondencep (fn-own-conn-index conn)
                                           (fn-state-articles
                                            (fn-own-conn-archive conn))))))
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-own-control-okp fn-own-conn-okp)
                                  (fn-own-prefix-archive fn-ctl-visible-articles
                                   fn-ctl-withdrawn-articles fn-ctl-subseq-diff
                                   fn-own-conn-boundedp fn-own-view-okp fn-own-conn-control
                                   fn-midx-correspondencep))
           :use ((:instance fn-own-find-conn-okp
                            (conns (fn-own-conns o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o)))))))))
