;; Packet C3 (control-c3e, PRF-084): the served withdrawal answers stated
;; over the function the host calls.
;;
;; Host path (reader), as for HDR :fn-verified (books/owner-verdict-read):
;; host/native/owner.lisp calls fn-owner-chunk-span-at (host/owner-host.lisp),
;; which runs fn-ocfg-read-tls-prefix over the span (fn-scr-ocfg-read-span-is-reference-under-ocl-relation), equal to fn-ocfg-read over the octets it
;; consumed (all of them unless a submission made it yield) by
;; fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix (books/owner-tls-prefix), which is
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

;; The pinned dispatcher's reply to one command line, over connection CONN,
;; under the posting configuration the delegate serves it: the connection's
;; moderation view (books/nntp-auth.lisp `fn-auth-moderation-config', P3,
;; PRF-228; the connection's own configuration when its login moderates
;; nothing).
(defun fn-octl-reply (conn line fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((ns (fn-post-session-base
              (fn-peer-session-base
               (fn-auth-session-base (fn-served-conn-session conn)))))
         (tokens (fn-nntp-tokenize line)))
    (fn-nntp-archive-command-pinned
     ns (fn-served-conn-archive conn) (fn-served-conn-pinned-index conn)
     (fn-served-conn-verdicts conn)
     (fn-post-reader-env (fn-auth-moderation-config (fn-served-conn-session conn)
                                                    (fn-served-conn-config conn))
                         (fn-served-conn-observation conn))
     (car tokens) (cdr tokens) fn-arena)))

(defthm fn-octl-reply-of-with-wire
  (equal (fn-octl-reply (fn-ovr-with-wire conn w) line fn-arena)
         (fn-octl-reply conn line fn-arena)))

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
   (true-listp (fn-nntp-result-effects (fn-nntp-article-response session article number kind updatep group fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-article-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-msgid-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-msgid-retrieval session archive kind token fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-msgid-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-number-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-number-retrieval session archive kind token fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-number-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-current-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-current-retrieval session archive kind fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-current-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-retrieval session archive kind args fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-retrieval fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-current-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-current session archive field legacyp fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-current fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-range session archive field token legacyp fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-msgid-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-msgid session archive field token legacyp fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-msgid fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-command session archive args legacyp fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-hdr-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-hdr-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-hdr-response session archive args fn-arena)))
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
 (defthm fn-octl-single-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-single session text)))
   :hints (("Goal" :in-theory (enable fn-nntp-single fn-nntp-make-result
                                      fn-nntp-result-effects)))))

(local
 (defthm fn-octl-multi-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-multi session initial lines)))
   :hints (("Goal" :in-theory (enable fn-nntp-multi fn-nntp-make-result
                                      fn-nntp-result-effects)))))

(local
 (defthm fn-octl-multi-octets-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-multi-octets session initial lines)))
   :hints (("Goal" :in-theory (enable fn-nntp-multi-octets fn-nntp-make-result
                                      fn-nntp-result-effects)))))

(local
 (defthm fn-octl-list-active-times-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-active-times session env args)))
   ; The wildmat decoder is opened on the argument and never contributes:
   ; 288k prover steps with it, 32k without (owner-books-split).
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-active-times fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-wildmat-decode-aux
                                    fn-wildmat-utf8-next))))))

(local
 (defthm fn-octl-list-counts-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-counts session archive groups closed)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-counts fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-counts-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-counts-command session archive closed args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-counts-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-list-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-command session archive env args)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-command
                                    fn-nntp-list-newsgroups-described fn-nntp-list-motd
                                    fn-nntp-list-status-response
                                    fn-nntp-list-active-status)
                                   (fn-nntp-result-effects fn-nntp-single
                                    fn-nntp-multi fn-nntp-multi-octets))))))

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
   (true-listp (fn-nntp-result-effects (fn-nntp-next-or-last session archive direction fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-next-or-last fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-current-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-current session archive fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-current fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-range session archive token fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-msgid-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-msgid session archive token fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-msgid fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-over-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-response session archive args fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xhdr-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xhdr-response session archive args fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xhdr-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xover-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xover-range session archive token fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xover-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xover-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xover-response session archive args fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xover-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xpat-range-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xpat-range session archive field patterns token fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xpat-range fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xpat-msgid-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xpat-msgid session archive field patterns token fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xpat-msgid fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-xpat-response-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-xpat-response session archive args fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-xpat-response fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-gidx-list-counts-command-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-gidx-list-counts-command session archive buckets closed args)))
   ; As above: 414k prover steps with the wildmat decoder, 44k without.
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-gidx-list-counts-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-wildmat-decode-aux
                                    fn-wildmat-utf8-next))))))

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
   (true-listp (fn-nntp-result-effects (fn-nntp-over-range-indexed session buckets trie token legacyp fn-arena)))
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
   (true-listp (fn-nntp-result-effects (fn-nntp-msgid-retrieval-indexed session archive index kind token fn-arena)))
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
   (true-listp (fn-nntp-result-effects (fn-nntp-newnews-response session archive env args fn-arena)))
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
   (true-listp (fn-nntp-result-effects (fn-nntp-archive-command session archive env keyword args fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-archive-command fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects))))))

(local
 (defthm fn-octl-control-hdr-response-effects-true-listp
   (true-listp (fn-nntp-result-effects
                (fn-nntp-control-hdr-response session archive index verdicts args fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-control-hdr-response fn-nntp-single
                                    fn-nntp-multi fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-nntp-control-cleanp
                                    fn-ctl-served-held fn-ctl-control-item
                                    fn-ctl-served-status fn-nntp-hdr-line
                                    fn-nntp-string-octets fn-nntp-hdr-initial
                                    fn-nntp-stuff-lines fn-nntp-crlf
                                    fn-ctl-target-octets fn-nntp-decimal-field))))))

(local
 (defthm fn-octl-nntp-over-range-served-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-range-served session buckets trie token legacyp server fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-range-served fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-nov-served-line
                                    fn-nov-served-lines-numbered fn-nov-overview))))))

(local
 (defthm fn-octl-nntp-over-current-served-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-current-served session archive server fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-current-served fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-nov-served-line
                                    fn-nov-served-lines-numbered fn-nov-overview))))))

(local
 (defthm fn-octl-nntp-over-msgid-served-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-over-msgid-served session archive token server fn-arena)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-over-msgid-served fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-nov-served-line
                                    fn-nov-served-lines-numbered fn-nov-overview))))))

(local
 (defthm fn-octl-nntp-list-overview-fmt-served-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-overview-fmt-served session)))
   :hints (("Goal" :do-not-induct t
                   :in-theory (e/d (fn-nntp-list-overview-fmt-served fn-nntp-single fn-nntp-multi
                                    fn-nntp-multi-octets fn-nntp-make-result)
                                   (fn-nntp-result-effects fn-nov-served-line
                                    fn-nov-served-lines-numbered fn-nov-overview))))))

(local
 (defthm fn-octl-xref-reply-effects-true-listp
   (true-listp (fn-nntp-result-effects
                (fn-nntp-xref-reply session archive index env keyword args fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-xref-reply)
                                   (fn-nntp-result-effects fn-nntp-keywordp
                                    fn-nntp-xref-server
                                    fn-nntp-over-range-served fn-nntp-over-current-served
                                    fn-nntp-over-msgid-served
                                    fn-nntp-list-overview-fmt-served))))))

(defthm fn-octl-archive-command-pinned-effects-true-listp
  (true-listp (fn-nntp-result-effects
               (fn-nntp-archive-command-pinned session archive index verdicts
                                               env keyword args fn-arena)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-nntp-archive-command-pinned)
                                  (fn-nntp-result-effects fn-nntp-archive-command
                                   fn-nntp-withdrawn-reply fn-gidx-list-counts-command
                                   fn-nntp-msgid-retrieval-indexed fn-gidx-listgroup-command
                                   fn-nntp-over-range-indexed fn-nntp-verdict-hdr-response
                                   fn-nntp-over-range-served fn-nntp-over-current-served
                                   fn-nntp-over-msgid-served fn-nntp-list-overview-fmt-served
                                   fn-nntp-xref-reply
                                   fn-nntp-control-hdr-response fn-nntp-keywordp
                                   fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p)))))

;; One framed archive command line through the pinned chain: the dispatch's
;; effects are the pinned dispatcher's reply, and the wire is kept, when the
;; reply offers no article.
(defthm fn-octl-dispatch-archive-command
  (let ((tokens (fn-nntp-tokenize line)))
    (implies (and (fn-octl-reader-hyps (fn-served-conn-session conn) tokens line)
                  ;; PRF-222: a session without a group-access rule.
                  (not (fn-auth-access-restrictedp (fn-served-conn-session conn)
                                                   (fn-served-conn-config conn)))
                  ; a GROUP or LISTGROUP line is dispatched over the
                  ; re-pinned connection (NNT-042: books/served.lisp
                  ; fn-served-successful-selection-is-the-repinned-dispatch);
                  ; this book's subject is the control read, never a selection
                  (not (fn-served-advance-eventp (list :command line)))
                  (not (fn-post-offeredp
                        (fn-nntp-result-effects (fn-octl-reply conn line fn-arena)))))
             (and (equal (fn-served-result-effects
                          (fn-served-dispatch conn (list :command line) fn-arena))
                         (fn-nntp-result-effects (fn-octl-reply conn line fn-arena)))
                  (equal (fn-served-conn-wire
                          (fn-served-result-conn
                           (fn-served-dispatch conn (list :command line) fn-arena)))
                         (fn-served-conn-wire conn)))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-served-dispatch-core fn-auth-step-pinned
                                   fn-auth-command fn-auth-delegate-pinned
                                   fn-peer-step-pinned fn-peer-delegate-pinned
                                   fn-nntp-post-step-pinned fn-nntp-step-pinned
                                   fn-nntp-command-pinned
                                   fn-auth-tls-eventp fn-nntp-keywordp
                                   fn-nntp-archive-keywordp)
                                  (fn-nntp-archive-command-pinned fn-nntp-upcase-keyword
                                   fn-served-advance-eventp fn-served-repin
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
                  (not (fn-auth-access-restrictedp (fn-served-conn-session conn)
                                                   (fn-served-conn-config conn)))
                  (not (fn-served-advance-eventp (list :command line)))
                  (not (fn-post-offeredp
                        (fn-nntp-result-effects (fn-octl-reply conn line fn-arena)))))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte)) fn-arena))
                    (fn-nntp-result-effects (fn-octl-reply conn line fn-arena)))))
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
           :in-theory (e/d (fn-served-closed-wirep fn-served-haltedp fn-served-quitp fn-served-tls-handshakingp)
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
;; (Since NNT-042 the connection carries its pin and the owner's committed
;; view: books/owner.lisp fn-own-served-conn, the constructor fn-own-read-full
;; calls.)
(defun fn-octl-served-conn (o conn)
  (declare (xargs :verify-guards nil))
  (fn-own-served-conn o conn (fn-own-conn-live-session o conn)))

;; KEYSTONE (the host-called read).  One read of connection ID framing one
;; archive command line answers the pinned dispatcher's reply over that
;; connection's pinned archive, index, buckets and control pin.
(defthm fn-own-read-archive-command-is-the-pinned-dispatcher
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (tokens (fn-nntp-tokenize line))
         (reply (fn-octl-reply (fn-octl-served-conn o conn) line fn-arena)))
    (implies (and conn
                  (fn-wire-statep w0)
                  (not (equal (fn-wire-state-mode w0) :closed))
                  (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
                  (equal (fn-wire-result-events (fn-wire-feed-byte w1 byte))
                         (list (list :command line)))
                  (not (equal (fn-wire-state-mode w2) :closed))
                  (fn-octl-reader-hyps (fn-own-conn-live-session o conn) tokens line)
                  (not (fn-auth-access-restrictedp (fn-own-conn-live-session o conn)
                                                   (fn-own-conn-config conn)))
                  (not (fn-served-advance-eventp (list :command line)))
                  (not (fn-post-offeredp (fn-nntp-result-effects reply))))
             (equal (car (fn-own-read o id (append prefix (list byte)) fn-arena))
                    (fn-nntp-result-effects reply))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-octl-served-step-archive-command
                  (conn (fn-octl-served-conn o (fn-own-find-conn id (fn-own-conns o))))))
           ; The effects-shape and wire-input rules below are tried on every
           ; reply and wire term and never apply: 345k prover steps with
           ; them, 96k without (owner-books-split).
           :in-theory (e/d (fn-own-read fn-own-read-full fn-own-finish-read
                            fn-octl-served-conn fn-own-served-conn)
                           (fn-auth-effects-carry-no-submission
                            fn-auth-nntp-effects-are-auth-effects
                            fn-served-submission fn-wire-octet-listp
                            fn-wire-next-event-needs-input
                            fn-wire-next-loop-event-needs-input
                            fn-octl-served-step-archive-command fn-octl-reply
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
;; control pin whenever the connection has buckets, and also when its view
;; holds no article at all (PKT-443: every article withdrawn, so no buckets).
(defthm fn-octl-pinned-index-of-served-conn
  (implies (or (fn-own-conn-group-index conn)
               (and (fn-own-conn-control conn)
                    (not (consp (fn-state-articles (fn-own-conn-archive conn))))))
           (and (equal (fn-gidx-pin-control
                        (fn-served-conn-pinned-index (fn-octl-served-conn o conn)))
                       (fn-own-conn-control conn))
                (equal (fn-gidx-pin-trie
                        (fn-served-conn-pinned-index (fn-octl-served-conn o conn)))
                       (fn-own-conn-index conn))))
  :hints (("Goal" :in-theory (enable fn-served-conn-pinned-index
                                     fn-own-served-conn))))

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

;; PKT-443 KEYSTONE over the host-called reader port (host/owner-host.lisp
;; fn-owner-chunk, through fn-own-read): a read by Message-ID of an article
;; the connection's view withdrew answers `430 withdrawn' -- also when the
;; view holds no article at all, which has no buckets (two signed cancels
;; naming each other withdraw both; tests/test_native_control_across_peers.py
;; test_a_view_with_every_article_withdrawn).  Before PKT-443 such a view was
;; served from the bare trie and answered `430 no article with that
;; message-id'.
(defthm fn-own-read-of-a-withdrawn-article-answers-430-withdrawn
  (let* ((s (fn-own-store o))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (raw (fn-state-articles
               (fn-own-prefix-archive (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-sf-records (fn-sn-files s))
                                      (fn-own-conn-version conn)
                                      (fn-own-conn-frontier conn))))
         (control (fn-own-conn-control conn))
         (ws (fn-ctl-pin-ws control))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-own-conn-live-session o conn))
         (ns (fn-post-session-base
              (fn-peer-session-base (fn-auth-session-base as))))
         (tokens (fn-nntp-tokenize line))
         (msgid (fn-nntp-token-string (cadr tokens))))
    (implies (and (fn-own-relation o) conn control
                  (or (fn-own-conn-group-index conn)
                      (not (consp (fn-state-articles (fn-own-conn-archive conn)))))
                  (fn-wire-statep w0)
                  (not (equal (fn-wire-state-mode w0) :closed))
                  (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
                  (equal (fn-wire-result-events (fn-wire-feed-byte w1 byte))
                         (list (list :command line)))
                  (not (equal (fn-wire-state-mode w2) :closed))
                  (fn-octl-reader-hyps as tokens line)
                  (not (fn-auth-access-restrictedp as (fn-own-conn-config conn)))
                  (fn-nctl-retrievalp (car tokens))
                  (consp (cdr tokens)) (null (cddr tokens))
                  (fn-nntp-message-id-tokenp (cadr tokens))
                  (fn-octet-listp (cadr tokens))
                  (member-equal x raw) (consp x)
                  (not (member-equal x (fn-ctl-visible-articles
                                        raw ws (fn-own-conn-verdicts conn))))
                  (equal (fn-article-msgid x) msgid)
                  (not (consp (fn-find-article
                               msgid (fn-state-articles (fn-own-conn-archive conn))))))
             (equal (car (fn-own-read o id (append prefix (list byte)) fn-arena))
                    (fn-nntp-result-effects (fn-nntp-single ns "430 withdrawn")))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-own-read-archive-command-is-the-pinned-dispatcher)
                 (:instance fn-own-related-conn-control)
                 (:instance fn-octl-pinned-index-of-served-conn
                  (conn (fn-own-find-conn id (fn-own-conns o))))
                 (:instance fn-nntp-withdrawn-article-answers-430-withdrawn
                  (session (fn-post-session-base
                            (fn-peer-session-base
                             (fn-auth-session-base
                              (fn-served-conn-session
                               (fn-octl-served-conn
                                o (fn-own-find-conn id (fn-own-conns o))))))))
                  (archive (fn-served-conn-archive
                            (fn-octl-served-conn
                             o (fn-own-find-conn id (fn-own-conns o)))))
                  (index (fn-served-conn-pinned-index
                          (fn-octl-served-conn
                           o (fn-own-find-conn id (fn-own-conns o)))))
                  (verdicts (fn-served-conn-verdicts
                             (fn-octl-served-conn
                              o (fn-own-find-conn id (fn-own-conns o)))))
                  (env (fn-post-reader-env
                        (fn-auth-moderation-config
                         (fn-served-conn-session
                          (fn-octl-served-conn
                           o (fn-own-find-conn id (fn-own-conns o))))
                         (fn-served-conn-config
                          (fn-octl-served-conn
                           o (fn-own-find-conn id (fn-own-conns o)))))
                        (fn-served-conn-observation
                         (fn-octl-served-conn
                          o (fn-own-find-conn id (fn-own-conns o))))))
                  (keyword (car (fn-nntp-tokenize line)))
                  (args (cdr (fn-nntp-tokenize line)))
                  (raw (fn-state-articles
                        (fn-own-prefix-archive
                         (fn-sn-groups (fn-own-store o))
                         (fn-sn-capacity (fn-own-store o))
                         (fn-sf-records (fn-sn-files (fn-own-store o)))
                         (fn-own-conn-version (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-conn-frontier (fn-own-find-conn id (fn-own-conns o))))))
                  (ws (fn-ctl-pin-ws
                       (fn-own-conn-control (fn-own-find-conn id (fn-own-conns o)))))))
           :in-theory (e/d (fn-octl-reply fn-octl-served-conn fn-own-served-conn
                            fn-nntp-single fn-post-offeredp fn-nntp-reply-effect)
                           (fn-own-read-archive-command-is-the-pinned-dispatcher
                            fn-own-related-conn-control
                            fn-octl-pinned-index-of-served-conn
                            fn-nntp-withdrawn-article-answers-430-withdrawn
                            fn-nntp-archive-command-pinned
                            fn-served-conn-pinned-index
                            fn-ctl-withdrawn-articles fn-ctl-visible-articles
                            fn-own-prefix-archive fn-midx-correspondencep
                            fn-own-relation fn-find-article
                            fn-own-read fn-served-step fn-own-conn-live-session
                            fn-own-conn-wire fn-own-conn-archive fn-own-conn-config
                            fn-own-conn-observation fn-own-conn-verdicts
                            fn-own-conn-index fn-own-conn-group-index
                            fn-own-conn-control fn-own-conn-session fn-own-find-conn
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-tokenize fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-message-id-tokenp
                            fn-nntp-archive-keywordp
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp fn-octet-listp)))))
