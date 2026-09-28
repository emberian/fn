; fn: the pinned reader dispatcher's Message-ID arms are the archive scan.
;
; The served reader reaches fn-nntp-archive-command-pinned (books/nntp.lisp)
; on every archive command; ARTICLE, HEAD, BODY and STAT with a Message-ID
; argument are answered from the connection's pinned trie
; (fn-nntp-msgid-retrieval-indexed), never by walking the archive.  The
; function-level keystone is fn-nntp-msgid-retrieval-indexed-refines-scan
; (books/nntp-responses.lisp).  This book states it at the dispatcher the
; served path calls: for those four keywords, and for every argument list,
; the pinned dispatcher answers exactly what the unpinned archive dispatcher
; fn-nntp-archive-command -- whose Message-ID arm is the linear
; fn-find-article scan -- answers, given only that the pinned trie is the
; build of the pinned archive's article list.  The owner carries that
; relation for every connection (fn-own-conn-okp in fn-own-relation,
; books/owner-invariants.lisp, preserved by fn-own-step-preserves-relation);
; nothing evaluates it per command.
(in-package "ACL2")
(include-book "nntp")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-nntp-message-id-tokenp))))

;
; A Message-ID token begins with `<' (60), which is not a decimal digit, so
; the retrieval arm never reads it as an article number.
(defthm fn-nntp-message-id-token-is-not-a-number-token
  (implies (fn-nntp-message-id-tokenp token)
           (not (fn-nntp-number-tokenp token)))
  :hints (("Goal" :in-theory (enable fn-nntp-message-id-tokenp
                                     fn-nntp-number-tokenp
                                     fn-nntp-decimal-tokenp))))

; With a control pin, a number or Message-ID the archive lacks and the
; withdrawn list holds is answered `423 withdrawn' / `430 withdrawn'
; (books/nntp-control.lisp); every other retrieval is the scan, except
; ARTICLE and HEAD on the served path (an environment with a server name),
; which answer the article's served representation carrying its Xref line
; (PRF-243; fn-nntp-archive-command-pinned-article-head-is-served below).
(defthm fn-nntp-archive-command-pinned-msgid-arms-are-the-scan
  (implies (and (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (not (fn-nntp-number-withdrawn-p session archive index (car args)))
                (not (fn-nntp-msgid-withdrawn-p index (car args)))
                (or (fn-nntp-keywordp keyword "BODY")
                    (fn-nntp-keywordp keyword "STAT")
                    (and (not (fn-nntp-xref-server env))
                         (or (fn-nntp-keywordp keyword "ARTICLE")
                             (fn-nntp-keywordp keyword "HEAD")))))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args fn-arena)
                  (fn-nntp-archive-command session archive env keyword args fn-arena)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-archive-command-pinned fn-nntp-xref-reply
                            fn-rcompat-reply
                            fn-nntp-archive-command fn-nntp-keywordp
                            fn-nntp-retrieval
                            fn-nntp-msgid-retrieval-indexed-refines-scan
                            fn-nntp-message-id-token-is-not-a-number-token)
                           (fn-nntp-msgid-retrieval-indexed
                            fn-nntp-msgid-retrieval
                            fn-nntp-number-retrieval
                            fn-nntp-current-retrieval
                            fn-nntp-upcase-keyword
                            fn-midx-correspondencep)))))

; PRF-243 (PKT-668): on the served path ARTICLE and HEAD (no argument, a
; number or a Message-ID) are the served retrieval: the generic reply over
; the article's served representation (books/nntp-reader-compat.lisp
; `fn-rcompat-retrieval', whose session is the generic retrieval's,
; `fn-rcompat-retrieval-session-is-the-generic-session').
(defthm fn-nntp-archive-command-pinned-article-head-is-served
  (implies (and (fn-nntp-xref-server env)
                (fn-gidx-pinp index)
                (or (null args) (and (consp args) (null (cdr args))))
                (not (fn-nntp-number-withdrawn-p session archive index (car args)))
                (not (and (fn-nntp-message-id-tokenp (car args))
                          (fn-nntp-msgid-withdrawn-p index (car args))))
                (or (fn-nntp-keywordp keyword "ARTICLE")
                    (fn-nntp-keywordp keyword "HEAD")))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args fn-arena)
                  (fn-rcompat-retrieval session archive (fn-gidx-pin-trie index)
                                        (fn-rcompat-retrieval-kind keyword)
                                        args (fn-nntp-xref-server env) fn-arena)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-archive-command-pinned fn-nntp-xref-reply
                            fn-rcompat-reply fn-nntp-keywordp)
                           (fn-rcompat-retrieval fn-nntp-xref-server
                            fn-nntp-upcase-keyword fn-gidx-pinp)))))
