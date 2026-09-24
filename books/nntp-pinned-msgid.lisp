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
;
; A Message-ID token begins with `<' (60), which is not a decimal digit, so
; the retrieval arm never reads it as an article number.
(defthm fn-nntp-message-id-token-is-not-a-number-token
  (implies (fn-nntp-message-id-tokenp token)
           (not (fn-nntp-number-tokenp token)))
  :hints (("Goal" :in-theory (enable fn-nntp-message-id-tokenp
                                     fn-nntp-number-tokenp
                                     fn-nntp-decimal-tokenp))))

(defthm fn-nntp-archive-command-pinned-msgid-arms-are-the-scan
  (implies (and (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (or (fn-nntp-keywordp keyword "ARTICLE")
                    (fn-nntp-keywordp keyword "HEAD")
                    (fn-nntp-keywordp keyword "BODY")
                    (fn-nntp-keywordp keyword "STAT")))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)
                  (fn-nntp-archive-command session archive env keyword args)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-archive-command-pinned
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
