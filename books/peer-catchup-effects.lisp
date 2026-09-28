; fn: the catch-up reply is a well-formed NNTP response (PRF-325).
;
; books/nntp-pinned-effects.lisp proves every effect the pinned dispatcher
; emits is a well-formed reply (`fn-nntp-effectsp', RFC 3977 section 3.1);
; its XFNCATCHUP arm is `fn-cu-serve-reply' (books/peer-catchup-serve.lisp),
; and this book gives that proof the one fact it needs of the arm:
;
;   fn-cu-serve-reply-effects-well-formed   the reply is one response whose
;                                            initial line fits 512 octets and
;                                            whose block lines carry no CR,
;                                            LF or NUL
;
; The initial line is fixed-width (four u64 fields in hexadecimal and the
; chain), each record header is "R", a stored Message-ID (a served article
; has a valid identifier, `fn-cu-select-serves-only-retrievable') and a
; hexadecimal count, and the article lines are `fn-nntp-crlf-lines' of a
; framed article.
(in-package "ACL2")
(include-book "nntp-effects")
(include-book "peer-catchup-serve")

(local (in-theory (enable fn-nntp-response-textp fn-nntp-block-textp
                          fn-nntp-response-octetp)))

(local (defthm fn-cu-len-append
         (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-cu-hex-digit-is-response-octet
  (fn-nntp-response-octetp (fn-cu-hex-digit n)))

(defthm fn-cu-hex-is-response-text
  (fn-nntp-response-textp (fn-cu-hex octets))
  :hints (("Goal" :in-theory (disable fn-cu-hex-digit))))

(defthm fn-cu-len-hex
  (equal (len (fn-cu-hex octets)) (* 2 (len octets))))

(defthm fn-cu-len-u64-octets-aux
  (equal (len (fn-cu-u64-octets-aux k n acc)) (+ (nfix k) (len acc))))

(defthm fn-cu-len-u64-hex
  (equal (len (fn-cu-u64-hex n)) 16))

(defthm fn-cu-u64-hex-is-response-text
  (fn-nntp-response-textp (fn-cu-u64-hex n)))

(in-theory (disable fn-cu-hex fn-cu-u64-hex))

(defthm fn-cu-response-text-append
  (equal (fn-nntp-response-textp (append a b))
         (and (fn-nntp-response-textp (true-list-fix a))
              (fn-nntp-response-textp b))))

(defthm fn-cu-block-text-append
  (implies (fn-nntp-block-textp a)
           (equal (fn-nntp-block-textp (append a b))
                  (fn-nntp-block-textp b))))

(defthm fn-cu-response-text-true-list-fix
  (implies (fn-nntp-response-textp a)
           (fn-nntp-response-textp (true-list-fix a))))

(defthm fn-cu-initial-line-facts
  (implies (equal (len chain) 32)
           (let ((line (fn-cu-initial-line next end chain)))
             (and (fn-nntp-response-textp line)
                  (fn-nntp-initial-status-linep line)
                  (<= (+ (len line) 2) *fn-nntp-max-response-octets*))))
  :hints (("Goal" :in-theory (enable fn-cu-initial-line))))

(defthm fn-cu-article-lines-are-block-text
  (fn-nntp-block-textp (fn-cu-article-lines bytes))
  :hints (("Goal" :in-theory (e/d (fn-cu-article-lines fn-cu-list)
                                  (fn-nntp-crlf-lines))
           :use ((:instance fn-nntp-crlf-lines-is-response-text)))))

(defun fn-cu-all-idp (articles)
  (if (consp articles)
      (and (fn-nntp-article-idp (car articles))
           (fn-cu-all-idp (cdr articles)))
    t))

(defthm fn-cu-record-header-is-response-text
  (implies (fn-nntp-article-idp article)
           (fn-nntp-response-textp
            (fn-cu-record-header (fn-article-msgid article) count)))
  :hints (("Goal" :in-theory (enable fn-cu-record-header fn-cu-msgid-octets))))

(defthm fn-cu-render-lines-are-block-text
  (implies (fn-cu-all-idp articles)
           (fn-nntp-block-textp (fn-cu-render-lines articles fn-arena)))
  :hints (("Goal" :in-theory (disable fn-cu-article-lines fn-cu-record-header
                                      fn-nntp-article-idp fn-nntp-article-bytes))))

(defun fn-cu-all-servedp (xs groups trie fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp xs)
      (and (fn-cu-servedp (car xs) groups trie fn-arena)
           (fn-cu-all-servedp (cdr xs) groups trie fn-arena))
    t))

(local
 (defthm fn-cu-all-servedp-rev
   (implies (and (fn-cu-all-servedp x groups trie fn-arena)
                 (fn-cu-all-servedp y groups trie fn-arena))
            (fn-cu-all-servedp (fn-cu-rev x y) groups trie fn-arena))
   :hints (("Goal" :induct (fn-cu-rev x y)
            :in-theory (disable fn-cu-servedp)))))

(local
 (defthm fn-cu-select-aux-all-servedp
   (implies (fn-cu-all-servedp served groups trie fn-arena)
            (fn-cu-all-servedp
             (mv-nth 1 (fn-cu-select-aux entries groups trie quantum pos served
                                         used fn-arena))
             groups trie fn-arena))
   :hints (("Goal" :in-theory (disable fn-cu-servedp fn-nntp-article-bytes)))))

(local
 (defthm fn-cu-all-servedp-all-idp
   (implies (fn-cu-all-servedp xs groups trie fn-arena)
            (fn-cu-all-idp xs))
   :hints (("Goal" :in-theory (enable fn-cu-servedp)))))

(defthm fn-cu-select-all-idp
  (fn-cu-all-idp (mv-nth 1 (fn-cu-select articles from groups trie quantum fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-cu-select) (fn-cu-servedp fn-cu-select-aux
                                                  fn-nntp-article-idp fn-cu-rev))
           :use ((:instance fn-cu-all-servedp-all-idp
                            (xs (mv-nth 1 (fn-cu-select articles from groups trie
                                                        quantum fn-arena))))))))

(defthm fn-cu-len-blake3-stobj
  (equal (len (fn-blake3-stobj m)) 32)
  :hints (("Goal" :use ((:instance fn-blake3-stobj-is-blake3)
                        (:instance fn-blake3-shape))
           :in-theory (disable fn-blake3-shape fn-blake3-stobj-is-blake3
                               fn-blake3-stobj fn-blake3))))

(local
 (defthm fn-cu-octet-listp-true-listp
   (implies (fn-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-octet-listp)))))

(defthm fn-cu-parse-request-chain-len
  (implies (fn-cu-parse-request args)
           (and (true-listp (caddr (fn-cu-parse-request args)))
                (equal (len (caddr (fn-cu-parse-request args))) 32)))
  :hints (("Goal" :in-theory (e/d (fn-cu-parse-request fn-cu-chainp)
                                  (fn-wildmat-parse fn-cu-unhex fn-cu-u64-value
                                   fn-cu-decimal-value fn-octet-listp)))))

(local
 (defthm fn-cu-len-chain-over
   (implies (and (true-listp chain) (equal (len chain) 32))
            (equal (len (fn-cu-chain-over chain articles fn-arena)) 32))
   :hints (("Goal" :in-theory (e/d (fn-cu-chain-step fn-cu-list)
                                   (fn-blake3-stobj fn-nntp-article-bytes))))))

; KEYSTONE (PRF-325; books/nntp-pinned-effects.lisp cites it for the
; XFNCATCHUP arm of `fn-nntp-command-pinned').
(local
 (defthm fn-cu-batch-effects
   (implies (and (true-listp chain) (equal (len chain) 32)
                 (fn-cu-all-idp served))
            (fn-nntp-effectsp
             (fn-nntp-result-effects
              (fn-nntp-multi-octets
               session
               (fn-cu-initial-line next end (fn-cu-chain-over chain served fn-arena))
               (fn-cu-render-lines served fn-arena)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-nntp-effects-multi-octets
                             (initial (fn-cu-initial-line
                                       next end (fn-cu-chain-over chain served fn-arena)))
                             (lines (fn-cu-render-lines served fn-arena)))
                  (:instance fn-cu-initial-line-facts
                             (chain (fn-cu-chain-over chain served fn-arena))))
            :in-theory (disable fn-nntp-effects-multi-octets fn-cu-initial-line-facts
                                fn-cu-initial-line fn-cu-render-lines fn-cu-chain-over
                                fn-nntp-multi-octets fn-nntp-effectsp
                                fn-nntp-result-effects fn-nntp-response-textp
                                fn-nntp-block-textp fn-nntp-initial-status-linep)))))

(local
 (defthm fn-cu-single-effects
   (implies (member-equal text '("501 syntax error"
                                 "503 catch-up log position out of range"
                                 "423 catch-up position past the end of the log"))
            (fn-nntp-effectsp (fn-nntp-result-effects (fn-nntp-single session text))))
   :hints (("Goal" :in-theory (disable fn-nntp-single fn-nntp-effectsp
                                       fn-nntp-result-effects)))))

(defthm fn-cu-serve-reply-effects-well-formed
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-cu-serve-reply session archive index args fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cu-serve-reply)
                           (fn-cu-select fn-cu-chain-over fn-cu-render-lines
                            fn-cu-initial-line fn-cu-parse-request
                            fn-nntp-multi-octets fn-nntp-single
                            fn-nntp-effectsp fn-nntp-result-effects
                            fn-nntp-response-textp fn-nntp-block-textp
                            fn-nntp-initial-status-linep
                            fn-nntp-filter-groups-by-wildmat
                            fn-gidx-pin-trie fn-cu-list)))))
