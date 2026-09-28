; fn: the served ARTICLE's reply built in one pass over the stored octets
; (lane gate-regress, 2026-09-27).
;
; The throughput gate (PKT-477) measured the served ARTICLE of a 2 KiB
; article at 1.28 MB consed on dev (e8cd979af), 0.53 MB at f370581bf: the
; Xref arm (books/nntp-reader-compat.lisp `fn-rcompat-article-reply')
; answers over two representations and each answer read the payload through
; the arena, split it into a list of line lists twice (the section and the
; framing check) and rebuilt it again to dot-stuff and to append the
; terminator: about forty payload-sized list copies per ARTICLE.
;
; What is left here (the rest moved below books/nntp-responses.lisp, lane
; served-columns-body, PRF-334; see books/nntp-article-pass.lisp):
;   fn-nntp-response-okp-of-bytes       whether the response over given
;                              octets answers the article (the only thing
;                              its session depends on), allocating nothing
;                              for ARTICLE and only the split for HEAD/BODY
;
; Keystones:
;   fn-nntp-block-rev-is-the-block          (books/nntp-article-pass.lisp)
;   fn-nntp-article-response-is-of-bytes    (books/nntp-responses.lisp)
;   fn-nntp-response-of-bytes-session       its session is decided by
;                                           fn-nntp-response-okp-of-bytes

(in-package "ACL2")
(include-book "nntp-responses")

(local (in-theory (enable fn-nntp-crlf-lines fn-nntp-stuff-lines fn-nntp-crlf)))

; The one pass (fn-nntp-block-rev, fn-nntp-crlf-validp, fn-nntp-blank-linep),
; the section over given octets and their equations are
; books/nntp-article-pass.lisp, and fn-nntp-article-response-of-bytes with
; KEYSTONE fn-nntp-article-response-is-of-bytes is books/nntp-responses.lisp
; (lane served-columns-body, PRF-334: fn-nntp-article-response's executable
; runs it, so every retrieval reads the octets once).

; Whether the response over BYTES answers the article (the cursor moves
; when UPDATEP): everything the response's session depends on.  For ARTICLE
; it allocates nothing.
(defun fn-nntp-response-okp-of-bytes (article bytes kind)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-nntp-crlf-lines
                                                            fn-nntp-split-article
                                                            fn-nntp-split-okp
                                                            fn-nntp-response-validp-is-framed-section)
                                 :use ((:instance fn-nntp-response-validp-is-framed-section))))))
  (mbe :logic (and (fn-nntp-article-idp article)
                   (not (fn-rcl-tombstonep bytes))
                   (or (equal kind :stat)
                       (and (fn-nntp-framed-of-bytes bytes)
                            (equal (car (fn-nntp-section-of-bytes bytes kind)) :ok)))
                   t)
       :exec (and (fn-nntp-article-idp article)
                  (not (fn-rcl-tombstonep bytes))
                  (or (equal kind :stat)
                      (fn-nntp-response-validp bytes kind))
                  t)))

; KEYSTONE (the response's session).  The session a response answers with
; is the cursor-moved one exactly when fn-nntp-response-okp-of-bytes says
; the article is answered, and the session unchanged otherwise.
(defthm fn-nntp-response-of-bytes-session
  (equal (fn-nntp-result-session
          (fn-nntp-article-response-of-bytes session article bytes number kind
                                             updatep group))
         (if (fn-nntp-response-okp-of-bytes article bytes kind)
             (if updatep (fn-nntp-set-cursor session group number) session)
           session))
  :hints (("Goal" :in-theory (e/d (fn-nntp-single fn-nntp-make-result
                                                  fn-nntp-result-session)
                                  (fn-nntp-crlf-lines fn-nntp-split-article
                                   fn-nntp-split-okp fn-nntp-stuff-lines
                                   fn-nntp-retrieval-initial
                                   fn-nntp-article-idp fn-rcl-tombstonep
                                   fn-nntp-set-cursor)))))

; The equations above restate the served machine's own functions; books
; that reason about those functions keep their theory (enable these by name).
(in-theory (disable fn-nntp-article-response-is-of-bytes
                    fn-nntp-article-section-unfolds
                    fn-nntp-article-framedp-unfolds
                    fn-nntp-blank-linep-is-split-okp
                    fn-nntp-crlf-validp-is-crlf-lines-ok))
