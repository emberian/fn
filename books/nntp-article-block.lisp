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
; This book is the concrete side of that answer, over the octets a caller
; already holds:
;   fn-nntp-block-rev          one pass: validates RFC 3977 section 3.1.1
;                              framing (every line CRLF-terminated; no NUL,
;                              bare LF or bare CR) and dot-stuffs each line
;                              onto a reversed accumulator
;   fn-nntp-crlf-validp        the same pass's verdict, allocating nothing
;   fn-nntp-blank-linep        the header/body separator is present,
;                              allocating nothing
;   fn-nntp-article-response-of-bytes   `fn-nntp-article-response' over
;                              given octets; its :exec answers ARTICLE with
;                              the one pass
;   fn-nntp-response-okp-of-bytes       whether that response answers the
;                              article (the only thing its session depends
;                              on), allocating nothing for ARTICLE
;
; Keystones:
;   fn-nntp-block-rev-is-the-block          the pass is the specification's
;                                           block (crlf-lines, stuff-lines)
;   fn-nntp-article-response-is-of-bytes    the host-reached response is
;                                           the of-bytes one over the
;                                           article's bytes
;   fn-nntp-response-of-bytes-session       its session is decided by
;                                           fn-nntp-response-okp-of-bytes

(in-package "ACL2")
(include-book "nntp-responses")

(local (in-theory (enable fn-nntp-crlf-lines fn-nntp-stuff-lines fn-nntp-crlf)))

; -----------------------------------------------------------------------------
; The one pass

(defun fn-nntp-block-rev (bytes startp acc)
  (declare (xargs :guard t :measure (acl2-count bytes)))
  (if (consp bytes)
      (let ((b (car bytes)))
        (cond ((equal b 13)
               (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10))
                   (fn-nntp-block-rev (cdr (cdr bytes)) t (cons 10 (cons 13 acc)))
                 :error))
              ((or (equal b 10) (equal b 0)) :error)
              (t (fn-nntp-block-rev (cdr bytes) nil
                                    (cons b (if (and startp (equal b 46))
                                                (cons 46 acc)
                                              acc))))))
    (if startp acc :error)))

(defun fn-nntp-crlf-validp (bytes startp)
  (declare (xargs :guard t :measure (acl2-count bytes)))
  (if (consp bytes)
      (let ((b (car bytes)))
        (cond ((equal b 13)
               (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10)
                    (fn-nntp-crlf-validp (cdr (cdr bytes)) t)))
              ((or (equal b 10) (equal b 0)) nil)
              (t (fn-nntp-crlf-validp (cdr bytes) nil))))
    (if startp t nil)))

; The specification's split into lines, without the accumulator of lines.
(defun fn-nntp-crlf-lines-spec (bytes lr)
  (declare (xargs :measure (acl2-count bytes)))
  (if (consp bytes)
      (if (equal (car bytes) 13)
          (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10))
              (let ((r (fn-nntp-crlf-lines-spec (cdr (cdr bytes)) nil)))
                (if (equal (car r) :ok)
                    (list :ok (cons (reverse lr) (car (cdr r))))
                  r))
            (list :error))
        (if (or (equal (car bytes) 10) (equal (car bytes) 0))
            (list :error)
          (fn-nntp-crlf-lines-spec (cdr bytes) (cons (car bytes) lr))))
    (if (consp lr) (list :error) (list :ok nil))))

(local
 (defthm fn-nntp-crlf-lines-aux-is-spec
   (implies (and (true-listp lines) (true-listp lr))
            (equal (fn-nntp-crlf-lines-aux bytes lr lines)
                   (let ((r (fn-nntp-crlf-lines-spec bytes lr)))
                     (if (equal (car r) :ok)
                         (list :ok (revappend lines (car (cdr r))))
                       r))))
   :hints (("Goal" :induct (fn-nntp-crlf-lines-aux bytes lr lines)
            :in-theory (enable fn-nntp-crlf-lines-aux)))))

(local
 (defthm fn-nntp-stuff-line-of-append-consp
   (implies (consp x)
            (equal (fn-wire-stuff-line (append x y))
                   (append (fn-wire-stuff-line x) y)))
   :hints (("Goal" :in-theory (enable fn-wire-stuff-line)))))

(local
 (defthm fn-nntp-stuff-line-of-singleton
   (equal (fn-wire-stuff-line (list b))
          (if (equal b 46) (list 46 46) (list b)))
   :hints (("Goal" :in-theory (enable fn-wire-stuff-line)))))

(local
 (defthm fn-nntp-stuff-line-of-nil
   (equal (fn-wire-stuff-line nil) nil)
   :hints (("Goal" :in-theory (enable fn-wire-stuff-line)))))

(local
 (defun fn-nntp-block-rev-ind (bytes lr a)
   (declare (xargs :measure (acl2-count bytes)))
   (if (consp bytes)
       (if (equal (car bytes) 13)
           (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10))
               (fn-nntp-block-rev-ind (cdr (cdr bytes)) nil
                                      (cons 10 (cons 13 (revappend (fn-wire-stuff-line (reverse lr)) a))))
             nil)
         (if (or (equal (car bytes) 10) (equal (car bytes) 0))
             nil
           (fn-nntp-block-rev-ind (cdr bytes) (cons (car bytes) lr) a)))
     (list lr a))))

(local
 (defthm fn-nntp-block-rev-is-spec
   (implies (true-listp lr)
            (let ((r (fn-nntp-crlf-lines-spec bytes lr)))
              (equal (fn-nntp-block-rev bytes (not (consp lr))
                                        (revappend (fn-wire-stuff-line (reverse lr)) a))
                     (if (equal (car r) :ok)
                         (revappend (fn-nntp-stuff-lines (car (cdr r))) a)
                       :error))))
   :hints (("Goal" :induct (fn-nntp-block-rev-ind bytes lr a)))))

(local
 (defthm fn-nntp-crlf-validp-is-spec
   (implies (true-listp lr)
            (equal (fn-nntp-crlf-validp bytes (not (consp lr)))
                   (equal (car (fn-nntp-crlf-lines-spec bytes lr)) :ok)))
   :hints (("Goal" :induct (fn-nntp-crlf-lines-spec bytes lr)))))

; KEYSTONE (D27, the served ARTICLE's block).  Over octets that frame, the
; one pass reversed onto the terminator is the specification's block: the
; lines of fn-nntp-crlf-lines, each dot-stuffed and CRLF-terminated
; (fn-nntp-stuff-lines), then ".CRLF"; over octets that do not, the pass
; answers :error exactly when fn-nntp-crlf-lines does.
(defthm fn-nntp-block-rev-is-the-block
  (let ((acc (fn-nntp-block-rev bytes t nil))
        (r (fn-nntp-crlf-lines bytes)))
    (implies (fn-octet-listp bytes)
             (and (iff (equal acc :error) (not (equal (car r) :ok)))
                  (implies (equal (car r) :ok)
                           (equal (revappend acc '(46 13 10))
                                  (append (fn-nntp-stuff-lines (car (cdr r)))
                                          '(46 13 10)))))))
  :hints (("Goal" :use ((:instance fn-nntp-block-rev-is-spec (lr nil) (a nil))))))

(defthm fn-nntp-crlf-validp-is-crlf-lines-ok
  (implies (fn-octet-listp bytes)
           (equal (fn-nntp-crlf-validp bytes t)
                  (equal (car (fn-nntp-crlf-lines bytes)) :ok)))
  :hints (("Goal" :use ((:instance fn-nntp-crlf-validp-is-spec (lr nil))))))

; The header/body separator (CRLFCRLF) is present: fn-nntp-split-article's
; verdict, allocating nothing.
(defun fn-nntp-blank-linep (bytes)
  (declare (xargs :guard t :measure (acl2-count bytes)))
  (if (and (consp bytes)
           (consp (cdr bytes))
           (consp (cdr (cdr bytes)))
           (consp (cdr (cdr (cdr bytes))))
           (equal (car bytes) 13)
           (equal (car (cdr bytes)) 10)
           (equal (car (cdr (cdr bytes))) 13)
           (equal (car (cdr (cdr (cdr bytes)))) 10))
      t
    (if (consp bytes)
        (fn-nntp-blank-linep (cdr bytes))
      nil)))

(local
 (defthm fn-nntp-split-article-aux-okp
   (equal (fn-nntp-split-okp (fn-nntp-split-article-aux bytes rev))
          (fn-nntp-blank-linep bytes))
   :hints (("Goal" :induct (fn-nntp-split-article-aux bytes rev)
            :in-theory (enable fn-nntp-split-article-aux fn-nntp-split-okp)))))

(defthm fn-nntp-blank-linep-is-split-okp
  (equal (fn-nntp-split-okp (fn-nntp-split-article bytes))
         (and (fn-octet-listp bytes) (fn-nntp-blank-linep bytes)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-split-article)
                                  (fn-nntp-split-article-aux fn-nntp-blank-linep))
           :use ((:instance fn-nntp-split-article-aux-okp (rev nil))))))

(local
 (defthm fn-nntp-block-rev-true-listp
   (implies (and (true-listp acc)
                 (not (equal (fn-nntp-block-rev bytes startp acc) :error)))
            (true-listp (fn-nntp-block-rev bytes startp acc)))))

; -----------------------------------------------------------------------------
; The response over given octets

; fn-nntp-article-section and fn-nntp-article-framedp over the octets.
(defun fn-nntp-section-of-bytes (payload kind)
  (declare (xargs :guard t))
  (if (equal kind :article)
      (fn-nntp-crlf-lines payload)
    (let ((split (fn-nntp-split-article payload)))
      (if (fn-nntp-split-okp split)
          (if (equal kind :head)
              (fn-nntp-crlf-lines (fn-nntp-split-head split))
            (fn-nntp-crlf-lines (fn-nntp-split-body split)))
        (list :error)))))

(defun fn-nntp-framed-of-bytes (payload)
  (declare (xargs :guard t))
  (and (equal (car (fn-nntp-crlf-lines payload)) :ok)
       (fn-nntp-split-okp (fn-nntp-split-article payload))))

(defthm fn-nntp-article-section-unfolds
  (equal (fn-nntp-article-section article kind fn-arena)
         (fn-nntp-section-of-bytes (fn-nntp-article-bytes article fn-arena) kind))
  :hints (("Goal" :in-theory '(fn-nntp-article-section fn-nntp-section-of-bytes))))

(defthm fn-nntp-article-framedp-unfolds
  (equal (fn-nntp-article-framedp article fn-arena)
         (fn-nntp-framed-of-bytes (fn-nntp-article-bytes article fn-arena)))
  :hints (("Goal" :in-theory '(fn-nntp-article-framedp fn-nntp-framed-of-bytes))))

; Whether the response over BYTES answers the article (the cursor moves
; when UPDATEP): everything the response's session depends on.  For ARTICLE
; it allocates nothing.
(defun fn-nntp-response-okp-of-bytes (article bytes kind)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-nntp-crlf-lines
                                                            fn-nntp-split-article
                                                            fn-nntp-split-okp)))))
  (mbe :logic (and (fn-nntp-article-idp article)
                   (not (fn-rcl-tombstonep bytes))
                   (or (equal kind :stat)
                       (and (fn-nntp-framed-of-bytes bytes)
                            (equal (car (fn-nntp-section-of-bytes bytes kind)) :ok)))
                   t)
       :exec (and (fn-nntp-article-idp article)
                  (not (fn-rcl-tombstonep bytes))
                  (cond ((equal kind :stat) t)
                        ((equal kind :article)
                         (and (fn-octet-listp bytes)
                              (fn-nntp-blank-linep bytes)
                              (fn-nntp-crlf-validp bytes t)))
                        (t (and (fn-nntp-framed-of-bytes bytes)
                                (equal (car (fn-nntp-section-of-bytes bytes kind)) :ok)
                                t))))))

(defun fn-nntp-article-response-of-bytes (session article bytes number kind updatep group)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-nntp-crlf-lines
                                                            fn-nntp-split-article
                                                            fn-nntp-split-okp
                                                            fn-nntp-stuff-lines
                                                            fn-nntp-block-rev
                                                            fn-nntp-retrieval-initial
                                                            fn-nntp-article-idp
                                                            fn-rcl-tombstonep)
                                 :use ((:instance fn-nntp-block-rev-is-the-block
                                                  (bytes bytes)))))))
  (if (not (fn-nntp-article-idp article))
      (fn-nntp-single session "503 stored article identifier unavailable")
    (if (fn-rcl-tombstonep bytes)
        (fn-nntp-single session (if updatep
                                    "423 article reclaimed"
                                  "430 article reclaimed"))
      (let ((next-session (if updatep
                              (fn-nntp-set-cursor session group number)
                            session)))
        (if (equal kind :stat)
            (fn-nntp-make-result
             next-session
             (list (fn-nntp-reply-effect
                    (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article)))))
          (mbe :logic
               (let ((section (fn-nntp-section-of-bytes bytes kind)))
                 (if (and (fn-nntp-framed-of-bytes bytes)
                          (equal (car section) :ok))
                     (fn-nntp-make-result
                      next-session
                      (list (fn-nntp-reply-effect
                             (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                                     (fn-nntp-stuff-lines (car (cdr section)))
                                     '(46 13 10)))))
                   (fn-nntp-single session "503 stored article framing unavailable")))
               :exec
               (if (equal kind :article)
                   (let ((acc (if (and (fn-octet-listp bytes) (fn-nntp-blank-linep bytes))
                                  (fn-nntp-block-rev bytes t nil)
                                :error)))
                     (if (equal acc :error)
                         (fn-nntp-single session "503 stored article framing unavailable")
                       (fn-nntp-make-result
                        next-session
                        (list (fn-nntp-reply-effect
                               (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                                       (revappend acc '(46 13 10))))))))
                 (let ((section (fn-nntp-section-of-bytes bytes kind)))
                   (if (and (fn-nntp-framed-of-bytes bytes)
                            (equal (car section) :ok))
                       (fn-nntp-make-result
                        next-session
                        (list (fn-nntp-reply-effect
                               (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                                       (fn-nntp-stuff-lines (car (cdr section)))
                                       '(46 13 10)))))
                     (fn-nntp-single session "503 stored article framing unavailable"))))))))))

; KEYSTONE (the host-reached response).  fn-nntp-article-response, which
; the served ARTICLE/HEAD/BODY/STAT arms call with the arena, is the
; of-bytes response over the article's bytes.
(defthm fn-nntp-article-response-is-of-bytes
  (equal (fn-nntp-article-response session article number kind updatep group fn-arena)
         (fn-nntp-article-response-of-bytes session article
                                            (fn-nntp-article-bytes article fn-arena)
                                            number kind updatep group))
  :hints (("Goal" :in-theory '(fn-nntp-article-response
                               fn-nntp-article-response-of-bytes
                               fn-nntp-article-section-unfolds
                               fn-nntp-article-framedp-unfolds
                               fn-nntp-article-tombstonep))))

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
