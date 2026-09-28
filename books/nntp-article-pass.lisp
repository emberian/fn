; fn: the served retrieval's one pass over the stored octets (lane
; gate-regress, 2026-09-27; moved below books/nntp-responses.lisp by lane
; served-columns-body, 2026-09-27, PRF-334).
;
; The served ARTICLE/HEAD/BODY reply is a function of the article's stored
; octets.  Its specification (books/nntp-session.lisp) splits the octets into
; a list of line lists (fn-nntp-crlf-lines) twice -- the section and the
; framing check -- splits at the header/body separator twice, and rebuilds
; the section to dot-stuff it.  This book is the concrete side, over octets
; a caller already holds, each piece with the equation that makes it the
; specification's:
;   fn-nntp-block-rev          one pass: validates RFC 3977 section 3.1.1
;                              framing (every line CRLF-terminated; no NUL,
;                              bare LF or bare CR) and dot-stuffs each line
;                              onto a reversed accumulator
;                              (fn-nntp-block-rev-is-the-block)
;   fn-nntp-crlf-validp        the same pass's verdict, allocating nothing
;                              (fn-nntp-crlf-validp-is-crlf-lines-ok)
;   fn-nntp-blank-linep        the header/body separator is present,
;                              allocating nothing
;                              (fn-nntp-blank-linep-is-split-okp)
;   fn-nntp-section-rev        HEAD's or BODY's block from ONE split and one
;                              pass over the section, after a framing check
;                              that allocates nothing
;                              (fn-nntp-section-rev-is-the-section)
;   fn-nntp-response-validp   whether a reply's block exists, allocating
;                              only the split
;                              (fn-nntp-response-validp-is-framed-section)
;   fn-nntp-response-block-rev the block of every kind
;                              (fn-nntp-response-block-rev-is-the-block)
; books/nntp-responses.lisp fn-nntp-article-response-of-bytes runs them.

(in-package "ACL2")
(include-book "nntp-session")
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))

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

(defthm fn-nntp-block-rev-true-listp
  (implies (and (true-listp acc)
                (not (equal (fn-nntp-block-rev bytes startp acc) :error)))
           (true-listp (fn-nntp-block-rev bytes startp acc))))

; -----------------------------------------------------------------------------
; The section over given octets

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


; -----------------------------------------------------------------------------
; HEAD and BODY from one split (PRF-334).
;
; The specification's HEAD/BODY reply is framed when the whole payload's
; lines are CRLF-terminated (fn-nntp-crlf-lines) and the separator is found
; (fn-nntp-split-article), and its block is the stuffed lines of the
; section.  Here the framing check is fn-nntp-crlf-validp (allocating
; nothing), the separator is found once (fn-nntp-split-article-aux: the
; head is copied, the body is the payload's own tail), and the section is
; stuffed in one pass (fn-nntp-block-rev).

(local
 (defthm fn-nntp-octet-listp-revappend
   (implies (and (fn-octet-listp a) (fn-octet-listp b))
            (fn-octet-listp (revappend a b)))
   :hints (("Goal" :in-theory (enable fn-octet-listp)))))

(local
 (defthm fn-nntp-split-aux-parts-octets
   (implies (and (fn-octet-listp bytes) (fn-octet-listp rev)
                 (fn-nntp-split-okp (fn-nntp-split-article-aux bytes rev)))
            (and (fn-octet-listp (fn-nntp-split-head (fn-nntp-split-article-aux bytes rev)))
                 (fn-octet-listp (fn-nntp-split-body (fn-nntp-split-article-aux bytes rev)))))
   :hints (("Goal" :induct (fn-nntp-split-article-aux bytes rev)
            :in-theory (enable fn-nntp-split-article-aux fn-nntp-split-okp
                               fn-nntp-split-head fn-nntp-split-body fn-octet-listp)))))

(defun fn-nntp-section-part (split kind)
  (declare (xargs :guard t))
  (if (equal kind :head) (fn-nntp-split-head split) (fn-nntp-split-body split)))

(defun fn-nntp-section-rev (bytes kind)
  (declare (xargs :guard t))
  (if (and (fn-octet-listp bytes) (fn-nntp-crlf-validp bytes t))
      (let ((split (fn-nntp-split-article-aux bytes nil)))
        (if (fn-nntp-split-okp split)
            (fn-nntp-block-rev (fn-nntp-section-part split kind) t nil)
          :error))
    :error))

(defun fn-nntp-section-validp (bytes kind)
  (declare (xargs :guard t))
  (and (fn-octet-listp bytes)
       (fn-nntp-crlf-validp bytes t)
       (let ((split (fn-nntp-split-article-aux bytes nil)))
         (and (fn-nntp-split-okp split)
              (fn-nntp-crlf-validp (fn-nntp-section-part split kind) t)))))

; Whether the reply of every retrieval kind but STAT has a block, allocating
; nothing for ARTICLE and only the split for HEAD/BODY.
(defun fn-nntp-response-validp (bytes kind)
  (declare (xargs :guard t))
  (if (equal kind :article)
      (and (fn-octet-listp bytes)
           (fn-nntp-blank-linep bytes)
           (fn-nntp-crlf-validp bytes t))
    (fn-nntp-section-validp bytes kind)))

; KEYSTONE (PRF-334, the served HEAD/BODY block).  For HEAD and BODY the one
; split and one pass answer :error exactly when the specification's reply
; is not framed or its section does not split into lines, and otherwise
; the reversed pass onto the terminator is the specification's block.
(defthm fn-nntp-section-rev-is-the-section
  (implies (not (equal kind :article))
           (let ((acc (fn-nntp-section-rev bytes kind))
                 (section (fn-nntp-section-of-bytes bytes kind)))
             (and (iff (equal acc :error)
                       (not (and (fn-nntp-framed-of-bytes bytes)
                                 (equal (car section) :ok))))
                  (implies (not (equal acc :error))
                           (equal (revappend acc '(46 13 10))
                                  (append (fn-nntp-stuff-lines (car (cdr section)))
                                          '(46 13 10)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-split-article)
                           (fn-nntp-block-rev fn-nntp-crlf-validp fn-nntp-crlf-lines
                            fn-nntp-stuff-lines fn-nntp-split-article-aux
                            fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body))
           :cases ((fn-octet-listp bytes))
           :use ((:instance fn-nntp-crlf-validp-is-crlf-lines-ok)
                 (:instance fn-nntp-split-aux-parts-octets (rev nil))
                 (:instance fn-nntp-block-rev-is-the-block
                            (bytes (fn-nntp-section-part
                                    (fn-nntp-split-article-aux bytes nil) kind)))))))

; The same without the block, every kind: whether the specification's
; reply is framed and its section splits into lines.
(defthm fn-nntp-response-validp-is-framed-section
  (equal (fn-nntp-response-validp bytes kind)
         (and (fn-nntp-framed-of-bytes bytes)
              (equal (car (fn-nntp-section-of-bytes bytes kind)) :ok)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-split-article fn-nntp-blank-linep-is-split-okp)
                           (fn-nntp-crlf-validp fn-nntp-crlf-lines fn-nntp-blank-linep
                            fn-nntp-split-article-aux
                            fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body))
           :cases ((fn-octet-listp bytes))
           :use ((:instance fn-nntp-crlf-validp-is-crlf-lines-ok)
                 (:instance fn-nntp-split-aux-parts-octets (rev nil))
                 (:instance fn-nntp-crlf-validp-is-crlf-lines-ok
                            (bytes (fn-nntp-section-part
                                    (fn-nntp-split-article-aux bytes nil) kind)))))))

(defthm fn-nntp-section-rev-true-listp
  (implies (not (equal (fn-nntp-section-rev bytes kind) :error))
           (true-listp (fn-nntp-section-rev bytes kind)))
  :hints (("Goal" :in-theory (disable fn-nntp-block-rev fn-nntp-crlf-validp
                                      fn-nntp-split-article-aux))))

; The reply's block for ARTICLE, HEAD or BODY, reversed, or :error: what
; books/nntp-responses.lisp fn-nntp-article-response-of-bytes runs.
(defun fn-nntp-response-block-rev (bytes kind)
  (declare (xargs :guard t))
  (if (equal kind :article)
      (if (and (fn-octet-listp bytes) (fn-nntp-blank-linep bytes))
          (fn-nntp-block-rev bytes t nil)
        :error)
    (fn-nntp-section-rev bytes kind)))

; KEYSTONE (PRF-334, the served block of every retrieval kind but STAT):
; :error exactly when the specification's reply is not framed or its
; section does not split into lines; otherwise a true list whose reverse
; onto the terminator is the specification's block.
(defthm fn-nntp-response-block-rev-is-the-block
  (let ((acc (fn-nntp-response-block-rev bytes kind))
        (section (fn-nntp-section-of-bytes bytes kind)))
    (and (iff (equal acc :error)
              (not (and (fn-nntp-framed-of-bytes bytes)
                        (equal (car section) :ok))))
         (implies (not (equal acc :error))
                  (and (true-listp acc)
                       (equal (revappend acc '(46 13 10))
                              (append (fn-nntp-stuff-lines (car (cdr section)))
                                      '(46 13 10)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-blank-linep-is-split-okp)
                           (fn-nntp-block-rev fn-nntp-crlf-validp fn-nntp-crlf-lines
                            fn-nntp-stuff-lines fn-nntp-split-article
                            fn-nntp-section-rev fn-nntp-blank-linep))
           :cases ((equal kind :article))
           :use ((:instance fn-nntp-block-rev-is-the-block)
                 (:instance fn-nntp-section-rev-is-the-section)
                 (:instance fn-nntp-block-rev-true-listp (startp t) (acc nil))
                 (:instance fn-nntp-section-rev-true-listp)))))

; The equations restate the served machine's own functions; books that
; reason about those functions keep their theory (enable these by name).
(in-theory (disable fn-nntp-article-section-unfolds
                    fn-nntp-article-framedp-unfolds
                    fn-nntp-blank-linep-is-split-okp
                    fn-nntp-crlf-validp-is-crlf-lines-ok
                    fn-nntp-section-rev fn-nntp-section-validp fn-nntp-response-validp
                    fn-nntp-response-block-rev))
