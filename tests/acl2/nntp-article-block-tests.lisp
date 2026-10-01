; Teeth for the served ARTICLE's one-pass reply (lane gate-regress,
; 2026-09-27; books/nntp-article-block.lisp, books/nntp-reader-compat.lisp
; `fn-rcompat-article-reply-exec').  Reachable witnesses over the arena the
; reader-compat tests serve, and each keystone's hypothesis failing by name.
(in-package "ACL2")
(include-book "../../books/nntp-reader-compat")
(include-book "arena-lift")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-nabt-octets (s) (fn-nntp-string-octets s))

; A stored article with a dot-leading body line (stuffed) and an empty line.
(defconst *nabt-payload*
  (append (fn-nabt-octets "Message-ID: <nabt-a@example.invalid>") '(13 10)
          (fn-nabt-octets "Subject: A") '(13 10 13 10)
          (fn-nabt-octets ".hidden") '(13 10 13 10)
          (fn-nabt-octets "body") '(13 10)))
(defconst *nabt-stuffed-block*
  (append (fn-nabt-octets "Message-ID: <nabt-a@example.invalid>") '(13 10)
          (fn-nabt-octets "Subject: A") '(13 10 13 10)
          (fn-nabt-octets "..hidden") '(13 10 13 10)
          (fn-nabt-octets "body") '(13 10 46 13 10)))

; fn-nntp-block-rev-is-the-block, reachable: octets that frame, every
; literal of the conclusion asserted, and the block is the stuffed one.
(assert-event
 (let ((acc (fn-nntp-block-rev *nabt-payload* t nil))
       (r (fn-nntp-crlf-lines *nabt-payload*)))
   (and (fn-octet-listp *nabt-payload*)
        (equal (car r) :ok)
        (not (equal acc :error))
        (equal (revappend acc '(46 13 10))
               (append (fn-nntp-stuff-lines (car (cdr r))) '(46 13 10)))
        (equal (revappend acc '(46 13 10)) *nabt-stuffed-block*))))
; ... and its :error arm: a bare LF, both refuse.
(defconst *nabt-bare-lf* (append (fn-nabt-octets "a") '(10 13 10)))
(assert-event
 (and (fn-octet-listp *nabt-bare-lf*)
      (equal (fn-nntp-block-rev *nabt-bare-lf* t nil) :error)
      (not (equal (car (fn-nntp-crlf-lines *nabt-bare-lf*)) :ok))
      (not (fn-nntp-crlf-validp *nabt-bare-lf* t))))
; The hypothesis (fn-octet-listp) is needed: a non-octet line frames for the
; pass and not for fn-nntp-crlf-lines, so the iff fails, and with it
; fn-nntp-crlf-validp-is-crlf-lines-ok.
(defconst *nabt-not-octets* '(300 13 10))
(assert-event
 (let ((acc (fn-nntp-block-rev *nabt-not-octets* t nil))
       (r (fn-nntp-crlf-lines *nabt-not-octets*)))
   (and (not (fn-octet-listp *nabt-not-octets*))
        (not (iff (equal acc :error) (not (equal (car r) :ok))))
        (not (equal (fn-nntp-crlf-validp *nabt-not-octets* t)
                    (equal (car r) :ok))))))
(assert-event
 (equal (fn-nntp-crlf-validp *nabt-payload* t)
        (equal (car (fn-nntp-crlf-lines *nabt-payload*)) :ok)))
(assert-event (fn-nntp-crlf-validp *nabt-payload* t))

; fn-nntp-blank-linep-is-split-okp both ways.
(assert-event
 (and (fn-nntp-blank-linep *nabt-payload*)
      (fn-nntp-split-okp (fn-nntp-split-article *nabt-payload*))
      (not (fn-nntp-blank-linep *nabt-bare-lf*))
      (not (fn-nntp-split-okp (fn-nntp-split-article *nabt-bare-lf*)))))

; The served arena: handle 0 = the stored article above.
(defconst *nabt-arena* (list *nabt-payload*))
(defconst *nabt-a*
  (fn-make-article "<nabt-a@example.invalid>" 0
                   '("fn.one" "fn.two")
                   (list (cons "fn.one" 2) (cons "fn.two" 7))
                   t 841000000))
(defconst *nabt-session*
  (fn-nntp-make-session t nil nil t))
(defconst *nabt-server* (fn-nabt-octets "news.example.org"))
(bpr-lift fn-nntp-article-response 6)
(bpr-lift fn-nntp-article-bytes 1)
(bpr-lift fn-rcompat-article-reply 7)
(bpr-lift fn-rcompat-article-reply-exec 7)

; fn-nntp-article-response-is-of-bytes, reachable through the arena: a 220
; with the stuffed block, the cursor moved.
(assert-event
 (let ((r (in-arena-fn-nntp-article-response *nabt-arena* *nabt-session* *nabt-a*
                                             7 :article t "fn.two"))
       (bytes (in-arena-fn-nntp-article-bytes *nabt-arena* *nabt-a*)))
   (and (equal bytes *nabt-payload*)
        (equal r (fn-nntp-article-response-of-bytes *nabt-session* *nabt-a* bytes
                                                    7 :article t "fn.two"))
        (equal (fn-nntp-result-effects r)
               (list (fn-nntp-reply-effect
                      (append (fn-nabt-octets "220 7 <nabt-a@example.invalid> article follows")
                              '(13 10) *nabt-stuffed-block*))))
        (equal (fn-nntp-result-session r)
               (fn-nntp-set-cursor *nabt-session* "fn.two" 7)))))

; fn-nntp-response-of-bytes-session, both arms: answered (cursor moved) and
; refused framing (session unchanged).
(assert-event
 (and (fn-nntp-response-okp-of-bytes *nabt-a* *nabt-payload* :article)
      (equal (fn-nntp-result-session
              (fn-nntp-article-response-of-bytes *nabt-session* *nabt-a* *nabt-payload*
                                                 7 :article t "fn.two"))
             (fn-nntp-set-cursor *nabt-session* "fn.two" 7))
      (not (fn-nntp-response-okp-of-bytes *nabt-a* *nabt-bare-lf* :article))
      (equal (fn-nntp-article-response-of-bytes *nabt-session* *nabt-a* *nabt-bare-lf*
                                                7 :article t "fn.two")
             (fn-nntp-single *nabt-session* "503 stored article framing unavailable"))
      (equal (fn-nntp-result-session
              (fn-nntp-article-response-of-bytes *nabt-session* *nabt-a* *nabt-bare-lf*
                                                 7 :article t "fn.two"))
             *nabt-session*)))

; fn-rcompat-article-reply-exec-is-the-reply, reachable: the live arena, an
; article numbered here: the exec is the reply, a 220 whose block leads with
; this node's Xref line.
(assert-event
 (let ((exec (in-arena-fn-rcompat-article-reply-exec
              *nabt-arena* *nabt-session* *nabt-a* 7 :article t "fn.two" *nabt-server*))
       (spec (in-arena-fn-rcompat-article-reply
              *nabt-arena* *nabt-session* *nabt-a* 7 :article t "fn.two" *nabt-server*)))
   (and (equal exec spec)
        (equal (fn-nntp-result-effects exec)
               (list (fn-nntp-reply-effect
                      (append (fn-nabt-octets "220 7 <nabt-a@example.invalid> article follows")
                              '(13 10)
                              (fn-nabt-octets "Xref: news.example.org fn.one:2 fn.two:7")
                              '(13 10) *nabt-stuffed-block*))))
        (equal (fn-nntp-result-session exec)
               (fn-nntp-set-cursor *nabt-session* "fn.two" 7)))))
; ... and HEAD, the arm the exec leaves to the specification's section.
(assert-event
 (equal (in-arena-fn-rcompat-article-reply-exec
         *nabt-arena* *nabt-session* *nabt-a* 7 :head t "fn.two" *nabt-server*)
        (in-arena-fn-rcompat-article-reply
         *nabt-arena* *nabt-session* *nabt-a* 7 :head t "fn.two" *nabt-server*)))

; The hypothesis (fn-arena-p) is needed.  A value that is not an arena
; (a handle's slot holds a number, 1, and handle 1 an article) is read by the
; specification's served article as the article at handle 1, and by the
; exec as the number: the specification answers 220, the exec 503.
(defthm fn-nabt-reply-exec-needs-an-arena
  (let ((bad (list 1 *nabt-payload*))
        (a (fn-make-article "<nabt-a@example.invalid>" 0
                            '("fn.one" "fn.two")
                            (list (cons "fn.one" 2) (cons "fn.two" 7))
                            t 841000000)))
    (and (not (fn-arena-p bad))
         (equal (fn-nntp-result-effects
                 (fn-rcompat-article-reply-exec *nabt-session* a 7 :article nil "fn.two"
                                                *nabt-server* bad))
                (list (fn-nntp-reply-effect
                       (fn-nntp-crlf (fn-nabt-octets "503 stored article framing unavailable")))))
         (not (equal (fn-rcompat-article-reply-exec *nabt-session* a 7 :article nil "fn.two"
                                                    *nabt-server* bad)
                     (fn-rcompat-article-reply *nabt-session* a 7 :article nil "fn.two"
                                               *nabt-server* bad)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; PRF-334 (lane served-columns-body): HEAD and BODY from one split, and the
; retrieval's one read (fn-nntp-article-response's exec is the of-bytes
; reply over one fn-nntp-article-bytes).

(defconst *nabt-head-block*
  (append (fn-nabt-octets "Message-ID: <nabt-a@example.invalid>") '(13 10)
          (fn-nabt-octets "Subject: A") '(13 10 46 13 10)))
(defconst *nabt-body-block*
  (append (fn-nabt-octets "..hidden") '(13 10 13 10)
          (fn-nabt-octets "body") '(13 10 46 13 10)))

; fn-nntp-section-rev-is-the-section, reachable for HEAD and BODY: the
; hypothesis (kind is not :article) holds, the pass is not :error, the
; specification's reply is framed with a section, and the reversed pass is
; its block, byte for byte the expected one.
(assert-event
 (and (let* ((kind :head)
               (acc (fn-nntp-section-rev *nabt-payload* kind))
               (section (fn-nntp-section-of-bytes *nabt-payload* kind)))
          (and (not (equal kind :article))
               (not (equal acc :error))
               (fn-nntp-framed-of-bytes *nabt-payload*)
               (equal (car section) :ok)
               (equal (revappend acc '(46 13 10))
                      (append (fn-nntp-stuff-lines (car (cdr section))) '(46 13 10)))
               (equal (revappend acc '(46 13 10)) *nabt-head-block*)))
        (let* ((kind :body)
               (acc (fn-nntp-section-rev *nabt-payload* kind))
               (section (fn-nntp-section-of-bytes *nabt-payload* kind)))
          (and (not (equal acc :error))
               (fn-nntp-framed-of-bytes *nabt-payload*)
               (equal (car section) :ok)
               (equal (revappend acc '(46 13 10))
                      (append (fn-nntp-stuff-lines (car (cdr section))) '(46 13 10)))
               (equal (revappend acc '(46 13 10)) *nabt-body-block*)))))

; ... its :error arm: no separator (framed lines, no CRLFCRLF), and a bare LF.
(defconst *nabt-no-separator* (append (fn-nabt-octets "Subject: A") '(13 10)))
(assert-event
 (and (equal (fn-nntp-section-rev *nabt-no-separator* :head) :error)
      (not (fn-nntp-framed-of-bytes *nabt-no-separator*))
      (equal (fn-nntp-section-rev *nabt-bare-lf* :body) :error)
      (not (fn-nntp-framed-of-bytes *nabt-bare-lf*))))

; The hypothesis (kind is not :article) is needed: for :article the
; specification's section is the whole payload, the one-split pass is the
; body's block, so the equation fails (the pass is not :error and its block
; is not the article's).
(assert-event
 (let* ((acc (fn-nntp-section-rev *nabt-payload* :article))
        (section (fn-nntp-section-of-bytes *nabt-payload* :article)))
   (and (not (equal acc :error))
        (equal (car section) :ok)
        (not (equal (revappend acc '(46 13 10))
                    (append (fn-nntp-stuff-lines (car (cdr section))) '(46 13 10)))))))

; fn-nntp-response-validp-is-framed-section (no hypothesis), both values,
; every kind.
(assert-event
 (and (fn-nntp-response-validp *nabt-payload* :article)
      (fn-nntp-response-validp *nabt-payload* :head)
      (fn-nntp-response-validp *nabt-payload* :body)
      (fn-nntp-framed-of-bytes *nabt-payload*)
      (not (fn-nntp-response-validp *nabt-no-separator* :head))
      (not (fn-nntp-response-validp *nabt-no-separator* :article))
      (not (fn-nntp-framed-of-bytes *nabt-no-separator*))
      (not (fn-nntp-response-validp *nabt-bare-lf* :body))))

; fn-nntp-response-block-rev-is-the-block (no hypothesis), every kind.
(assert-event
 (and (equal (revappend (fn-nntp-response-block-rev *nabt-payload* :article) '(46 13 10))
             *nabt-stuffed-block*)
      (equal (revappend (fn-nntp-response-block-rev *nabt-payload* :head) '(46 13 10))
             *nabt-head-block*)
      (equal (revappend (fn-nntp-response-block-rev *nabt-payload* :body) '(46 13 10))
             *nabt-body-block*)
      (true-listp (fn-nntp-response-block-rev *nabt-payload* :body))
      (equal (fn-nntp-response-block-rev *nabt-bare-lf* :article) :error)
      (equal (fn-nntp-response-block-rev *nabt-not-octets* :head) :error)))

; fn-nntp-article-response-is-of-bytes through the arena for HEAD and BODY
; (the host's BODY arm, books/served-catalog.lisp fn-nntp-number-retrieval-cat,
; calls it): the reply the exec builds from one read is the specification's.
(assert-event
 (let ((h (in-arena-fn-nntp-article-response *nabt-arena* *nabt-session* *nabt-a*
                                             7 :head t "fn.two"))
       (b (in-arena-fn-nntp-article-response *nabt-arena* *nabt-session* *nabt-a*
                                             7 :body t "fn.two")))
   (and (equal h (fn-nntp-article-response-of-bytes *nabt-session* *nabt-a* *nabt-payload*
                                                    7 :head t "fn.two"))
        (equal (fn-nntp-result-effects h)
               (list (fn-nntp-reply-effect
                      (append (fn-nabt-octets "221 7 <nabt-a@example.invalid> headers follow")
                              '(13 10) *nabt-head-block*))))
        (equal (fn-nntp-result-effects b)
               (list (fn-nntp-reply-effect
                      (append (fn-nabt-octets "222 7 <nabt-a@example.invalid> body follows")
                              '(13 10) *nabt-body-block*))))
        (equal (fn-nntp-result-session b)
               (fn-nntp-set-cursor *nabt-session* "fn.two" 7)))))

; ... a reclaimed article (a tombstone at the handle): 423, session unchanged.
(defconst *nabt-tombstone* (append *fn-rcl-magic* (make-list 81 :initial-element 0)))
(assert-event
 (let ((r (in-arena-fn-nntp-article-response (list *nabt-tombstone*) *nabt-session* *nabt-a*
                                             7 :body t "fn.two")))
   (and (fn-rcl-tombstonep *nabt-tombstone*)
        (equal r (fn-nntp-single *nabt-session* "423 article reclaimed")))))

; ... a malformed payload (a bare LF): 503 for HEAD and BODY, session unchanged.
(assert-event
 (let ((h (in-arena-fn-nntp-article-response (list *nabt-bare-lf*) *nabt-session* *nabt-a*
                                             7 :head t "fn.two"))
       (b (in-arena-fn-nntp-article-response (list *nabt-no-separator*) *nabt-session* *nabt-a*
                                             7 :body t "fn.two")))
   (and (equal h (fn-nntp-single *nabt-session* "503 stored article framing unavailable"))
        (equal b (fn-nntp-single *nabt-session* "503 stored article framing unavailable")))))
