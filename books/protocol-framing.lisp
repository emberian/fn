; The protocol table's :framing column, proved of the reader dispatcher
; (lane defprotocol; books/protocol-table.lisp).
;
; A command whose row says :framing :command never hands the connection to
; article mode: fn-nntp-command-pinned's effects carry no
; (fn-nntp-begin-article-effect) for it.  The case split is the table's:
; one generated theorem per reader row whose framing is :command, one for
; the unrecognized and the syntax pseudo-rows, and the keystone
; fn-proto-command-pinned-offers-only-article-framing is their union.  A new
; dispatcher arm that offers an article fails its row's theorem until the row
; says :article -- the property books/nntp-auth-fold.lisp's
; fn-auth-fold-command-pinned-offers-only-post states for POST, which broke
; silently on XFNCATCHUP (batch AY cite round 4) because nothing named the
; arms it had to cover.
;
; Subject: fn-nntp-command-pinned, as in books/protocol-codes.lisp.

(in-package "ACL2")
(include-book "nntp-auth-fold")
(include-book "protocol-codes")

; The rows whose replies may hand the connection to article mode.
(defun fn-proto-article-framing-p (keyword names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (and (stringp (car names)) (fn-nntp-keywordp keyword (car names)))
          (fn-proto-article-framing-p keyword (cdr names)))
    nil))

(defun fn-proto-command-framed-names (alist article)
  (declare (xargs :guard (true-listp article)))
  (if (consp alist)
      (if (and (consp (car alist)) (not (member-equal (car (car alist)) article)))
          (cons (car (car alist)) (fn-proto-command-framed-names (cdr alist) article))
        (fn-proto-command-framed-names (cdr alist) article))
    nil))

(defconst *fn-proto-dispatch-offer-theory*
  '(fn-nntp-command-pinned fn-nntp-archive-keywordp))

(defun fn-proto-framing-events (names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons
       `(defthm ,(fn-proto-row-thm-name (if (stringp (car names)) (car names) "") "-FRAMING")
          (implies (fn-nntp-keywordp (car tokens) ,(car names))
                   (not (fn-post-offeredp
                         (fn-nntp-result-effects
                          (fn-nntp-command-pinned session archive index verdicts
                                                  env tokens fn-arena)))))
          :hints (("Goal"
                   :use ((:instance fn-auth-fold-session-command-offers-only-post
                                    (keyword (car tokens)) (args (cdr tokens))))
                   :in-theory (e/d ,*fn-proto-dispatch-offer-theory*
                                   (fn-auth-fold-command-pinned-offers-only-post
                                    fn-nntp-session-command
                                    fn-nntp-archive-command-pinned fn-post-offeredp
                                    fn-cu-serve-reply fn-zar-command
                                    ,@*fn-proto-token-theory*)))))
       (fn-proto-framing-events (cdr names)))
    nil))

(make-event
 (cons 'progn
       (fn-proto-framing-events
        (fn-proto-command-framed-names *fn-proto-reader-alist*
                                       *fn-proto-article-framing*))))

(defun fn-proto-name-cases (names term)
  (declare (xargs :guard t))
  (if (consp names)
      (cons `(fn-nntp-keywordp ,term ,(car names))
            (fn-proto-name-cases (cdr names) term))
    nil))

; The unrecognized and syntax pseudo-rows: a first token no reader row
; names is answered 500 or 501, which offer nothing.
(make-event
 `(defthm fn-proto-row-unrecognized-framing
    (implies (and ,@(fn-proto-not-any-row *fn-proto-reader-alist* '(car tokens)))
             (not (fn-post-offeredp
                   (fn-nntp-result-effects
                    (fn-nntp-command-pinned session archive index verdicts
                                            env tokens fn-arena)))))
    :hints (("Goal"
             :use ((:instance fn-auth-fold-session-command-offers-only-post
                              (keyword (car tokens)) (args (cdr tokens))))
             :in-theory (e/d ,*fn-proto-dispatch-offer-theory*
                             (fn-auth-fold-command-pinned-offers-only-post
                              fn-nntp-session-command
                              fn-nntp-archive-command-pinned fn-post-offeredp
                              fn-cu-serve-reply fn-zar-command
                              ,@*fn-proto-token-theory*))))))

(make-event
 `(local (defthm fn-proto-command-pinned-offers-only-article-framing-by-rows
    (implies (not (fn-proto-article-framing-p (car tokens) *fn-proto-article-framing*))
             (not (fn-post-offeredp
                   (fn-nntp-result-effects
                    (fn-nntp-command-pinned session archive index verdicts
                                            env tokens fn-arena)))))
    :hints (("Goal"
             :cases (,@(fn-proto-name-cases *fn-proto-article-framing* '(car tokens))
                     ,@(fn-proto-name-cases
                        (fn-proto-command-framed-names *fn-proto-reader-alist*
                                                       *fn-proto-article-framing*)
                        '(car tokens)))
             :in-theory (disable fn-nntp-command-pinned
                                 fn-auth-fold-command-pinned-offers-only-post
                                 ,@*fn-proto-token-theory*))))))

(defthm fn-proto-command-pinned-offers-only-article-framing
  (implies (not (fn-proto-article-framing-p (car tokens) *fn-proto-article-framing*))
           (not (fn-post-offeredp
                 (fn-nntp-result-effects
                  (fn-nntp-command-pinned session archive index verdicts
                                          env tokens fn-arena)))))
  :hints (("Goal" :by fn-proto-command-pinned-offers-only-article-framing-by-rows)))

; The table has one :article row, POST, so the keystone is
; fn-auth-fold-command-pinned-offers-only-post's statement read off the table.
(defthm fn-proto-article-framing-is-post
  (iff (fn-proto-article-framing-p keyword *fn-proto-article-framing*)
       (fn-nntp-keywordp keyword "POST"))
  :hints (("Goal" :in-theory (disable fn-nntp-keywordp))))

; fn-auth-fold-command-pinned-offers-only-post, from the table and not from
; its own arm-by-arm proof: the table's :article rows are POST alone.
(defthm fn-proto-offers-only-post-by-table
  (implies (not (fn-nntp-keywordp (car tokens) "POST"))
           (not (fn-post-offeredp
                 (fn-nntp-result-effects
                  (fn-nntp-command-pinned session archive index verdicts
                                          env tokens fn-arena)))))
  :hints (("Goal" :use ((:instance fn-proto-command-pinned-offers-only-article-framing)
                        (:instance fn-proto-article-framing-is-post
                                   (keyword (car tokens))))
           :in-theory (disable fn-auth-fold-command-pinned-offers-only-post
                               fn-proto-command-pinned-offers-only-article-framing
                               fn-proto-article-framing-is-post
                               fn-nntp-command-pinned fn-post-offeredp
                               fn-proto-article-framing-p fn-nntp-keywordp))))
