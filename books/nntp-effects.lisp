; Effect-shape facts for the experimental fn NNTP reader.
(in-package "ACL2")
(include-book "nntp")

; A reply is a proper octet sequence; close has no payload.  This is the
; concrete effect vocabulary emitted by books/nntp.lisp, not a new protocol
; event representation.
(defun fn-nntp-effectp (effect)
  (or (and (true-listp effect)
           (equal (len effect) 2)
           (equal (car effect) :reply)
           (fn-octet-listp (car (cdr effect))))
      (equal effect (fn-nntp-close-effect))))

(defun fn-nntp-effectsp (effects)
  (if (consp effects)
      (and (fn-nntp-effectp (car effects))
           (fn-nntp-effectsp (cdr effects)))
    (null effects)))

; Keep byte rendering facts below the response constructors.  Exposing the
; complete command parser while proving these facts creates a large, irrelevant
; case split over token syntax.
(defthm fn-nntp-effects-octet-listp-append
  (implies (and (fn-octet-listp x)
                (fn-octet-listp y))
           (fn-octet-listp (append x y))))

(defthm fn-nntp-effects-octet-listp-revappend
  (implies (and (fn-octet-listp x)
                (fn-octet-listp accumulator))
           (fn-octet-listp (revappend x accumulator))))

(defthm fn-nntp-effects-octet-listp-reverse
  (implies (fn-octet-listp x)
           (fn-octet-listp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm fn-nntp-effects-string-octets-aux
  (implies (character-listp chars)
           (fn-octet-listp (fn-nntp-string-octets-aux chars))))

(defthm fn-nntp-effects-string-octets
  (fn-octet-listp (fn-nntp-string-octets text))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets))))

(defthm fn-nntp-effects-decimal-characters-aux
  (implies (and (natp number)
                (character-listp accumulator))
           (character-listp
            (explode-nonnegative-integer number 10 accumulator))))

(defthm fn-nntp-effects-decimal-characters
  (implies (natp number)
           (character-listp (explode-nonnegative-integer number 10 nil))))

(defthm fn-nntp-effects-decimal-rev-octets
  (implies (natp number)
           (fn-octet-listp (fn-nntp-decimal-rev number)))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-rev)
                   :use ((:instance fn-nntp-effects-string-octets-aux
                                    (chars (explode-nonnegative-integer
                                            number 10 nil)))))))

(defthm fn-nntp-effects-decimal-octets
  (fn-octet-listp (fn-nntp-decimal number))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal))))

(defthm fn-nntp-effects-crlf-octets
  (implies (fn-octet-listp line)
           (fn-octet-listp (fn-nntp-crlf line)))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf))))

(defthm fn-nntp-effects-wire-stuff-line-octets
  (implies (fn-octet-listp line)
           (fn-octet-listp (fn-wire-stuff-line line)))
  :hints (("Goal" :in-theory (enable fn-wire-stuff-line))))

(defun fn-nntp-octet-linesp (lines)
  (if (consp lines)
      (and (fn-octet-listp (car lines))
           (fn-nntp-octet-linesp (cdr lines)))
    (null lines)))

(defthm fn-nntp-effects-octet-linesp-revappend
  (implies (and (fn-nntp-octet-linesp x)
                (fn-nntp-octet-linesp accumulator))
           (fn-nntp-octet-linesp (revappend x accumulator))))

(defthm fn-nntp-effects-octet-linesp-reverse
  (implies (fn-nntp-octet-linesp x)
           (fn-nntp-octet-linesp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm fn-nntp-effects-stuff-lines-octets
  (implies (fn-nntp-octet-linesp lines)
           (fn-octet-listp (fn-nntp-stuff-lines lines)))
  :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-reply-effect
  (implies (fn-octet-listp octets)
           (fn-nntp-effectp (fn-nntp-reply-effect octets)))
  :hints (("Goal" :in-theory (enable fn-nntp-effectp
                                      fn-nntp-reply-effect))))

(defthm fn-nntp-effects-of-make-result
  (equal (fn-nntp-result-effects (fn-nntp-make-result session effects))
         effects))

(defthm fn-nntp-effects-single
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-single session text)))
  :hints (("Goal" :in-theory (enable fn-nntp-single
                                      fn-nntp-effectsp))))

(defthm fn-nntp-effects-multi
  (implies (fn-nntp-octet-linesp lines)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-multi session initial lines))))
  :hints (("Goal" :in-theory (enable fn-nntp-multi
                                      fn-nntp-effectsp))))

(defthm fn-nntp-effects-multi-octets
  (implies (and (fn-octet-listp initial)
                (fn-nntp-octet-linesp lines))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-multi-octets session initial lines))))
  :hints (("Goal" :in-theory (enable fn-nntp-multi-octets
                                      fn-nntp-effectsp))))

(defthm fn-nntp-effects-append-pieces-octets
  (implies (fn-nntp-octet-linesp pieces)
           (fn-octet-listp (fn-nntp-append-pieces pieces)))
  :hints (("Goal" :in-theory (enable fn-nntp-append-pieces
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-number-lines-octets
  (fn-nntp-octet-linesp (fn-nntp-number-lines numbers))
  :hints (("Goal" :in-theory (enable fn-nntp-number-lines
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-group-initial-octets
  (fn-octet-listp (fn-nntp-group-initial archive group))
  :hints (("Goal" :in-theory (enable fn-nntp-group-initial
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-listgroup-initial-octets
  (fn-octet-listp (fn-nntp-listgroup-initial archive group))
  :hints (("Goal" :in-theory (enable fn-nntp-listgroup-initial))))

(defthm fn-nntp-effects-retrieval-initial-octets
  (fn-octet-listp (fn-nntp-retrieval-initial kind number article))
  :hints (("Goal" :in-theory (enable fn-nntp-retrieval-initial
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-active-line-octets
  (fn-octet-listp (fn-nntp-active-line archive group))
  :hints (("Goal" :in-theory (enable fn-nntp-active-line
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-active-lines-octets
  (fn-nntp-octet-linesp (fn-nntp-active-lines archive groups))
  :hints (("Goal" :in-theory (e/d (fn-nntp-active-lines
                                     fn-nntp-octet-linesp)
                                    (fn-nntp-active-line)))))

(defthm fn-nntp-effects-newsgroup-lines-octets
  (fn-nntp-octet-linesp (fn-nntp-newsgroup-lines groups))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-newsgroup-lines fn-nntp-octet-linesp)
                (fn-nntp-append-pieces fn-nntp-string-octets)))))

(defthm fn-nntp-effects-crlf-lines-aux-octets
  (implies (and (fn-octet-listp bytes)
                (fn-octet-listp line-rev)
                (fn-nntp-octet-linesp lines-rev)
                (equal (car (fn-nntp-crlf-lines-aux
                             bytes line-rev lines-rev)) :ok))
           (fn-nntp-octet-linesp
            (car (cdr (fn-nntp-crlf-lines-aux
                       bytes line-rev lines-rev)))))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-lines-aux
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-crlf-lines-octets
  (implies (equal (car (fn-nntp-crlf-lines bytes)) :ok)
           (fn-nntp-octet-linesp
            (car (cdr (fn-nntp-crlf-lines bytes)))))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-lines))))

(defthm fn-nntp-effects-article-section-octets
  (implies (and (fn-nntp-projection-articlep article)
                (equal (car (fn-nntp-article-section article kind)) :ok))
           (fn-nntp-octet-linesp
            (car (cdr (fn-nntp-article-section article kind)))))
  :hints (("Goal" :in-theory (enable fn-nntp-article-section
                                      fn-nntp-projection-articlep))))

; From here on response constructors are opaque except for the one constructor
; currently being composed.  Their effect theorems above and below are the
; interface; expanding their byte renderers recreates the parser-wide split
; that this book is intended to avoid.
(in-theory (disable fn-nntp-result-effects
                    fn-nntp-make-result fn-nntp-reply-effect
                    fn-nntp-single fn-nntp-multi fn-nntp-multi-octets
                    fn-nntp-group-result fn-nntp-listgroup-result
                    fn-nntp-article-response
                    fn-nntp-list-active fn-nntp-list-newsgroups))

(defthm fn-nntp-effects-group-result
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-group-result session archive group)))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-group-result fn-nntp-effectsp)
                (fn-nntp-reply-effect fn-nntp-crlf
                 fn-nntp-group-initial fn-nntp-set-cursor
                 fn-nntp-make-result)))))

(defthm fn-nntp-effects-listgroup-result
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-listgroup-result session archive group range)))
  :hints (("Goal" :in-theory (enable fn-nntp-listgroup-result))))

(defthm fn-nntp-effects-listgroup-command
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-listgroup-command session archive args)))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-listgroup-command)
                (fn-nntp-listgroup-result fn-nntp-single
                 fn-nntp-parse-range fn-nntp-token-string
                 fn-nntp-result-effects)))))

(defthm fn-nntp-effects-article-response
  (implies (fn-nntp-projection-articlep article)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-article-response session article number kind updatep group))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-article-response fn-nntp-effectsp)
                (fn-nntp-retrieval-initial
                 fn-nntp-article-section
                 fn-nntp-stuff-lines
                 fn-nntp-crlf
                 fn-nntp-decimal
                 fn-nntp-string-octets)))))

(defthm fn-nntp-effects-article-response-stat
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-article-response session article number :stat updatep group)))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-article-response fn-nntp-effectsp)
                (fn-nntp-make-result fn-nntp-result-effects
                 fn-nntp-reply-effect fn-nntp-crlf
                 fn-nntp-retrieval-initial)))))

(defthm fn-nntp-effects-find-group-number-projection
  (implies (and (fn-nntp-projection-articlesp articles)
                (consp (fn-nntp-find-group-number group number articles)))
           (fn-nntp-projection-articlep
            (fn-nntp-find-group-number group number articles)))
  :hints (("Goal" :in-theory (enable fn-nntp-find-group-number
                                      fn-nntp-projection-articlesp))))

(defthm fn-nntp-effects-find-article-projection
  (implies (and (fn-nntp-projection-articlesp articles)
                (consp (fn-find-article msgid articles)))
           (fn-nntp-projection-articlep (fn-find-article msgid articles)))
  :hints (("Goal" :in-theory (enable fn-find-article
                                      fn-nntp-projection-articlesp))))

(defthm fn-nntp-effects-current-retrieval
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-current-retrieval session archive kind))))
  :hints (("Goal" :in-theory (enable fn-nntp-current-retrieval))))

(defthm fn-nntp-effects-number-retrieval
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-number-retrieval session archive kind token))))
  :hints (("Goal" :in-theory (enable fn-nntp-number-retrieval))))

(defthm fn-nntp-effects-msgid-retrieval
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-msgid-retrieval session archive kind token))))
  :hints (("Goal" :in-theory (enable fn-nntp-msgid-retrieval))))

(defthm fn-nntp-effects-retrieval
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-retrieval session archive kind args))))
  :hints (("Goal" :in-theory (enable fn-nntp-retrieval))))

(defthm fn-nntp-effects-next-or-last
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-next-or-last session archive direction))))
  :hints (("Goal" :in-theory (enable fn-nntp-next-or-last))))

(defthm fn-nntp-effects-list-active
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-list-active session archive groups)))
  :hints (("Goal" :in-theory (enable fn-nntp-list-active))))

(defthm fn-nntp-effects-list-newsgroups
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-list-newsgroups session groups)))
  :hints (("Goal" :in-theory (enable fn-nntp-list-newsgroups))))

(defthm fn-nntp-effects-list-filtered-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-list-filtered-response session archive kind wildmat)))
  :hints (("Goal" :in-theory (enable fn-nntp-list-filtered-response))))

(defthm fn-nntp-effects-list-active-or-newsgroups
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-list-active-or-newsgroups session archive kind args)))
  :hints (("Goal" :in-theory (enable fn-nntp-list-active-or-newsgroups))))

(defthm fn-nntp-effects-list-unmaintained-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-list-unmaintained-response session keyword args)))
  :hints (("Goal" :in-theory (enable fn-nntp-list-unmaintained-response))))

(defthm fn-nntp-effects-list-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-list-response session archive args)))
  :hints (("Goal" :in-theory (enable fn-nntp-list-response))))

(defthm fn-nntp-effects-capabilities
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-capabilities session)))
  :hints (("Goal" :in-theory (enable fn-nntp-capabilities
                                      fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-help
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-help session)))
  :hints (("Goal" :in-theory (enable fn-nntp-help
                                      fn-nntp-octet-linesp))))

(in-theory (disable fn-nntp-listgroup-command
                    fn-nntp-current-retrieval
                    fn-nntp-number-retrieval
                    fn-nntp-msgid-retrieval
                    fn-nntp-retrieval fn-nntp-next-or-last
                    fn-nntp-list-filtered-response
                    fn-nntp-list-active-or-newsgroups
                    fn-nntp-list-unmaintained-response
                    fn-nntp-list-response
                    fn-nntp-capabilities fn-nntp-help))

(defthm fn-nntp-effects-close-effect
  (fn-nntp-effectp (fn-nntp-close-effect))
  :hints (("Goal" :in-theory (enable fn-nntp-effectp
                                      fn-nntp-close-effect))))

(defthm fn-nntp-command-effects-well-formed
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-command session archive tokens))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-command fn-nntp-effectsp)
                (fn-nntp-result-effects fn-nntp-make-result
                 fn-nntp-reply-effect fn-nntp-close-effect
                 fn-nntp-single fn-nntp-group-result
                 fn-nntp-listgroup-command fn-nntp-list-response
                 fn-nntp-next-or-last fn-nntp-retrieval
                 fn-nntp-capabilities fn-nntp-help
                 fn-nntp-crlf fn-nntp-string-octets)))))

(defthm fn-nntp-step-effects-well-formed
  (implies (and (fn-nntp-sessionp session)
                (fn-nntp-projectionp archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-step session archive wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-step)
                (fn-nntp-result-effects fn-nntp-make-result
                 fn-nntp-single fn-nntp-command)))))

(defthm fn-nntp-close-effect-is-well-formed
  (fn-nntp-effectp (fn-nntp-close-effect))
  :hints (("Goal" :in-theory (enable fn-nntp-effectp fn-nntp-close-effect))))

(defthm fn-nntp-closed-step-has-no-effects
  (implies (or (not (fn-nntp-sessionp session))
               (not (equal (fn-nntp-session-openp session) t)))
           (equal (fn-nntp-result-effects (fn-nntp-step session archive wire-event))
                  nil))
  :hints (("Goal" :in-theory (enable fn-nntp-step))))

(defthm fn-nntp-closed-step-effects-well-formed
  (implies (or (not (fn-nntp-sessionp session))
               (not (equal (fn-nntp-session-openp session) t)))
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-step session archive wire-event))))
  :hints (("Goal" :use fn-nntp-closed-step-has-no-effects)))

(defthm fn-nntp-quit-step-effects-well-formed
  (implies (and (fn-nntp-sessionp session)
                (equal (fn-nntp-session-openp session) t)
                (fn-nntp-projectionp archive))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-step session archive '(:command (81 85 73 84))))))
  :hints (("Goal" :in-theory (enable fn-nntp-step
                                      fn-nntp-command
                                      fn-nntp-effectsp
                                      fn-nntp-effectp
                                      fn-nntp-reply-effect
                                      fn-nntp-close-effect))))
