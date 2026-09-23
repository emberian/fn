; RFC 3977 HDR :fn-verified, over the verdict list pinned with this reader's
; accepted archive.  It never asks a current keyring to reverify an article.
(in-package "ACL2")
(include-book "nntp-responses")
(include-book "stx-reader")

(defun fn-nntp-verdict-hdr-lines (group numbers articles verdicts)
  (declare (xargs :guard t))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-nntp-available-article group number articles)))
        (if (consp article)
            (cons (fn-nntp-hdr-line
                   (fn-nntp-decimal-field number)
                   (fn-stx-reader-verdict (fn-article-msgid article) verdicts))
                  (fn-nntp-verdict-hdr-lines group (cdr numbers)
                                             articles verdicts))
          (fn-nntp-verdict-hdr-lines group (cdr numbers) articles verdicts)))
    nil))

(defun fn-nntp-verdict-hdr-current (session archive verdicts)
  (declare (xargs :guard t))
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-nntp-available-article
                        group current (fn-state-articles archive))))
          (if (not (consp article))
              (fn-nntp-single session "420 no current article")
            (fn-nntp-multi
             session (fn-nntp-hdr-initial nil)
             (list (fn-nntp-hdr-line
                    (fn-nntp-decimal-field current)
                    (fn-stx-reader-verdict (fn-article-msgid article)
                                           verdicts))))))))))

(defun fn-nntp-verdict-hdr-range (session archive verdicts token)
  (declare (xargs :guard t))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((numbers (fn-nntp-group-range-numbers
                       group (fn-nntp-range-low range)
                       (fn-nntp-range-high range) (fn-state-articles archive)))
             (lines (fn-nntp-verdict-hdr-lines
                     group numbers (fn-state-articles archive) verdicts)))
        (if (consp lines)
            (fn-nntp-multi session (fn-nntp-hdr-initial nil) lines)
          (fn-nntp-single session "423 no articles in that range"))))))

(defun fn-nntp-verdict-hdr-msgid (session archive verdicts token)
  (declare (xargs :guard t))
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (if (not (consp article))
        (fn-nntp-single session "430 no article with that message-id")
      (fn-nntp-multi
       session (fn-nntp-hdr-initial nil)
       (list (fn-nntp-hdr-line
              (fn-nntp-decimal-field 0)
              (fn-stx-reader-verdict (fn-article-msgid article) verdicts)))))))

(defun fn-nntp-verdict-hdr-response (session archive verdicts args)
  (declare (xargs :guard t))
  (if (not (and (consp args)
                (fn-nntp-keywordp (car args) ":FN-VERIFIED")))
      (fn-nntp-single session "501 syntax error")
    (let ((rest (cdr args)))
      (if (null rest)
          (fn-nntp-verdict-hdr-current session archive verdicts)
        (if (and (consp rest) (null (cdr rest)))
            (let ((token (car rest)))
              (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                  (fn-nntp-verdict-hdr-range session archive verdicts token)
                (if (fn-nntp-message-id-tokenp token)
                    (fn-nntp-verdict-hdr-msgid session archive verdicts token)
                  (fn-nntp-single session "501 syntax error"))))
          (fn-nntp-single session "501 syntax error"))))))

; The Message-ID arm is the composition's key statement: the content is
; selected from the pinned list, not computed from a keyring or current Store.
(defthm fn-nntp-verdict-hdr-msgid-is-recorded
  (implies (consp (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive)))
           (equal
            (fn-nntp-result-effects
             (fn-nntp-verdict-hdr-msgid session archive verdicts token))
            (fn-nntp-result-effects
             (fn-nntp-multi
              session (fn-nntp-hdr-initial nil)
              (list (fn-nntp-hdr-line
                     (fn-nntp-decimal-field 0)
                     (fn-stx-reader-item
                      (fn-stx-reader-lookup
                       (fn-article-msgid
                        (fn-find-article (fn-nntp-token-string token)
                                         (fn-state-articles archive)))
                       verdicts))))))))
  :hints (("Goal" :in-theory (enable fn-nntp-verdict-hdr-msgid
                                      fn-stx-reader-verdict))))

(defthm fn-nntp-verdict-hdr-response-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-verdict-hdr-response session archive verdicts args))
         session)
  :hints (("Goal" :in-theory (enable fn-nntp-single fn-nntp-multi
                                      fn-nntp-make-result fn-nntp-result-session
                                      fn-nntp-verdict-hdr-response
                                      fn-nntp-verdict-hdr-current
                                      fn-nntp-verdict-hdr-range
                                      fn-nntp-verdict-hdr-msgid))))
