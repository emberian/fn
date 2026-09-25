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

; ---------------------------------------------------------------------------
; HDR :fn-control (control-message design 2026-09-25 section 4), spike.
; SPIKE: defers the dev owner of the control items (a Store record family
; read at refresh, books/owner.lisp fn-own-refresh); on the spike the host
; places each item in the pinned verdict list under the key
; (:fn-control . MSGID), which no Message-ID string equals, so HDR
; :fn-verified never sees it (host/owner-host.lisp fn-owner-ctl-filter).
; Like :fn-verified the item is the node's historical claim.
(defconst *fn-nntp-control-none* '(110 111 110 101))  ; "none"

(defun fn-nntp-control-item (msgid verdicts)
  (declare (xargs :guard t))
  (let ((item (fn-stx-reader-lookup (cons :fn-control msgid) verdicts)))
    (if (and (consp item) (fn-stx-printablep item)) item
      *fn-nntp-control-none*)))

(defun fn-nntp-control-hdr-lines (group numbers articles verdicts)
  (declare (xargs :guard t))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-nntp-available-article group number articles)))
        (if (consp article)
            (cons (fn-nntp-hdr-line
                   (fn-nntp-decimal-field number)
                   (fn-nntp-control-item (fn-article-msgid article) verdicts))
                  (fn-nntp-control-hdr-lines group (cdr numbers)
                                             articles verdicts))
          (fn-nntp-control-hdr-lines group (cdr numbers) articles verdicts)))
    nil))

(defun fn-nntp-control-hdr-response (session archive verdicts args)
  (declare (xargs :guard t))
  (let ((rest (if (consp args) (cdr args) nil)))
    (if (not (and (consp rest) (null (cdr rest))))
        (fn-nntp-single session "501 syntax error")
      (let ((token (car rest)))
        (cond
         ((fn-nntp-range-okp (fn-nntp-parse-range token))
          (let ((group (fn-nntp-session-group session))
                (range (fn-nntp-parse-range token)))
            (if (null group)
                (fn-nntp-single session "412 no newsgroup selected")
              (let* ((numbers (fn-nntp-group-range-numbers
                               group (fn-nntp-range-low range)
                               (fn-nntp-range-high range)
                               (fn-state-articles archive)))
                     (lines (fn-nntp-control-hdr-lines
                             group numbers (fn-state-articles archive)
                             verdicts)))
                (if (consp lines)
                    (fn-nntp-multi session (fn-nntp-hdr-initial nil) lines)
                  (fn-nntp-single session "423 no articles in that range"))))))
         ((fn-nntp-message-id-tokenp token)
          (let ((article (fn-find-article (fn-nntp-token-string token)
                                          (fn-state-articles archive))))
            (if (not (consp article))
                (fn-nntp-single session "430 no article with that message-id")
              (fn-nntp-multi
               session (fn-nntp-hdr-initial nil)
               (list (fn-nntp-hdr-line
                      (fn-nntp-decimal-field 0)
                      (fn-nntp-control-item (fn-article-msgid article)
                                            verdicts)))))))
         (t (fn-nntp-single session "501 syntax error")))))))

(defthm fn-nntp-control-hdr-response-keeps-session
  (equal (fn-nntp-result-session
          (fn-nntp-control-hdr-response session archive verdicts args))
         session)
  :hints (("Goal" :in-theory (enable fn-nntp-single fn-nntp-multi
                                     fn-nntp-make-result
                                     fn-nntp-result-session))))

(defthm fn-nntp-control-item-is-printable
  (fn-stx-printablep (fn-nntp-control-item msgid verdicts)))

(in-theory (disable fn-nntp-control-hdr-response fn-nntp-control-item))
