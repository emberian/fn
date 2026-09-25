; fn: the served withdrawal answers (packet C3, control-c3e).
;
; The subject is `fn-nntp-archive-command-pinned' (books/nntp.lisp), the
; pinned dispatcher every served read reaches: host/owner-host.lisp
; fn-owner-chunk -> fn-own-read (books/owner.lisp) -> fn-served-step ->
; fn-served-dispatch -> fn-auth-step-pinned -> fn-peer-step-pinned ->
; fn-nntp-post-step-pinned -> fn-nntp-step-pinned -> fn-nntp-command-pinned
; -> fn-nntp-archive-command-pinned (books/owner-control-read.lisp states the
; three answers over fn-own-read).  Its index argument is the group pin
; whose fourth slot is the connection's control pin (`fn-ctl-pin' W WS,
; books/control-served.lisp).  Over a pin whose W is the withdrawn list of
; the raw list RAW the served archive is the visible list of
; (`fn-own-control-okp', books/owner-invariants.lisp, carries exactly that
; for every owner connection), the three arms mean:
;
;   fn-nntp-423-withdrawn-is-a-withdrawn-holder     ARTICLE/HEAD/BODY/STAT n
;   fn-nntp-withdrawn-holder-answers-423-withdrawn  (and its converse)
;   fn-nntp-430-withdrawn-is-a-withdrawn-article    ... <msgid>
;   fn-nntp-withdrawn-article-answers-430-withdrawn (and its converse)
;   fn-nntp-hdr-fn-control-is-the-status            HDR :fn-control <msgid>
;   fn-nntp-hdr-fn-control-executed-means-withdrawn (with the kernel keystone)
;
; Prefix `fn-nctl-' for local lemmas (docs/prefixes.md).
(in-package "ACL2")
(include-book "nntp-pinned-msgid")

(defmacro fn-nctl-retrievalp (keyword)
  `(or (fn-nntp-keywordp ,keyword "ARTICLE")
       (fn-nntp-keywordp ,keyword "HEAD")
       (fn-nntp-keywordp ,keyword "BODY")
       (fn-nntp-keywordp ,keyword "STAT")))

; -----------------------------------------------------------------------------
; 423 withdrawn.

(defthm fn-nntp-number-withdrawn-p-answers
  (implies (and (fn-nctl-retrievalp keyword)
                (consp args) (null (cdr args))
                (fn-nntp-number-withdrawn-p session archive index (car args)))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)
                  (fn-nntp-single session "423 withdrawn")))
  :hints (("Goal" :in-theory (e/d (fn-nntp-archive-command-pinned fn-nntp-keywordp)
                                  (fn-nntp-single fn-nntp-upcase-keyword)))))

; KEYSTONE (423 withdrawn, sound).  The served answer to a retrieval by
; number is `423 withdrawn' only for a number the pinned archive does not
; hold and an article of RAW holds, which the view does not serve.
(defthm fn-nntp-423-withdrawn-is-a-withdrawn-holder
  (let* ((group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value token))
         (y (fn-ctl-number-withdrawn group number
                                     (fn-ctl-withdrawn-articles raw ws verdicts))))
    (implies (and (equal (fn-ctl-pin-withdrawn (fn-gidx-pin-control index))
                         (fn-ctl-withdrawn-articles raw ws verdicts))
                  (fn-nntp-number-withdrawn-p session archive index token))
             (and (member-equal y raw)
                  (not (member-equal y (fn-ctl-visible-articles raw ws verdicts)))
                  (equal (fn-nntp-membership-number group (fn-article-memberships y))
                         number)
                  (not (consp (fn-nntp-find-group-number
                               group number (fn-state-articles archive)))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-number-withdrawn-p)
                                  (fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                   fn-ctl-number-withdrawn-is-a-withdrawn-holder))
           :use ((:instance fn-ctl-number-withdrawn-is-a-withdrawn-holder
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-decimal-value token)))))))

; KEYSTONE (423 withdrawn, complete).  A number the pinned archive does not
; hold in the selected group, held there by an article of RAW the view does
; not serve, is answered `423 withdrawn'.
(defthm fn-nntp-withdrawn-holder-answers-423-withdrawn
  (let* ((group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value (car args))))
    (implies (and (equal (fn-ctl-pin-withdrawn (fn-gidx-pin-control index))
                         (fn-ctl-withdrawn-articles raw ws verdicts))
                  (fn-nctl-retrievalp keyword)
                  (consp args) (null (cdr args))
                  (fn-nntp-number-tokenp (car args))
                  group
                  (member-equal x raw) (consp x) (posp number)
                  (not (member-equal x (fn-ctl-visible-articles raw ws verdicts)))
                  (equal (fn-nntp-membership-number group (fn-article-memberships x))
                         number)
                  (not (consp (fn-nntp-find-group-number
                               group number (fn-state-articles archive)))))
             (equal (fn-nntp-archive-command-pinned
                     session archive index verdicts env keyword args)
                    (fn-nntp-single session "423 withdrawn"))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-number-withdrawn-p)
                                  (fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                   fn-nntp-single fn-nntp-archive-command-pinned
                                   fn-ctl-withdrawn-holder-is-found-by-number))
           :use ((:instance fn-ctl-withdrawn-holder-is-found-by-number
                            (group (fn-nntp-session-group session))
                            (number (fn-nntp-decimal-value (car args))))))))

; -----------------------------------------------------------------------------
; 430 withdrawn.

(defthm fn-nntp-msgid-withdrawn-p-answers
  (implies (and (fn-nctl-retrievalp keyword)
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args))
                (fn-nntp-msgid-withdrawn-p index (car args)))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)
                  (fn-nntp-single session "430 withdrawn")))
  :hints (("Goal" :in-theory (e/d (fn-nntp-archive-command-pinned fn-nntp-keywordp
                                   fn-nntp-number-withdrawn-p)
                                  (fn-nntp-single fn-nntp-upcase-keyword
                                   fn-nntp-message-id-tokenp)))))

(local
 (defthm fn-nctl-trie-lookup-is-find-article
   (implies (and (fn-midx-correspondencep trie articles)
                 (fn-nntp-message-id-tokenp token)
                 (fn-octet-listp token))
            (equal (fn-midx-lookup (fn-nntp-token-string token) trie)
                   (fn-find-article (fn-nntp-token-string token) articles)))
   :hints (("Goal" :in-theory (e/d (fn-midx-correspondencep)
                                   (fn-midx-lookup fn-midx-build fn-find-article
                                    fn-nntp-token-string fn-midx-key-chars
                                    fn-nntp-message-id-tokenp))))))

; KEYSTONE (430 withdrawn, sound).
(defthm fn-nntp-430-withdrawn-is-a-withdrawn-article
  (let* ((msgid (fn-nntp-token-string token))
         (y (fn-ctl-msgid-withdrawn msgid (fn-ctl-withdrawn-articles raw ws verdicts))))
    (implies (and (equal (fn-ctl-pin-withdrawn (fn-gidx-pin-control index))
                         (fn-ctl-withdrawn-articles raw ws verdicts))
                  (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                           (fn-state-articles archive))
                  (fn-nntp-message-id-tokenp token)
                  (fn-nntp-msgid-withdrawn-p index token))
             (and (member-equal y raw)
                  (not (member-equal y (fn-ctl-visible-articles raw ws verdicts)))
                  (equal (fn-article-msgid y) msgid)
                  (not (consp (fn-find-article msgid (fn-state-articles archive)))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-msgid-withdrawn-p)
                                  (fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                   fn-midx-correspondencep fn-midx-lookup
                                   fn-find-article fn-nntp-token-string
                                   fn-nntp-message-id-tokenp
                                   fn-ctl-msgid-withdrawn-is-a-withdrawn-article))
           :use ((:instance fn-ctl-msgid-withdrawn-is-a-withdrawn-article
                            (msgid (fn-nntp-token-string token)))
                 (:instance fn-nctl-trie-lookup-is-find-article
                            (trie (fn-gidx-pin-trie index))
                            (articles (fn-state-articles archive)))))))

; KEYSTONE (430 withdrawn, complete).
(defthm fn-nntp-withdrawn-article-answers-430-withdrawn
  (let ((msgid (fn-nntp-token-string (car args))))
    (implies (and (equal (fn-ctl-pin-withdrawn (fn-gidx-pin-control index))
                         (fn-ctl-withdrawn-articles raw ws verdicts))
                  (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                           (fn-state-articles archive))
                  (fn-nctl-retrievalp keyword)
                  (consp args) (null (cdr args))
                  (fn-nntp-message-id-tokenp (car args))
                  (fn-octet-listp (car args))
                  (member-equal x raw) (consp x)
                  (not (member-equal x (fn-ctl-visible-articles raw ws verdicts)))
                  (equal (fn-article-msgid x) msgid)
                  (not (consp (fn-find-article msgid (fn-state-articles archive)))))
             (equal (fn-nntp-archive-command-pinned
                     session archive index verdicts env keyword args)
                    (fn-nntp-single session "430 withdrawn"))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-msgid-withdrawn-p)
                                  (fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                   fn-midx-correspondencep fn-midx-lookup
                                   fn-find-article fn-nntp-token-string
                                   fn-nntp-message-id-tokenp fn-nntp-single
                                   fn-nntp-archive-command-pinned
                                   fn-ctl-withdrawn-article-is-found-by-msgid))
           :use ((:instance fn-ctl-withdrawn-article-is-found-by-msgid
                            (msgid (fn-nntp-token-string (car args))))
                 (:instance fn-nctl-trie-lookup-is-find-article
                            (token (car args))
                            (trie (fn-gidx-pin-trie index))
                            (articles (fn-state-articles archive)))))))

; -----------------------------------------------------------------------------
; HDR :fn-control.

; KEYSTONE (HDR :fn-control).  Over the trie of the served list, the reply
; to `HDR :fn-control <msgid>' is one line: 0 and the item of the kernel's
; status `fn-ctl-control-status' of the article C with that Message-ID,
; served or withdrawn (`fn-ctl-find-held'); 430 when there is none.
(defthm fn-nntp-hdr-fn-control-is-the-status
  (let* ((control (fn-gidx-pin-control index))
         (visible (fn-state-articles archive))
         (withdrawn (fn-ctl-pin-withdrawn control))
         (c (fn-ctl-find-held (fn-nntp-token-string (cadr args)) visible withdrawn)))
    (implies (and (fn-midx-correspondencep (fn-gidx-pin-trie index) visible)
                  (fn-nntp-keywordp keyword "HDR")
                  (consp args) (consp (cdr args)) (null (cddr args))
                  (fn-nntp-keywordp (car args) ":FN-CONTROL")
                  (fn-nntp-message-id-tokenp (cadr args))
                  (fn-octet-listp (cadr args)))
             (equal (fn-nntp-archive-command-pinned
                     session archive index verdicts env keyword args)
                    (if (consp c)
                        (fn-nntp-multi
                         session (fn-nntp-hdr-initial nil)
                         (list (fn-nntp-hdr-line
                                (fn-nntp-decimal-field 0)
                                (fn-nntp-string-octets
                                 (fn-ctl-control-item
                                  (fn-ctl-control-status c visible withdrawn
                                                         (fn-ctl-pin-ws control)
                                                         verdicts)
                                  (fn-ctl-target-octets (fn-article-payload c)))))))
                      (fn-nntp-single session "430 no article with that message-id")))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-archive-command-pinned fn-nntp-keywordp
                                   fn-nntp-control-hdr-response)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-upcase-keyword
                                   fn-ctl-control-item fn-ctl-control-status
                                   fn-ctl-served-status fn-ctl-served-held
                                   fn-ctl-find-held fn-midx-correspondencep
                                   fn-nntp-hdr-line fn-nntp-decimal-field
                                   fn-nntp-string-octets fn-ctl-target-octets
                                   fn-nntp-message-id-tokenp)))))

; KEYSTONE (HDR :fn-control, executed, over the served step).  When the
; pin's W is RAW's withdrawn list, the served list is RAW's visible list and
; WS the pinned records, an `executed' item names a target the view holds in
; RAW and does not serve, withdrawn by the record the article caused, on
; the stated basis (the kernel keystone `fn-ctl-executed-status-means-
; withdrawn' applied to the article the served reply names).
(defthm fn-nntp-hdr-fn-control-executed-means-withdrawn
  (let* ((visible (fn-ctl-visible-articles raw ws verdicts))
         (withdrawn (fn-ctl-withdrawn-articles raw ws verdicts))
         (c (fn-ctl-find-held m visible withdrawn))
         (st (fn-ctl-control-status c visible withdrawn ws verdicts))
         (target (fn-ctl-target-octets (fn-article-payload c)))
         (held (fn-ctl-find-held target visible withdrawn))
         (rec (fn-ctl-cause-record ws (fn-article-msgid c) target)))
    (implies (and (consp c) (equal (car st) :executed))
             (and (member-equal c raw)
                  (member-equal held raw)
                  (not (member-equal held visible))
                  (equal (fn-article-msgid held) target)
                  (member-equal rec ws)
                  (equal (fn-ctl-w-cause rec) (fn-article-msgid c))
                  (fn-ctl-effect-withdrawsp (cadr st)))))
  :hints (("Goal" :in-theory (disable fn-ctl-find-held fn-ctl-control-status
                                      fn-ctl-visible-articles fn-ctl-withdrawn-articles
                                      fn-ctl-target-octets fn-ctl-cause-record
                                      fn-ctl-effect-withdrawsp fn-ctl-w-cause
                                      fn-ctl-withdrawal-effect
                                      fn-ctl-executed-status-means-withdrawn)
           :use ((:instance fn-ctl-find-held-is-in-raw)
                 (:instance fn-ctl-executed-status-means-withdrawn
                            (c (fn-ctl-find-held m (fn-ctl-visible-articles raw ws verdicts)
                                                 (fn-ctl-withdrawn-articles raw ws verdicts))))))))
