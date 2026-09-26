; fn: what the Injection-Info parameters do to an injected article
; (PKT-597; the definitions are books/injection-info-params.lisp).
;
; Proved here, over fn-ipp-with-params (called by fn-ipp-stored-octets,
; which books/owner-served-invariants.lisp fn-own-sub-stored-octets-keyed
; calls for every local submission the owner stages; host/owner-host.lisp
; fn-owner-take stages that value and fn-owner-finish-submission compares
; the completed record with it):
;   * `fn-ipp-with-params-of-an-injection': with parameters, an injected
;     article is its injected block with the Injection-Info line carrying
;     them, followed by the source (the same block, the same place, the same
;     source octets): exactly one Injection-Info, since the proto-article
;     check refuses a source that carries one (books/article-fields.lisp
;     fn-af-proto-article-check, :injection-info).
;   * `fn-ipp-with-params-keeps-the-source': the injection inverse still
;     gives back the source (books/injection.lisp fn-inj-source-of reads
;     the line through fn-inj-strip-info), so D25's comparison and the
;     operator's retry test treat the article with parameters as the one
;     without.
;   * `fn-ipp-params-of-a-login' and `fn-ipp-params-without-a-login': the
;     parameters under a key and a login open with the posting-account
;     value of that login, and without a login they carry none.

(in-package "ACL2")
(include-book "injection-info-params")
(include-book "poster-bytes-invariants")

(local
 (defthm fn-ipp-inj-append-is-append
   (equal (fn-inj-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-ipp-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; The prefix and block of books/injection.lisp with the parameter line.
(defun fn-ipp-block-with (date msgid agent generate-id generate-date params)
  (declare (xargs :guard t))
  (fn-inj-append
   (if (or generate-id generate-date) (fn-inj-injection-date-line date) nil)
   (fn-inj-append
    (if generate-id (fn-inj-message-id-line msgid) nil)
    (fn-inj-append
     (if generate-date (fn-inj-date-line date) nil)
     (fn-inj-injection-info-line-with agent params)))))

(defun fn-ipp-prefix-with (date msgid agent generate-id generate-date params)
  (declare (xargs :guard t))
  (fn-inj-append (fn-inj-path-line agent)
                 (fn-ipp-block-with date msgid agent generate-id generate-date
                                    params)))

; A parameter run the inverse reads past: it opens with ";" and has no CR
; or LF.
(defun fn-ipp-no-crlfp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (equal (car x) 13)) (not (equal (car x) 10))
           (fn-ipp-no-crlfp (cdr x)))
    t))

(defun fn-ipp-params-okp (params)
  (declare (xargs :guard t))
  (and (consp params) (equal (car params) 59) (true-listp params)
       (fn-ipp-no-crlfp params)))
