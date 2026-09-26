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

; -----------------------------------------------------------------------------
; List facts about the injected lines.

(local
 (defthm fn-ipp-strip-of-append-left
   (implies (true-listp a)
            (equal (fn-inj-strip a (append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-ipp-strip-of-a-different-first-octet
   (implies (and (consp a) (consp b) (not (equal (car a) (car b))))
            (equal (fn-inj-strip a (append b x)) :no))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-ipp-take-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-take n (append a b)) a))
   :hints (("Goal" :in-theory (enable fn-inj-take)))))

(local
 (defthm fn-ipp-drop-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-drop n (append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-drop)))))

(local
 (defthm fn-ipp-lines-shape
   (and (consp (fn-inj-path-line agent))
        (equal (car (fn-inj-path-line agent)) 80)
        (consp (fn-inj-injection-date-line date))
        (equal (car (fn-inj-injection-date-line date)) 73)
        (consp (fn-inj-injection-info-line agent))
        (equal (car (fn-inj-injection-info-line agent)) 73)
        (consp (fn-inj-injection-info-line-with agent params))
        (equal (car (fn-inj-injection-info-line-with agent params)) 73)
        (consp (fn-inj-message-id-line msgid))
        (equal (car (fn-inj-message-id-line msgid)) 77)
        (consp (fn-inj-date-line date))
        (equal (car (fn-inj-date-line date)) 68)
        (true-listp (fn-inj-path-line agent))
        (true-listp (fn-inj-injection-date-line date))
        (true-listp (fn-inj-injection-info-line agent))
        (true-listp (fn-inj-injection-info-line-with agent params))
        (true-listp (fn-inj-message-id-line msgid))
        (true-listp (fn-inj-date-line date)))
   :hints (("Goal" :in-theory (enable fn-inj-path-line fn-inj-injection-date-line
                                      fn-inj-injection-info-line
                                      fn-inj-injection-info-line-with
                                      fn-inj-message-id-line fn-inj-date-line)))))

(local
 (defthm fn-ipp-len-of-the-dated-lines
   (implies (equal (len date) 31)
            (and (equal (len (fn-inj-injection-date-line date)) 49)
                 (equal (len (fn-inj-date-line date)) 39)))
   :hints (("Goal" :in-theory (enable fn-inj-injection-date-line fn-inj-date-line)))))

; Which field a line opens with, as the walk asks it.
(local
 (defthm fn-ipp-opens-of-the-lines
   (and (fn-pb-opensp *fn-inj-injection-date-field*
                      (append (fn-inj-injection-date-line date) x))
        (not (fn-pb-opensp *fn-inj-injection-date-field*
                           (append (fn-inj-injection-info-line agent) x)))
        (not (fn-pb-opensp *fn-inj-date-field*
                           (append (fn-inj-injection-info-line agent) x)))
        (fn-pb-opensp *fn-inj-date-field* (append (fn-inj-date-line date) x))
        (not (fn-pb-opensp *fn-inj-injection-date-field*
                           (append (fn-inj-message-id-line msgid) x)))
        (not (fn-pb-opensp *fn-inj-injection-date-field*
                           (append (fn-inj-date-line date) x))))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip
                                      fn-inj-injection-date-line fn-inj-date-line
                                      fn-inj-injection-info-line
                                      fn-inj-message-id-line)))))

(local (in-theory (disable fn-pb-opensp fn-inj-path-line fn-inj-injection-date-line
                           fn-inj-injection-info-line fn-inj-injection-info-line-with
                           fn-inj-message-id-line fn-inj-date-line)))

; -----------------------------------------------------------------------------
; The walk over the injected block.

(local
 (defthm fn-ipp-at-stamp-of-a-block
   (implies (and (true-listp date) (equal (len date) 31))
            (equal (fn-ipp-at-stamp (append (fn-inj-block date msgid agent gid gdate)
                                            source)
                                    agent msgid params)
                   (append (fn-ipp-block-with date msgid agent gid gdate params)
                           source)))
   :hints (("Goal" :in-theory (enable fn-inj-block fn-ipp-block-with)
            :cases ((and gid gdate) (and gid (not gdate))
                    (and (not gid) gdate))))))

(local
 (defthm fn-ipp-a-block-is-not-a-path-line
   (equal (fn-inj-strip (fn-inj-path-line agent)
                        (append (fn-inj-block date msgid agent2 gid gdate) x))
          :no)
   :hints (("Goal" :in-theory (enable fn-inj-block)
            :cases ((or gid gdate))))))

(local
 (defthm fn-ipp-prefix-is-the-path-line-and-the-block
   (equal (append (fn-inj-prefix date msgid agent gid gdate) x)
          (append (fn-inj-path-line agent)
                  (append (fn-inj-block date msgid agent gid gdate) x)))
   :hints (("Goal" :in-theory (enable fn-inj-prefix fn-inj-block)))))
