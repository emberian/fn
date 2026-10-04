; fn: the steps of the pattern plans that touch the article kind's codec, the
; spool and the consumer's reports (books/app-pattern.lisp is the table and
; the plans; host/native/pattern.lisp the one loop that runs them).
;
; Posting role:  (:encode) fn-pat-encode -- the kind's source of the
;   command's values and payload, nil outside the kind; (:sign) the host
;   signs it and keeps the signed author request in the SPOOL file before it
;   sends it; a rerun over an existing SPOOL resends the SAME request (never
;   re-signs: ML-DSA is randomized, a new signature is a new carrier and a
;   refused conflict, D25 / C-0b) after fn-pat-spool-check has found it to be
;   this message.
; Reading role:  (:project) fn-pat-project -- the poll pair through
;   fn-cpj-project (the binding checks of the authored source to the stored
;   record) or the report's kind (empty, withdrawn); (:decode) fn-pat-decode
;   -- the kind's decoder over the projected authored source; (:deliver) the
;   payload file fn-pat-delivery-name, written before (:ack).
;
; KEYSTONE fn-pat-reader-delivers-what-the-writer-encoded: when a poll pair
; projects, and the authored source it binds is the source the posting role
; encoded from values that passed its check, the reading role delivers
; exactly that payload, at the event's sequence, with the record's
; Message-ID.  That the projected source is the one the writer posted is the
; Store's retention (fn-hsig-injected-carrier-retains-exact-signed-source)
; and the consumer cursor's (the poll reads the group's committed history);
; this theorem is the pattern's part.

(in-package "ACL2")
(include-book "app-pattern")
(include-book "article-kind-codec")
(include-book "consumer-poll-projection")
(include-book "consumer-reason")
(include-book "native-hybrid-control")

; -----------------------------------------------------------------------------
; Posting role

(defun fn-pat-encode (name-word from seconds group msgid payload)
  (declare (xargs :guard t))
  (fn-ak-encode (fn-pat-values name-word from seconds group msgid) payload))

; The key files a posting role's KEYS directory holds, in the order
; fnn-hsig-sign-source takes them: the principal (32 octets), the Ed25519
; public key (32) and secret key (64), the ML-DSA-65 public and private PEM.
(defun fn-pat-key-names ()
  (declare (xargs :guard t))
  (list (fn-pat-octets-of-chars (coerce "principal" 'list))
        (fn-pat-octets-of-chars (coerce "ed-public" 'list))
        (fn-pat-octets-of-chars (coerce "ed-secret" 'list))
        (fn-pat-octets-of-chars (coerce "ml-public.pem" 'list))
        (fn-pat-octets-of-chars (coerce "ml-private.pem" 'list))))

; nil when REQUEST is an author request of GENERATION whose source is a value
; of the kind carrying this pattern's Subject, FROM, GROUP, MSGID and
; PAYLOAD (its Date is the first run's); otherwise the reason word.
(defun fn-pat-spool-check (request generation name-word from group msgid payload)
  (declare (xargs :guard t))
  (let ((author (fn-native-hybrid-control-author-decode request)))
    (if (not (and (consp author) (equal (fn-pat-at 1 author) generation)))
        :spool-request
      (let ((d (fn-ak-decode (fn-pat-at 2 author))))
        (if (not (equal (car d) :ok))
            :spool-kind
          (let ((vals (fn-pat-at 1 d)))
            (if (and (equal (fn-pat-at 0 vals) from)
                     (equal (fn-pat-at 2 vals) group)
                     (equal (fn-pat-at 3 vals) (fn-pat-subject name-word))
                     (equal (fn-pat-at 4 vals) msgid)
                     (equal (fn-pat-at 2 d) payload))
                nil
              :spool-conflict)))))))

; -----------------------------------------------------------------------------
; Reading role

; (:article SEQUENCE MSGID SOURCE) | (:withdrawn MSGID) | (:empty)
; | (:foreign REASON MSGID-OR-NIL)
(defun fn-pat-project (cursor event)
  (declare (xargs :guard t))
  (let ((p (fn-cpj-project cursor event)))
    (if (equal (car p) :ok)
        (list :article (fn-pat-at 2 p) (fn-pat-at 5 p) (fn-pat-at 6 p))
      (let ((s (fn-ncr-report-summary event)))
        (cond ((equal (car s) :empty) (list :empty))
              ((equal (car s) :withdrawn) (list :withdrawn (fn-pat-at 1 s)))
              (t (list :foreign (fn-pat-at 1 p)
                       (if (equal (car s) :article) (fn-pat-at 1 s) nil))))))))

; (:deliver SEQUENCE MSGID PAYLOAD), or the projection unchanged, or
; (:foreign REASON MSGID) for an article outside the pattern's kind.
(defun fn-pat-decode (kind projected)
  (declare (xargs :guard t))
  (if (and (equal kind :opaque-1) (equal (fn-pat-at 0 projected) :article))
      (let ((d (fn-ak-decode (fn-pat-at 3 projected))))
        (if (equal (car d) :ok)
            (list :deliver (fn-pat-at 1 projected) (fn-pat-at 2 projected) (fn-pat-at 2 d))
          (list :foreign (fn-pat-at 1 d) (fn-pat-at 2 projected))))
    projected))

; The payload file of a delivery: SEQUENCE in twenty digits, ".payload".
(defun fn-pat-delivery-name (sequence)
  (declare (xargs :guard t))
  (append (fn-pat-padded sequence 20)
          '(46 112 97 121 108 111 97 100)))

; -----------------------------------------------------------------------------
; KEYSTONE

(local
 (defthm fn-pat-at-is-nth
   (equal (fn-pat-at n x) (nth n x))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-pat-reader-delivers-what-the-writer-encoded
  (let ((p (fn-cpj-project cursor event)))
    (implies (and (equal (car p) :ok)
                  (not (fn-pat-values-check name-word from seconds group msgid))
                  (fn-ak-payloadp payload)
                  (equal (nth 6 p)
                         (fn-pat-encode name-word from seconds group msgid payload)))
             (equal (fn-pat-decode :opaque-1 (fn-pat-project cursor event))
                    (list :deliver (nth 2 p) (nth 5 p) payload))))
  :hints (("Goal" :in-theory (disable fn-pat-values-check fn-pat-values fn-ak-encode
                                      fn-ak-decode fn-cpj-project fn-ncr-report-summary
                                      fn-ak-payloadp fn-ak-rows-valuesp
                                      (:e fn-ak-rows-valuesp))
                  :use ((:instance fn-pat-values-check-is-the-kind)
                        (:instance fn-ak-decode-of-encode
                                   (vals (fn-pat-values name-word from seconds group msgid)))))))
