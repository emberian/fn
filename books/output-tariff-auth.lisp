; fn: the tariff of the authentication layer's first-command replies (lane
; tariff4, 2026-10-04): CAPABILITIES, STARTTLS and COMPRESS.
;
; The served step answers these in fn-auth-command (books/nntp-auth.lisp),
; ahead of the reader: the gate (480), the compressed-layer refusal and each
; command's own arms.  Each reply bound below is proved over fn-auth-command
; itself, at the command's keyword, for every session, configuration and
; argument list (a delegated or refused command is nil or one line, both
; within the bound).  The tariff multiplies the bound by the line figure
; (books/output-tariff-line.lisp).
;
; CAPABILITIES is a block of lines: the reader's label list, the peer layer's
; two labels, the access layer's STARTTLS / AUTHINFO / SASL lines (at most
; three mechanism names, each at most 20 octets), the COMPRESS label and the
; XFN-DICT line, whose length is the shipped dictionaries' (a ground function
; of the tree, so a new dictionary raises the bound with it).
(in-package "ACL2")
(include-book "output-tariff-line")
(include-book "nntp-auth")
(include-book "nntp-compress-dict")

; The octets of a block's lines on the wire: each line, a possible
; dot-stuffing octet, CRLF.
(defun fn-tariff-lines-octets (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (+ (len (car lines)) 3 (fn-tariff-lines-octets (cdr lines)))
    0))

(defthm fn-tariff-lines-octets-natp
  (natp (fn-tariff-lines-octets lines))
  :rule-classes :type-prescription)

(defthm fn-tariff-lines-octets-of-append
  (equal (fn-tariff-lines-octets (append a b))
         (+ (fn-tariff-lines-octets a) (fn-tariff-lines-octets b))))

(defthm fn-tariff-effects-octets-of-append
  (equal (fn-tariff-effects-octets (append a b))
         (+ (fn-tariff-effects-octets a) (fn-tariff-effects-octets b)))
  :hints (("Goal" :in-theory (enable fn-tariff-effects-octets))))

(local
 (defthm fn-tariff-len-stuff-line
   (<= (len (fn-wire-stuff-line line)) (+ 1 (len line)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-wire-stuff-line)))))

(local
 (defthm fn-tariff-len-crlf-of
   (equal (len (fn-nntp-crlf line)) (+ 2 (len line)))
   :hints (("Goal" :in-theory (enable fn-nntp-crlf)))))

(defthm fn-tariff-len-stuff-lines
  (<= (len (fn-nntp-stuff-lines lines)) (fn-tariff-lines-octets lines))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-tariff-lines-octets lines)
           :in-theory (enable fn-nntp-stuff-lines))))

(defthm fn-tariff-single-within
  (<= (fn-tariff-effects-octets (fn-nntp-result-effects (fn-nntp-single session text)))
      (+ 2 (len (fn-nntp-string-octets text))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nntp-single fn-nntp-make-result fn-nntp-result-effects
                                     fn-nntp-reply-effect fn-tariff-effects-octets))))

(defthm fn-tariff-multi-within
  (<= (fn-tariff-effects-octets (fn-nntp-result-effects (fn-nntp-multi session initial lines)))
      (+ (len (fn-nntp-string-octets initial)) 2 (fn-tariff-lines-octets lines) 3))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nntp-multi fn-nntp-make-result fn-nntp-result-effects
                                     fn-nntp-reply-effect fn-tariff-effects-octets))))

(defthm fn-tariff-drop-withdrawn-within
  (<= (fn-tariff-lines-octets (fn-zc-drop-withdrawn lines)) (fn-tariff-lines-octets lines))
  :rule-classes :linear)

(defthm fn-tariff-zc-within
  (<= (fn-tariff-lines-octets (fn-zc-capability-lines lines zs mayp))
      (+ (fn-tariff-lines-octets lines) 3 (len (fn-zc-label-line))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-zc-capability-lines))))

(defthm fn-tariff-zdn-within
  (<= (fn-tariff-lines-octets (fn-zdn-capability-lines lines mayp))
      (+ (fn-tariff-lines-octets lines) 3 (len (fn-zdn-capability-line))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-zdn-capability-lines))))

(defthm fn-tariff-capability-lines-within
  (<= (fn-tariff-lines-octets (fn-nntp-capability-lines postingp)) 220)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nntp-capability-lines))))

(defthm fn-tariff-peer-capability-lines-within
  (<= (fn-tariff-lines-octets (fn-peer-capability-lines record postingp)) 250)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-peer-capability-lines))))

(local
 (defthm fn-tariff-len-sasl-firstn
   (<= (len (fn-sasl-firstn n xs)) (nfix n))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-sasl-firstn)))))

(local
 (defthm fn-tariff-len-mechanism-words
   (<= (len (fn-auth-mechanism-words mechs)) (* 21 (len mechs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-auth-mechanism-words)))))

(local
 (defthm fn-tariff-len-sasl-offers
   (<= (len (fn-sasl-offers tlsp seed binding)) 3)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-sasl-offers)))))

(defthm fn-tariff-access-lines-within
  (<= (fn-tariff-lines-octets (fn-auth-access-capability-lines acfg subject tlsp ctx)) 200)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-auth-access-capability-lines fn-auth-starttls-lines
                                     fn-auth-authinfo-lines fn-auth-sasl-lines
                                     fn-auth-sasl-mechanisms fn-auth-sasl-capability-line))))

; "101 capability list follows" and CRLF, the reader's and peer's labels, the
; access lines, the COMPRESS label, the XFN-DICT line, the terminator.
(defun fn-tariff-capabilities-reply-octets ()
  (declare (xargs :guard t))
  (+ 30 2 250 200 (+ 3 (len (fn-zc-label-line))) (+ 3 (len (fn-zdn-capability-line))) 3))

(defthm fn-tariff-capabilities-reply-within
  (implies (fn-nntp-keywordp keyword "CAPABILITIES")
           (<= (fn-tariff-effects-octets
                (fn-post-result-effects (fn-auth-command as config keyword args)))
               (fn-tariff-capabilities-reply-octets)))
  :hints (("Goal" :in-theory (e/d (fn-auth-command fn-auth-single fn-tariff-capabilities-reply-octets
                                   fn-auth-capability-lines fn-auth-capability-lines-for-peer)
                                  (fn-post-make-result fn-post-result-effects fn-auth-gatedp
                                   fn-auth-compressed-refusedp fn-auth-starttls fn-auth-compress
                                   fn-auth-authinfo fn-auth-xredeem fn-auth-postingp
                                   fn-nntp-multi fn-nntp-single fn-nntp-result-effects)))))

; STARTTLS and COMPRESS answer one literal line, STARTTLS with the
; (:starttls) effect after it (no octets).
(defconst *fn-tariff-transition-reply-octets* 160)

(defthm fn-tariff-starttls-reply-within
  (implies (fn-nntp-keywordp keyword "STARTTLS")
           (<= (fn-tariff-effects-octets
                (fn-post-result-effects (fn-auth-command as config keyword args)))
               *fn-tariff-transition-reply-octets*))
  :hints (("Goal" :in-theory (e/d (fn-auth-command fn-auth-single fn-auth-starttls)
                                  (fn-post-make-result fn-post-result-effects fn-auth-gatedp
                                   fn-auth-compressed-refusedp fn-auth-compress fn-auth-authinfo
                                   fn-auth-xredeem fn-auth-postingp fn-nntp-multi fn-nntp-single
                                   fn-nntp-result-effects)))))

(defthm fn-tariff-compress-reply-within
  (implies (fn-nntp-keywordp keyword "COMPRESS")
           (<= (fn-tariff-effects-octets
                (fn-post-result-effects (fn-auth-command as config keyword args)))
               *fn-tariff-transition-reply-octets*))
  :hints (("Goal" :in-theory (e/d (fn-auth-command fn-auth-single fn-auth-compress)
                                  (fn-post-make-result fn-post-result-effects fn-auth-gatedp
                                   fn-auth-compressed-refusedp fn-auth-starttls fn-auth-authinfo
                                   fn-auth-xredeem fn-auth-postingp fn-nntp-multi fn-nntp-single
                                   fn-nntp-result-effects)))))

; ---------------------------------------------------------------------------
; The peer layer's transit commands (books/peer-inbound.lisp fn-peer-command):
; IHAVE answers one decision line (the reason text at most 100 octets), CHECK
; one status code and the echoed Message-ID (at most 250 octets), TAKETHIS
; no reply (it begins the article).  COVERED SCOPE: a peer connection.  A
; reader connection's IHAVE/CHECK/TAKETHIS is the delegated 502 or 500 line
; of the reader step, one literal line, not bounded here.
(local
 (defthm fn-tariff-len-string-octets-aux
   (equal (len (fn-nntp-string-octets-aux chars)) (len chars))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(defthm fn-tariff-len-string-octets
  (equal (len (fn-nntp-string-octets text)) (if (stringp text) (length text) 0))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets))))

(local
 (defthm fn-tariff-len-coerce
   (implies (stringp s) (equal (len (coerce s 'list)) (length s)))))

(local
 (defthm fn-tariff-length-string-append
   (implies (and (stringp a) (stringp b))
            (equal (length (string-append a b)) (+ (length a) (length b))))
   :hints (("Goal" :in-theory (enable string-append)))))

(local
 (defthm fn-tariff-reason-length
   (<= (length (fn-peer-reason-text reason)) 100)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-peer-reason-text)))))

(local
 (defthm fn-tariff-reason-stringp
   (stringp (fn-peer-reason-text reason))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-peer-reason-text)))))

(local
 (defthm fn-tariff-ihave-line-within
   (<= (len (fn-nntp-string-octets (fn-peer-ihave-offer-line d))) 130)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-peer-ihave-offer-line)
            :use ((:instance fn-tariff-reason-length
                             (reason (fn-peer-decision-reason d))))))))

(local
 (defthm fn-tariff-cbor-at-mostp-len
   (implies (fn-cbor-at-mostp xs bound) (<= (len xs) (nfix bound)))
   :rule-classes :linear))

(local
 (defthm fn-tariff-af-message-id-len
   (implies (fn-af-message-idp msgid) (<= (len msgid) 250))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-af-message-idp)
            :use ((:instance fn-tariff-cbor-at-mostp-len (xs msgid) (bound 250)))))))

(local
 (defthm fn-tariff-check-code-len
   (<= (length (fn-peer-check-code d)) 4)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-peer-check-code)))))

(local
 (defthm fn-tariff-ihave-reply-within
   (<= (fn-tariff-effects-octets (fn-peer-single ps (fn-peer-ihave-offer-line d))) 132)
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-peer-single)
                                   (fn-peer-ihave-offer-line fn-tariff-single-within))
            :use ((:instance fn-tariff-single-within
                             (session (fn-peer-reader-session ps))
                             (text (fn-peer-ihave-offer-line d)))
                  (:instance fn-tariff-ihave-line-within))))))

(local
 (defthm fn-tariff-single-reply-within
   (implies (and (stringp text) (<= (length text) 100))
            (<= (fn-tariff-effects-octets (fn-peer-single ps text)) 102))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-peer-single) (fn-tariff-single-within))
            :use ((:instance fn-tariff-single-within
                             (session (fn-peer-reader-session ps))))))))

(local
 (defthm fn-tariff-echo-reply-within
   (<= (fn-tariff-effects-octets (fn-peer-echo-reply code msgid))
       (+ 2 (len (fn-nntp-string-octets code)) (len msgid)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-peer-echo-reply fn-nntp-reply-effect
                                      fn-tariff-effects-octets)))))

(defconst *fn-tariff-peer-reply-octets* 400)

(defthm fn-tariff-peer-command-reply-within
  (implies (or (fn-nntp-keywordp keyword "IHAVE")
               (fn-nntp-keywordp keyword "CHECK")
               (fn-nntp-keywordp keyword "TAKETHIS"))
           (<= (fn-tariff-effects-octets
                (fn-post-result-effects (fn-peer-command ps keyword args)))
               *fn-tariff-peer-reply-octets*))
  :hints (("Goal" :in-theory (e/d (fn-peer-command fn-peer-msgid-argp)
                                  (fn-post-make-result fn-post-result-effects
                                   fn-peer-ihave-offer-line fn-af-message-idp
                                   fn-nntp-string-octets fn-peer-check-code
                                   fn-nntp-single fn-nntp-result-effects fn-nntp-make-result
                                   fn-peer-single fn-peer-echo-reply fn-tariff-single-within)))))

; POST: the first event reaches fn-nntp-session-command (the post step
; builds its environment and calls the reader step), whose POST arm is the
; one-line offer.  The 440 refusals are literal lines of the same size.
(defthm fn-tariff-post-reply-within-line
  (implies (fn-nntp-keywordp keyword "POST")
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects (fn-nntp-session-command session env keyword args)))
               *fn-tariff-session-line-octets*))
  :hints (("Goal" :in-theory (enable fn-nntp-session-command fn-nntp-post-offer
                                     fn-nntp-make-result fn-nntp-result-effects
                                     fn-nntp-reply-effect fn-nntp-single
                                     fn-tariff-effects-octets fn-nntp-begin-article-effect))))
