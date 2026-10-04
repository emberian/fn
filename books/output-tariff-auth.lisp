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
