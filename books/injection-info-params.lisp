; fn: the parameters of the Injection-Info line (PKT-597; prefix `fn-ipp-').
;
; RFC 5536 section 3.2.8: Injection-Info is the injecting agent's
; <path-identity> followed by parameters, among them "posting-account" (the
; source the article came from, "in a form that cannot be interpreted by
; other sites") and "mail-complaints-to" (an <address-list> for complaints
; about the poster).  books/injection.lisp writes the line without
; parameters: the injection decision is made per connection under the
; pinned configuration and holds no secret.  The parameters are the owner's:
; the posting-account value is the HMAC of the connection's login under the
; node's posting-account key (books/posting-account.lisp), and the key is
; the owner's.  So the owner puts them into the octets it hands the Store
; (books/owner-served-invariants.lisp `fn-own-sub-stored-octets', the local
; arm), in place of the plain line, before the Cancel-Lock line the same
; definition adds (newsreader-cancel-2; the order is Injection-Info first).
;
; This book is the executable part: the parameter octets
; (`fn-ipp-params') and the rewrite of the one Injection-Info line of an
; injected article (`fn-ipp-with-params').  The walk reads the injected
; block exactly as the D25 comparison does (books/poster-bytes.lisp
; `fn-pb-path-agent' and `fn-pb-block-agent'): this agent's Path line when
; the article opens with it (recipe v1/v2), then the optional Injection-Date
; line (49 octets), the generated Message-ID line of MSGID, the generated
; Date line (39 octets), and there the plain Injection-Info line of the
; agent, which is replaced.  Anything else is left as it is.  The theorems
; are books/injection-info-params-invariants.lisp.

(in-package "ACL2")
(include-book "poster-bytes")
(include-book "injection-info-policy")
(include-book "config")

; "; posting-account=\"" and "; mail-complaints-to=\"" and the closing quote.
(defconst *fn-ipp-account-open*
  '(59 32 112 111 115 116 105 110 103 45 97 99 99 111 117 110 116 61 34))
(defconst *fn-ipp-complaints-open*
  '(59 32 109 97 105 108 45 99 111 109 112 108 97 105 110 116 115 45 116 111 61 34))
(defconst *fn-ipp-quote* '(34))

; The address the live configuration names, as octets, or nil when it is
; unset or not an addr-spec.
(defun fn-ipp-complaints (cfg)
  (declare (xargs :guard t))
  (let ((a (fn-ipp-octets (fn-cfg-policy (fn-cfg-value cfg) *fn-ipp-complaints-slot*))))
    (if (fn-ipp-addr-specp a) a nil)))

; The parameter octets: posting-account when the owner holds the node
; secret and the submission has a login (the AUTHINFO USER octets,
; books/served.lisp fn-served-login), mail-complaints-to when an address is
; set, in that order; nil when neither.
(defun fn-ipp-account-param (secret login)
  (declare (xargs :guard t))
  (fn-inj-append *fn-ipp-account-open*
                 (fn-inj-append (fn-pa-account-value secret (fn-ipp-octets login))
                                *fn-ipp-quote*)))

(defun fn-ipp-complaints-param (addr)
  (declare (xargs :guard t))
  (fn-inj-append *fn-ipp-complaints-open* (fn-inj-append addr *fn-ipp-quote*)))

(defun fn-ipp-accountp (secret login)
  (declare (xargs :guard t))
  (and (fn-ns-secretp secret) (consp (fn-ipp-octets login))))

(defun fn-ipp-params (secret login addr)
  (declare (xargs :guard t))
  (fn-inj-append (if (fn-ipp-accountp secret login)
                     (fn-ipp-account-param secret login)
                   nil)
                 (if (consp addr) (fn-ipp-complaints-param addr) nil)))

; -----------------------------------------------------------------------------
; The rewrite of the Injection-Info line

(defun fn-ipp-at-info (x agent params)
  (declare (xargs :guard t))
  (let ((r (fn-inj-strip (fn-inj-injection-info-line agent) x)))
    (if (equal r :no)
        x
      (fn-inj-append (fn-inj-injection-info-line-with agent params) r))))

(defun fn-ipp-at-date (x agent params)
  (declare (xargs :guard t))
  (if (fn-pb-opensp *fn-inj-date-field* x)
      (fn-inj-append (fn-inj-take *fn-pb-date-line-length* x)
                     (fn-ipp-at-info (fn-inj-drop *fn-pb-date-line-length* x)
                                     agent params))
    (fn-ipp-at-info x agent params)))

(defun fn-ipp-at-msgid (x agent msgid params)
  (declare (xargs :guard t))
  (let ((r (fn-inj-strip (fn-inj-message-id-line msgid) x)))
    (if (equal r :no)
        (fn-ipp-at-date x agent params)
      (fn-inj-append (fn-inj-message-id-line msgid)
                     (fn-ipp-at-date r agent params)))))

(defun fn-ipp-at-stamp (x agent msgid params)
  (declare (xargs :guard t))
  (if (fn-pb-opensp *fn-inj-injection-date-field* x)
      (fn-inj-append (fn-inj-take *fn-pb-stamp-line-length* x)
                     (fn-ipp-at-msgid (fn-inj-drop *fn-pb-stamp-line-length* x)
                                      agent msgid params))
    (fn-ipp-at-msgid x agent msgid params)))

; The injected article X under Message-ID MSGID with PARAMS in its
; Injection-Info line.  No parameters, or an article whose agent the walk
; cannot name, is X unchanged.
(defun fn-ipp-with-params (x msgid params)
  (declare (xargs :guard t))
  (let ((agent (fn-pb-path-agent x msgid)))
    (if (or (not (consp params)) (not agent))
        x
      (let ((r (fn-inj-strip (fn-inj-path-line agent) x)))
        (if (equal r :no)
            (fn-ipp-at-stamp x agent msgid params)
          (fn-inj-append (fn-inj-path-line agent)
                         (fn-ipp-at-stamp r agent msgid params)))))))

; The injected octets of decision D submitted under LOGIN (nil: no login)
; with the Injection-Info parameters, under the node SECRET and the
; complaints address of the live configuration CFG.
; books/owner-served-invariants.lisp fn-own-sub-stored-octets hands these
; to the Cancel-Lock insertion (books/cancel-lock.lisp
; fn-cl-served-payload), so the Injection-Info line is written first.
(defun fn-ipp-injected-octets (d secret login cfg)
  (declare (xargs :guard t))
  (fn-ipp-with-params (fn-inj-decision-octets d)
                      (fn-inj-decision-msgid d)
                      (fn-ipp-params secret login (fn-ipp-complaints cfg))))
