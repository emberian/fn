; Evidence for AUTHINFO SASL (RFC 4643 section 2.4, NNT-056) on the served
; auth step: books/nntp-auth.lisp fn-auth-step with books/sasl.lisp's
; exchanges, and the SASL way to a peer role (books/nntp-auth-roles.lisp).
;
; The client side of every exchange is written from the RFCs here: PLAIN's
; message (RFC 4616 section 2), SCRAM's client-first and client-final
; (RFC 5802 section 7, through books/scram.lisp's client half, which
; tests/acl2/scram-tests.lisp checks byte for byte against RFC 7677's
; client), and base64 (RFC 4648).  The server's replies are read back off
; the wire octets and decoded; nothing expected is produced by calling the
; server function under test.

(in-package "ACL2")
(include-book "../../books/nntp-auth-roles")
(include-book "../../books/codec-attach")
(include-book "arena-lift")
(include-book "must-fail-checked")

(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary fn-nntp-vocabulary
                          fn-nntp-post-vocabulary fn-peer-vocabulary
                          fn-auth-vocabulary)))

; -----------------------------------------------------------------------------
; Guard world: the SASL arms are executable.

(assert-event (equal (symbol-class 'fn-auth-sasl-command (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-auth-sasl-continue (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-auth-install-context (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-sasl-step (w state))
                     :common-lisp-compliant))

; -----------------------------------------------------------------------------
; The scenario

(defconst *sa-groups* '("fn.letters"))
(defconst *sa-payload*
  (append (fn-nntp-string-octets "Message-ID: <sasl@example.invalid>")
          '(13 10) (fn-nntp-string-octets "Subject: hello") '(13 10 13 10)
          (fn-nntp-string-octets "Hello") '(13 10)))
(defconst *sa-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *sa-groups*) 1 "<sasl@example.invalid>"
                      0 *sa-groups* 841000000)
   0 1 :durable))
(defconst *sa-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *sa-config*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      (list (fn-nntp-string-octets "fn.letters")) 32768))
(defconst *sa-arena* (list *sa-payload*))

(defconst *sa-principal* (make-list 32 :initial-element 7))
(defconst *sa-name* (fn-nntp-string-octets "reader"))
(defconst *sa-secret* (fn-nntp-string-octets "correct-horse"))
(defconst *sa-salt* (make-list 16 :initial-element 3))
; The fast digest is written out: it is the crypto seam's attachment, which
; a `defconst' may not call (tests/acl2/nntp-auth-tests.lisp says why); the
; assert-event re-derives the whole verifier under the attachment.  The SCRAM
; keys are plain functions and are computed.
(defconst *sa-digest*
  '(42 82 187 10 181 221 230 125 199 188 135 91 193 55 205 245
    177 50 208 139 71 236 67 86 54 24 223 76 55 144 61 51))
(defconst *sa-keys* (fn-scram-keys *sa-secret* *sa-salt* 4096))
(defconst *sa-verifier*
  (fn-authsec-verifier *sa-salt* *sa-digest* (car *sa-keys*) (cadr *sa-keys*)))
(assert-event (equal *sa-verifier* (fn-authsec-enrol *sa-salt* *sa-secret*)))
(defconst *sa-cred* (fn-auth-make-cred *sa-name* *sa-principal* *sa-verifier* t))
(assert-event (fn-auth-credp *sa-cred*))

; Required authentication, a certificate configured, one login.
(defconst *sa-required* (fn-auth-make-config t nil t (list *sa-cred*)))
(defconst *sa-protected* (fn-auth-make-config t t t (list *sa-cred*)))

(defun sa-step (as event fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-auth-step as *sa-archive* *sa-config* *sa-obs* *sa-obs* event fn-arena))
(bpr-lift sa-step 2)

(defun sa-send (as text)
  (declare (xargs :verify-guards nil))
  (in-arena-sa-step *sa-arena* as (list :command (fn-nntp-string-octets text))))
(defun sa-send-octets (as octets)
  (declare (xargs :verify-guards nil))
  (in-arena-sa-step *sa-arena* as (list :command octets)))
(defun sa-event (as event)
  (declare (xargs :verify-guards nil))
  (in-arena-sa-step *sa-arena* as event))

; The expected-reply assembler, independent of the book's.
(defun sa-single (text)
  (list (list :reply (append (fn-nntp-string-octets text) '(13 10)))))
(defun sa-lines (texts)
  (if (consp texts)
      (append (fn-nntp-string-octets (car texts)) '(13 10) (sa-lines (cdr texts)))
    nil))
(defun sa-block (initial texts)
  (list (list :reply (append (fn-nntp-string-octets initial) '(13 10)
                             (sa-lines texts) '(46 13 10)))))

; base64 of octets, and the command line "AUTHINFO SASL MECH <b64>".
(defun sa-b64 (octets) (fn-ot-b64-encode octets))
(defun sa-sasl-line (mech octets)
  (append (fn-nntp-string-octets "AUTHINFO SASL ") (fn-nntp-string-octets mech)
          (list 32) (sa-b64 octets)))

; The challenge a "383 X" or "283 X" reply carries, decoded: the octets after
; the code and space, before CRLF.
(defun sa-reply-octets (effects)
  (if (and (consp effects) (consp (car effects))) (cadr (car effects)) nil))
(defun sa-strip-crlf (xs)
  (if (and (consp xs) (consp (cdr xs)))
      (cons (car xs) (sa-strip-crlf (cdr xs)))
    nil))
(defun sa-challenge (effects)
  (let ((line (sa-strip-crlf (sa-strip-crlf (sa-reply-octets effects)))))
    (mv-let (err octets) (fn-ot-b64-decode (nthcdr 4 line))
      (declare (ignore err))
      octets)))
(defun sa-code (effects)
  (take 3 (sa-reply-octets effects)))

; Fields of a server-first message "r=NONCE,s=SALT,i=COUNT".
(defun sa-field-value (field)
  (if (and (consp field) (consp (cdr field))) (cddr field) nil))

(defconst *sa-seed* (make-list 32 :initial-element 9))
(defconst *sa-seed-2* (make-list 32 :initial-element 10))
(defconst *sa-binding* (make-list 32 :initial-element 42))

(defun sa-open (acfg tlsp)
  (fn-auth-open-session *sa-archive* nil nil nil acfg tlsp))

; The host's context event installs the seed (and, on TLS, the binding).
(defconst *sa-plain-ctx*
  (fn-post-result-session
   (sa-event (sa-open *sa-required* nil) (list :sasl-context *sa-seed* nil))))
(defconst *sa-plain-ctx-2*
  (fn-post-result-session
   (sa-event (sa-open *sa-required* nil) (list :sasl-context *sa-seed-2* nil))))
(defconst *sa-tls-ctx*
  (fn-post-result-session
   (sa-event (sa-open *sa-required* t) (list :sasl-context *sa-seed* *sa-binding*))))
(assert-event (fn-auth-sessionp *sa-plain-ctx*))
(assert-event (fn-auth-sessionp *sa-tls-ctx*))
(assert-event (equal (fn-auth-session-ctx *sa-plain-ctx*)
                     (list :sasl-context *sa-seed* nil)))
(assert-event (equal (fn-auth-session-ctx *sa-tls-ctx*)
                     (list :sasl-context *sa-seed* *sa-binding*)))
; The event answers nothing.
(assert-event (null (fn-post-result-effects
                     (sa-event (sa-open *sa-required* nil)
                               (list :sasl-context *sa-seed* nil)))))
; A binding offered on a plaintext connection is not kept: there is no TLS
; layer it could name.
(assert-event (equal (fn-auth-session-ctx
                      (fn-post-result-session
                       (sa-event (sa-open *sa-required* nil)
                                 (list :sasl-context *sa-seed* *sa-binding*))))
                     (list :sasl-context *sa-seed* nil)))
; A seed that is not 32 octets installs no context.
(assert-event (null (fn-auth-session-ctx
                     (fn-post-result-session
                      (sa-event (sa-open *sa-required* nil)
                                (list :sasl-context '(1 2 3) nil))))))

; -----------------------------------------------------------------------------
; CAPABILITIES (RFC 4643 sections 2.1 and 2.2)

(defconst *sa-reader-lines*
  '("VERSION 2" "READER" "OVER MSGID" "HDR" "XPAT" "NEWNEWS"
    "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT"
    "IMPLEMENTATION fn-nntp-lab"))
(defconst *sa-reader-lines-posting*
  '("VERSION 2" "READER" "POST" "OVER MSGID" "HDR" "XPAT" "NEWNEWS"
    "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT"
    "IMPLEMENTATION fn-nntp-lab"))

; Plaintext with a context: SCRAM, never PLAIN.
(assert-event
 (equal (fn-post-result-effects (sa-send *sa-plain-ctx* "CAPABILITIES"))
        (sa-block "101 capability list follows"
                  (append *sa-reader-lines*
                          '("STARTTLS" "AUTHINFO USER SASL" "SASL SCRAM-SHA-256")))))
; TLS with a context and a binding: all three, strongest first.
(assert-event
 (equal (fn-post-result-effects (sa-send *sa-tls-ctx* "CAPABILITIES"))
        (sa-block "101 capability list follows"
                  (append *sa-reader-lines*
                          '("AUTHINFO USER SASL"
                            "SASL SCRAM-SHA-256-PLUS SCRAM-SHA-256 PLAIN")))))
; Protected-only before TLS: no AUTHINFO argument and no mechanism (every
; AUTHINFO form is 483 there).
(assert-event
 (equal (fn-post-result-effects
         (sa-send (fn-post-result-session
                   (sa-event (sa-open *sa-protected* nil)
                             (list :sasl-context *sa-seed* nil)))
                  "CAPABILITIES"))
        (sa-block "101 capability list follows"
                  (append *sa-reader-lines* '("STARTTLS")))))

; -----------------------------------------------------------------------------
; PLAIN (RFC 4616), over TLS

(defconst *sa-plain-good*
  (append '(0) *sa-name* '(0) *sa-secret*))
(defconst *sa-plain-bad*
  (append '(0) *sa-name* '(0) (fn-nntp-string-octets "correct-horsf")))

; Macros, not constants: PLAIN's check is the fast digest, an attachment.
(defmacro sa-plain-reply (as octets)
  `(fn-post-result-effects (sa-send-octets ,as (sa-sasl-line "PLAIN" ,octets))))
(defmacro sa-plain-after (as octets)
  `(fn-post-result-session (sa-send-octets ,as (sa-sasl-line "PLAIN" ,octets))))

(assert-event (equal (sa-plain-reply *sa-tls-ctx* *sa-plain-good*)
                     (sa-single "281 authentication accepted")))
(assert-event (equal (fn-auth-session-subject (sa-plain-after *sa-tls-ctx* *sa-plain-good*))
                     *sa-principal*))
(assert-event (equal (fn-auth-session-pending (sa-plain-after *sa-tls-ctx* *sa-plain-good*))
                     *sa-name*))
(assert-event (fn-auth-sessionp (sa-plain-after *sa-tls-ctx* *sa-plain-good*)))
; The authzid, when present, must be the authcid.
(assert-event (equal (sa-plain-reply *sa-tls-ctx* (append *sa-name* *sa-plain-good*))
                     (sa-single "281 authentication accepted")))
(assert-event (equal (sa-plain-reply *sa-tls-ctx*
                                     (append (fn-nntp-string-octets "other")
                                             *sa-plain-good*))
                     (sa-single "481 authentication failed")))
; A wrong password.
(assert-event (equal (sa-plain-reply *sa-tls-ctx* *sa-plain-bad*)
                     (sa-single "481 authentication failed")))
(assert-event (null (fn-auth-session-subject (sa-plain-after *sa-tls-ctx* *sa-plain-bad*))))
; Before TLS: 483, whatever the message.
(assert-event (equal (sa-plain-reply *sa-plain-ctx* *sa-plain-good*)
                     (sa-single "483 a protected channel is required; use STARTTLS")))
; Without an initial response: "383 =", then the response line.
(defconst *sa-plain-wait* (fn-post-result-session (sa-send *sa-tls-ctx* "AUTHINFO SASL PLAIN")))
(assert-event (equal (fn-post-result-effects (sa-send *sa-tls-ctx* "AUTHINFO SASL PLAIN"))
                     (sa-single "383 =")))
(assert-event (equal (fn-auth-session-pending *sa-plain-wait*) '(:sasl-plain)))
(assert-event (equal (fn-post-result-effects
                      (sa-send-octets *sa-plain-wait* (sa-b64 *sa-plain-good*)))
                     (sa-single "281 authentication accepted")))
; The client's cancel is 481 and ends the exchange (RFC 4643 section 2.4.2).
(assert-event (equal (fn-post-result-effects (sa-send *sa-plain-wait* "*"))
                     (sa-single "481 authentication cancelled")))
(assert-event (null (fn-auth-session-pending
                     (fn-post-result-session (sa-send *sa-plain-wait* "*")))))
; A response that is not canonical base64 is 504 and ends the exchange.
(assert-event (equal (fn-post-result-effects (sa-send *sa-plain-wait* "abcd=efg"))
                     (sa-single "504 base64 encoding error")))
; While an exchange is kept a line is its response, never a command:
; "GROUP fn.letters" is not base64, so 504, and nothing was selected.
(assert-event (equal (fn-post-result-effects (sa-send *sa-plain-wait* "GROUP fn.letters"))
                     (sa-single "504 base64 encoding error")))
; A mechanism this connection does not offer is 503.
(assert-event (equal (fn-post-result-effects (sa-send *sa-tls-ctx* "AUTHINFO SASL CRAM-MD5"))
                     (sa-single "503 mechanism not recognized")))
(assert-event (equal (fn-post-result-effects (sa-send *sa-plain-ctx* "AUTHINFO SASL SCRAM-SHA-256-PLUS"))
                     (sa-single "503 mechanism not recognized")))
; The command's own syntax: too many arguments.
(assert-event (equal (fn-post-result-effects (sa-send *sa-tls-ctx* "AUTHINFO SASL PLAIN = x"))
                     (sa-single "501 syntax error")))

; -----------------------------------------------------------------------------
; SCRAM-SHA-256 (RFC 5802, RFC 7677), on a plaintext connection

(defconst *sa-cnonce* (fn-nntp-string-octets "rOprNGfwEbeRWgbNEkqO"))
(defconst *sa-client-first*
  (append (fn-nntp-string-octets "n,,n=reader,r=") *sa-cnonce*))
(defconst *sa-bare* (nthcdr 3 *sa-client-first*))

(defconst *sa-r1* (sa-send-octets *sa-plain-ctx* (sa-sasl-line "SCRAM-SHA-256" *sa-client-first*)))
(defconst *sa-server-first* (sa-challenge (fn-post-result-effects *sa-r1*)))
(defconst *sa-sf-fields* (fn-scram-split *sa-server-first*))
(defconst *sa-nonce* (sa-field-value (car *sa-sf-fields*)))

; 383 with a server-first message: the nonce extends the client's, the salt
; is the enrolled one, the count 4096 (RFC 7677 section 4).
(assert-event (equal (sa-code (fn-post-result-effects *sa-r1*)) (fn-nntp-string-octets "383")))
(assert-event (equal (len *sa-sf-fields*) 3))
(assert-event (equal (take 20 *sa-nonce*) *sa-cnonce*))
(assert-event (< 20 (len *sa-nonce*)))
(assert-event (equal (cadr *sa-sf-fields*)
                     (append (fn-nntp-string-octets "s=") (sa-b64 *sa-salt*))))
(assert-event (equal (caddr *sa-sf-fields*) (fn-nntp-string-octets "i=4096")))
(assert-event (fn-sasl-statep (fn-auth-session-pending (fn-post-result-session *sa-r1*))))
(assert-event (null (fn-auth-session-subject (fn-post-result-session *sa-r1*))))

; The client's final message, from the password, per RFC 5802.
(defun sa-final (password flag gs2 binding nonce bare sf)
  (fn-scram-client-final password *sa-salt* 4096 flag gs2 binding nonce bare sf))
(defconst *sa-final-good*
  (sa-final *sa-secret* :n (fn-nntp-string-octets "n,,") nil *sa-nonce* *sa-bare*
            *sa-server-first*))
(defconst *sa-r2* (sa-send-octets (fn-post-result-session *sa-r1*) (sa-b64 *sa-final-good*)))

; POSITIVE WITNESS: 283 with the server-final message the client verifies:
; "v=" base64(HMAC(ServerKey, AuthMessage)).
(defconst *sa-auth-message*
  (append *sa-bare* '(44) *sa-server-first* '(44)
          (fn-scram-client-final-without-proof :n (fn-nntp-string-octets "n,,")
                                               nil *sa-nonce*)))
(assert-event (equal (sa-code (fn-post-result-effects *sa-r2*)) (fn-nntp-string-octets "283")))
(assert-event (equal (sa-challenge (fn-post-result-effects *sa-r2*))
                     (append (fn-nntp-string-octets "v=")
                             (sa-b64 (fn-hmac-sha256 (cadr *sa-keys*) *sa-auth-message*)))))
(assert-event (equal (fn-auth-session-subject (fn-post-result-session *sa-r2*)) *sa-principal*))
(assert-event (equal (fn-auth-session-pending (fn-post-result-session *sa-r2*)) *sa-name*))
(assert-event (fn-auth-sessionp (fn-post-result-session *sa-r2*)))

; After SCRAM: no AUTHINFO label, the same SASL line (RFC 4643 section 2.2),
; POST offered to this principal, and AUTHINFO SASL again is 502.
(assert-event
 (equal (fn-post-result-effects (sa-send (fn-post-result-session *sa-r2*) "CAPABILITIES"))
        (sa-block "101 capability list follows"
                  (append *sa-reader-lines-posting*
                          ; COMPRESS (RFC 8054) is offered once authenticated.
                          '("STARTTLS" "SASL SCRAM-SHA-256" "COMPRESS DEFLATE"
                            "XFN-DICT 845aa5e18680ef219a9b0f0d0b959cd8886d5eabc12236aae19f301aed9de75e")))))
(assert-event
 (equal (fn-post-result-effects (sa-send (fn-post-result-session *sa-r2*)
                                         "AUTHINFO SASL SCRAM-SHA-256"))
        (sa-single "502 already authenticated")))

; A wrong password: the same exchange's final message computed from another
; password is 481, and the connection is not authenticated.
(defconst *sa-final-bad*
  (sa-final (fn-nntp-string-octets "correct-horsf") :n (fn-nntp-string-octets "n,,")
            nil *sa-nonce* *sa-bare* *sa-server-first*))
(defconst *sa-r2-bad* (sa-send-octets (fn-post-result-session *sa-r1*) (sa-b64 *sa-final-bad*)))
(assert-event (equal (fn-post-result-effects *sa-r2-bad*)
                     (sa-single "481 authentication failed")))
(assert-event (null (fn-auth-session-subject (fn-post-result-session *sa-r2-bad*))))
(assert-event (null (fn-auth-session-pending (fn-post-result-session *sa-r2-bad*))))

; REPLAY: the same client-first on another connection (another seed) gets
; another server nonce, and the first connection's final message -- valid
; there -- is refused here.
(defconst *sa-r1-other* (sa-send-octets *sa-plain-ctx-2*
                                        (sa-sasl-line "SCRAM-SHA-256" *sa-client-first*)))
(assert-event (equal (sa-code (fn-post-result-effects *sa-r1-other*)) (fn-nntp-string-octets "383")))
(assert-event (not (equal (sa-challenge (fn-post-result-effects *sa-r1-other*))
                          *sa-server-first*)))
(defconst *sa-replayed* (sa-send-octets (fn-post-result-session *sa-r1-other*)
                                        (sa-b64 *sa-final-good*)))
(assert-event (equal (fn-post-result-effects *sa-replayed*)
                     (sa-single "481 authentication failed")))
(assert-event (null (fn-auth-session-subject (fn-post-result-session *sa-replayed*))))

; An unknown login: a server-first like any other (383), then 481 whatever
; the final message.
(defconst *sa-u1* (sa-send-octets *sa-plain-ctx*
                                  (sa-sasl-line "SCRAM-SHA-256"
                                                (append (fn-nntp-string-octets "n,,n=nobody,r=")
                                                        *sa-cnonce*))))
(assert-event (equal (sa-code (fn-post-result-effects *sa-u1*)) (fn-nntp-string-octets "383")))
(defconst *sa-u-sf* (sa-challenge (fn-post-result-effects *sa-u1*)))
(defconst *sa-u2*
  (sa-send-octets (fn-post-result-session *sa-u1*)
                  (sa-b64 (sa-final *sa-secret* :n (fn-nntp-string-octets "n,,") nil
                                    (sa-field-value (car (fn-scram-split *sa-u-sf*)))
                                    (append (fn-nntp-string-octets "n=nobody,r=")
                                            *sa-cnonce*)
                                    *sa-u-sf*))))
(assert-event (equal (fn-post-result-effects *sa-u2*) (sa-single "481 authentication failed")))

; SCRAM without an initial response: "383 =", then the client-first line.
(defconst *sa-s-wait* (fn-post-result-session (sa-send *sa-plain-ctx* "AUTHINFO SASL SCRAM-SHA-256")))
(assert-event (equal (fn-post-result-effects (sa-send *sa-plain-ctx* "AUTHINFO SASL SCRAM-SHA-256"))
                     (sa-single "383 =")))
(assert-event (equal (fn-auth-session-pending *sa-s-wait*) '(:sasl-scram-first nil)))
(assert-event (equal (fn-post-result-effects
                      (sa-send-octets *sa-s-wait* (sa-b64 *sa-client-first*)))
                     (fn-post-result-effects *sa-r1*)))

; -----------------------------------------------------------------------------
; SCRAM-SHA-256-PLUS (RFC 9266 tls-exporter), on TLS

(defconst *sa-plus-first*
  (append (fn-nntp-string-octets "p=tls-exporter,,n=reader,r=") *sa-cnonce*))
(defconst *sa-plus-bare* (nthcdr 16 *sa-plus-first*))
(defconst *sa-p1* (sa-send-octets *sa-tls-ctx* (sa-sasl-line "SCRAM-SHA-256-PLUS" *sa-plus-first*)))
(defconst *sa-p-sf* (sa-challenge (fn-post-result-effects *sa-p1*)))
(defconst *sa-p-nonce* (sa-field-value (car (fn-scram-split *sa-p-sf*))))
(defun sa-plus-final (binding)
  (sa-final *sa-secret* :p (fn-nntp-string-octets "p=tls-exporter,,") binding
            *sa-p-nonce* *sa-plus-bare* *sa-p-sf*))
(assert-event (equal (sa-code (fn-post-result-effects *sa-p1*)) (fn-nntp-string-octets "383")))
; The client bound to THIS connection's exporter value: 283.
(assert-event (equal (sa-code (fn-post-result-effects
                               (sa-send-octets (fn-post-result-session *sa-p1*)
                                               (sa-b64 (sa-plus-final *sa-binding*)))))
                     (fn-nntp-string-octets "283")))
; The same client bound to another TLS session's exporter value (a relayed
; exchange): 481.
(assert-event (equal (fn-post-result-effects
                      (sa-send-octets (fn-post-result-session *sa-p1*)
                                      (sa-b64 (sa-plus-final (make-list 32 :initial-element 43)))))
                     (sa-single "481 authentication failed")))
; The downgrade: a client that could bind ("y") on a connection that offers
; -PLUS is refused at its first message.
(assert-event (equal (fn-post-result-effects
                      (sa-send-octets *sa-tls-ctx*
                                      (sa-sasl-line "SCRAM-SHA-256"
                                                    (append (fn-nntp-string-octets "y,,n=reader,r=")
                                                            *sa-cnonce*))))
                     (sa-single "481 authentication failed")))
; Plain SCRAM with "n" on the same TLS connection is fine (the client does
; not bind).
(assert-event (equal (sa-code (fn-post-result-effects
                               (sa-send-octets *sa-tls-ctx*
                                               (sa-sasl-line "SCRAM-SHA-256" *sa-client-first*))))
                     (fn-nntp-string-octets "383")))

; -----------------------------------------------------------------------------
; The SASL way to a peer role (books/nntp-auth-roles.lisp
; fn-auth-step-binds-a-peer-role-by-sasl-only-to-a-found-credential):
; POSITIVE WITNESS.  A login whose principal the pinned configuration binds to
; exactly one (:principal HEX) peer gains that role by SCRAM.

(defconst *sa-principal-peer-record*
  (fn-cfg-peer-make
   "principal-peer" "principal.example.invalid" '(:nntp "127.0.0.1" 119)
   '("fn.*" 32768 16) nil
   (list :principal (fn-digest-hex *sa-principal*))))
(defconst *sa-principal-peer-cfg*
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make
          0 0 1 (append *fn-cfg-default-change*
                        (list (fn-cfg-set-peer-delta *sa-principal-peer-record*)))
          *fn-cfg-default-stamp*))))
(defconst *sa-peer-node* (fn-node-initial-state '("fn.letters") 1048576))
(defconst *sa-principal-reader*
  (fn-post-result-session
   (sa-event (fn-auth-open-session (fn-node-acceptance *sa-peer-node*) nil
                                   *sa-peer-node* *sa-principal-peer-cfg*
                                   *sa-required* nil)
             (list :sasl-context *sa-seed* nil))))
(assert-event (null (fn-auth-session-peer *sa-principal-reader*)))
(defconst *sa-q1* (sa-send-octets *sa-principal-reader*
                                  (sa-sasl-line "SCRAM-SHA-256" *sa-client-first*)))
(defconst *sa-q-sf* (sa-challenge (fn-post-result-effects *sa-q1*)))
(defconst *sa-q2*
  (sa-send-octets (fn-post-result-session *sa-q1*)
                  (sa-b64 (sa-final *sa-secret* :n (fn-nntp-string-octets "n,,") nil
                                    (sa-field-value (car (fn-scram-split *sa-q-sf*)))
                                    *sa-bare* *sa-q-sf*))))
(assert-event (equal (sa-code (fn-post-result-effects *sa-q2*)) (fn-nntp-string-octets "283")))
(assert-event (equal (fn-auth-session-peer (fn-post-result-session *sa-q2*)) "principal-peer"))
(assert-event (fn-auth-principal-rolep (fn-post-result-session *sa-q2*)))
(assert-event (equal (fn-auth-session-subject (fn-post-result-session *sa-q2*))
                     (fn-auth-cred-principal
                      (fn-auth-find-cred (fn-auth-session-pending (fn-post-result-session *sa-q2*))
                                         (fn-auth-config-creds *sa-required*)))))
; And a failed exchange on the same session binds nothing.
(defconst *sa-q2-bad*
  (sa-send-octets (fn-post-result-session *sa-q1*)
                  (sa-b64 (sa-final (fn-nntp-string-octets "correct-horsf") :n
                                    (fn-nntp-string-octets "n,,") nil
                                    (sa-field-value (car (fn-scram-split *sa-q-sf*)))
                                    *sa-bare* *sa-q-sf*))))
(assert-event (null (fn-auth-session-peer (fn-post-result-session *sa-q2-bad*))))

; -----------------------------------------------------------------------------
; Teeth for the hypothesis (not (fn-auth-sasl-waitingp as)) that the
; command-line keystones gained (books/nntp-auth.lisp, nntp-auth-invariants,
; nntp-help, public-exposure, nntp-auth-roles): on a session that keeps an
; exchange -- well formed, not handshaking, not authenticated, authentication
; required -- each keystone's own line is the exchange's response and is
; answered 504 (not base64) or 481 (base64 that is no client-first message), never the keystone's conclusion (480, 440, 483,
; the 101 block, 500, the peer's transit answer, 381).
(defconst *sa-waiting* *sa-s-wait*)
(assert-event (fn-auth-sessionp *sa-waiting*))
(assert-event (not (fn-auth-session-handshakingp *sa-waiting*)))
(assert-event (null (fn-auth-session-subject *sa-waiting*)))
(assert-event (fn-auth-config-requiredp (fn-auth-session-config *sa-waiting*)))
(assert-event (fn-auth-sasl-waitingp *sa-waiting*))
(defmacro sa-504-for (line)
  `(assert-event (equal (fn-post-result-effects (sa-send *sa-waiting* ,line))
                        (sa-single "504 base64 encoding error"))))
(sa-504-for "GROUP fn.letters")          ; the 480 gate
; "POST" and "CAPABILITIES" are canonical base64 (4 and 12 alphabet
; octets): they decode, fail as a client-first message, and are 481.
(assert-event (equal (fn-post-result-effects (sa-send *sa-waiting* "POST"))
                     (sa-single "481 authentication failed")))
(sa-504-for "AUTHINFO USER reader")      ; 381 / protected-only's 483
(sa-504-for "AUTHINFO PASS correct-horse") ; the PASS keystones
(assert-event (equal (fn-post-result-effects (sa-send *sa-waiting* "CAPABILITIES"))
                     (sa-single "481 authentication failed")))
(sa-504-for "XREDEEM code reader")       ; XREDEEM's 483 and hold
(sa-504-for "IHAVE <x@example.invalid>") ; the transit delegation
(sa-504-for "NOSUCHCOMMAND")             ; HELP's 500

; -----------------------------------------------------------------------------
; Teeth of the PRF-916 / PRF-917 keystones the host's AUTHINFO SASL arm
; reaches (books/nntp-auth.lisp fn-auth-step -> fn-auth-sasl-finish ->
; fn-sasl-step; the offer through fn-auth-sasl-mechanisms), each stated
; literally over the scenario's credential.  Macros where the fast digest
; (an attachment) is evaluated.

; fn-sasl-plain-succeeds-exactly-on-the-stored-check
(defmacro sa-s1-lhs (response verifier)
  `(fn-sasl-successp (fn-sasl-step (list :sasl-plain) ,response ,verifier
                                   *sa-seed* *sa-binding*)))
;; nth under guard t: the logical car/cadr/caddr of the parse, which is the
;; keyword :bad when the message does not parse.
(defun sa-nth-t (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x) (if (zp n) (car x) (sa-nth-t (1- n) (cdr x))) nil))
(defmacro sa-s1-rhs (response verifier)
  `(let ((p (fn-sasl-plain-parse ,response)))
     (and (or (not (sa-nth-t 0 p)) (equal (sa-nth-t 0 p) (sa-nth-t 1 p)))
          (fn-authsec-checkp ,verifier (sa-nth-t 2 p)))))
(defmacro sa-s1-holds (response verifier)
  `(equal (sa-s1-lhs ,response ,verifier) (sa-s1-rhs ,response ,verifier)))
; Positive witness, both sides true: the enrolled password, no authzid.
(assert-event (not (equal (fn-sasl-plain-parse *sa-plain-good*) :bad)))
(assert-event (and (sa-s1-lhs *sa-plain-good* *sa-verifier*)
                   (sa-s1-rhs *sa-plain-good* *sa-verifier*)))
; Both sides false: the wrong password; the authzid that is not the authcid.
(assert-event (and (not (sa-s1-lhs *sa-plain-bad* *sa-verifier*))
                   (sa-s1-holds *sa-plain-bad* *sa-verifier*)))
(defconst *sa-plain-other-authz*
  (append (fn-nntp-string-octets "other") *sa-plain-good*))
(assert-event (and (not (equal (fn-sasl-plain-parse *sa-plain-other-authz*) :bad))
                   (not (sa-s1-rhs *sa-plain-other-authz* *sa-verifier*))
                   (sa-s1-holds *sa-plain-other-authz* *sa-verifier*)))
; Hypothesis (not (equal (fn-sasl-plain-parse response) :bad)) removed: a
; message with no NUL does not parse, and against the verifier enrolled
; with the empty password the stored check of the parse's (empty) password
; holds while the step fails.
(defconst *sa-no-nul* (fn-nntp-string-octets "readercorrect-horse"))
(assert-event (equal (fn-sasl-plain-parse *sa-no-nul*) :bad))
(defmacro sa-empty-verifier () '(fn-authsec-enrol *sa-salt* nil))
(assert-event (and (sa-s1-rhs *sa-no-nul* (sa-empty-verifier))
                   (not (sa-s1-lhs *sa-no-nul* (sa-empty-verifier)))))
(must-fail-checked (assert-event (sa-s1-holds *sa-no-nul* (sa-empty-verifier))))

; fn-sasl-plain-honest-client-succeeds
(defun sa-s1c-hyps (salt login pw)
  (and (fn-authsec-saltp salt)
       (fn-sha256-octet-listp login) (consp login) (<= (len login) 255)
       (fn-sasl-no-nulp login)
       (fn-sha256-octet-listp pw) (consp pw) (<= (len pw) 255)
       (fn-sasl-no-nulp pw)))
(defmacro sa-s1c-concl (salt login pw)
  `(fn-sasl-successp
    (fn-sasl-step (list :sasl-plain) (fn-sasl-plain-message nil ,login ,pw)
                  (fn-authsec-enrol ,salt ,pw) *sa-seed* *sa-binding*)))
; Positive witness: the scenario's login and password.
(assert-event (sa-s1c-hyps *sa-salt* *sa-name* *sa-secret*))
(assert-event (sa-s1c-concl *sa-salt* *sa-name* *sa-secret*))
; One removal per hypothesis that has a counter-witness; each keeps the
; others (checked) and fails the omitted one and the conclusion.
;   salt: 15 octets, so the stored verifier is not a verifier
(defconst *sa-short-salt* (make-list 15 :initial-element 3))
(assert-event (not (fn-authsec-saltp *sa-short-salt*)))
(assert-event (sa-s1c-hyps *sa-salt* *sa-name* *sa-secret*))
(must-fail-checked (assert-event (sa-s1c-concl *sa-short-salt* *sa-name* *sa-secret*)))
;   login empty
(assert-event (and (not (consp nil)) (fn-sasl-no-nulp nil) (fn-sha256-octet-listp nil)))
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* nil *sa-secret*)))
;   login past 255 octets
(defconst *sa-long* (make-list 256 :initial-element 114))
(assert-event (and (not (<= (len *sa-long*) 255)) (consp *sa-long*)
                   (fn-sasl-no-nulp *sa-long*) (fn-sha256-octet-listp *sa-long*)))
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* *sa-long* *sa-secret*)))
;   login with a NUL
(defconst *sa-nul-login* (append *sa-name* '(0) *sa-name*))
(assert-event (and (not (fn-sasl-no-nulp *sa-nul-login*)) (consp *sa-nul-login*)
                   (<= (len *sa-nul-login*) 255) (fn-sha256-octet-listp *sa-nul-login*)))
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* *sa-nul-login* *sa-secret*)))
;   login not octets: a symbol where an octet stands (the message's
;   coercion makes it another login than the parse reads back)
(defconst *sa-sym-login* (list 'a 101))
(assert-event (and (not (fn-sha256-octet-listp *sa-sym-login*)) (consp *sa-sym-login*)
                   (<= (len *sa-sym-login*) 255) (fn-sasl-no-nulp *sa-sym-login*)))
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* *sa-sym-login* *sa-secret*)))
;   password not octets: 300 is no octet
(defconst *sa-wide-pw* (list 300 101))
(assert-event (and (not (fn-sha256-octet-listp *sa-wide-pw*)) (consp *sa-wide-pw*)
                   (<= (len *sa-wide-pw*) 255) (fn-sasl-no-nulp *sa-wide-pw*)))
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* *sa-name* *sa-wide-pw*)))
;   password empty
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* *sa-name* nil)))
;   password past 255 octets
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* *sa-name* *sa-long*)))
;   password with a NUL
(must-fail-checked (assert-event (sa-s1c-concl *sa-salt* *sa-name* *sa-nul-login*)))

; fn-authsec-enrolled-secret-proves-by-scram (no hypotheses)
(defconst *sa-k5-message* (fn-nntp-string-octets "n=reader,r=abc,r=abcdef,s=AwMD,i=4096,c=biws,r=abcdef"))
(defconst *sa-enrolled-proof*
  (fn-scram-client-proof *sa-secret* *sa-salt* *fn-scram-iterations* *sa-k5-message*))
(assert-event (equal (fn-authsec-ver-salt *sa-verifier*) *sa-salt*))
(assert-event (fn-scram-proof-validp (fn-authsec-ver-stored-key *sa-verifier*)
                                     *sa-k5-message* *sa-enrolled-proof*))
; Contrast (not a hypothesis): a proof from another password fails.
(must-fail-checked
 (assert-event (fn-scram-proof-validp (fn-authsec-ver-stored-key *sa-verifier*)
                                      *sa-k5-message*
                                      (fn-scram-client-proof
                                       (fn-nntp-string-octets "correct-horsf") *sa-salt*
                                       *fn-scram-iterations* *sa-k5-message*))))

; fn-acct-text-verifier-of-verifier-text
(assert-event (fn-authsec-verifierp *sa-verifier*))
(assert-event (equal (fn-acct-text-verifier (fn-acct-verifier-text *sa-verifier*))
                     *sa-verifier*))
; Hypothesis (fn-authsec-verifierp ver) removed: a verifier whose salt is
; 15 octets does not come back from its text.
(defconst *sa-bad-verifier* (update-nth 1 *sa-short-salt* *sa-verifier*))
(assert-event (not (fn-authsec-verifierp *sa-bad-verifier*)))
(must-fail-checked
 (assert-event (equal (fn-acct-text-verifier (fn-acct-verifier-text *sa-bad-verifier*))
                      *sa-bad-verifier*)))

; fn-auth-sasl-mechanisms-never-offer-plain-before-tls
(defconst *sa-plain-acfg* (fn-auth-session-config *sa-plain-ctx*))
(defconst *sa-tls-ctx-value* (fn-auth-session-ctx *sa-tls-ctx*))
; Positive witness: no TLS, the context of a TLS session (seed and binding
; installed): SCRAM is offered, PLAIN is not.
(assert-event (consp (fn-auth-sasl-mechanisms *sa-plain-acfg* nil *sa-tls-ctx-value*)))
(assert-event (not (member-equal *fn-sasl-plain*
                                 (fn-auth-sasl-mechanisms *sa-plain-acfg* nil
                                                          *sa-tls-ctx-value*))))
; Hypothesis (not tlsp) removed: on TLS PLAIN is offered.
(must-fail-checked
 (assert-event (not (member-equal *fn-sasl-plain*
                                  (fn-auth-sasl-mechanisms *sa-plain-acfg* t
                                                           *sa-tls-ctx-value*)))))


; fn-sasl-scram-honest-client-completes
(defun sa-hc-hyps (salt login cn seed)
  (and (fn-authsec-saltp salt)
       (consp login) (fn-sha256-octet-listp login) (fn-scram-no-nulp login)
       (fn-scram-noncep cn) (fn-sasl-seedp seed)))
(defmacro sa-hc-concl (salt login cn seed pw)
  `(let* ((v (fn-authsec-enrol ,salt ,pw))
          (o1 (fn-sasl-step '(:sasl-scram-first nil)
                            (append (fn-scram-text "n,,n=")
                                    (fn-scram-saslname-encode ,login)
                                    (fn-scram-text ",r=") ,cn)
                            v ,seed nil))
          (st (fn-scram-nth 2 o1)))
     (and (equal (fn-sasl-outcome-kind o1) :continue)
          (fn-sasl-successp
           (fn-sasl-step st
                         (fn-scram-client-final ,pw ,salt 4096 :n
                                                (fn-scram-text "n,,")
                                                nil (fn-sasl-st 5 st)
                                                (fn-sasl-st 6 st)
                                                (fn-scram-nth 1 o1))
                         v ,seed nil)))))
; Positive witness: the scenario's login, nonce, seed and password.
(assert-event (sa-hc-hyps *sa-salt* *sa-name* *sa-cnonce* *sa-seed*))
(assert-event (sa-hc-concl *sa-salt* *sa-name* *sa-cnonce* *sa-seed* *sa-secret*))
;   salt: 15 octets
(assert-event (and (not (fn-authsec-saltp *sa-short-salt*))
                   (sa-hc-hyps *sa-salt* *sa-name* *sa-cnonce* *sa-seed*)))
(must-fail-checked
 (assert-event (sa-hc-concl *sa-short-salt* *sa-name* *sa-cnonce* *sa-seed* *sa-secret*)))
;   login empty
(assert-event (and (fn-sha256-octet-listp nil) (fn-scram-no-nulp nil)))
(must-fail-checked
 (assert-event (sa-hc-concl *sa-salt* nil *sa-cnonce* *sa-seed* *sa-secret*)))
;   login not octets
(assert-event (and (not (fn-sha256-octet-listp *sa-sym-login*)) (fn-scram-no-nulp *sa-sym-login*)))
(must-fail-checked
 (assert-event (sa-hc-concl *sa-salt* *sa-sym-login* *sa-cnonce* *sa-seed* *sa-secret*)))
;   login with a NUL
(assert-event (and (not (fn-scram-no-nulp *sa-nul-login*)) (fn-sha256-octet-listp *sa-nul-login*)))
(must-fail-checked
 (assert-event (sa-hc-concl *sa-salt* *sa-nul-login* *sa-cnonce* *sa-seed* *sa-secret*)))
;   client nonce with a comma: not a nonce
(defconst *sa-comma-nonce* (fn-nntp-string-octets "rOprNG,wEbeRWgbNEkqO"))
(assert-event (not (fn-scram-noncep *sa-comma-nonce*)))
(must-fail-checked
 (assert-event (sa-hc-concl *sa-salt* *sa-name* *sa-comma-nonce* *sa-seed* *sa-secret*)))
;   seed of 31 octets
(defconst *sa-short-seed* (make-list 31 :initial-element 9))
(assert-event (not (fn-sasl-seedp *sa-short-seed*)))
(must-fail-checked
 (assert-event (sa-hc-concl *sa-salt* *sa-name* *sa-cnonce* *sa-short-seed* *sa-secret*)))

; fn-sasl-scram-unknown-login-never-succeeds
(defconst *sa-st1* (fn-auth-session-pending (fn-post-result-session *sa-r1*)))
; Positive witness: the honest final message against no verifier.
(assert-event (not (fn-authsec-verifierp nil)))
(assert-event (not (fn-sasl-successp (fn-sasl-scram-final-step *sa-st1* *sa-final-good* nil nil))))
; Hypothesis removed: against the enrolled verifier it succeeds.
(assert-event (fn-authsec-verifierp *sa-verifier*))
(must-fail-checked
 (assert-event (not (fn-sasl-successp
                     (fn-sasl-scram-final-step *sa-st1* *sa-final-good* *sa-verifier* nil)))))

; fn-sasl-scram-final-success-is-bound-to-the-exchange
(defmacro sa-s4-concl (st response verifier binding)
  `(and (equal (fn-scram-cfin-nonce (fn-scram-parse-client-final ,response))
               (fn-scram-octets (fn-sasl-st 5 ,st)))
        (equal (fn-scram-cfin-cbind (fn-scram-parse-client-final ,response))
               (fn-scram-expected-cbind (fn-sasl-st 2 ,st) (fn-sasl-st 3 ,st) ,binding))
        (fn-authsec-verifierp ,verifier)))
; Positive witness: the honest exchange succeeds; its nonce and binding are
; this exchange's.
(assert-event (fn-sasl-successp (fn-sasl-scram-final-step *sa-st1* *sa-final-good* *sa-verifier* nil)))
(assert-event (sa-s4-concl *sa-st1* *sa-final-good* *sa-verifier* nil))
; Hypothesis removed: a final message with another nonce fails, and its
; nonce is not the exchange's.
(defconst *sa-final-other-nonce*
  (sa-final *sa-secret* :n (fn-nntp-string-octets "n,,") nil
            (append *sa-nonce* (fn-nntp-string-octets "x")) *sa-bare* *sa-server-first*))
(assert-event (not (fn-sasl-successp
                    (fn-sasl-scram-final-step *sa-st1* *sa-final-other-nonce* *sa-verifier* nil))))
(must-fail-checked (assert-event (sa-s4-concl *sa-st1* *sa-final-other-nonce* *sa-verifier* nil)))

; fn-sasl-scram-y-flag-with-a-binding-is-refused
(defconst *sa-y-first* (append (fn-nntp-string-octets "y,,n=reader,r=") *sa-cnonce*))
(defun sa-y-hyps (response binding)
  (and (fn-sasl-bindingp binding)
       (not (fn-scram-failp (fn-scram-parse-client-first response)))
       (equal (fn-scram-cf-flag (fn-scram-parse-client-first response)) :y)))
(defmacro sa-y-concl (plusp response binding)
  `(equal (fn-sasl-scram-first-step ,plusp ,response *sa-verifier* *sa-seed* ,binding)
          (if ,plusp (list :fail :binding-required) (list :fail :downgrade))))
; Positive witnesses, both arms.
(assert-event (sa-y-hyps *sa-y-first* *sa-binding*))
(assert-event (sa-y-concl t *sa-y-first* *sa-binding*))
(assert-event (sa-y-concl nil *sa-y-first* *sa-binding*))
;   no binding installed: "y" is honest (the server offers no -PLUS)
(assert-event (and (not (fn-sasl-bindingp nil))
                   (not (fn-scram-failp (fn-scram-parse-client-first *sa-y-first*)))))
(must-fail-checked (assert-event (sa-y-concl nil *sa-y-first* nil)))
;   the "n" flag
(assert-event (and (fn-sasl-bindingp *sa-binding*)
                   (not (fn-scram-failp (fn-scram-parse-client-first *sa-client-first*)))
                   (not (equal (fn-scram-cf-flag (fn-scram-parse-client-first *sa-client-first*)) :y))))
(must-fail-checked (assert-event (sa-y-concl nil *sa-client-first* *sa-binding*)))
;   (not (fn-scram-failp ...)): NO counter-witness.  The flag of a failed
;   parse is its reason (fn-scram-cf-flag is its second element), e.g.
;   :invalid-username-encoding for "y,,n=,r=abc", never :y; so the flag
;   hypothesis already excludes every failure seen.  Not proved redundant.
(assert-event (equal (fn-scram-cf-flag (fn-scram-parse-client-first
                                        (fn-nntp-string-octets "y,,n=,r=abc")))
                     :invalid-username-encoding))

; fn-auth-step-preserves-consistent-session (the served step itself)
; Positive witnesses: a consistent session stays consistent across a
; command and across the first SCRAM message.
(assert-event (fn-auth-session-consistentp *sa-tls-ctx* *sa-archive*))
(assert-event (fn-auth-session-consistentp
               (fn-post-result-session (sa-send *sa-tls-ctx* "CAPABILITIES")) *sa-archive*))
(assert-event (fn-auth-session-consistentp *sa-plain-ctx* *sa-archive*))
(assert-event (fn-auth-session-consistentp (fn-post-result-session *sa-r1*) *sa-archive*))
; Hypothesis removed: from a value that is no session the step's session is
; not consistent.
(assert-event (not (fn-auth-session-consistentp nil *sa-archive*)))
(must-fail-checked
 (assert-event (fn-auth-session-consistentp
                (fn-post-result-session (sa-send nil "CAPABILITIES")) *sa-archive*)))

; fn-auth-sasl-finish-binds-only-on-success, at the call the host's step
; makes (books/nntp-auth.lisp fn-auth-step's kept exchange:
; (fn-auth-sasl-finish as (fn-auth-session-pending as) response)).
(defconst *sa-q-as* (fn-post-result-session *sa-q1*))
(defconst *sa-q-st* (fn-auth-session-pending *sa-q-as*))
(defconst *sa-q-nonce* (sa-field-value (car (fn-scram-split *sa-q-sf*))))
(defconst *sa-q-final*
  (sa-final *sa-secret* :n (fn-nntp-string-octets "n,,") nil *sa-q-nonce* *sa-bare* *sa-q-sf*))
(defconst *sa-q-final-bad*
  (sa-final (fn-nntp-string-octets "correct-horsf") :n (fn-nntp-string-octets "n,,") nil
            *sa-q-nonce* *sa-bare* *sa-q-sf*))
(defmacro sa-fin-hyps (as st response)
  `(and (not (fn-auth-session-peer ,as))
        (fn-auth-session-peer
         (fn-post-result-session (fn-auth-sasl-finish ,as ,st ,response)))))
(defmacro sa-fin-concl (as st response)
  `(let* ((acfg (fn-auth-session-config ,as))
          (ctx (fn-auth-session-ctx ,as))
          (cred (fn-auth-find-cred (fn-sasl-response-login ,st ,response)
                                   (fn-auth-config-creds acfg)))
          (next (fn-post-result-session (fn-auth-sasl-finish ,as ,st ,response))))
     (and (consp cred)
          (fn-sasl-successp
           (fn-sasl-step ,st ,response (fn-auth-cred-secret cred)
                         (fn-auth-ctx-seed ctx) (fn-auth-ctx-binding ctx)))
          (equal (fn-auth-session-pending next) (fn-auth-cred-name cred))
          (equal (fn-auth-session-subject next) (fn-auth-cred-principal cred))
          (equal (fn-auth-session-peer next)
                 (fn-auth-principal-match
                  (fn-auth-cred-principal cred)
                  (fn-peer-session-cfg (fn-auth-session-base ,as))))
          (fn-auth-principal-rolep next))))
; Positive witness: the pinned principal's honest SCRAM final binds the
; peer role "principal-peer".
(assert-event (sa-fin-hyps *sa-q-as* *sa-q-st* *sa-q-final*))
(assert-event (equal (fn-auth-session-peer
                      (fn-post-result-session (fn-auth-sasl-finish *sa-q-as* *sa-q-st* *sa-q-final*)))
                     "principal-peer"))
(assert-event (sa-fin-concl *sa-q-as* *sa-q-st* *sa-q-final*))
; Hypothesis "the step's session has a peer" removed: the wrong password
; binds nothing (the first hypothesis kept) and nothing succeeded.
(assert-event (and (not (fn-auth-session-peer *sa-q-as*))
                   (not (fn-auth-session-peer
                         (fn-post-result-session
                          (fn-auth-sasl-finish *sa-q-as* *sa-q-st* *sa-q-final-bad*))))))
(must-fail-checked (assert-event (sa-fin-concl *sa-q-as* *sa-q-st* *sa-q-final-bad*)))
; Hypothesis "no peer before" removed: a session that already holds the
; role keeps it through a refused exchange (the second hypothesis holds),
; and nothing succeeded.
(defconst *sa-q-peer-as* (fn-post-result-session *sa-q2*))
(assert-event (and (fn-auth-session-peer *sa-q-peer-as*)
                   (fn-auth-session-peer
                    (fn-post-result-session
                     (fn-auth-sasl-finish *sa-q-peer-as* *sa-q-st* *sa-q-final-bad*)))))
(must-fail-checked (assert-event (sa-fin-concl *sa-q-peer-as* *sa-q-st* *sa-q-final-bad*)))
