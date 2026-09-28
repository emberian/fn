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
                  (append *sa-reader-lines-posting* '("STARTTLS" "SASL SCRAM-SHA-256")))))
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
