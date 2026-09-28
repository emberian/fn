; fn: the RFC 7677 exchange and the teeth of books/scram.lisp.
;
; RFC 7677 section 3 prints one complete SCRAM-SHA-256 exchange (user
; "user", password "pencil"):
;
;   C: n,,n=user,r=rOprNGfwEbeRWgbNEkqO
;   S: r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,
;      s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096
;   C: c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,
;      p=dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ=
;   S: v=6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4=
;
; Below, the server's half runs on the client's two messages with the keys
; `fn-scram-keys' derives from "pencil": it must print the RFC's
; server-first byte for byte (given the RFC's server nonce and salt) and
; accept the RFC's proof with the RFC's server-final.  Then the teeth: each
; clause of the check is shown refusing, on the same exchange with one
; thing changed, so that no clause is vacuous.  Evidence on these inputs,
; not proof; `fn-scram-honest-proof-verifies' and the refusal keystones are
; the universal statements.

(in-package "ACL2")
(include-book "../../books/scram")

(defmacro st-text (s) `(fn-scram-text ,s))

(defconst *st-client-first* (st-text "n,,n=user,r=rOprNGfwEbeRWgbNEkqO"))
(defconst *st-snonce* (st-text "%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0"))
(defconst *st-nonce*
  (st-text "rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0"))
(defconst *st-salt*
  (mv-let (err octets) (fn-ot-b64-decode (st-text "W22ZaJ0SNY7soEsUEjb6gQ=="))
    (declare (ignore err))
    octets))
(defconst *st-client-final*
  (st-text "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="))
(defconst *st-server-final*
  (st-text "v=6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4="))

(defconst *st-cf* (fn-scram-parse-client-first *st-client-first*))
(defconst *st-keys* (fn-scram-keys (st-text "pencil") *st-salt* 4096))

; The client-first parse: no binding, no authzid, the user and the nonce,
; the gs2 header "n,," and the bare message.
(assert-event (equal (car *st-cf*) :client-first))
(assert-event (equal (fn-scram-cf-flag *st-cf*) :n))
(assert-event (equal (fn-scram-cf-authzid *st-cf*) nil))
(assert-event (equal (fn-scram-cf-username *st-cf*) (st-text "user")))
(assert-event (equal (fn-scram-cf-cnonce *st-cf*) (st-text "rOprNGfwEbeRWgbNEkqO")))
(assert-event (equal (fn-scram-cf-gs2 *st-cf*) (st-text "n,,")))
(assert-event (equal (fn-scram-cf-bare *st-cf*)
                     (st-text "n=user,r=rOprNGfwEbeRWgbNEkqO")))

; The server-first message, byte for byte.
(defconst *st-sf*
  (fn-scram-server-first (fn-scram-cf-cnonce *st-cf*) *st-snonce* *st-salt* 4096))
(assert-event
 (equal *st-sf*
        (st-text "r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096")))

(defmacro st-finish (msg flag gs2 binding nonce stored server)
  `(fn-scram-finish ,msg ,flag ,gs2 ,binding ,nonce
                    (fn-scram-cf-bare *st-cf*) *st-sf* ,stored ,server))

; POSITIVE WITNESS: the RFC's proof is accepted with the RFC's server-final.
(assert-event
 (equal (st-finish *st-client-final* :n (st-text "n,,") nil *st-nonce*
                   (car *st-keys*) (cadr *st-keys*))
        (list :accept *st-server-final*)))

; The client half agrees with the RFC's client: the client-final it builds
; from the password is the RFC's message.
(assert-event
 (equal (fn-scram-client-final (st-text "pencil") *st-salt* 4096 :n
                               (st-text "n,,") nil *st-nonce*
                               (fn-scram-cf-bare *st-cf*) *st-sf*)
        *st-client-final*))

; TEETH.  Each is the same exchange with one thing changed.

; A wrong password's keys: the proof is refused.
(assert-event
 (let ((keys (fn-scram-keys (st-text "pencim") *st-salt* 4096)))
   (equal (st-finish *st-client-final* :n (st-text "n,,") nil *st-nonce*
                     (car keys) (cadr keys))
          (list :fail :invalid-proof))))

; No stored key (an unknown login): refused as a wrong proof is.
(assert-event
 (equal (st-finish *st-client-final* :n (st-text "n,,") nil *st-nonce* nil nil)
        (list :fail :invalid-proof)))

; Another exchange's nonce (a replayed final message): refused before any key.
(assert-event
 (equal (st-finish *st-client-final* :n (st-text "n,,") nil
                   (st-text "rOprNGfwEbeRWgbNEkqOanother-server-nonce")
                   (car *st-keys*) (cadr *st-keys*))
        (list :fail :nonce-mismatch)))

; A binding the exchange did not fix: the client said "n" but the server
; expects a tls-exporter header (as if the first message had said "p").
(assert-event
 (equal (st-finish *st-client-final* :p (st-text "p=tls-exporter,,")
                   (make-list 32 :initial-element 7) *st-nonce*
                   (car *st-keys*) (cadr *st-keys*))
        (list :fail :channel-bindings-dont-match)))

; The proof altered in one octet (base64 "dHzb" -> "eHzb"): refused.
(assert-event
 (equal (st-finish (st-text "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=eHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ=")
                   :n (st-text "n,,") nil *st-nonce*
                   (car *st-keys*) (cadr *st-keys*))
        (list :fail :invalid-proof)))

; A proof that is not base64: refused as an encoding error.
(assert-event
 (equal (st-finish (st-text "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=!!!!")
                   :n (st-text "n,,") nil *st-nonce*
                   (car *st-keys*) (cadr *st-keys*))
        (list :fail :invalid-encoding)))

; -PLUS: an honest client over a tls-exporter binding is accepted, and the
; same client-final against another connection's exporter value is refused.
(defconst *st-binding* (make-list 32 :initial-element 42))
(defconst *st-plus-cf*
  (fn-scram-parse-client-first (st-text "p=tls-exporter,,n=user,r=rOprNGfwEbeRWgbNEkqO")))
(assert-event (equal (fn-scram-cf-flag *st-plus-cf*) :p))
(defconst *st-plus-final*
  (fn-scram-client-final (st-text "pencil") *st-salt* 4096 :p
                         (fn-scram-cf-gs2 *st-plus-cf*) *st-binding* *st-nonce*
                         (fn-scram-cf-bare *st-plus-cf*) *st-sf*))
(assert-event
 (equal (car (fn-scram-finish *st-plus-final* :p (fn-scram-cf-gs2 *st-plus-cf*)
                              *st-binding* *st-nonce* (fn-scram-cf-bare *st-plus-cf*)
                              *st-sf* (car *st-keys*) (cadr *st-keys*)))
        :accept))
(assert-event
 (equal (fn-scram-finish *st-plus-final* :p (fn-scram-cf-gs2 *st-plus-cf*)
                         (make-list 32 :initial-element 43) *st-nonce*
                         (fn-scram-cf-bare *st-plus-cf*)
                         *st-sf* (car *st-keys*) (cadr *st-keys*))
        (list :fail :channel-bindings-dont-match)))

; The client-first grammar's refusals.
(assert-event
 (equal (fn-scram-parse-client-first (st-text "p=tls-unique,,n=user,r=abc"))
        (list :fail :unsupported-channel-binding-type)))
(assert-event
 (equal (fn-scram-parse-client-first (st-text "n,,m=ext,n=user,r=abc"))
        (list :fail :extensions-not-supported)))
(assert-event
 (equal (fn-scram-parse-client-first (st-text "n,,n=us=er,r=abc"))
        (list :fail :invalid-username-encoding)))
(assert-event
 (equal (fn-scram-parse-client-first (st-text "n,,n=,r=abc"))
        (list :fail :invalid-username-encoding)))
(assert-event
 (equal (fn-scram-parse-client-first (st-text "x,,n=user,r=abc"))
        (list :fail :other-error)))
(assert-event
 (equal (fn-scram-parse-client-first (st-text "n,,n=user"))
        (list :fail :other-error)))
; A saslname's escapes decode: "=2C" is ",", "=3D" is "=".
(assert-event
 (equal (fn-scram-cf-username
         (fn-scram-parse-client-first (st-text "n,,n=a=2Cb=3Dc,r=abc")))
        (st-text "a,b=c")))
; An authzid is read.
(assert-event
 (equal (fn-scram-cf-authzid
         (fn-scram-parse-client-first (st-text "n,a=user,n=user,r=abc")))
        (st-text "user")))
