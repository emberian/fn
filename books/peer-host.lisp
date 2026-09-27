; fn: a peer's host and the TLS verification its transport selects
; (PKT-613, PRF-231; specs/peering.md section 1.2.4).
;
; A peer's transport names its host as text.  Three things are decided here,
; each by a function the host calls:
;
;   fn-peer-dial-target      how one connection attempt reaches the host:
;                            (:address (a b c d)) for an IPv4 literal (no
;                            resolver is asked), (:resolve NAME) for an RFC
;                            1123 section 2.1 host name (the host asks the
;                            system resolver on that attempt and caches
;                            nothing), (:refused :host-syntax) for anything
;                            else.  host/native/io.lisp `fnn-peer-connect'.
;   fn-peer-tls-verification which certificate check a TLS transport selects:
;                            (:verify NAME SNI TRUST), NAME the configured
;                            server name the chain must match
;                            (SSL_set1_host), SNI whether NAME is sent as
;                            server_name (only a DNS name: RFC 6066 section
;                            3 forbids a literal), TRUST (:pinned PATH) or
;                            (:system-roots).  host/native/feed-service.lisp
;                            `fnn-feed-enable-tls', host/native/pull-service
;                            .lisp `fnn-pull-round'.
;   fn-peer-tls-select       the record `peer add' writes from the operator's
;                            words: `-' as the server name is the host's own
;                            DNS name; `-' as the anchor is the system's
;                            public roots (the default for a named peer), a
;                            path pins that file.
;                            books/native-admin-peer.lisp.
;
; IPv6 literals are refused as peer hosts: the peer dial opens AF_INET
; sockets only (public-node-2 gap H).  A trailing root dot is refused.

(in-package "ACL2")
(include-book "native-config")

(defconst *fn-phost-max-name* 253)   ; RFC 1123 s2.1 / RFC 1035 s2.3.4, text form
(defconst *fn-phost-max-label* 63)

(defun fn-phost-letterp (c)
  (declare (xargs :guard t))
  (and (integerp c) (or (and (<= 65 c) (<= c 90)) (and (<= 97 c) (<= c 122)))))

(defun fn-phost-digitp (c)
  (declare (xargs :guard t))
  (and (integerp c) (<= 48 c) (<= c 57)))

(defun fn-phost-label-endp (n last)
  (declare (xargs :guard t))
  (and (posp n) (<= n *fn-phost-max-label*) (not (equal last 45))))

; One pass over the text: N the current label's length, LAST its last octet,
; ALPHA whether it holds a non-digit.  Labels are letters, digits and hyphens,
; 1 to 63 of them, never beginning or ending with a hyphen (RFC 1123 s2.1
; relaxes RFC 952 to allow a leading digit); the last label is not all digits,
; so a dotted-decimal form is never a name (RFC 1123 s2.1).
(defun fn-phost-scan (xs n last alpha)
  (declare (xargs :guard t))
  (cond ((atom xs) (and (null xs) (fn-phost-label-endp n last) (if alpha t nil)))
        ((equal (car xs) 46)
         (and (fn-phost-label-endp n last)
              (fn-phost-scan (cdr xs) 0 nil nil)))
        ((fn-phost-letterp (car xs))
         (fn-phost-scan (cdr xs) (+ 1 (nfix n)) (car xs) t))
        ((fn-phost-digitp (car xs))
         (fn-phost-scan (cdr xs) (+ 1 (nfix n)) (car xs) alpha))
        ((equal (car xs) 45)
         (and (posp n) (fn-phost-scan (cdr xs) (+ 1 (nfix n)) 45 t)))
        (t nil)))

(defun fn-peer-host-namep (octets)
  (declare (xargs :guard t))
  (and (consp octets)
       (<= (len octets) *fn-phost-max-name*)
       (fn-phost-scan octets 0 nil nil)
       t))

; The octets a resolver may be handed: letters, digits, hyphen, dot.
(defun fn-phost-ldh-dot-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (or (fn-phost-letterp (car xs)) (fn-phost-digitp (car xs))
               (equal (car xs) 45) (equal (car xs) 46))
           (fn-phost-ldh-dot-listp (cdr xs)))
    (null xs)))

(defthm fn-phost-scan-is-ldh
  (implies (fn-phost-scan xs n last alpha)
           (fn-phost-ldh-dot-listp xs)))

; The last label of a name holds a letter or hyphen; a dotted-decimal literal
; holds none.  Stated over the scanner: a scan that succeeds has seen a
; non-digit, non-dot octet in its last label.
(defun fn-phost-some-alphap (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (or (fn-phost-letterp (car xs)) (equal (car xs) 45)
          (fn-phost-some-alphap (cdr xs)))
    nil))

(defthm fn-phost-scan-sees-a-non-digit
  (implies (and (fn-phost-scan xs n last alpha) (not alpha))
           (fn-phost-some-alphap xs)))

(defthm fn-ncfg-ipv4-address-aux-has-no-alpha
  (implies (fn-phost-some-alphap xs)
           (equal (fn-ncfg-ipv4-address-aux xs value digits parts-rev) :bad)))

(defthm fn-peer-host-name-is-not-an-ipv4-literal
  (implies (fn-peer-host-namep octets)
           (equal (fn-native-config-ipv4-address octets) :bad))
  :hints (("Goal" :in-theory (enable fn-native-config-ipv4-address))))

(in-theory (disable fn-phost-scan))

; -----------------------------------------------------------------------------
; The dial target

; KEYSTONE SUBJECT.  host/native/io.lisp `fnn-peer-connect' (called by the
; feed dial, host/native/feed-service.lisp `fnn-feed-dial', and the pull
; dial, host/native/pull-service.lisp `fnn-pull-round').
(defun fn-peer-dial-target (host)
  (declare (xargs :guard t))
  (let ((address (fn-native-config-ipv4-address host)))
    (cond ((not (equal address :bad)) (list :address address))
          ((fn-peer-host-namep host) (list :resolve host))
          (t (list :refused :host-syntax)))))

(defun fn-peer-hostp (host)
  ; A host a peer record may name: an IPv4 literal or an RFC 1123 name.
  (declare (xargs :guard t))
  (not (equal (car (fn-peer-dial-target host)) :refused)))

; KEYSTONE.  The resolver is asked only for an RFC 1123 host name, exactly the
; configured one, of at most 253 octets drawn from letters, digits, hyphen and
; dot; a numeric literal is dialled as the four octets it spells and never
; reaches the resolver; anything else is refused by name before any socket.
(defthm fn-peer-dial-target-decides-the-path
  (let ((target (fn-peer-dial-target host)))
    (and (member-equal (car target) '(:address :resolve :refused))
         (implies (equal (car target) :resolve)
                  (and (equal (cadr target) host)
                       (fn-peer-host-namep host)
                       (<= (len host) *fn-phost-max-name*)
                       (fn-phost-ldh-dot-listp host)
                       (equal (fn-native-config-ipv4-address host) :bad)))
         (implies (equal (car target) :address)
                  (and (equal (cadr target) (fn-native-config-ipv4-address host))
                       (fn-ncfg-octet-listp (cadr target))
                       (equal (len (cadr target)) 4)
                       (not (fn-peer-host-namep host))))
         (implies (equal (car target) :refused)
                  (and (equal target '(:refused :host-syntax))
                       (not (fn-peer-host-namep host))
                       (equal (fn-native-config-ipv4-address host) :bad)))))
  :hints (("Goal" :in-theory (enable fn-phost-scan)
                  :use ((:instance fn-phost-scan-is-ldh (xs host) (n 0) (last nil)
                                   (alpha nil))
                        (:instance fn-peer-host-name-is-not-an-ipv4-literal
                                   (octets host))))))

; -----------------------------------------------------------------------------
; The certificate check a TLS transport selects

(defun fn-phost-cstringp (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (consp (fn-record-string-octets x))
       (not (member-equal 0 (fn-record-string-octets x)))))

(defun fn-peer-trustp (trust)
  ; A transport's trust: a pinned anchor file or the system's public roots.
  (declare (xargs :guard t))
  (or (equal trust :system-roots) (fn-phost-cstringp trust)))

; KEYSTONE SUBJECT.  host/native/feed-service.lisp `fnn-feed-enable-tls' and
; host/native/pull-service.lisp `fnn-pull-round' (the (:tls NAME TRUST)
; effect) call it before any SSL_CTX exists.
(defun fn-peer-tls-verification (server-name trust)
  (declare (xargs :guard t))
  (let ((octets (if (stringp server-name) (fn-record-string-octets server-name) nil)))
    (cond ((not (fn-peer-hostp octets)) (list :refused :server-name))
          ((equal trust :system-roots)
           (list :verify server-name (fn-peer-host-namep octets) '(:system-roots)))
          ((fn-phost-cstringp trust)
           (list :verify server-name (fn-peer-host-namep octets) (list :pinned trust)))
          (t (list :refused :trust)))))

; KEYSTONE.  A TLS transport selects exactly one of: a check of the chain
; against the configured name under the pinned anchor file, a check against
; the configured name under the system's public roots, or a refusal before any
; context exists; never an unchecked or clear session.  The name checked is
; the configured name (an RFC 1123 name or an IPv4 literal); it is sent as
; SNI exactly when it is a DNS name; the system roots are selected only by
; :system-roots and a pinned file only by a path.
(defthm fn-peer-tls-verification-selects-one-check
  (let ((v (fn-peer-tls-verification server-name trust)))
    (and (member-equal (car v) '(:verify :refused))
         (implies (equal (car v) :verify)
                  (and (equal (cadr v) server-name)
                       (stringp server-name)
                       (fn-peer-hostp (fn-record-string-octets server-name))
                       (equal (caddr v)
                              (fn-peer-host-namep
                               (fn-record-string-octets server-name)))
                       (iff (equal (cadddr v) '(:system-roots))
                            (equal trust :system-roots))
                       (iff (equal (cadddr v) (list :pinned trust))
                            (fn-phost-cstringp trust))))
         (implies (and (stringp server-name)
                       (fn-peer-hostp (fn-record-string-octets server-name))
                       (fn-peer-trustp trust))
                  (equal (car v) :verify))))
  :hints (("Goal" :in-theory (disable fn-peer-dial-target fn-peer-host-namep))))

; SNI never carries an address literal (RFC 6066 section 3).
(defthm fn-peer-tls-verification-sni-is-never-a-literal
  (let ((v (fn-peer-tls-verification server-name trust)))
    (implies (and (equal (car v) :verify) (caddr v))
             (equal (fn-native-config-ipv4-address
                     (fn-record-string-octets server-name)) :bad)))
  :hints (("Goal" :in-theory (disable fn-peer-dial-target fn-peer-hostp))))

; -----------------------------------------------------------------------------
; The record `peer add' writes

; (NAME TRUST) for the words SERVER-NAME and ANCHOR of `peer add ... starttls
; SERVER-NAME ANCHOR', or nil.  HOST is the transport's host text.
(defun fn-peer-tls-select (host name-word anchor-word)
  (declare (xargs :guard t))
  (let* ((host-octets (if (stringp host) (fn-record-string-octets host) nil))
         (name (if (equal name-word "-")
                   (if (fn-peer-host-namep host-octets) host nil)
                 name-word))
         (trust (cond ((equal anchor-word "-") :system-roots)
                      ((stringp anchor-word) anchor-word)
                      (t nil))))
    (if (and name
             (equal (car (fn-peer-tls-verification name trust)) :verify))
        (list name trust)
      nil)))

; KEYSTONE.  A named peer given no server name and no anchor is checked
; against its own host name under the system's public roots; a numeric host
; must be given the name its certificate carries; a pinned anchor stays
; available, and whatever is selected is a check fn-peer-tls-verification
; accepts.
(defthm fn-peer-tls-select-named-default
  (implies (and (stringp host) (fn-peer-host-namep (fn-record-string-octets host)))
           (equal (fn-peer-tls-select host "-" "-")
                  (list host :system-roots)))
  :hints (("Goal" :in-theory (enable fn-peer-dial-target))))

(defthm fn-peer-tls-select-numeric-host-needs-a-name-by-definition
  (implies (not (fn-peer-host-namep (if (stringp host) (fn-record-string-octets host) nil)))
           (equal (fn-peer-tls-select host "-" anchor-word) nil)))

(defthm fn-peer-tls-select-is-a-check
  (let ((sel (fn-peer-tls-select host name-word anchor-word)))
    (implies sel
             (and (equal (car (fn-peer-tls-verification (car sel) (cadr sel)))
                         :verify)
                  (iff (equal (cadr sel) :system-roots)
                       (equal anchor-word "-"))
                  (implies (not (equal anchor-word "-"))
                           (equal (cadr sel) anchor-word)))))
  :hints (("Goal" :in-theory (disable fn-peer-dial-target fn-peer-host-namep))))

(in-theory (disable fn-peer-dial-target fn-peer-tls-verification
                    fn-peer-tls-select fn-peer-host-namep))

; -----------------------------------------------------------------------------
; The service-log line of a failed peer dial (host/native/io.lisp
; `fnn-peer-dial-report', from the feed and pull workers).  OUTCOME is the
; host's classification of what it observed; the line names the peer, the
; host as configured and the outcome, and says the attempt is retried: the
; feed's ACL2 backoff (`fn-feed-lost') or the pull's next round.

(defconst *fn-peer-dial-outcome-words*
  '((:unresolved . "unresolved") (:no-address . "no-ipv4-address")
    (:host-syntax . "host-syntax") (:server-name . "server-name")
    (:trust . "trust") (:name-mismatch . "name-mismatch")
    (:certificate . "certificate") (:tls . "tls") (:connect . "connect")))

(defun fn-phost-tokenp (x)
  ; Printable, no space: one token of a log line.
  (declare (xargs :guard t))
  (if (consp x)
      (and (integerp (car x)) (< 32 (car x)) (< (car x) 127)
           (fn-phost-tokenp (cdr x)))
    (null x)))

(defun fn-phost-token (x)
  (declare (xargs :guard t))
  (if (and (consp x) (fn-phost-tokenp x)) x (list 45)))

(defun fn-peer-dial-log-line (via peer host outcome)
  (declare (xargs :guard t))
  (let ((word (cdr (assoc-equal outcome *fn-peer-dial-outcome-words*))))
    (append (fn-record-string-octets "peer dial via=")
            (fn-record-string-octets (if (equal via :pull) "pull" "feed"))
            (fn-record-string-octets " peer=") (fn-phost-token peer)
            (fn-record-string-octets " host=") (fn-phost-token host)
            (fn-record-string-octets " outcome=")
            (fn-record-string-octets (if (stringp word) word "connect"))
            (fn-record-string-octets " retry=yes"))))

; -----------------------------------------------------------------------------
; `fn redeem HOST[:PORT] CODE LOGIN' (the stranger rehearsal's stop 10,
; 2026-09-27): a friend redeems an invitation code without hand-typing
; XREDEEM through `openssl s_client'.  The host (host/native/io.lisp
; fnn-command-redeem) dials, runs TLS (STARTTLS on the reader port or
; implicit TLS with --tls), sends each command this answers and reads each
; reply line; ACL2 decides from the reply's code what comes next and every
; word the friend reads.  The exchange is the server's (books/nntp-auth.lisp
; fn-auth-xredeem; specs/nntp.md "Invitation-code accounts"):
;
;   greeting   200/201            -> STARTTLS (or, under --tls, the code)
;   STARTTLS   382                -> the TLS handshake, then the code
;   XREDEEM CODE LOGIN   381      -> XREDEEM PASS PASSWORD
;   XREDEEM PASS PASSWORD 281     -> done
;
; Any other reply ends it, refused by name with the server's own line.

(defun fn-redeem-reply-code (line)
  "The three-digit code a reply LINE (octets) begins with, or NIL."
  (declare (xargs :guard t))
  (if (and (true-listp line) (<= 3 (len line))
           (natp (nth 0 line)) (<= 48 (nth 0 line)) (<= (nth 0 line) 57)
           (natp (nth 1 line)) (<= 48 (nth 1 line)) (<= (nth 1 line) 57)
           (natp (nth 2 line)) (<= 48 (nth 2 line)) (<= (nth 2 line) 57)
           (or (equal (len line) 3) (equal (nth 3 line) 32)))
      (+ (* 100 (- (nth 0 line) 48)) (* 10 (- (nth 1 line) 48)) (- (nth 2 line) 48))
    nil))

(defun fn-redeem-step (stage line)
  "What `fn redeem' does after reading reply LINE at STAGE.
STAGE is :greeting-starttls, :greeting-tls, :starttls, :code or :password.
Answers (:starttls), (:handshake), (:send-code), (:send-password),
(:done) or (:refused WORD)."
  (declare (xargs :guard t))
  (let ((code (fn-redeem-reply-code line)))
    (cond ((member-equal stage '(:greeting-starttls :greeting-tls))
           (if (member-equal code '(200 201))
               (if (equal stage :greeting-tls) (list :send-code) (list :starttls))
             (list :refused :greeting)))
          ((equal stage :starttls)
           (if (equal code 382) (list :handshake) (list :refused :starttls)))
          ((equal stage :code)
           (if (equal code 381) (list :send-password) (list :refused :code)))
          ((equal stage :password)
           (if (equal code 281) (list :done) (list :refused :password)))
          (t (list :refused :stage)))))

; KEYSTONE.  `fn redeem' reports an account ready only on the server's 281
; to the password, and sends the password only after the server's 381 to
; the code: never on another reply, never out of order.
(defthm fn-redeem-done-only-on-281-after-the-password
  (and (iff (equal (fn-redeem-step stage line) (list :done))
            (and (equal stage :password)
                 (equal (fn-redeem-reply-code line) 281)))
       (iff (equal (fn-redeem-step stage line) (list :send-password))
            (and (equal stage :code)
                 (equal (fn-redeem-reply-code line) 381)))))

(defun fn-redeem-text (outcome login server-line)
  "The line the friend reads for OUTCOME ((:done) or (:refused WORD)); LOGIN
and SERVER-LINE (the server's last reply, octets) are named in it."
  (declare (xargs :guard t))
  (let ((login-octets (if (stringp login) (fn-record-string-octets login) nil))
        (said (if (true-listp server-line) server-line nil)))
    (if (equal outcome (list :done))
        (append (fn-record-string-octets "redeemed: the account ")
                login-octets
                (fn-record-string-octets " is ready; put it and its password in your newsreader (it logs in with AUTHINFO on a new connection)"))
      (append (fn-record-string-octets "refused redeem ")
              (fn-record-string-octets
               (let ((word (and (consp outcome) (consp (cdr outcome)) (cadr outcome))))
                 (cond ((equal word :greeting) "greeting: the server did not greet as a news server")
                       ((equal word :starttls) "starttls: this port does not offer STARTTLS; try --tls with the node's TLS port (563)")
                       ((equal word :code) "code: the invitation code or the login was refused (an expired or used code, or a login already taken)")
                       ((equal word :password) "password: the password was refused")
                       (t "stage"))))
              (fn-record-string-octets "; the server said: ")
              said))))
