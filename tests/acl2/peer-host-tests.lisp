; Witnesses and teeth for a peer's host and the TLS check its transport
; selects (books/peer-host.lisp, PRF-231, PKT-613), and for the three
; callers that write or read it: `peer add' (books/native-admin-peer.lisp),
; the peer record's rows (books/peer-config.lisp) and the pull plan
; (books/peer-pull.lisp).
(in-package "ACL2")
(include-book "../../books/peer-host")
(include-book "../../books/native-admin-peer")
(include-book "../../books/peer-pull")
(include-book "std/testing/must-fail" :dir :system)

(defun pht (s) (fn-record-string-octets s))

; -----------------------------------------------------------------------------
; KEYSTONE fn-peer-dial-target-decides-the-path (no hypotheses; three
; implications, each witnessed with its antecedent and every conclusion).

; :resolve -- a name.
(defconst *pht-name* (pht "news.example.org"))
(assert-event (equal (fn-peer-dial-target *pht-name*) (list :resolve *pht-name*)))
(assert-event (fn-peer-host-namep *pht-name*))
(assert-event (<= (len *pht-name*) *fn-phost-max-name*))
(assert-event (fn-phost-ldh-dot-listp *pht-name*))
(assert-event (equal (fn-native-config-ipv4-address *pht-name*) :bad))
; RFC 1123 s2.1: a leading digit, a hyphen inside, one label.
(assert-event (equal (car (fn-peer-dial-target (pht "1st-node.example"))) :resolve))
(assert-event (equal (car (fn-peer-dial-target (pht "localhost"))) :resolve))
(assert-event (equal (car (fn-peer-dial-target (pht "no-such-peer.invalid"))) :resolve))
; :address -- a literal, never the resolver.
(defconst *pht-v4* (pht "192.0.2.7"))
(assert-event (equal (fn-peer-dial-target *pht-v4*) (list :address '(192 0 2 7))))
(assert-event (fn-ncfg-octet-listp '(192 0 2 7)))
(assert-event (not (fn-peer-host-namep *pht-v4*)))
; :refused -- by name, before any socket.
(assert-event (equal (fn-peer-dial-target (pht "bad_host.example")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (pht "999.1.1.1")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (pht "1.2.3")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (pht "-a.example")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (pht "a-.example")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (pht "a..example")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (pht "example.org.")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (pht "::1")) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target nil) '(:refused :host-syntax)))
(assert-event (equal (fn-peer-dial-target (append (pht "a b") '(0))) '(:refused :host-syntax)))
; The label and name bounds: 63 and 253 admitted, 64 and 254 refused.
(defconst *pht-63* (make-list 63 :initial-element 97))
(assert-event (fn-peer-host-namep *pht-63*))
(assert-event (not (fn-peer-host-namep (cons 97 *pht-63*))))
(defconst *pht-253* (append *pht-63* '(46) *pht-63* '(46) *pht-63* '(46)
                            (make-list 61 :initial-element 98)))
(assert-event (equal (len *pht-253*) 253))
(assert-event (fn-peer-host-namep *pht-253*))
(assert-event (not (fn-peer-host-namep (cons 97 *pht-253*))))
; Teeth: without the :resolve antecedent the host need not be a name; without
; :address it need not be a literal; without :refused it need not be refused.
(must-fail (assert-event (fn-peer-host-namep *pht-v4*)))
(must-fail (assert-event (not (equal (fn-native-config-ipv4-address *pht-name*) :bad))))
(must-fail (assert-event (equal (fn-peer-dial-target *pht-name*) '(:refused :host-syntax))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-peer-tls-verification-selects-one-check.
; Witness (:verify, system roots): a DNS name, SNI sent.
(assert-event (equal (fn-peer-tls-verification "news.example.org" :system-roots)
                     '(:verify "news.example.org" t (:system-roots))))
; Witness (:verify, pinned): a literal name, pinned anchor, no SNI.
(assert-event (equal (fn-peer-tls-verification "192.0.2.7" "/a/ca.pem")
                     '(:verify "192.0.2.7" nil (:pinned "/a/ca.pem"))))
(assert-event (fn-peer-trustp :system-roots))
(assert-event (fn-peer-trustp "/a/ca.pem"))
; The third implication's hypotheses, each removed:
; (stringp server-name)
(assert-event (equal (fn-peer-tls-verification 'news :system-roots) '(:refused :server-name)))
; (fn-peer-hostp ...)
(assert-event (equal (fn-peer-tls-verification "bad name" :system-roots) '(:refused :server-name)))
; (fn-peer-trustp trust)
(assert-event (equal (fn-peer-tls-verification "news.example.org" nil) '(:refused :trust)))
(assert-event (equal (fn-peer-tls-verification "news.example.org" "") '(:refused :trust)))
(assert-event (equal (fn-peer-tls-verification "news.example.org"
                                               (coerce (list #\/ (code-char 0)) 'string))
                     '(:refused :trust)))
(must-fail (assert-event (equal (car (fn-peer-tls-verification 'news :system-roots)) :verify)))
(must-fail (assert-event (equal (car (fn-peer-tls-verification "bad name" "/a/ca.pem")) :verify)))
(must-fail (assert-event (equal (car (fn-peer-tls-verification "news.example.org" nil)) :verify)))

; fn-peer-tls-verification-sni-is-never-a-literal: SNI for a name; a literal
; is checked (SSL_set1_host) but never sent as SNI.
(assert-event (third (fn-peer-tls-verification "news.example.org" "/a/ca.pem")))
(must-fail (assert-event (third (fn-peer-tls-verification "192.0.2.7" "/a/ca.pem"))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-peer-tls-select-named-default and its neighbours.
(assert-event (equal (fn-peer-tls-select "news.example.org" "-" "-")
                     '("news.example.org" :system-roots)))
; Tooth (a DNS name): a numeric host has no name to default to.
(assert-event (equal (fn-peer-tls-select "192.0.2.7" "-" "-") nil))
(must-fail (assert-event (fn-peer-tls-select "192.0.2.7" "-" "-")))
; A numeric host with the name its certificate carries.
(assert-event (equal (fn-peer-tls-select "192.0.2.7" "news.example.org" "-")
                     '("news.example.org" :system-roots)))
; A pinned anchor stays available, for a name or a literal.
(assert-event (equal (fn-peer-tls-select "news.example.org" "-" "/a/ca.pem")
                     '("news.example.org" "/a/ca.pem")))
(assert-event (equal (fn-peer-tls-select "192.0.2.7" "192.0.2.7" "/a/ca.pem")
                     '("192.0.2.7" "/a/ca.pem")))
; A server name that is not a host is refused.
(assert-event (equal (fn-peer-tls-select "news.example.org" "bad name" "-") nil))

; -----------------------------------------------------------------------------
; `peer add' (books/native-admin-peer.lisp): the host and the TLS words.
(defun pht-add (host name anchor)
  (fn-native-admin-peer-plan
   (list "peer" "add" "far" "far.example" host "563" "fn.*" "fn.*"
                   "principal"
                   "0707070707070707070707070707070707070707070707070707070707070707"
                   "/etc/fn/out.auth" "false" "true" "implicit" name anchor)))
(defconst *pht-named* (pht-add "news.example.org" "-" "-"))
(assert-event (equal (fn-native-admin-result-status *pht-named*) :accepted))
(assert-event (equal (fn-cfg-peer-transport (fn-native-admin-result-peer *pht-named*))
                     '(:nntp 1 "news.example.org" 563
                             (:tls :implicit "news.example.org" :system-roots))))
; The rows carry the trust (n = 1) and read back to the same record.
(defconst *pht-named-peer* (fn-native-admin-result-peer *pht-named*))
(assert-event (member-equal '("far" "transport-trust-anchor" "" 1)
                            (fn-cfg-peer-rows *pht-named-peer*)))
(assert-event (equal (fn-cfg-peer-of-rows "far" (fn-cfg-peer-rows *pht-named-peer*))
                     *pht-named-peer*))
; A pinned record's rows are the rows every earlier record wrote (n = 0).
(defconst *pht-pinned-peer*
  (fn-native-admin-result-peer (pht-add "192.0.2.7" "news.example.org" "/a/ca.pem")))
(assert-event (member-equal '("far" "transport-trust-anchor" "/a/ca.pem" 0)
                            (fn-cfg-peer-rows *pht-pinned-peer*)))
(assert-event (equal (fn-cfg-peer-of-rows "far" (fn-cfg-peer-rows *pht-pinned-peer*))
                     *pht-pinned-peer*))
; Refusals: a host that is neither; `-' for the name of a numeric host.
(assert-event (equal (fn-native-admin-result-status (pht-add "bad_host" "-" "-")) :refused))
(assert-event (equal (fn-native-admin-result-status (pht-add "192.0.2.7" "-" "-")) :refused))
(must-fail (assert-event (equal (fn-native-admin-result-status (pht-add "192.0.2.7" "-" "-"))
                                :accepted)))

; The pull plan reads the system roots from the rows (books/peer-pull.lisp).
(assert-event (equal (fn-pull-security-of-rows (fn-cfg-peer-rows *pht-named-peer*))
                     '(:tls :implicit "news.example.org" :system-roots)))

; The dial log line.
(assert-event (equal (fn-peer-dial-log-line :feed (pht "far") (pht "no-such-peer.invalid")
                                            :unresolved)
                     (pht "peer dial via=feed peer=far host=no-such-peer.invalid outcome=unresolved retry=yes")))
(assert-event (equal (fn-peer-dial-log-line :pull (pht "far") (pht "a b") :name-mismatch)
                     (pht "peer dial via=pull peer=far host=- outcome=name-mismatch retry=yes")))

; -----------------------------------------------------------------------------
; fn redeem: fn-redeem-done-only-on-281-after-the-password, witnesses of both
; arms of each iff (the keystone has no hypothesis).
(defconst *rd-281* (fn-record-string-octets "281 account bound; authenticate with AUTHINFO on a new connection"))
(defconst *rd-381* (fn-record-string-octets "381 send the password with XREDEEM PASS"))
(defconst *rd-481* (fn-record-string-octets "481 invitation refused"))
(assert-event (equal (fn-redeem-reply-code *rd-281*) 281))
(assert-event (equal (fn-redeem-step :password *rd-281*) (list :done)))
(assert-event (equal (fn-redeem-step :code *rd-281*) (list :refused :code)))
(assert-event (equal (fn-redeem-step :password *rd-481*) (list :refused :password)))
(assert-event (equal (fn-redeem-step :password (fn-record-string-octets "482 invitation code refused"))
                     (list :refused :code)))
(assert-event (equal (fn-redeem-step :code *rd-381*) (list :send-password)))
(assert-event (equal (fn-redeem-step :password *rd-381*) (list :refused :password)))
(assert-event (equal (fn-redeem-step :greeting-starttls
                                     (fn-record-string-octets "200 fn-nntp ready"))
                     (list :starttls)))
(assert-event (equal (fn-redeem-step :greeting-tls
                                     (fn-record-string-octets "201 fn-nntp ready"))
                     (list :send-code)))
(assert-event (equal (fn-redeem-step :starttls (fn-record-string-octets "382 continue"))
                     (list :handshake)))
(assert-event (equal (fn-redeem-reply-code (fn-record-string-octets "2811 x")) nil))
(assert-event (consp (fn-redeem-text (list :done) "carol" *rd-281*)))
