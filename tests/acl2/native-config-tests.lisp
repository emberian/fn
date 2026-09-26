; Executable cases and teeth for the bounded native fn.toml profile.
(in-package "ACL2")
(include-book "../../books/native-config")
(include-book "../../host/native-config-host")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-ncfg-test-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10)
              (fn-ncfg-test-lines (cdr lines)))
    nil))

(defconst *fn-ncfg-minimal*
  (fn-ncfg-test-lines
   '("# emitted by an operator" "[store]" "path = \"/var/lib/fn/store\"")))
(defconst *fn-ncfg-minimal-result* (fn-native-config-load *fn-ncfg-minimal*))
(defconst *fn-ncfg-minimal-config* (car (cdr *fn-ncfg-minimal-result*)))

(assert-event (equal (car *fn-ncfg-minimal-result*) :accepted))
(assert-event (equal (fn-native-config-store *fn-ncfg-minimal-config*) "/var/lib/fn/store"))
(assert-event (equal (fn-native-config-listener-host *fn-ncfg-minimal-config*) "127.0.0.1"))
(assert-event (equal (fn-native-config-listener-port *fn-ncfg-minimal-config*) 1119))
(assert-event (equal (fn-native-config-auth-path *fn-ncfg-minimal-config*) "/var/lib/fn/store/auth.toml"))
(assert-event (equal (fn-native-config-control-path *fn-ncfg-minimal-config*) "/var/lib/fn/store/control.sock"))
(assert-event (fn-native-config-operator-availablep *fn-ncfg-minimal-config*))
(assert-event
 (equal (fn-native-config-listener-address
         (fn-record-string-octets
          (fn-native-config-listener-host *fn-ncfg-minimal-config*)))
        '(:inet (127 0 0 1))))

; The native owner consumes the ACL2-selected credential path and policy.
; Required auth and a custom path are live.  Protected-only requires the
; paired TLS paths that the native OpenSSL boundary consumes.
(defconst *fn-ncfg-native-auth*
  (fn-native-config-load
   (fn-ncfg-test-lines
    '("[store]" "path = \"/srv/fn\""
      "[auth]" "required = true" "path = \"/run/fn/credentials.toml\""))))
(assert-event (equal (car *fn-ncfg-native-auth*) :accepted))
(assert-event
 (fn-native-config-operator-availablep (car (cdr *fn-ncfg-native-auth*))))
(defconst *fn-ncfg-native-protected-auth*
  (fn-native-config-load
   (fn-ncfg-test-lines
    '("[store]" "path = \"/srv/fn\""
      "[auth]" "required = true" "protected_only = true"))))
(assert-event
 (not (fn-native-config-operator-availablep
       (car (cdr *fn-ncfg-native-protected-auth*)))))
(defconst *fn-ncfg-native-protected-tls*
  (fn-native-config-load
   (fn-ncfg-test-lines
    '("[store]" "path = \"/srv/fn\""
      "[listener]" "tls_cert = \"/run/fn/cert.pem\""
      "tls_key = \"/run/fn/key.pem\""
      "[auth]" "required = true" "protected_only = true"))))
(assert-event
 (fn-native-config-operator-availablep
  (car (cdr *fn-ncfg-native-protected-tls*))))

(defconst *fn-ncfg-disabled-result*
  (fn-native-config-load
   (fn-ncfg-test-lines
    '("[store]" "path = \"/var/lib/fn/store\""
      "[posting]" "enabled = false"))))
(assert-event
 (fn-native-config-operator-availablep (cadr *fn-ncfg-disabled-result*)))

; A 512-octet store path is legal itself, but its two derived defaults would
; exceed the same path bound.  Supplying bounded auth/control paths explicitly
; is the non-degenerate accepted alternative.
(defconst *fn-ncfg-path-512*
  (coerce (make-list 512 :initial-element #\a) 'string))
(defconst *fn-ncfg-store-512-line*
  (concatenate 'string "path = \"" *fn-ncfg-path-512* "\""))
(defconst *fn-ncfg-derived-over-bound*
  (fn-native-config-load (fn-ncfg-test-lines (list "[store]" *fn-ncfg-store-512-line*))))
(assert-event (equal *fn-ncfg-derived-over-bound* '(:refused :invalid)))
(defconst *fn-ncfg-explicit-bounded-paths*
  (fn-native-config-load
   (fn-ncfg-test-lines
    (list "[store]" *fn-ncfg-store-512-line*
          "[auth]" "path = \"/a\""
          "[control]" "path = \"/c\""))))
(assert-event (equal (car *fn-ncfg-explicit-bounded-paths*) :accepted))

; One operator-written profile with every documented table/key.  Parsing and
; normalization preserve the complete surface; the availability gate refuses
; fields whose native consumers have not landed instead of dropping them.
(defconst *fn-ncfg-full*
  (fn-ncfg-test-lines
   '("[store]" "path = \"/srv/fn\""
     "[listener]" "host = \"::1\"" "port = 2119"
     "tls_cert = \"/etc/fn/cert.pem\"" "tls_key = \"/etc/fn/key.pem\""
     "[auth]" "required = true" "protected_only = true" "path = \"/srv/fn/auth.toml\""
     "[posting]" "enabled = false" "agent = \"news@example.invalid\""
     "[anchor]" "server = \"int08h\""
     "[acl2]" "path = \"acl2\"" "slots = 4"
     "[log]" "path = \"/var/log/fn.log\""
     "[control]" "path = \"/srv/fn/control.sock\"")))
(defconst *fn-ncfg-full-result* (fn-native-config-load *fn-ncfg-full*))
(defconst *fn-ncfg-full-config* (car (cdr *fn-ncfg-full-result*)))

(assert-event (equal (car *fn-ncfg-full-result*) :accepted))
(assert-event (equal (fn-native-config-listener-port *fn-ncfg-full-config*) 2119))
(assert-event (equal (fn-native-config-tls-cert *fn-ncfg-full-config*) "/etc/fn/cert.pem"))
(assert-event (equal (fn-native-config-tls-key *fn-ncfg-full-config*) "/etc/fn/key.pem"))
(assert-event (fn-native-config-auth-requiredp *fn-ncfg-full-config*))
(assert-event (fn-native-config-auth-protected-onlyp *fn-ncfg-full-config*))
(assert-event (not (fn-native-config-posting-enabledp *fn-ncfg-full-config*)))
(assert-event (equal (fn-native-config-posting-agent *fn-ncfg-full-config*) "news@example.invalid"))
(assert-event (equal (fn-native-config-anchor-server *fn-ncfg-full-config*) "int08h"))
(assert-event (equal (fn-native-config-acl2-slots *fn-ncfg-full-config*) 4))
(assert-event (not (fn-native-config-operator-availablep *fn-ncfg-full-config*)))
; The refusal names the first key the native owner cannot consume.
(assert-event (equal (fn-native-config-unsupported-key *fn-ncfg-full-config*)
                     "agent"))
(assert-event
 (equal (fn-native-config-listener-address
         (fn-record-string-octets
          (fn-native-config-listener-host *fn-ncfg-full-config*)))
        '(:inet6 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))))

; `localhost' remains admitted but has the fixed IPv4 loopback projection;
; no raw resolver selects a different address family at run time.
(defconst *fn-ncfg-localhost-result*
  (fn-native-config-load
   (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\""
                         "[listener]" "host = \"localhost\""))))
(assert-event (equal (car *fn-ncfg-localhost-result*) :accepted))
(assert-event
 (equal (fn-native-config-listener-address
         (fn-record-string-octets
          (fn-native-config-listener-host
           (car (cdr *fn-ncfg-localhost-result*)))))
        '(:inet (127 0 0 1))))
(assert-event (equal (fn-native-config-listener-address '(127 0 0 2)) :bad))
(assert-event
 (equal (fn-native-config-listener-address
         (fn-record-string-octets "192.0.2.44"))
        '(:inet (192 0 2 44))))
(assert-event
 (fn-native-config-listener-hostp "192.0.2.44"))
(assert-event
 (not (fn-native-config-listener-hostp "192.0.2.999")))
(assert-event
 (not (fn-native-config-listener-hostp "192.0.2")))
(assert-event
 (not (fn-native-config-listener-hostp "192.000.2.44")))
(assert-event
 (equal (fn-native-config-host-listener-address
         (fn-record-string-octets "127.0.0.1"))
        '(:inet (127 0 0 1))))
(assert-event
 (equal (fn-native-config-host-listener-address
         (fn-record-string-octets "::1"))
        '(:inet6 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))))

; Syntax teeth: each invalid source removes one accepted-profile premise.
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "unknown = true")))
                     '(:refused :syntax)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "path = \"/other\"")))
                     '(:refused :syntax)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\\quoted\"")))
                     '(:refused :syntax)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "host = \"0.0.0.0\"")))
                     '(:refused :listener-unspecified)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "tls_cert = \"/x\"")))
                     '(:refused :invalid)))
;; The implicit-TLS listener (`[listener] tls_port'): offered only with the
;; certificate and key its handshake needs, on a port of its own.
(defconst *fn-ncfg-tls-port-lines*
  '("[store]" "path = \"/srv/fn\"" "[listener]" "port = 1119"
    "tls_cert = \"/c.pem\"" "tls_key = \"/k.pem\"" "tls_port = 1563"))
(assert-event (equal (fn-native-config-listener-tls-port
                      (cadr (fn-native-config-load (fn-ncfg-test-lines *fn-ncfg-tls-port-lines*))))
                     1563))
(assert-event (equal (fn-native-config-listener-tls-port
                      (cadr (fn-native-config-load
                             (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"")))))
                     nil))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "tls_port = 1563")))
                     '(:refused :invalid)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "port = 1119"
                                            "tls_cert = \"/c.pem\"" "tls_key = \"/k.pem\"" "tls_port = 1119")))
                     '(:refused :invalid)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]"
                                            "tls_cert = \"/c.pem\"" "tls_key = \"/k.pem\"" "tls_port = 0")))
                     '(:refused :invalid)))
; The theorem's two hypotheses have concrete counter-inputs: invalid UTF-8
; octet domain and an over-bound input both return the named refusal.
(assert-event (equal (fn-native-config-load (list 255)) '(:refused :bounds-or-encoding)))
(assert-event (equal (fn-native-config-load
                      (append (fn-ncfg-test-lines '("[store]" "path = \"/x\""))
                              (make-list 16400 :initial-element 32)))
                     '(:refused :bounds-or-encoding)))

; -----------------------------------------------------------------------------
; What the native owner admits, key by key (fn-native-config-unsupported-key).

(defun fn-ncfg-test-config (lines)
  (car (cdr (fn-native-config-load (fn-ncfg-test-lines lines)))))

; `[log] path' is consumed: an absolute path is admitted, with and without
; the rest of a deployed profile around it.
(defconst *fn-ncfg-log-config*
  (fn-ncfg-test-config '("[store]" "path = \"/srv/fn\""
                         "[log]" "path = \"/var/log/fn/fn.log\"")))
(assert-event (equal (fn-native-config-log-path *fn-ncfg-log-config*)
                     "/var/log/fn/fn.log"))
(assert-event (fn-native-config-operator-availablep *fn-ncfg-log-config*))
(defconst *fn-ncfg-deployed-config*
  (fn-ncfg-test-config
   '("[store]" "path = \"/tank/fn/node/store\""
     "[listener]" "host = \"192.168.50.39\"" "port = 1119"
     "tls_cert = \"/tank/fn/node/tls/cert.pem\""
     "tls_key = \"/tank/fn/node/tls/key.pem\""
     "[auth]" "required = true" "protected_only = true"
     "path = \"/tank/fn/node/store/auth.toml\""
     "[posting]" "enabled = true"
     "[log]" "path = \"/tank/fn/node/log/fn.log\""
     "[control]" "path = \"/tank/fn/node/store/control.sock\"")))
(assert-event (fn-native-config-operator-availablep *fn-ncfg-deployed-config*))
(assert-event (null (fn-native-config-unsupported-key *fn-ncfg-deployed-config*)))

; A relative log path is refused by name: the service's working directory
; is not part of the profile.
(defconst *fn-ncfg-relative-log-config*
  (fn-ncfg-test-config '("[store]" "path = \"/srv/fn\""
                         "[log]" "path = \"fn.log\"")))
(assert-event (not (fn-native-config-operator-availablep
                    *fn-ncfg-relative-log-config*)))
(assert-event (equal (fn-native-config-unsupported-key
                      *fn-ncfg-relative-log-config*)
                     "log"))

; `[posting] agent' is refused by name whatever it says, the former default
; included: the injecting agent is the path-identity policy
; (books/owner-agent.lisp), and a second slot could only disagree with Path.
; Absent, it normalizes to nil.
(assert-event (null (fn-native-config-posting-agent *fn-ncfg-minimal-config*)))
(defconst *fn-ncfg-agent-config*
  (fn-ncfg-test-config '("[store]" "path = \"/srv/fn\""
                         "[posting]" "agent = \"fn@hbox.ember.software\"")))
(assert-event (equal (fn-native-config-unsupported-key *fn-ncfg-agent-config*)
                     "agent"))
(defconst *fn-ncfg-old-default-agent-config*
  (fn-ncfg-test-config '("[store]" "path = \"/srv/fn\""
                         "[posting]" "agent = \"fn-operator@localhost\"")))
(assert-event (equal (fn-native-config-unsupported-key
                      *fn-ncfg-old-default-agent-config*)
                     "agent"))

; The keys that stay unconsumed, each refused by its own name.
(assert-event
 (equal (fn-native-config-unsupported-key
         (fn-ncfg-test-config '("[store]" "path = \"/srv/fn\""
                                "[anchor]" "server = \"int08h\"")))
        "anchor"))
(assert-event
 (equal (fn-native-config-unsupported-key
         (fn-ncfg-test-config '("[store]" "path = \"/srv/fn\""
                                "[acl2]" "slots = 4")))
        "acl2"))
(assert-event
 (equal (fn-native-config-unsupported-key
         (car (cdr *fn-ncfg-native-protected-auth*)))
        "protected_only"))

;; NNT-041 / PRF-197: the listener address grammar.
(defun fn-ncfg-test-addrs (text)
  (fn-native-config-listener-addresses (fn-record-string-octets text)))
(defun fn-ncfg-test-plan (text)
  (fn-native-config-listener-plan (fn-record-string-octets text)))
(defconst *fn-ncfg-v6-lo* '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))
;; RFC 4291 section 2.2 forms 1, 2 and 3, and RFC 3986 section 3.2.2 brackets.
(assert-event (equal (fn-ncfg-test-addrs "::1") (list (list :inet6 *fn-ncfg-v6-lo*))))
(assert-event (equal (fn-ncfg-test-addrs "[::1]") (list (list :inet6 *fn-ncfg-v6-lo*))))
(assert-event (equal (fn-ncfg-test-addrs "0:0:0:0:0:0:0:1") (list (list :inet6 *fn-ncfg-v6-lo*))))
(assert-event (equal (fn-ncfg-test-addrs "2001:DB8:0:0:8:800:200C:417A")
                     '((:inet6 (32 1 13 184 0 0 0 0 0 8 8 0 32 12 65 122)))))
(assert-event (equal (fn-ncfg-test-addrs "2001:db8::8:800:200c:417a")
                     '((:inet6 (32 1 13 184 0 0 0 0 0 8 8 0 32 12 65 122)))))
(assert-event (equal (fn-ncfg-test-addrs "fe80::")
                     '((:inet6 (254 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))))
(assert-event (equal (fn-ncfg-test-addrs "::13.1.68.3")
                     '((:inet6 (0 0 0 0 0 0 0 0 0 0 0 0 13 1 68 3)))))
;; Several listeners: written order, spaces around commas trimmed.
(assert-event (equal (fn-ncfg-test-addrs "[::1], 127.0.0.1")
                     (list (list :inet6 *fn-ncfg-v6-lo*) '(:inet (127 0 0 1)))))
(assert-event (equal (fn-ncfg-test-addrs "192.0.2.7,2001:db8::7,localhost")
                     '((:inet (192 0 2 7))
                       (:inet6 (32 1 13 184 0 0 0 0 0 0 0 0 0 0 0 7))
                       (:inet (127 0 0 1)))))
;; Refusals name the reason.
(assert-event (equal (fn-ncfg-test-plan "::") '(:refused :listener-unspecified)))
(assert-event (equal (fn-ncfg-test-plan "[::]") '(:refused :listener-unspecified)))
(assert-event (equal (fn-ncfg-test-plan "::ffff:192.0.2.7") '(:refused :listener-mapped)))
(assert-event (equal (fn-ncfg-test-plan "::1,[::1]") '(:refused :listener-duplicate)))
(assert-event (equal (fn-ncfg-test-plan "localhost,127.0.0.1") '(:refused :listener-duplicate)))
(assert-event (equal (fn-ncfg-test-plan "1::2::3") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "1:2:3:4:5:6:7") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "1:2:3:4:5:6:7:8:9") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "12345::1") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "::1:") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "[::1]:1119") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "[::1") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "1.2.3.4::") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "example.org") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "") '(:refused :listener-address)))
(assert-event (equal (fn-ncfg-test-plan "::1,") '(:refused :listener-address)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "host = \"[::1], 192.0.2.7\"")))
                     (list :accepted
                           (fn-native-config-make "/srv/fn" "[::1], 192.0.2.7" 1119 nil nil nil nil
                                                  "/srv/fn/auth.toml" t nil nil nil
                                                  "/srv/fn/control.sock" nil nil nil 10 30 900
                                                  nil nil "user" 3 67108864 7 nil nil))))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "host = \"::ffff:10.0.0.1\"")))
                     '(:refused :listener-mapped)))
(assert-event (equal (fn-native-config-host-listener-addresses
                      (fn-record-string-octets "[::1],127.0.0.1"))
                     (list (list :inet6 *fn-ncfg-v6-lo*) '(:inet (127 0 0 1)))))

;; Teeth for the keystone fn-native-config-listener-addresses-are-bindable-projections.
;; Positive witness: the complete antecedent and conclusion on a two-family list.
(assert-event
 (let ((ps (fn-ncfg-test-addrs "[::1], 192.0.2.7")))
   (and (not (equal ps :bad)) (consp ps)
        (fn-native-config-listener-projection-listp ps)
        (no-duplicatesp-equal ps))))
;; Its one hypothesis: without "not :bad" the conclusion fails (on "::").
(assert-event (equal (fn-ncfg-test-addrs "::") :bad))
(assert-event (not (fn-native-config-listener-projection-listp (fn-ncfg-test-addrs "::"))))
;; The search is closed over the subject so the refusal is quick (the
;; open search took 41.7 s on persvati); "::" above is the counterexample.
(must-fail
 (defthm fn-ncfg-test-addresses-without-admission
   (fn-native-config-listener-projection-listp
    (fn-native-config-listener-addresses host-octets))
   :hints (("Goal" :in-theory (disable fn-native-config-listener-addresses)))))
;; Each clause of the conclusion has a refusal that would violate it.
(assert-event (not (fn-native-config-listener-projectionp '(:inet6 (0 0 0 0 0 0 0 0 0 0 255 255 10 0 0 1)))))
(assert-event (not (fn-native-config-listener-projectionp (list :inet6 *fn-ncfg-ipv6-unspecified*))))
(assert-event (not (fn-native-config-listener-projectionp '(:inet (0 0 0 0)))))
(assert-event (not (no-duplicatesp-equal (list (list :inet6 *fn-ncfg-v6-lo*) (list :inet6 *fn-ncfg-v6-lo*)))))
