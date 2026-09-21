; Executable cases and teeth for the bounded native fn.toml profile.
(in-package "ACL2")
(include-book "../../books/native-config")
(include-book "../../host/native-config-host")

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
                     '(:refused :invalid)))
(assert-event (equal (fn-native-config-load
                      (fn-ncfg-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "tls_cert = \"/x\"")))
                     '(:refused :invalid)))
; The theorem's two hypotheses have concrete counter-inputs: invalid UTF-8
; octet domain and an over-bound input both return the named refusal.
(assert-event (equal (fn-native-config-load (list 255)) '(:refused :bounds-or-encoding)))
(assert-event (equal (fn-native-config-load
                      (append (fn-ncfg-test-lines '("[store]" "path = \"/x\""))
                              (make-list 16400 :initial-element 32)))
                     '(:refused :bounds-or-encoding)))
