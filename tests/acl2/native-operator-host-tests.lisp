; The host wrapper calls the exact ACL2 operator subject.
(in-package "ACL2")
(include-book "../../host/native-operator-host")
(include-book "../../books/codec-attach")

(defconst *fn-nop-host-config*
  (append (fn-record-string-octets "[store]") (list 10)
          (fn-record-string-octets "path = \"/srv/fn\"") (list 10)))
(defconst *fn-nop-host-status-argv*
  (list (fn-record-string-octets "status")))
(defconst *fn-nop-host-result*
  (fn-native-operator-host-run *fn-nop-host-config* *fn-nop-host-status-argv*))
(assert-event (equal (fn-native-operator-result-status *fn-nop-host-result*) :accepted))
(assert-event (equal (fn-native-operator-result-command *fn-nop-host-result*) "status"))
(assert-event (equal (fn-native-operator-host-argv-max-arguments) 32))
(assert-event (equal (fn-native-operator-host-argv-max-octets) 512))
(assert-event (equal (fn-native-operator-host-result-native-action *fn-nop-host-result*)
                     :status))
(assert-event (equal (fn-native-operator-host-result-exit-code *fn-nop-host-result*) 0))
(assert-event (equal (fn-native-operator-host-result-config *fn-nop-host-result*)
                     (fn-native-operator-result-config *fn-nop-host-result*)))
(assert-event (equal (fn-native-operator-host-result-arguments *fn-nop-host-result*)
                     '(:status)))


(defconst *fn-nop-host-run-result*
  (fn-native-operator-host-run *fn-nop-host-config*
                               (list (fn-record-string-octets "run")
                                     (fn-record-string-octets "--once"))))
(assert-event (equal (fn-native-operator-host-result-native-action *fn-nop-host-run-result*)
                     :run))
(assert-event (equal (fn-native-operator-host-result-run-store-octets *fn-nop-host-run-result*)
                     (fn-record-string-octets "/srv/fn")))
(assert-event (equal (fn-native-operator-host-result-run-listener-host-octets *fn-nop-host-run-result*)
                     (fn-record-string-octets "127.0.0.1")))
(assert-event (equal (fn-native-operator-host-result-run-listener-port *fn-nop-host-run-result*) 1119))
(assert-event (equal (fn-native-operator-host-result-run-oncep *fn-nop-host-run-result*) t))
(assert-event (equal (fn-native-operator-host-result-run-max-connections *fn-nop-host-run-result*) 32))

(defconst *fn-nop-host-preflight-help*
  (fn-native-operator-host-preflight
   (list (fn-record-string-octets "help") (fn-record-string-octets "run"))))
(assert-event (equal (fn-native-operator-host-result-status *fn-nop-host-preflight-help*)
                     :accepted))
(assert-event (fn-native-operator-host-preflight-needs-config-p
               (fn-native-operator-host-preflight
                (list (fn-record-string-octets "recover")))))
(assert-event
 (equal (fn-native-operator-host-result-run-auth-path-octets
         *fn-nop-host-run-result*)
        (fn-record-string-octets "/srv/fn/auth.toml")))
(assert-event
 (not (fn-native-operator-host-result-run-auth-requiredp
       *fn-nop-host-run-result*)))
(assert-event
 (not (fn-native-operator-host-result-run-auth-protected-onlyp
       *fn-nop-host-run-result*)))
(assert-event
 (not (fn-native-operator-host-result-run-tls-cert-octets
       *fn-nop-host-run-result*)))
(assert-event
 (not (fn-native-operator-host-result-run-tls-key-octets
       *fn-nop-host-run-result*)))

(defconst *fn-nop-host-auth-config*
  (append *fn-nop-host-config*
          (fn-record-string-octets "[auth]") (list 10)
          (fn-record-string-octets "required = true") (list 10)
          (fn-record-string-octets "path = \"/run/fn/auth.toml\"") (list 10)))
(defconst *fn-nop-host-auth-run-result*
  (fn-native-operator-host-run *fn-nop-host-auth-config*
                               (list (fn-record-string-octets "run"))))
(assert-event
 (equal (fn-native-operator-host-result-native-action
         *fn-nop-host-auth-run-result*) :run))
(assert-event
 (fn-native-operator-host-result-run-auth-requiredp
  *fn-nop-host-auth-run-result*))
(assert-event
 (equal (fn-native-operator-host-result-run-auth-path-octets
         *fn-nop-host-auth-run-result*)
        (fn-record-string-octets "/run/fn/auth.toml")))

(defconst *fn-nop-host-tls-config*
  (append *fn-nop-host-config*
          (fn-record-string-octets "[listener]") (list 10)
          (fn-record-string-octets "tls_cert = \"/run/fn/cert.pem\"") (list 10)
          (fn-record-string-octets "tls_key = \"/run/fn/key.pem\"") (list 10)))
(defconst *fn-nop-host-tls-run-result*
  (fn-native-operator-host-run *fn-nop-host-tls-config*
                               (list (fn-record-string-octets "run"))))
(assert-event
 (equal (fn-native-operator-host-result-native-action
         *fn-nop-host-tls-run-result*) :run))
(assert-event
 (equal (fn-native-operator-host-result-run-tls-cert-octets
         *fn-nop-host-tls-run-result*)
        (fn-record-string-octets "/run/fn/cert.pem")))
(assert-event
 (equal (fn-native-operator-host-result-run-tls-key-octets
         *fn-nop-host-tls-run-result*)
        (fn-record-string-octets "/run/fn/key.pem")))
(defconst *fn-nop-host-admin-result*
  (fn-native-operator-host-run *fn-nop-host-config*
                               (list (fn-record-string-octets "group")
                                     (fn-record-string-octets "create")
                                     (fn-record-string-octets "fn.host"))))
(assert-event (equal (fn-native-operator-host-result-native-action *fn-nop-host-admin-result*)
                     :admin))
(assert-event (equal (fn-native-admin-result-kind
                      (fn-native-operator-host-result-admin-plan *fn-nop-host-admin-result*))
                     :create-group))
(defconst *fn-nop-host-principal-result*
  (fn-native-operator-host-run
   *fn-nop-host-auth-config*
   (list (fn-record-string-octets "principal")
         (fn-record-string-octets "list"))))
(assert-event
 (equal (fn-native-operator-host-result-native-action
         *fn-nop-host-principal-result*) :principal))
(assert-event
 (equal (fn-native-auth-admin-action-kind
         (fn-native-operator-host-result-principal-plan
          *fn-nop-host-principal-result*)) :list))
(assert-event
 (equal (fn-native-operator-host-result-principal-auth-path-octets
         *fn-nop-host-principal-result*)
        (fn-record-string-octets "/run/fn/auth.toml")))
