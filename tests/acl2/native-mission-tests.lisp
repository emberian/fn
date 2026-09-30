; Witnesses and teeth for books/native-mission.lisp (PKT-097) and the
; mission verbs of books/native-operator.lisp.
(in-package "ACL2")
(include-book "../../books/native-mission")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun nmt-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (nmt-argv (cdr words)))
    nil))

; The three missions' profiles: admitted, with the spike's article and
; group bounds over the D27 defaults.
(assert-event (fn-bs-profile-admittedp (fn-native-mission-profile "small-community")))
(assert-event (equal (fn-bs-profile-max-article-octets (fn-native-mission-profile "relay"))
                     1048576))
(assert-event (equal (fn-bs-profile-max-groups-per-article
                      (fn-native-mission-profile "small-community"))
                     8))
(assert-event (equal (fn-bs-profile-max-groups-per-article (fn-native-mission-profile "archive"))
                     16))
; Teeth for fn-native-mission-store-opens-with-its-profile: a name outside
; the table has no profile.
(must-fail-checked (assert-event (fn-bs-profile-admittedp (fn-native-mission-profile "moon"))))

; The verb: `mission relay' at a config path writes the relay rendering.
(defconst *nmt-path* (fn-record-string-octets "/tank/fn/scratch/operator-config/relay/fn.toml"))
(defconst *nmt-mission*
  (fn-native-operator-mission-run *nmt-path* (nmt-argv '("mission" "relay" "--port" "11942"))))
(assert-event (equal (fn-native-operator-result-status *nmt-mission*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *nmt-mission*) :mission))
(defconst *nmt-text* (fn-native-operator-result-mission-octets *nmt-mission*))
(assert-event (equal (fn-native-operator-result-mission-directory-octets *nmt-mission*)
                     (list (fn-record-string-octets "/tank/fn/scratch/operator-config/relay/log")
                           (fn-record-string-octets "/tank/fn/scratch/operator-config/relay/tls"))))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-mission-outcome *nmt-mission* t))
                     :refused))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-mission-run *nmt-path* (nmt-argv '("mission" "moon"))))
                     :refused))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-mission-run *nmt-path* (nmt-argv '("mission" "relay" "--port"))))
                     :usage))
(assert-event (fn-native-operator-preflight-needs-config-path-p
               (fn-native-operator-command-preflight (nmt-argv '("mission" "relay")))))

; fn-native-operator-run-init-under-a-mission.  Witness: `init fn.test'
; under the relay fn.toml plans the relay request; `init' alone under a
; small community serves its default pair.
(defconst *nmt-init*
  (fn-native-operator-run *nmt-text* (nmt-argv '("init" "fn.test"))))
(assert-event (equal (fn-native-operator-result-status *nmt-init*) :accepted))
; PKT-648: a store `init' makes under a mission's fn.toml requires durable
; storage (books/store-mount-identity.lisp fn-smid-init-policy of this).
(assert-event (fn-native-operator-result-config-mission *nmt-init*))
(assert-event (equal (fn-native-operator-result-init-profile *nmt-init*)
                     (fn-native-mission-request "relay")))
(defconst *nmt-sc-text*
  (fn-native-operator-result-mission-octets
   (fn-native-operator-mission-run *nmt-path* (nmt-argv '("mission" "small-community")))))
(defconst *nmt-sc-init* (fn-native-operator-run *nmt-sc-text* (nmt-argv '("init"))))
; PKT-708: and control.cancel, where readers' own cancels are filed.
(assert-event (equal (fn-native-operator-result-init-group-octets *nmt-sc-init*)
                     (list (fn-record-string-octets "local.general")
                           (fn-record-string-octets "local.test")
                           (fn-record-string-octets "control.cancel"))))
(assert-event (equal (fn-native-operator-result-init-profile *nmt-sc-init*)
                     (fn-native-mission-request "small-community")))
; A profile word is refused under a mission; relay has no default groups.
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run *nmt-text* (nmt-argv '("init" "--profile" "scale" "x"))))
                     :mission-fixes-profile))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *nmt-text* (nmt-argv '("init"))))
                     :usage))
; Teeth, one per hypothesis of the run keystone.
; Without a mission in the configuration: the plain init plans the defaults.
(defconst *nmt-plain* (append (fn-record-string-octets "[store]") '(10)
                              (fn-record-string-octets "path = \"/x\"") '(10)))
(must-fail-checked
 (assert-event (equal (fn-native-operator-result-init-profile
                       (fn-native-operator-run *nmt-plain* (nmt-argv '("init" "fn.test"))))
                      (fn-native-mission-request nil))))
; Without the init command: another verb plans no profile.
(must-fail-checked
 (assert-event (equal (fn-native-operator-result-init-profile
                       (fn-native-operator-run *nmt-text* (nmt-argv '("status"))))
                      (fn-native-mission-request "relay"))))
; Without acceptance: a refused init plans no profile.
(must-fail-checked
 (assert-event (equal (fn-native-operator-result-init-profile
                       (fn-native-operator-run *nmt-text* (nmt-argv '("init" "--profile" "scale" "x"))))
                      (fn-native-mission-request "relay"))))
; Without a loadable configuration: nothing is planned.
(must-fail-checked
 (assert-event (equal (fn-native-operator-result-init-profile
                       (fn-native-operator-run '(255) (nmt-argv '("init" "fn.test"))))
                      (fn-native-mission-request "relay"))))

; `show' through the operator.
(defconst *nmt-show* (fn-native-operator-run *nmt-text* (nmt-argv '("show"))))
(assert-event (equal (fn-native-operator-result-native-action *nmt-show*) :show))
(assert-event (equal (fn-native-operator-result-show-octets *nmt-show*) *nmt-text*))
(assert-event (equal (fn-native-operator-result-show-octets
                      (fn-native-operator-run *nmt-text* (nmt-argv '("show" "ops" "mission"))))
                     (fn-record-string-octets "relay")))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *nmt-text* (nmt-argv '("show" "ops" "nope"))))
                     :usage))

; HST-008 (the walk, finding a): the usage line under a mission says what init
; accepts there.
(assert-event (stringp (fn-native-operator-result-hint
                        (fn-native-operator-run *nmt-text* (nmt-argv '("init" "--profile" "scale" "x"))))))

; Row Q10a: `mission ... --tls-port P [--tls-name NAME ...]'.  The fn.toml
; names the TLS port and the pair beside it; the request names the pair.
(defconst *nmt-tls*
  (fn-native-operator-mission-run *nmt-path*
                                  (nmt-argv '("mission" "relay" "--port" "11942"
                                              "--tls-port" "11943"
                                              "--tls-name" "news.example.org"
                                              "--tls-name" "127.0.0.1"))))
(assert-event (equal (fn-native-operator-result-status *nmt-tls*) :accepted))
(assert-event (equal (fn-native-operator-result-self-signed *nmt-tls*)
                     (list (list "news.example.org" "127.0.0.1") 365
                           (fn-record-string-octets "/tank/fn/scratch/operator-config/relay/tls/cert.pem")
                           (fn-record-string-octets "/tank/fn/scratch/operator-config/relay/tls/key.pem"))))
(assert-event (equal (fn-native-config-listener-tls-port
                      (cadr (fn-native-config-load
                             (fn-native-operator-result-mission-octets *nmt-tls*))))
                     11943))
; No --tls-name: the --host address is the name.
(assert-event (equal (car (fn-native-operator-result-self-signed
                           (fn-native-operator-mission-run
                            *nmt-path* (nmt-argv '("mission" "relay" "--host" "192.0.2.7"
                                                   "--tls-port" "563")))))
                     (list "192.0.2.7")))
; Without --tls-port there is no pair.
(assert-event (null (fn-native-operator-result-self-signed *nmt-mission*)))
; Refused by name: the unspecified address as a name, a bad name, the TLS
; port equal to the port.
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-mission-run
                       *nmt-path* (nmt-argv '("mission" "relay" "--tls-port" "563"
                                              "--tls-name" "0.0.0.0"))))
                     :tls-name))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-mission-run
                       *nmt-path* (nmt-argv '("mission" "relay" "--tls-port" "563"
                                              "--tls-name" "bad_name"))))
                     :tls-name))
; --tls-name alone: the pair for STARTTLS, no TLS port.
(assert-event (let ((r (fn-native-operator-mission-run
                        *nmt-path* (nmt-argv '("mission" "relay" "--tls-name" "a.example")))))
                (and (equal (car (fn-native-operator-result-self-signed r)) (list "a.example"))
                     (null (fn-native-config-listener-tls-port
                            (cadr (fn-native-config-load
                                   (fn-native-operator-result-mission-octets r))))))))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-mission-run
                       *nmt-path* (nmt-argv '("mission" "relay" "--port" "563"
                                              "--tls-port" "563"))))
                     :refused))
; An existing certificate or key is refused by name (`exists').
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-self-signed-outcome *nmt-tls* t nil))
                     :exists))
(assert-event (equal (fn-native-operator-self-signed-outcome *nmt-tls* nil nil) *nmt-tls*))

; `tls self-signed NAME... [--days N]' under the mission's configuration.
(defconst *nmt-tls-text* (fn-native-operator-result-mission-octets *nmt-tls*))
(defun nmt-tls-run (words)
  (fn-native-operator-run-at (fn-record-string-octets "/") *nmt-path* *nmt-tls-text*
                             (nmt-argv words)))
(defconst *nmt-ss* (nmt-tls-run '("tls" "self-signed" "news.example.org" "--days" "30")))
(assert-event (equal (fn-native-operator-result-status *nmt-ss*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *nmt-ss*) :tls-self-signed))
(assert-event (equal (fn-native-operator-result-self-signed *nmt-ss*)
                     (list (list "news.example.org") 30
                           (fn-record-string-octets "/tank/fn/scratch/operator-config/relay/tls/cert.pem")
                           (fn-record-string-octets "/tank/fn/scratch/operator-config/relay/tls/key.pem"))))
(assert-event (equal (cadr (fn-native-operator-result-self-signed
                            (nmt-tls-run '("tls" "self-signed" "a.example" "b.example"))))
                     365))
(assert-event (equal (fn-native-operator-result-reason
                      (nmt-tls-run '("tls" "self-signed" "::"))) :tls-name))
(assert-event (equal (fn-native-operator-result-status
                      (nmt-tls-run '("tls" "self-signed"))) :usage))
(assert-event (equal (fn-native-operator-result-status
                      (nmt-tls-run '("tls" "self-signed" "a.example" "--days"))) :usage))
(assert-event (equal (fn-native-operator-result-native-action (nmt-tls-run '("tls" "reload")))
                     :tls))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-self-signed-refused *nmt-ss* :clock))
                     :clock))
