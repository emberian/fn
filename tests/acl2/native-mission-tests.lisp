; Witnesses and teeth for books/native-mission.lisp (PKT-097) and the
; mission verbs of books/native-operator.lisp.
(in-package "ACL2")
(include-book "../../books/native-mission")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

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
(must-fail (assert-event (fn-bs-profile-admittedp (fn-native-mission-profile "moon"))))

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
(assert-event (equal (fn-native-operator-result-init-profile *nmt-init*)
                     (fn-native-mission-request "relay")))
(defconst *nmt-sc-text*
  (fn-native-operator-result-mission-octets
   (fn-native-operator-mission-run *nmt-path* (nmt-argv '("mission" "small-community")))))
(defconst *nmt-sc-init* (fn-native-operator-run *nmt-sc-text* (nmt-argv '("init"))))
(assert-event (equal (fn-native-operator-result-init-group-octets *nmt-sc-init*)
                     (list (fn-record-string-octets "local.general")
                           (fn-record-string-octets "local.test"))))
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
(must-fail
 (assert-event (equal (fn-native-operator-result-init-profile
                       (fn-native-operator-run *nmt-plain* (nmt-argv '("init" "fn.test"))))
                      (fn-native-mission-request nil))))
; Without the init command: another verb plans no profile.
(must-fail
 (assert-event (equal (fn-native-operator-result-init-profile
                       (fn-native-operator-run *nmt-text* (nmt-argv '("status"))))
                      (fn-native-mission-request "relay"))))
; Without acceptance: a refused init plans no profile.
(must-fail
 (assert-event (equal (fn-native-operator-result-init-profile
                       (fn-native-operator-run *nmt-text* (nmt-argv '("init" "--profile" "scale" "x"))))
                      (fn-native-mission-request "relay"))))
; Without a loadable configuration: nothing is planned.
(must-fail
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
