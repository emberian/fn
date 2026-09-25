; Witnesses and teeth for books/native-config-show.lisp (PKT-096, PKT-097)
; and the [alerts]/[ops] rows of books/native-config.lisp.
(in-package "ACL2")
(include-book "../../books/native-config-show")
(include-book "std/testing/must-fail" :dir :system)

(defun ncst-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10) (ncst-lines (cdr lines)))
    nil))

(defconst *ncst-full-text*
  (ncst-lines
   '("[store]" "path = \"/srv/fn/store\""
     "[listener]" "host = \"127.0.0.1\"" "port = 11932"
     "tls_cert = \"/srv/fn/tls/cert.pem\"" "tls_key = \"/srv/fn/tls/key.pem\""
     "[auth]" "required = true" "protected_only = true"
     "[log]" "path = \"/srv/fn/log/fn.log\""
     "[alerts]" "command = \"/usr/local/bin/fn-alert\"" "headroom_min_percent = 15"
     "refusal_rate_per_minute = 60" "cooldown_seconds = 600"
     "[ops]" "mission = \"relay\"" "unit = \"fn-relay.service\"" "scope = \"system\""
     "keep_releases = 5" "log_max_bytes = 67108864" "log_keep = 9"
     "memory_max = \"24G\"")))
(defconst *ncst-full* (fn-native-config-load *ncst-full-text*))
(defconst *ncst-c* (cadr *ncst-full*))

; The operator's rows are admitted and normalized.
(assert-event (equal (car *ncst-full*) :accepted))
(assert-event (equal (fn-native-config-alerts-command *ncst-c*) "/usr/local/bin/fn-alert"))
(assert-event (equal (fn-native-config-alerts-headroom-min-percent *ncst-c*) 15))
(assert-event (equal (fn-native-config-ops-log-max-bytes *ncst-c*) 67108864))
(assert-event (equal (fn-native-config-ops-scope *ncst-c*) "system"))
(assert-event (equal (fn-native-config-ops-mission *ncst-c*) "relay"))
; They are the operator command's, never the owner's: the run gate is unchanged.
(assert-event (fn-native-config-operator-availablep *ncst-c*))
; Defaults for an absent table.
(defconst *ncst-min* (cadr (fn-native-config-load (ncst-lines '("[store]" "path = \"/x\"")))))
(assert-event (equal (fn-native-config-alerts-headroom-min-percent *ncst-min*) 10))
(assert-event (equal (fn-native-config-alerts-refusal-rate-per-minute *ncst-min*) 30))
(assert-event (equal (fn-native-config-alerts-cooldown-seconds *ncst-min*) 900))
(assert-event (equal (fn-native-config-ops-scope *ncst-min*) "user"))
(assert-event (equal (fn-native-config-ops-keep-releases *ncst-min*) 3))
(assert-event (equal (fn-native-config-ops-log-keep *ncst-min*) 7))
(assert-event (null (fn-native-config-ops-mission *ncst-min*)))

; Invalid rows are refused, each by its own relation.
(defun ncst-with (lines)
  (fn-native-config-load (ncst-lines (append '("[store]" "path = \"/x\"") lines))))
(assert-event (equal (ncst-with '("[alerts]" "headroom_min_percent = 101")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[alerts]" "command = \"fn-alert\"")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[alerts]" "refusal_rate_per_minute = 18446744073709551616"))
                     '(:refused :invalid)))
(assert-event (equal (ncst-with '("[alerts]" "cooldown = 5")) '(:refused :syntax)))
(assert-event (equal (ncst-with '("[ops]" "scope = \"cluster\"")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[ops]" "mission = \"moon\"")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[ops]" "keep_releases = 0")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[ops]" "log_max_bytes = 0")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[ops]" "log_keep = true")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[ops]" "unit = \"a\"" "[ops]" "log_keep = 1")) '(:refused :syntax)))
; The accepted boundary values.
(assert-event (equal (car (ncst-with '("[alerts]" "headroom_min_percent = 100"))) :accepted))
(assert-event (equal (car (ncst-with '("[ops]" "log_keep = 0"))) :accepted))
(assert-event (equal (car (ncst-with '("[alerts]" "refusal_rate_per_minute = 18446744073709551615")))
                     :accepted))

; -----------------------------------------------------------------------------
; fn-native-config-show-round-trip.  Witness: both configurations are
; renderable, and their rendering loads back to them.
(assert-event (fn-native-config-show-wfp *ncst-c*))
(assert-event (fn-native-config-show-wfp *ncst-min*))
(assert-event (equal (fn-native-config-load (fn-native-config-show-octets *ncst-c*))
                     (list :accepted *ncst-c*)))
(assert-event (equal (fn-native-config-load (fn-native-config-show-octets *ncst-min*))
                     (list :accepted *ncst-min*)))
; Teeth (the one hypothesis, well-formedness): a store path with a quote
; is not a configuration the grammar can name, and it does not come back.
(defconst *ncst-quoted*
  (fn-native-config-make "/srv/\"fn" "127.0.0.1" 1119 nil nil nil nil "/a" t nil nil nil "/c"
                         nil nil nil 10 30 900 nil nil "user" 3 67108864 7 nil))
(assert-event (not (fn-native-config-show-wfp *ncst-quoted*)))
(must-fail
 (assert-event (equal (fn-native-config-load (fn-native-config-show-octets *ncst-quoted*))
                      (list :accepted *ncst-quoted*))))
; ... and one whose port is outside the grammar is not rendered as itself.
(defconst *ncst-port*
  (fn-native-config-make "/srv/fn" "127.0.0.1" 70000 nil nil nil nil "/a" t nil nil nil "/c"
                         nil nil nil 10 30 900 nil nil "user" 3 67108864 7 nil))
(must-fail
 (assert-event (equal (fn-native-config-load (fn-native-config-show-octets *ncst-port*))
                      (list :accepted *ncst-port*))))

; `show TABLE KEY'.
(assert-event (equal (fn-native-config-show *ncst-c* "alerts" "headroom_min_percent")
                     (list :shown (fn-record-string-octets "15"))))
(assert-event (equal (fn-native-config-show *ncst-c* "ops" "memory_max")
                     (list :shown (fn-record-string-octets "24G"))))
(assert-event (equal (fn-native-config-show *ncst-c* "auth" "required")
                     (list :shown (fn-record-string-octets "true"))))
(assert-event (equal (fn-native-config-show *ncst-min* "alerts" "command") '(:refused :unset)))
(assert-event (equal (fn-native-config-show *ncst-min* "alerts" "nope") '(:refused :unknown-key)))

; fn-native-config-load-renderable (PRF-094): what the loader accepts is
; renderable, so `show' carries no run-time check.  Witnesses: the full and
; the minimal file load to renderable configurations, and the rendering of
; the full one comes back (fn-native-config-loaded-show-round-trip).
(assert-event (equal (car (fn-native-config-load *ncst-full-text*)) :accepted))
(assert-event (fn-native-config-show-wfp (cadr (fn-native-config-load *ncst-full-text*))))
(assert-event (fn-native-config-show-wfp
               (cadr (fn-native-config-load (ncst-lines '("[store]" "path = \"/x\""))))))
(assert-event (equal (fn-native-config-show *ncst-c* nil nil)
                     (list :shown (fn-native-config-show-octets *ncst-c*))))
; Teeth (the one hypothesis, an accepted load): a refused load's payload is
; not a renderable configuration.
(must-fail
 (assert-event (fn-native-config-show-wfp
                (cadr (ncst-with '("[alerts]" "headroom_min_percent = 101"))))))
(must-fail
 (assert-event (fn-native-config-show-wfp
                (cadr (fn-native-config-load (ncst-lines '("[listener]" "port = 1119")))))))

; -----------------------------------------------------------------------------
; Missions.  Each mission plan is accepted for a node directory, and what it
; writes loads back naming the mission.
(defconst *ncst-node* "/tank/fn/scratch/operator-config/relay")
(defconst *ncst-plans*
  (list (fn-native-mission-plan "small-community" *ncst-node* "127.0.0.1" 11941)
        (fn-native-mission-plan "relay" *ncst-node* "127.0.0.1" 11942)
        (fn-native-mission-plan "archive" *ncst-node* "::1" 11943)))
(assert-event (equal (strip-cars *ncst-plans*) '(:accepted :accepted :accepted)))
(defconst *ncst-relay* (cadr (cadr *ncst-plans*)))
(assert-event (equal (fn-native-config-load (caddr (cadr *ncst-plans*)))
                     (list :accepted *ncst-relay*)))
(assert-event (equal (fn-native-config-ops-mission *ncst-relay*) "relay"))
(assert-event (not (fn-native-config-posting-enabledp *ncst-relay*)))
(assert-event (fn-native-config-auth-protected-onlyp *ncst-relay*))
(assert-event (equal (fn-native-config-alerts-refusal-rate-per-minute *ncst-relay*) 120))
(assert-event (fn-native-config-operator-availablep *ncst-relay*))
(assert-event (equal (fn-native-config-store *ncst-relay*)
                     "/tank/fn/scratch/operator-config/relay/store"))
; Refusals.
(assert-event (equal (fn-native-mission-plan "moon" *ncst-node* "127.0.0.1" 1)
                     '(:refused :unknown-mission)))
(assert-event (equal (fn-native-mission-plan "relay" "/tank/fn/" "127.0.0.1" 1)
                     '(:refused :node-path)))
(assert-event (equal (fn-native-mission-plan "relay" "relative" "127.0.0.1" 1)
                     '(:refused :node-path)))
(assert-event (equal (fn-native-mission-plan "relay" *ncst-node* "0.0.0.0" 1)
                     '(:refused :listener)))
(assert-event (equal (fn-native-mission-plan "relay" *ncst-node* "127.0.0.1" 0)
                     '(:refused :listener)))
; Teeth for fn-native-mission-plan-loads-back (one hypothesis: accepted).
(defconst *ncst-refused* (fn-native-mission-plan "relay" *ncst-node* "0.0.0.0" 1))
(must-fail
 (assert-event (equal (fn-native-config-load (caddr *ncst-refused*))
                      (list :accepted (cadr *ncst-refused*)))))
