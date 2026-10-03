; Witnesses and teeth for books/native-config-show.lisp (PKT-096, PKT-097)
; and the [alerts]/[ops] rows of books/native-config.lisp.
(in-package "ACL2")
(include-book "../../books/native-config-show")
(include-book "must-fail-checked")

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
; The implicit-TLS listener's port renders and comes back.
(defconst *ncst-tls*
  (cadr (fn-native-config-load
         (ncst-lines
          '("[store]" "path = \"/srv/fn\"" "[listener]" "tls_cert = \"/c.pem\""
            "tls_key = \"/k.pem\"" "tls_port = 1563")))))
(assert-event (equal (fn-native-config-listener-tls-port *ncst-tls*) 1563))
(assert-event (equal (fn-native-config-load (fn-native-config-show-octets *ncst-tls*))
                     (list :accepted *ncst-tls*)))
 ; Explicit output resources survive show/load, alone and beside cold resources.
(defconst *ncst-output*
  (ncst-with '("[resources]" "output_heap_octets = 4096"
               "output_quantum_heap_octets = 1024")))
(defconst *ncst-cold-output*
  (ncst-with '("[resources]" "cold_heap_octets = 8192" "cold_workers = 1"
               "cold_descriptors = 2" "cold_read_ids = 3" "cold_file_ids = 4"
               "output_heap_octets = 4096" "output_quantum_heap_octets = 1024")))
(assert-event
 (let ((c (cadr *ncst-output*)))
   (and (equal (car *ncst-output*) :accepted)
        (fn-native-config-show-wfp c)
        (equal (fn-native-config-output-resources c) '(4096 1024))
        (equal (fn-native-config-load (fn-native-config-show-octets c))
               (list :accepted c)))))
(assert-event
 (let ((c (cadr *ncst-cold-output*)))
   (and (equal (car *ncst-cold-output*) :accepted)
        (fn-native-config-show-wfp c)
        (equal (fn-native-config-cold-resources c) '(8192 1 2 3 4))
        (equal (fn-native-config-output-resources c) '(4096 1024))
        (equal (fn-native-config-load (fn-native-config-show-octets c))
               (list :accepted c)))))
(assert-event
 (equal (fn-native-config-show (cadr *ncst-output*) "resources" "output_heap_octets")
        (list :shown (fn-record-string-octets "4096"))))
(assert-event
 (equal (fn-native-config-show (cadr *ncst-cold-output*) "resources" "output_quantum_heap_octets")
        (list :shown (fn-record-string-octets "1024"))))
(assert-event (equal (ncst-with '("[resources]" "output_heap_octets = 4096"))
                     '(:refused :invalid)))
(assert-event (equal (ncst-with '("[resources]" "output_heap_octets = 1024"
                                 "output_quantum_heap_octets = 1024"))
                     '(:refused :invalid)))

; Teeth (the one hypothesis, well-formedness): a store path with a quote
; is not a configuration the grammar can name, and it does not come back.
(defconst *ncst-quoted*
  (fn-native-config-make "/srv/\"fn" "127.0.0.1" 1119 nil nil nil nil "/a" t nil nil nil "/c"
                         nil nil nil 10 30 900 nil nil "user" 3 67108864 7 nil nil))
(assert-event (not (fn-native-config-show-wfp *ncst-quoted*)))
(must-fail-checked
 (assert-event (equal (fn-native-config-load (fn-native-config-show-octets *ncst-quoted*))
                      (list :accepted *ncst-quoted*))))
; ... and one whose port is outside the grammar is not rendered as itself.
(defconst *ncst-port*
  (fn-native-config-make "/srv/fn" "127.0.0.1" 70000 nil nil nil nil "/a" t nil nil nil "/c"
                         nil nil nil 10 30 900 nil nil "user" 3 67108864 7 nil nil))
(must-fail-checked
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
(must-fail-checked
 (assert-event (fn-native-config-show-wfp
                (cadr (ncst-with '("[alerts]" "headroom_min_percent = 101"))))))
(must-fail-checked
 (assert-event (fn-native-config-show-wfp
                (cadr (fn-native-config-load (ncst-lines '("[listener]" "port = 1119")))))))

; -----------------------------------------------------------------------------
; Missions.  Each mission plan is accepted for a node directory, and what it
; writes loads back naming the mission.
(defconst *ncst-node* "/tank/fn/scratch/operator-config/relay")
(defconst *ncst-plans*
  (list (fn-native-mission-plan "small-community" *ncst-node* "127.0.0.1" 11941 nil)
        (fn-native-mission-plan "relay" *ncst-node* "127.0.0.1" 11942 nil)
        (fn-native-mission-plan "archive" *ncst-node* "::1" 11943 nil)
        ; Row Q10a: a mission with a TLS port.
        (fn-native-mission-plan "relay" *ncst-node* "127.0.0.1" 11944 11945)))
(assert-event (equal (strip-cars *ncst-plans*) '(:accepted :accepted :accepted :accepted)))
(assert-event (let ((c (cadr (cadddr *ncst-plans*))))
                (and (equal (fn-native-config-load (caddr (cadddr *ncst-plans*)))
                            (list :accepted c))
                     (equal (fn-native-config-listener-tls-port c) 11945))))
(defconst *ncst-relay* (cadr (cadr *ncst-plans*)))
(assert-event (equal (fn-native-config-load (caddr (cadr *ncst-plans*)))
                     (list :accepted *ncst-relay*)))
(assert-event (equal (fn-native-config-ops-mission *ncst-relay*) "relay"))
(assert-event (not (fn-native-config-posting-enabledp *ncst-relay*)))
(assert-event (fn-native-config-auth-protected-onlyp *ncst-relay*))
(assert-event (equal (fn-native-config-alerts-refusal-rate-per-minute *ncst-relay*) 120))
; Row S8: the mission writes its paths relative to the node directory; the
; operator resolves them (tests/acl2/native-config-paths-tests.lisp has the
; resolved configuration, which `run' accepts).
(assert-event (equal (fn-native-config-store *ncst-relay*) "store"))
(assert-event (equal (fn-native-config-log-path *ncst-relay*) "log/fn.log"))
; Refusals.
(assert-event (equal (fn-native-mission-plan "moon" *ncst-node* "127.0.0.1" 1 nil)
                     '(:refused :unknown-mission)))
(assert-event (equal (fn-native-mission-plan "relay" "/tank/fn/" "127.0.0.1" 1 nil)
                     '(:refused :node-path)))
(assert-event (equal (fn-native-mission-plan "relay" "relative" "127.0.0.1" 1 nil)
                     '(:refused :node-path)))
(assert-event (equal (fn-native-mission-plan "relay" *ncst-node* "0.0.0.0" 1 nil)
                     '(:refused :listener)))
(assert-event (equal (fn-native-mission-plan "relay" *ncst-node* "127.0.0.1" 0 nil)
                     '(:refused :listener)))
; Teeth for fn-native-mission-plan-loads-back (one hypothesis: accepted).
(defconst *ncst-refused* (fn-native-mission-plan "relay" *ncst-node* "0.0.0.0" 1 nil))
(must-fail-checked
 (assert-event (equal (fn-native-config-load (caddr *ncst-refused*))
                      (list :accepted (cadr *ncst-refused*)))))

; P12 explicit cold policy is normalized and canonically rendered; its
; numerical allocator/launcher suitability is a separate admission boundary.
(defconst *ncst-cold*
  (ncst-with '("[resources]" "cold_heap_octets = 65536" "cold_workers = 2"
               "cold_descriptors = 16" "cold_read_ids = 1000" "cold_file_ids = 100")))
(assert-event (equal (car *ncst-cold*) :accepted))
(assert-event (equal (fn-native-config-cold-resources (cadr *ncst-cold*)) '(65536 2 16 1000 100)))
(assert-event (fn-native-config-show-wfp (cadr *ncst-cold*)))
(assert-event (equal (fn-native-config-load (fn-native-config-show-octets (cadr *ncst-cold*)))
                     *ncst-cold*))
(assert-event (not (fn-native-config-cold-resources *ncst-min*)))
(assert-event (equal (ncst-with '("[resources]" "cold_workers = 2")) '(:refused :invalid)))
(assert-event (equal (ncst-with '("[resources]" "cold_heap_octets = 1" "cold_workers = 0"
                                 "cold_descriptors = 1" "cold_read_ids = 1" "cold_file_ids = 1"))
                     '(:refused :invalid)))
(assert-event (equal (ncst-with '("[resources]" "cold_heap_octets = 18446744073709551616"
                                 "cold_workers = 1" "cold_descriptors = 1" "cold_read_ids = 1" "cold_file_ids = 1"))
                     '(:refused :invalid)))

(assert-event (equal (fn-native-config-unsupported-key (cadr *ncst-cold*)) "cold_resources"))
(assert-event (not (fn-native-config-operator-availablep (cadr *ncst-cold*))))
