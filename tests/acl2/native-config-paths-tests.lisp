; Witnesses and teeth for books/native-config-paths.lisp (row S8: fn.toml
; paths relative to fn.toml's own directory).
(in-package "ACL2")
(include-book "../../books/native-config-paths")
(include-book "must-fail-checked")

; The directory fn.toml is in, from the working directory and the path as
; given.
(defmacro ncpt-base (cwd path)
  `(fn-ncpath-base (fn-record-string-octets ,cwd) (fn-record-string-octets ,path)))
(assert-event (equal (ncpt-base "/home/robin" "fn.toml") "/home/robin"))
(assert-event (equal (ncpt-base "/home/robin" "node/fn.toml") "/home/robin/node"))
(assert-event (equal (ncpt-base "/home/robin/" "node/fn.toml") "/home/robin/node"))
(assert-event (equal (ncpt-base "/tmp" "/var/lib/fn/fn.toml") "/var/lib/fn"))
(assert-event (equal (ncpt-base "/tmp" "/fn.toml") "/"))
(assert-event (equal (ncpt-base "/" "fn.toml") "/"))
(assert-event (equal (ncpt-base "/" "node/fn.toml") "/node"))
(assert-event (null (ncpt-base "relative" "fn.toml")))
(assert-event (null (ncpt-base "" "fn.toml")))

; Resolution: relative under the base, absolute as written, nothing without
; a base.
(assert-event (equal (fn-ncpath-resolve "store" "/var/lib/fn") "/var/lib/fn/store"))
(assert-event (equal (fn-ncpath-resolve "store" "/") "/store"))
(assert-event (equal (fn-ncpath-resolve "/srv/fn-public" "/var/lib/fn") "/srv/fn-public"))
(assert-event (equal (fn-ncpath-resolve "store" nil) "store"))
(assert-event (equal (fn-ncpath-resolve nil "/var/lib/fn") nil))
; Complete positive for fn-ncpath-resolve-is-absolute.
(assert-event
 (and (fn-ncpath-basep "/var/lib/fn")
      (stringp "store") (< 0 (length "store"))
      (fn-ncfg-absolutep (fn-ncpath-resolve "store" "/var/lib/fn"))))

; Teeth for fn-ncpath-resolve-is-absolute: without a base the result is not
; absolute; without the path's being a non-empty string neither.
(assert-event (not (fn-ncfg-absolutep (fn-ncpath-resolve "store" "relative"))))
(assert-event (not (fn-ncfg-absolutep (fn-ncpath-resolve "" "/var/lib/fn"))))
(must-fail-checked
 (defthm ncpt-resolve-is-identity
   (equal (fn-ncpath-resolve path base) path)))

; A mission's fn.toml (relative paths since row S8) under its node
; directory: the operator's octets load as the configuration with every
; path under the node, and that configuration is one `run' accepts.
(defconst *ncpt-node* "/tank/fn/scratch/operator-config/relay")
(defconst *ncpt-plan* (fn-native-mission-plan "relay" *ncpt-node* "127.0.0.1" 11942 nil))
(defconst *ncpt-octets* (caddr *ncpt-plan*))
(defconst *ncpt-written* (cadr *ncpt-plan*))
(defconst *ncpt-resolved* (fn-ncpath-resolve-config *ncpt-written* *ncpt-node*))
; Positive witness of fn-ncpath-config-octets-load-the-resolved-configuration:
; every hypothesis (a base; octets the loader admits; not :bad) and the
; conclusion, on a configuration the resolution changes.
(assert-event (fn-ncpath-basep *ncpt-node*))
(assert-event (equal (car (fn-native-config-load *ncpt-octets*)) :accepted))
(assert-event (not (equal (fn-ncpath-config-octets *ncpt-octets* *ncpt-node*) :bad)))
(assert-event (not (equal *ncpt-resolved* *ncpt-written*)))
(assert-event
 (equal (fn-native-config-load (fn-ncpath-config-octets *ncpt-octets* *ncpt-node*))
        (list :accepted *ncpt-resolved*)))
(assert-event (equal (fn-native-config-store *ncpt-resolved*)
                     "/tank/fn/scratch/operator-config/relay/store"))
(assert-event (equal (fn-native-config-tls-cert *ncpt-resolved*)
                     "/tank/fn/scratch/operator-config/relay/tls/cert.pem"))
(assert-event (equal (fn-native-config-auth-path *ncpt-resolved*)
                     "/tank/fn/scratch/operator-config/relay/store/auth.toml"))
(assert-event (equal (fn-native-config-log-path *ncpt-resolved*)
                     "/tank/fn/scratch/operator-config/relay/log/fn.log"))
(assert-event (equal (fn-native-config-control-path *ncpt-resolved*)
                     "/tank/fn/scratch/operator-config/relay/store/control.sock"))
(assert-event (fn-native-config-operator-availablep *ncpt-resolved*))
; Unresolved, the relative log path is one `run' cannot open (it must be
; absolute): the resolution is what makes the mission's node runnable.
(assert-event (not (fn-native-config-operator-availablep *ncpt-written*)))
; Every other field is the one written.
(assert-event (equal (fn-native-config-ops-mission *ncpt-resolved*) "relay"))
(assert-event (equal (fn-native-config-listener-port *ncpt-resolved*) 11942))
; Teeth for the base hypothesis: with no base the octets pass unchanged, and
; their load is the unresolved configuration.
(assert-event (equal (fn-ncpath-config-octets *ncpt-octets* nil) *ncpt-octets*))
(assert-event (equal (fn-native-config-load (fn-ncpath-config-octets *ncpt-octets* nil))
                     (list :accepted *ncpt-written*)))
; Teeth for the loader hypothesis: octets the loader refuses pass unchanged.
(assert-event (equal (fn-ncpath-config-octets (fn-record-string-octets "junk")
                                              *ncpt-node*)
                     (fn-record-string-octets "junk")))
; A resolved path past the path bound (512) is :bad, never truncated.
(defconst *ncpt-deep*
  (concatenate 'string "/" (coerce (make-list 500 :initial-element #\d) 'string)))
(assert-event (equal (fn-ncpath-config-octets *ncpt-octets* *ncpt-deep*) :bad))

; Regression: path resolution retains every non-path field, including the
; explicit cold-resource policy at slot 29 and nondefault TLS port at 28.
; Cold resources remain unsupported by run at this staged source frontier;
; resolving paths must not erase the policy and bypass that refusal.
(defconst *ncpt-cold* '(65536 2 16 1000 100))
(defconst *ncpt-extended*
  (update-nth 29 *ncpt-cold* (update-nth 28 1563 *ncpt-written*)))
(defconst *ncpt-extended-resolved*
  (fn-ncpath-resolve-config *ncpt-extended* *ncpt-node*))

; Literal positive of fn-ncpath-resolve-config-without-a-base: both
; hypotheses and full configuration equality, with a nonnil policy.
(assert-event
 (and (not (fn-ncpath-basep nil))
      (fn-ncfg-show-shapep *ncpt-extended*)
      (equal (fn-ncpath-resolve-config *ncpt-extended* nil) *ncpt-extended*)))
(assert-event
 (and (fn-native-config-show-wfp *ncpt-extended*)
      (equal (fn-native-config-listener-tls-port *ncpt-extended-resolved*) 1563)
      (equal (fn-native-config-cold-resources *ncpt-extended-resolved*) *ncpt-cold*)
      ; Complete result: only the six path slots change.
      (equal *ncpt-extended-resolved*
             (update-nth 29 *ncpt-cold* (update-nth 28 1563 *ncpt-resolved*)))
      (equal (fn-native-config-unsupported-key *ncpt-extended-resolved*) "cold_resources")))
(assert-event
 (let ((text (fn-native-config-show-octets *ncpt-extended*)))
   (and (equal (fn-native-config-load text) (list :accepted *ncpt-extended*))
        (fn-ncpath-basep *ncpt-node*)
        (not (equal (fn-ncpath-config-octets text *ncpt-node*) :bad))
        (equal (fn-native-config-load (fn-ncpath-config-octets text *ncpt-node*))
               (list :accepted *ncpt-extended-resolved*)))))

; Output resources are authority, even when the actual consumer is still
; refused. Relative-path normalization must not erase the explicit policy.
(defconst *ncpt-output* '(4096 1024))
(defconst *ncpt-output-config* (update-nth 30 *ncpt-output* *ncpt-written*))
(defconst *ncpt-both-config* (update-nth 30 *ncpt-output* *ncpt-extended*))
(assert-event
 (let* ((text (fn-native-config-show-octets *ncpt-output-config*))
        (resolved (fn-ncpath-resolve-config *ncpt-output-config* *ncpt-node*))
        (handed (fn-ncpath-config-octets text *ncpt-node*)))
   (and (fn-ncpath-basep *ncpt-node*)
        (equal (car (fn-native-config-load text)) :accepted)
        (not (equal handed :bad))
        ; Complete antecedent/conclusion of the actual octet consumer.
        (equal (fn-native-config-load handed) (list :accepted resolved))
        (equal resolved (update-nth 30 *ncpt-output* *ncpt-resolved*))
        (equal (fn-native-config-output-resources (cadr (fn-native-config-load handed)))
               *ncpt-output*)
        ; An explicit output policy is an operator opt-in, not a refusal.
        (equal (fn-native-config-unsupported-key (cadr (fn-native-config-load handed))) nil)
        (fn-native-config-operator-availablep (cadr (fn-native-config-load handed))))))
(assert-event
 (and (not (fn-ncpath-basep nil))
      (fn-ncfg-show-shapep *ncpt-both-config*)
      (equal (fn-ncpath-resolve-config *ncpt-both-config* nil) *ncpt-both-config*)
      (equal (fn-ncpath-resolve-config *ncpt-both-config* *ncpt-node*)
             (update-nth 30 *ncpt-output* *ncpt-extended-resolved*))))
