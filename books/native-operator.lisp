; fn: bounded native operator command grammar.
;
; This is a command-plan boundary, not a second storage or owner
; implementation.  It takes raw argv octet lists and the raw configuration
; bytes, asks books/native-config.lisp for the one normalized configuration,
; and returns a tagged plan.  A raw host may transport/print this result but
; may not supply defaults, select a command, or decide an outcome.

(in-package "ACL2")
(include-book "native-config")
(include-book "native-config-show")
(include-book "native-admin")
(include-book "accounts")
(include-book "native-auth-admin")
(include-book "byte-store-frame")
(include-book "outcome-class")

(defconst *fn-nop-max-arguments* 32)
(defconst *fn-nop-max-argument-octets* 512)

(defun fn-nop-argvp (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (and (consp (car argv))
           (<= (len (car argv)) *fn-nop-max-argument-octets*)
           (fn-ncfg-ascii-octetsp (car argv))
           (fn-nop-argvp (cdr argv)))
    (null argv)))

(defun fn-nop-argument-texts (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (cons (fn-record-octets-string (car argv))
            (fn-nop-argument-texts (cdr argv)))
    nil))

(defun fn-nop-result (status reason command config arguments)
  (declare (xargs :guard t))
  (list status reason command config arguments))

(defun fn-native-operator-result-status (result)
  (declare (xargs :guard t)) (fn-ncfg-first result))
(defun fn-native-operator-result-reason (result)
  (declare (xargs :guard t)) (fn-ncfg-second result))
(defun fn-native-operator-result-command (result)
  (declare (xargs :guard t)) (fn-ncfg-third result))
(defun fn-native-operator-result-config (result)
  (declare (xargs :guard t)) (fn-ncfg-nth 3 result))
(defun fn-native-operator-result-arguments (result)
  (declare (xargs :guard t)) (fn-ncfg-nth 4 result))

(defun fn-native-operator-resultp (result)
  (declare (xargs :guard t))
  (and (true-listp result) (equal (len result) 5)
       (member-equal (fn-native-operator-result-status result)
                     '(:accepted :refused :uncertain :fault :usage))))

;  HST-008 (the operator walk) and HST-009 (PRF-143): the operator family's
; outcome class is its result's status through the fn-wide classifier
; (books/outcome-class.lisp), and its code is the fn-wide map's.  "No store
; here" is an ordinary refusal, exit 1, like every other known refusal: its
; reason word (NO-STORE) and its "run init" line are what tell a script and
; an operator a node that was never initialized from one that declined a
; well-formed request (PKT-295: a code is a class, never a reason).
(defun fn-native-operator-outcome-class (result)
  (declare (xargs :guard t))
  (fn-outcome-of-status (fn-native-operator-result-status result)))

(defun fn-native-operator-exit-code (result)
  "The tagged result, not a raw host condition, owns the CLI codes."
  (declare (xargs :guard t))
  (fn-outcome-code (fn-native-operator-outcome-class result)))

; KEYSTONE (PRF-143, operator family).  The host exits with
; fn-native-operator-exit-code (host/native-operator-host.lisp
; fn-native-operator-host-result-exit-code, called by
; host/native/operator.lisp fnn-operator-dispatch-plan): 3 exactly when the
; result is uncertain, so an uncertain result is never masked and no refusal
; (NO-STORE included) is ever reported as a fence.
(defthm fn-native-operator-exit-is-fenced-iff-uncertain
  (equal (equal (fn-native-operator-exit-code result) 3)
         (equal (fn-native-operator-result-status result) :uncertain))
  :hints (("Goal" :in-theory '(fn-native-operator-exit-code
                                fn-native-operator-outcome-class
                                fn-outcome-of-status-fences-iff-uncertain))))

(defun fn-nop-usage (reason command config arguments)
  (declare (xargs :guard t))
  (fn-nop-result :usage reason command config arguments))

(defun fn-nop-refused (reason command config arguments)
  (declare (xargs :guard t))
  (fn-nop-result :refused reason command config arguments))

(defun fn-nop-parse-run (words once)
  (declare (xargs :guard t))
  (if (consp words)
      (if (and (equal (car words) "--once") (not once))
          (fn-nop-parse-run (cdr words) t)
        :bad)
    (list :run :once once)))

(defun fn-nop-parse-post-aux (words msgid payload groups)
  (declare (xargs :guard t :measure (len words)))
  (if (atom words)
      (if (and (stringp msgid) (fn-record-msgidp msgid)
               (stringp payload) (not (equal payload ""))
               (<= (length payload) *fn-ncfg-max-path*)
               (consp groups) (fn-record-groupsp (fn-ncfg-reverse groups)))
          (list :post msgid payload (fn-ncfg-reverse groups))
        :bad)
    (if (atom (cdr words))
        :bad
      (let ((option (car words)) (value (cadr words)) (rest (cddr words)))
        (cond ((and (equal option "--message-id") (null msgid))
               (fn-nop-parse-post-aux rest value payload groups))
              ((and (equal option "--payload") (null payload))
               (fn-nop-parse-post-aux rest msgid value groups))
              ((and (equal option "--group")
                    (< (len groups) *fn-record-max-groups*))
               (fn-nop-parse-post-aux rest msgid payload (cons value groups)))
              (t :bad))))))

(defun fn-nop-parse-post (words config)
  (declare (xargs :guard t))
  (let ((arguments (fn-nop-parse-post-aux words nil nil nil)))
    (if (equal arguments :bad)
        (fn-nop-usage :invalid-post-options "post" config words)
      (if (not (fn-native-config-posting-enabledp config))
          (fn-nop-refused :posting-disabled "post" config arguments)
        (fn-nop-result :accepted :plan "post" config arguments)))))

(defun fn-nop-parse-init-groups (words groups)
  "The groups a new store is to serve, in the order the operator named them.

There is no default here and none below it: a node's served groups are an
operator decision, and an `init' that named none would have to be given one
by the raw initializer, which would be a second owner of that choice.  A
bare `init' is therefore a usage error, not a store with two guessed groups."
  (declare (xargs :guard t :measure (len words)))
  (if (atom words)
      (let ((names (fn-ncfg-reverse groups)))
        (if (and (consp names) (fn-record-groupsp names)) names :bad))
    (if (<= *fn-record-max-groups* (len groups))
        :bad
      (fn-nop-parse-init-groups (cdr words) (cons (car words) groups)))))

;  The store profile `init' writes and `store upgrade-profile' asks for
; (books/byte-store-frame.lisp, D27): the operator's fields.  A request is a
; base -- a preset word (`--profile development|scale|default' at init, a bare
; word after `upgrade-profile'), the D27 defaults at init when none is named,
; the store's current profile at upgrade -- and field overrides, one
; `--FIELD N' per field of `*fn-bs-profile-field-names*' (for example
; `--max-transactions 100000 --max-article-octets 20000').  N is a decimal
; natural of at most 20 digits (a frame natural, below 2^64); the relations
; between the fields are ACL2's (`fn-bs-profile-validp'), decided below at
; init and at the store for an upgrade.
(defun fn-nop-profile-preset-word (word)
  (declare (xargs :guard t))
  (cond ((equal word "development") :development)
        ((equal word "scale") :scale)
        ((equal word "default") :default)
        (t nil)))

(defun fn-nop-profile-flag-field (word names)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((entry (car names)))
        (if (and (consp entry) (natp (car entry)) (stringp (cdr entry))
                 (stringp word)
                 (equal word (string-append "--" (cdr entry))))
            (car entry)
          (fn-nop-profile-flag-field word (cdr names))))
    nil))

; A frame natural in decimal: 1 to 20 digits, no leading zero, below 2^64.
; This bounds the work of reading one flag value, not the profile's data.
(defun fn-nop-profile-decimal (text)
  (declare (xargs :guard t))
  (if (not (stringp text)) nil
    (let ((chars (coerce text 'list)))
      (if (and (consp chars) (<= (len chars) 20)
               (not (and (consp (cdr chars)) (equal (car chars) #\0))))
          (let ((value (fn-native-admin-decimal-value chars)))
            (if (and (natp value) (< value 18446744073709551616)) value nil))
        nil))))

; A flag's value: the history requirement's field (D31) takes a word,
; `unmarked' (0) or `required' (1); every other field a decimal.
(defun fn-nop-profile-flag-value (field text)
  (declare (xargs :guard t))
  (if (equal field *fn-bs-pf-history-marker*)
      (cond ((equal text "unmarked") 0)
            ((equal text "required") 1)
            (t nil))
    (fn-nop-profile-decimal text)))

(defun fn-nop-profile-field-namedp (field overrides)
  (declare (xargs :guard t))
  (if (consp overrides)
      (or (and (consp (car overrides)) (equal (caar overrides) field))
          (fn-nop-profile-field-namedp field (cdr overrides)))
    nil))

; Leading profile words of WORDS: (REQUEST REST), or :bad for a malformed or
; repeated flag.  BASE is the preset in force; OVERRIDES the fields so far.
(defun fn-nop-parse-profile-flags (words base named overrides)
  (declare (xargs :guard t :measure (len words)
                  :hints (("Goal" :in-theory (disable fn-nop-profile-flag-field
                                                      fn-nop-profile-decimal
                                                      fn-nop-profile-flag-value
                                                      fn-nop-profile-preset-word)))
                  :guard-hints (("Goal" :in-theory (disable fn-nop-profile-flag-field
                                                            fn-nop-profile-decimal
                                                            fn-nop-profile-flag-value
                                                            fn-nop-profile-preset-word)))))
  (if (or (atom words) (atom (cdr words))
          (not (or (equal (car words) "--profile")
                   (fn-nop-profile-flag-field (car words)
                                              *fn-bs-profile-field-names*))))
      (if (and (consp words)
               (or (equal (car words) "--profile")
                   (fn-nop-profile-flag-field (car words)
                                              *fn-bs-profile-field-names*)))
          :bad  ; a flag with no value
        (list (list base (fn-ncfg-reverse overrides)) words))
    (if (equal (car words) "--profile")
        (let ((preset (fn-nop-profile-preset-word (cadr words))))
          (if (or (null preset) named)
              :bad
            (fn-nop-parse-profile-flags (cddr words) preset t overrides)))
      (let ((field (fn-nop-profile-flag-field (car words)
                                              *fn-bs-profile-field-names*))
            (value (fn-nop-profile-flag-value
                    (fn-nop-profile-flag-field (car words)
                                               *fn-bs-profile-field-names*)
                    (cadr words))))
        (if (or (null value) (fn-nop-profile-field-namedp field overrides))
            :bad
          (fn-nop-parse-profile-flags (cddr words) base named
                                      (cons (cons field value) overrides)))))))

;  A command-line word that starts with `--' is a flag, never a group name.
; RFC 5536 section 3.1.4 admits such a newsgroup name; fn declines to take one
; from a command line (a local policy, PKT-103): a misspelt or unknown flag
; would otherwise become a group, as `--max-article-octets' and `4194304' did
; under the developer init (planning/evidence/large-article-2026-09-25.md
; section 4.1).
(defun fn-nop-flag-wordp (word)
  (declare (xargs :guard t))
  (and (stringp word)
       (<= 2 (length word))
       (equal (char word 0) #\-)
       (equal (char word 1) #\-)))

(defun fn-nop-some-flag-wordp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (or (fn-nop-flag-wordp (car words))
          (fn-nop-some-flag-wordp (cdr words)))
    nil))

; PKT-097: a mission's store profile, as an operator request over the D27
; defaults: its article bound and groups per article (the spike's figures).
; `fn-native-mission-profiles-valid' says each resolves to a valid profile;
; books/native-mission.lisp that it is the profile the store then opens with.
(defun fn-native-mission-request (name)
  (declare (xargs :guard t))
  (cond ((equal name "small-community") (list :default (list (cons 5 1048576) (cons 6 8))))
        ((equal name "relay") (list :default (list (cons 5 1048576) (cons 6 16))))
        ((equal name "archive") (list :default (list (cons 5 1048576) (cons 6 16))))
        (t nil)))

; The groups a mission's `init' serves when the operator names none; only a
; small community has a default pair.
(defun fn-native-mission-default-groups (name)
  (declare (xargs :guard t))
  (if (equal name "small-community") '("local.general" "local.test") nil))

(defthm fn-native-mission-profiles-valid
  (implies (member-equal name *fn-ncfg-mission-names*)
           (and (fn-bs-profile-validp
                 (fn-bs-profile-resolve (fn-native-mission-request name) nil))
                (not (equal (fn-bs-pf 14 (fn-bs-profile-resolve
                                          (fn-native-mission-request name) nil))
                            1))))
  :hints (("Goal" :in-theory (disable fn-bs-profile-validp fn-bs-profile-resolve
                                      (:e fn-bs-profile-validp)))
          ("Goal'" :in-theory (enable (:e fn-bs-profile-validp)))))

(defun fn-nop-parse-init-plain (words config)
  (declare (xargs :guard t))
  (let* ((parsed (fn-nop-parse-profile-flags words :default nil nil))
         (request (if (consp parsed) (car parsed) nil))
         (names (if (consp parsed) (fn-ncfg-second parsed) nil))
         ; The profile init will write, resolved over no store, or
         ; (:invalid REASON); the frame itself is encoded at the store.
         (profile (if (consp parsed) (fn-bs-profile-resolve request nil) nil))
         (groups (fn-nop-parse-init-groups names nil)))
    (cond ((not (consp parsed))
           (fn-nop-usage :invalid-init-profile "init" config words))
          ((equal groups :bad)
           (fn-nop-usage :invalid-init-groups "init" config words))
          ((fn-nop-some-flag-wordp names)
           (fn-nop-usage :flag-word-as-group "init" config words))
          ; The profile's own relations, by the name of the first that fails.
          ((equal (fn-ncfg-first profile) :invalid)
           (fn-nop-refused (fn-ncfg-second profile) "init" config words))
          ; RFC 5536 s3.1.4: "example.*" and "poster" MUST NOT be created.
          ; The command line is well formed; the node declines it.
          ; Checked over every init word: the profile words before the
          ; groups are flags, preset words and decimals, never a group name.
          ((fn-native-admin-some-group-name-reservedp words)
           (fn-nop-refused :reserved-group-name "init" config words))
          (t (fn-nop-result :accepted :plan "init" config
                            (list :init groups request))))))

;  `init' under a configuration that names a mission (`[ops] mission'): the
; mission fixes the profile, so a profile word is a usage error, and with no
; group named a small community serves its default pair.
(defun fn-nop-parse-init (words config)
  (declare (xargs :guard t))
  (let ((mission (fn-native-config-ops-mission config)))
    (if (and mission (fn-native-mission-request mission))
        (let ((groups (fn-nop-parse-init-groups
                       (if (consp words) words (fn-native-mission-default-groups mission))
                       nil)))
          (cond ((fn-nop-some-flag-wordp words)
                 (fn-nop-usage :mission-fixes-profile "init" config words))
                ((equal groups :bad)
                 (fn-nop-usage :invalid-init-groups "init" config words))
                ((fn-native-admin-some-group-name-reservedp words)
                 (fn-nop-refused :reserved-group-name "init" config words))
                (t (fn-nop-result :accepted :plan "init" config
                                  (list :init groups
                                        (fn-native-mission-request mission))))))
      (fn-nop-parse-init-plain words config))))

;  The developer image's `store ROOT init [PROFILE-FLAGS] [GROUP ...]'
; (host/native/io.lisp fnn-command-developer-init): the operator's profile
; grammar over the development base, so a profile flag sets its field, and a
; flag-shaped word left among the groups is refused instead of becoming a
; group.  (:init GROUPS REQUEST), GROUPS NIL for the image's default groups,
; or (:refused REASON).  The groups themselves are admitted at the store.
(defun fn-nop-developer-init (words)
  (declare (xargs :guard t))
  (let ((parsed (fn-nop-parse-profile-flags words :development nil nil)))
    (if (not (consp parsed))
        (list :refused :invalid-init-profile)
      (let* ((request (car parsed))
             (names (fn-ncfg-second parsed))
             (profile (fn-bs-profile-resolve request nil)))
        (cond ((equal (fn-ncfg-first profile) :invalid)
               (list :refused (fn-ncfg-second profile)))
              ((fn-nop-some-flag-wordp names)
               (list :refused :flag-word-as-group))
              (t (list :init names request)))))))

; An accepted developer init names no flag-shaped group (by its definition:
; the refusal arm above), and its request is the parsed profile flags.
(defthm fn-nop-developer-init-groups-are-not-flags-by-definition
  (implies (equal (car (fn-nop-developer-init words)) :init)
           (not (fn-nop-some-flag-wordp (cadr (fn-nop-developer-init words)))))
  :hints (("Goal" :in-theory (disable fn-nop-parse-profile-flags
                                      fn-bs-profile-resolve))))

; `store upgrade-profile [WORD] [--FIELD N ...]': the offline profile upgrade
; (books/store-profile-upgrade.lisp).  WORD names a preset base; without it
; the base is the store's current profile, so `store upgrade-profile' alone
; is the format 7 to 8 step.  Whether the request is an upgrade of the
; store's profile is decided at the store, by `fn-profile-upgrade-verdict',
; not here.
; `store compact': the offline compaction (books/store-compact-verb.lisp).
; It takes no argument; what it does to the store (pack and reclaim, resume a
; reclaim, or refuse) is `fn-cverb-decide' at the store, not here.
; `store checkpoint': publish the exact-state checkpoint (P3,
; books/store-checkpoint-open.lisp).  It takes no argument.
; `store reclaim [--dry-run]': content reclamation's durable step (D13,
; STO-017, books/store-reclaim-pack.lisp).  What it removes is
; `fn-rclp-decide' at the store, not here; `--dry-run' writes nothing.
; A Message-ID as a command word: "<", printable US-ASCII, ">" (RFC 3977
; section 3.6), within the store's Message-ID bound (fn-record-msgidp).
(defun fn-nop-msgid-wordp (word)
  (declare (xargs :guard t))
  (and (stringp word)
       (fn-record-msgidp word)
       (<= 3 (length word))
       (equal (char word 0) #\<)
       (equal (char word (1- (length word))) #\>)))

(defun fn-nop-parse-store (words config)
  (declare (xargs :guard t))
  (cond ((and (consp words) (equal (car words) "upgrade-profile"))
         (let* ((preset (and (consp (cdr words))
                             (fn-nop-profile-preset-word (cadr words))))
                (parsed (fn-nop-parse-profile-flags
                         (if preset (cddr words) (cdr words))
                         (or preset :current) (and preset t) nil)))
           (if (or (not (consp parsed)) (fn-ncfg-second parsed))
               (fn-nop-usage :invalid-store-profile "store" config words)
             (fn-nop-result :accepted :plan "store" config
                            (list :upgrade-profile (car parsed))))))
        ; PKT-099: whether the no-argument upgrade would write
        ; (fn-profile-needs-upgrade-verdict), and whether reinstating the
        ; kept older config.json at PATH is sound (fn-profile-rollback-verdict).
        ((and (consp words) (equal (car words) "needs-upgrade") (null (cdr words)))
         (fn-nop-result :accepted :plan "store" config (list :needs-upgrade)))
        ((and (consp words) (equal (car words) "rollback-check")
              (consp (cdr words)) (null (cddr words))
              (stringp (cadr words))
              (< 1 (length (cadr words)))
              (<= (length (cadr words)) *fn-ncfg-max-path*)
              (equal (char (cadr words) 0) #\/))
         (fn-nop-result :accepted :plan "store" config
                        (list :rollback-check (cadr words))))
        ; The walk's rollback item: what restoring a pre-upgrade snapshot
        ; (a copy of the stopped store at SNAPSHOT) loses against this store
        ; (fn-native-operator-snapshot-loss).
        ((and (consp words) (equal (car words) "rollback-check")
              (consp (cdr words)) (equal (cadr words) "--snapshot")
              (consp (cddr words)) (null (cdddr words))
              (stringp (caddr words))
              (< 1 (length (caddr words)))
              (<= (length (caddr words)) *fn-ncfg-max-path*)
              (equal (char (caddr words) 0) #\/))
         (fn-nop-result :accepted :plan "store" config
                        (list :rollback-snapshot (caddr words))))
        ((and (consp words) (equal (car words) "compact") (null (cdr words)))
         (fn-nop-result :accepted :plan "store" config (list :compact)))
        ; NNT-032: the operator's settling lookup.  Whether this store holds
        ; an article under MESSAGE-ID (fn-native-operator-inspect-report),
        ; the one privileged answer to a client left unresolved when a
        ; re-send meets the login or posting gate (PKT-164).
        ((and (consp words) (equal (car words) "inspect")
              (consp (cdr words)) (null (cddr words))
              (fn-nop-msgid-wordp (cadr words)))
         (fn-nop-result :accepted :plan "store" config
                        (list :inspect (cadr words))))
        ((and (consp words) (equal (car words) "checkpoint") (null (cdr words)))
         (fn-nop-result :accepted :plan "store" config (list :checkpoint)))
        ((and (consp words) (equal (car words) "reclaim") (null (cdr words)))
         (fn-nop-result :accepted :plan "store" config (list :reclaim)))
        ((and (consp words) (equal (car words) "reclaim")
              (equal (cdr words) '("--dry-run")))
         (fn-nop-result :accepted :plan "store" config (list :reclaim-dry-run)))
        (t (fn-nop-usage :invalid-store-command "store" config words))))

;; `status --watch N': the seconds between two asks.  A work bound on the
;; interval (one day), not a bound on any data.
(defconst *fn-nop-max-watch-seconds* 86400)

(defun fn-nop-watch-seconds (text)
  (declare (xargs :guard t))
  (let ((n (fn-nop-profile-decimal text)))
    (if (and (posp n) (<= n *fn-nop-max-watch-seconds*)) n nil)))

(defun fn-nop-help-subjectp (subject)
  (declare (xargs :guard t))
  (member-equal subject '("help" "init" "run" "post" "show" "mission" "status" "health" "pins" "obligations" "recover" "store" "group" "capacity" "peer" "bp-boundary" "bp-route" "policy" "control" "principal" "keys" "retention" "account")))

(defun fn-nop-help-text (subject)
  "Bounded operator help output, selected only from ACL2-normalized subjects."
  (declare (xargs :guard t))
  (cond ((equal subject "init")
         "usage: fn operator CONFIG init [--profile development|scale|default] [--max-transactions N] [--max-history-octets N] [--max-record-octets N] [--max-article-octets N] [--max-groups-per-article N] [--max-group-name-octets N] [--max-open-suffix N] [--max-consumers N] [--max-bp-rows N] [--max-config-generations N] [--max-credentials N] [--max-policy-members N] GROUP [GROUP...]; under [ops] mission: init [GROUP...] only (the mission fixes the profile; raise it afterwards with store upgrade-profile)")
        ((equal subject "run") "usage: fn operator CONFIG run [--once]")
        ((equal subject "show")
         "usage: fn operator CONFIG show [TABLE KEY] (the normalized configuration as fn.toml, or one key's value)")
        ((equal subject "mission")
         "usage: fn operator NODE/fn.toml mission small-community|relay|archive [--host H] [--port P] (writes a new fn.toml; then init)")
        ((equal subject "post")
         "usage: fn operator CONFIG post --message-id ID --payload PATH --group GROUP [--group GROUP]")
        ((equal subject "status")
         "usage: fn operator CONFIG status [--watch SECONDS] (asks the running owner over its control socket; offline, reads the store)")
        ((equal subject "health")
         "usage: fn operator CONFIG health (eight states, one line each: fenced, exhausted, unqualified-profile, space-pressure, no-route, stranded-transfer, unavailable-peer, receipt-debt; exit 20 to 27 names the first held, 19 some unobserved, 0 all clear)")
        ((equal subject "pins")
         "usage: fn operator CONFIG pins (retention pins and each open connection's configuration pin)")
        ((equal subject "obligations")
         "usage: fn operator CONFIG obligations (the retention ledger's held obligations)")
        ((equal subject "recover") "usage: fn operator CONFIG recover")
        ((equal subject "store")
         "usage: fn operator CONFIG store {upgrade-profile [development|scale|default] [--FIELD N ...] [--history-marker required] | needs-upgrade | rollback-check KEPT-CONFIG-JSON | rollback-check --snapshot SNAPSHOT-STORE | compact | checkpoint | reclaim [--dry-run] | inspect MESSAGE-ID} (offline; refused while an owner runs; no field may shrink; required needs a covering marker and is never undone)")
        ((equal subject "group") "usage: fn operator CONFIG group {create|retire} NAME")
        ((equal subject "capacity") "usage: fn operator CONFIG capacity DECIMAL-UINT32")
        ((equal subject "retention")
         "usage: fn operator CONFIG retention set {keep-forever | released-by-all-holders | release-after DAYS} (D13: the content-retention rule; keep-forever is the default)")
        ((equal subject "control")
         "usage: fn operator CONFIG control {grant PRINCIPAL-HEX cancel NAMESPACE | revoke PRINCIPAL-HEX cancel NAMESPACE | list} (NAMESPACE is a group name or one ending in .*; spec peering 8)")
        ((equal subject "peer")
         "usage: fn operator CONFIG peer add NAME PATH HOST PORT INBOUND|- OUTBOUND|- source-address|principal VALUE [PROFILE ALLOW-CLEAR] STREAMING [starttls|implicit SERVER-NAME ANCHOR-PEM] | peer remove NAME | peer list | peer pull NAME SECONDS | peer budget NAME OCTETS COUNT | peer keygen KEYDIR | peer genesis KEYDIR | peer invite NAME GROUPS HOST PORT PATH KEYDIR OUT MY-HOST|- MY-PORT|- | peer accept FILE KEYDIR PATH REACHABLE|- OUT | peer confirm ACCEPTANCE INVITATION (KEYDIR, FILE and OUT absolute; keygen makes a new KEYDIR with both key pairs and runs genesis; spec peering 9)")
        ((equal subject "bp-boundary")
         "usage: fn operator CONFIG bp-boundary add NAME PATH BP-EID PORT [INBOUND-GROUPS MAX-OCTETS MAX-INFLIGHT] [carries SOURCE-EID ...] (IPv4 loopback; the short form grants no inbound articles; carries lists the source EIDs this neighbour may relay, each judged under its own enrollment here)")
        ((equal subject "bp-route")
         "usage: fn operator CONFIG bp-route {add PATTERN BOUNDARY [PRIORITY] | remove PATTERN BOUNDARY} (PATTERN is a BP EID, or one ending in * for every EID with that prefix; the next hop of held transit, spec bp-node-machine 4.7)")
        ((equal subject "policy")
         "usage: fn operator CONFIG policy set {path-identity IDENTITY | posting-policy bound-logins|open}")
        ((equal subject "principal")
         "usage: fn operator CONFIG principal {list | set-password NAME [--principal HEX] [--posting|--no-posting] | bind NAME HEX | unbind NAME} (set-password reads the password twice from the terminal or two lines of stdin; restart to apply)")
        ((equal subject "account")
         "usage: fn operator CONFIG account {invite [--expires SECONDS] | list} (invite prints one code, once, for a friend's XREDEEM; the node keeps only its digest; SECONDS defaults to 604800; list shows logins and principals, never codes, digests or verifiers; spec nntp Invitation-code accounts)")
        ((equal subject "keys")
         "usage: fn operator CONFIG keys redecide MSGID (re-decide a stored key statement under the grants in force now; the running owner decides it over the control socket; refused when MSGID is no stored key statement or its change is already made; spec peering 7.4)")
        ((equal subject "help") "usage: fn operator CONFIG help [COMMAND]")
        (t "usage: fn operator CONFIG {help|init|run|post|show|mission|status|health|pins|obligations|recover|store|group|capacity|retention|peer|bp-boundary|bp-route|policy|control|principal|keys|account} (fn operator CONFIG help COMMAND for one command's words; fn --version for the source revision)")))

(defun fn-nop-parse-principal (argv config)
  "Compose the existing ACL2 credential plan under the public operator."
  ; The argv here is the raw host vector `fn-native-operator-run' was handed,
  ; so this boundary stays total: `fn-ncfg-rest' is the tail of a cons and nil
  ; of anything else, which is what `cdr' means in the logic and what `cdr'
  ; cannot be called on under a verified guard (the conjecture asked for
  ; (implies (not (consp argv)) (not argv))).
  (declare (xargs :guard t))
  (let ((plan (fn-native-auth-admin-parse-argv (fn-ncfg-rest argv))))
    (if (equal (fn-native-auth-admin-plan-status plan) :accepted)
        (fn-nop-result :accepted :plan "principal" config (list plan))
      (fn-nop-usage (list :principal (fn-native-auth-admin-plan-reason plan))
                    "principal" config (fn-ncfg-rest argv)))))

;; PRF-097: the peering verbs (specs/peering.md section 9).  Their words are
;; values and absolute paths; what the documents say, and whether they are
;; accepted, is books/peer-invite.lisp's, asked by host/native/peer-invite.lisp.
(defconst *fn-nop-peering-arity*
  '(("keygen" . 1) ("genesis" . 1) ("invite" . 9) ("accept" . 5) ("confirm" . 2)))

(defun fn-nop-peering-verbp (word)
  (declare (xargs :guard t))
  (and (stringp word) (assoc-equal word *fn-nop-peering-arity*) t))

(defun fn-nop-absolute-pathp (word)
  (declare (xargs :guard t))
  (and (stringp word)
       (< 1 (length word))
       (<= (length word) *fn-ncfg-max-path*)
       (equal (char word 0) #\/)))

(defun fn-nop-peering-paths-okp (verb args)
  ; The positions of the path words for each verb.
  (declare (xargs :guard (true-listp args)))
  (cond ((equal verb "keygen") (fn-nop-absolute-pathp (nth 0 args)))
        ((equal verb "genesis") (fn-nop-absolute-pathp (nth 0 args)))
        ((equal verb "invite") (and (fn-nop-absolute-pathp (nth 5 args))
                                    (fn-nop-absolute-pathp (nth 6 args))))
        ((equal verb "accept") (and (fn-nop-absolute-pathp (nth 0 args))
                                    (fn-nop-absolute-pathp (nth 1 args))
                                    (fn-nop-absolute-pathp (nth 4 args))))
        ((equal verb "confirm") (and (fn-nop-absolute-pathp (nth 0 args))
                                     (fn-nop-absolute-pathp (nth 1 args))))
        (t nil)))

(defun fn-nop-parse-peering (words config)
  (declare (xargs :guard t))
  (let* ((verb (fn-ncfg-first words))
         (args (fn-ncfg-rest words))
         (arity (cdr (assoc-equal verb *fn-nop-peering-arity*))))
    (if (and (true-listp args)
             (equal (len args) arity)
             (string-listp args)
             (fn-nop-peering-paths-okp verb args))
        (fn-nop-result :accepted :plan "peer" config
                       (list* :peering verb args))
      (fn-nop-usage :invalid-peering-command "peer" config words))))

;; PRF-166 (PKT-325): `keys redecide MSGID'.  The word is a Message-ID's
;; spelling, <...>, bounded like a header value; whether it names a stored key
;; statement, and what the statement now does, is the owner's
;; (books/key-statements.lisp fn-ks-redecide-plan, asked by
;; host/native/keys.lisp over the control socket).
(defun fn-nop-parse-keys (words config)
  (declare (xargs :guard t))
  (if (and (equal (fn-ncfg-first words) "redecide")
           (consp (fn-ncfg-rest words))
           (null (fn-ncfg-rest (fn-ncfg-rest words)))
           (fn-nop-msgid-wordp (fn-ncfg-second words)))
      (fn-nop-result :accepted :plan "keys" config
                     (list :keys "redecide" (fn-ncfg-second words)))
    (fn-nop-usage :invalid-keys-command "keys" config words)))

(defun fn-nop-parse-administration (command argv config)
  "Delegate the exact bounded argv vector to the ACL2 durable-admin grammar."
  (declare (xargs :guard t))
  (let ((plan (fn-native-admin-plan argv)))
    (cond ((equal (fn-native-admin-result-status plan) :accepted)
           (fn-nop-result :accepted :plan command config (list plan argv)))
          ; A reserved group name is a refusal, not a usage error: the
          ; command line is well formed and the node declines it (exit 1).
          ; The control verbs' named admission refusals likewise
          ; (books/native-admin.lisp `fn-native-admin-control-plan').
          ((member-equal (fn-native-admin-result-reason plan)
                         '(:reserved-group-name :namespace-pattern :principal
                           :verb-not-grantable))
           (fn-nop-refused (list :administration (fn-native-admin-result-reason plan))
                           command config argv))
          (t (fn-nop-usage (list :administration (fn-native-admin-result-reason plan))
                           command config argv)))))

;; PRF-164 (PKT-439): `account invite [--expires SECONDS]'.  The plan names
;; the seconds only; the host reads the entropy, and ACL2 renders the code
;; and its digest (books/accounts.lisp) before the digest-only admin argv is
;; planned.  `account list' is an administrative query.
(defun fn-nop-parse-account (words argv config)
  (declare (xargs :guard t))
  (cond ((and (equal (fn-ncfg-first words) "invite")
              (null (fn-ncfg-rest words)))
         (fn-nop-result :accepted :plan "account" config
                        (list :account-invite *fn-acct-default-expiry-seconds*)))
        ((and (equal (fn-ncfg-first words) "invite")
              (equal (fn-ncfg-second words) "--expires")
              (consp (fn-ncfg-rest (fn-ncfg-rest words)))
              (null (fn-ncfg-rest (fn-ncfg-rest (fn-ncfg-rest words))))
              (posp (fn-nop-profile-decimal
                     (fn-ncfg-first (fn-ncfg-rest (fn-ncfg-rest words))))))
         (fn-nop-result :accepted :plan "account" config
                        (list :account-invite
                              (fn-nop-profile-decimal
                               (fn-ncfg-first (fn-ncfg-rest (fn-ncfg-rest words)))))))
        ((equal words '("list")) (fn-nop-parse-administration "account" argv config))
        (t (fn-nop-usage :invalid-account-command "account" config words))))

(defun fn-nop-parse-command (words config argv)
  "The accepted tag means a bounded command *plan* exists; no host effect ran."
  (declare (xargs :guard t))
  (if (not (consp words))
      (fn-nop-usage :missing-command nil config nil)
    (let ((command (car words)) (rest (cdr words)))
      (cond ((equal command "help")
             (if (or (null rest)
                     (and (equal (len rest) 1) (fn-nop-help-subjectp (car rest))))
                 ; PKT-403: bare `help' (and so bare `fn') answers the
                 ; command list, not the grammar of `help' itself.
                 (let ((subject (if (consp rest) (car rest) "help")))
                   (fn-nop-result :accepted :plan "help" config
                                  (list :help subject
                                        (fn-nop-help-text
                                         (if (consp rest) subject nil)))))
               (fn-nop-usage :invalid-help "help" config rest)))
            ((equal command "run")
             (let ((arguments (fn-nop-parse-run rest nil)))
               (if (equal arguments :bad)
                   (fn-nop-usage :invalid-run-options "run" config rest)
                 (fn-nop-result :accepted :plan "run" config arguments))))
            ((equal command "init") (fn-nop-parse-init rest config))
            ((equal command "post") (fn-nop-parse-post rest config))
            ((equal command "status")
             (cond ((null rest)
                    (fn-nop-result :accepted :plan "status" config (list :status)))
                   ((and (equal (fn-ncfg-first rest) "--watch")
                         (null (fn-ncfg-rest (fn-ncfg-rest rest)))
                         (fn-nop-watch-seconds (fn-ncfg-second rest)))
                    (fn-nop-result :accepted :plan "status" config
                                   (list :status :watch
                                         (fn-nop-watch-seconds
                                          (fn-ncfg-second rest)))))
                   (t (fn-nop-usage :unexpected-arguments "status" config rest))))
            ((equal command "health")
             (if (null rest)
                 (fn-nop-result :accepted :plan "health" config (list :health))
               (fn-nop-usage :unexpected-arguments "health" config rest)))
            ((or (equal command "pins") (equal command "obligations"))
             (if (null rest)
                 (fn-nop-result :accepted :plan command config
                                (list (if (equal command "pins") :pins :obligations)))
               (fn-nop-usage :unexpected-arguments command config rest)))
            ((equal command "recover")
             (if (null rest)
                 (fn-nop-result :accepted :plan "recover" config (list :recover))
               (fn-nop-usage :unexpected-arguments "recover" config rest)))
            ((equal command "store") (fn-nop-parse-store rest config))
            ; PKT-096: the normalized configuration, rendered by ACL2
            ; (books/native-config-show.lisp fn-native-config-show).
            ((equal command "show")
             (if (or (null rest) (equal (len rest) 2))
                 (let ((shown (fn-native-config-show config (fn-ncfg-first rest)
                                                     (fn-ncfg-second rest))))
                   (cond ((equal (fn-ncfg-first shown) :shown)
                          (fn-nop-result :accepted :plan "show" config
                                         (list :show (fn-ncfg-second shown))))
                         ((equal (fn-ncfg-second shown) :unknown-key)
                          (fn-nop-usage :unknown-key "show" config rest))
                         (t (fn-nop-refused (fn-ncfg-second shown) "show" config rest))))
               (fn-nop-usage :unexpected-arguments "show" config rest)))
            ((and (equal command "peer")
                  (fn-nop-peering-verbp (fn-ncfg-first rest)))
             (fn-nop-parse-peering rest config))
            ((or (equal command "group") (equal command "capacity")
                 (equal command "peer") (equal command "bp-boundary")
                 (equal command "bp-route") (equal command "policy")
                 (equal command "control") (equal command "retention"))
             (fn-nop-parse-administration command argv config))
            ((equal command "principal")
             (fn-nop-parse-principal argv config))
            ((equal command "keys") (fn-nop-parse-keys rest config))
            ((equal command "account") (fn-nop-parse-account rest argv config))
            (t (fn-nop-usage :unsupported-command command config rest))))))

(defun fn-native-operator-command-preflight (argv-octets)
  "Parse only the config-free command boundary.

The distinguished `(:needs-config)' result directs the raw boundary to read a
configuration file.  Every other result is the ordinary tagged operator result,
so malformed argv and help syntax remain ACL2-owned before any host file I/O."
  (declare (xargs :guard t))
  (if (or (not (true-listp argv-octets))
          (< *fn-nop-max-arguments* (len argv-octets))
          (not (fn-nop-argvp argv-octets)))
      (fn-nop-usage :argv-bounds nil nil nil)
    (let ((words (fn-nop-argument-texts argv-octets)))
      (cond ((and (consp words) (equal (car words) "help"))
             (fn-nop-parse-command words nil argv-octets))
            ((and (consp words) (equal (car words) "mission"))
             (list :needs-config-path))
            (t (list :needs-config))))))

(defun fn-native-operator-preflight-needs-config-path-p (result)
  (declare (xargs :guard t))
  (equal result '(:needs-config-path)))

; PKT-097: `mission NAME [--host H] [--port P]' writes the mission's fn.toml
; at the configuration path, which does not exist yet.  PATH is that path's
; octets; the node directory is everything before its last `/'.
(defun fn-nop-mission-options (words host port)
  (declare (xargs :guard t :measure (len words)))
  (cond ((atom words) (list host port))
        ((and (equal (car words) "--host") (consp (cdr words)) (stringp (cadr words)))
         (fn-nop-mission-options (cddr words) (cadr words) port))
        ((and (equal (car words) "--port") (consp (cdr words))
              (fn-nop-profile-decimal (cadr words)))
         (fn-nop-mission-options (cddr words) host (fn-nop-profile-decimal (cadr words))))
        (t :bad)))

(defun fn-nop-dirname-rev (rev)
  ; REV is a path reversed: drop through the last `/'.
  (declare (xargs :guard t))
  (if (consp rev)
      (if (equal (car rev) 47) (cdr rev) (fn-nop-dirname-rev (cdr rev)))
    nil))

(defun fn-native-operator-mission-run (path-octets argv-octets)
  (declare (xargs :guard t))
  (let ((words (fn-nop-argument-texts argv-octets)))
    (if (or (not (true-listp argv-octets))
            (< *fn-nop-max-arguments* (len argv-octets))
            (not (fn-nop-argvp argv-octets))
            (not (equal (fn-ncfg-first words) "mission"))
            (not (consp (fn-ncfg-rest words)))
            (not (fn-ncfg-printablep path-octets))
            (not (true-listp path-octets)))
        (fn-nop-usage :invalid-mission "mission" nil nil)
      (let ((options (fn-nop-mission-options (fn-ncfg-rest (fn-ncfg-rest words))
                                             *fn-ncfg-default-listener-host*
                                             *fn-ncfg-default-listener-port*))
            (node (fn-record-octets-string
                   (fn-ncfg-reverse (fn-nop-dirname-rev (fn-ncfg-reverse path-octets)))))
            (name (fn-ncfg-second words)))
        (if (equal options :bad)
            (fn-nop-usage :invalid-mission-options "mission" nil (fn-ncfg-rest words))
          (let ((plan (fn-native-mission-plan name node (fn-ncfg-first options)
                                              (fn-ncfg-second options))))
            (if (equal (fn-ncfg-first plan) :accepted)
                (fn-nop-result :accepted :plan "mission" nil
                               (list :mission name
                                     (fn-ncfg-third plan)
                                     (fn-native-mission-directories node)))
              (fn-nop-refused (fn-ncfg-second plan) "mission" nil (fn-ncfg-rest words)))))))))

; The host's lstat of the configuration path: an existing file is refused;
; a mission writes a new node only.
(in-theory (disable fn-native-operator-mission-run))

(defun fn-native-operator-mission-outcome (result existsp)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted) existsp)
      (fn-nop-refused :config-exists "mission" nil nil)
    result))

(defun fn-native-operator-preflight-needs-config-p (result)
  (declare (xargs :guard t))
  (equal result '(:needs-config)))

(defun fn-native-operator-run (config-octets argv-octets)
  "One semantic authority for config defaults, argv grammar, and CLI tag.

A profile the current native owner cannot consume is USAGE, never an accepted
service plan.  `posting.enabled = false' is a configured refusal for POST and
is installed into the owner for both served and control submission."
  (declare (xargs :guard t))
  (let ((preflight (fn-native-operator-command-preflight argv-octets)))
    (if (not (fn-native-operator-preflight-needs-config-p preflight))
        preflight
      (let ((words (fn-nop-argument-texts argv-octets)))
        (if (or (not (fn-ncfg-ascii-octetsp config-octets))
                (< *fn-ncfg-max-octets* (len config-octets)))
            (fn-nop-usage :configuration-bounds nil nil nil)
          (let ((loaded (fn-native-config-load config-octets)))
            (if (not (equal (fn-ncfg-first loaded) :accepted))
                (fn-nop-usage (list :configuration (fn-ncfg-second loaded)) nil nil nil)
              (let ((config (fn-ncfg-second loaded)))
                (let ((parsed (fn-nop-parse-command words config argv-octets)))
                  ; Valid configuration is sufficient for offline store actions.
                  ; Only an accepted RUN plan requires every owner backend.
                  ; The refusal names the key (fn-native-config-unsupported-key),
                  ; so the operator is told which line to change.
                  (if (and (equal (fn-native-operator-result-status parsed) :accepted)
                           (equal (fn-native-operator-result-command parsed) "run")
                           (not (fn-native-config-operator-availablep config)))
                      (fn-nop-usage (list :unsupported-profile
                                          (fn-native-config-unsupported-key config))
                                    "run" config nil)
                    parsed))))))))))

(in-theory (disable fn-native-operator-run))

(defun fn-native-operator-result-run-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "run")))

(defun fn-native-operator-result-run-store-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-record-string-octets
       (fn-native-config-store (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-listener-host-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-record-string-octets
       (fn-native-config-listener-host (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-listener-port (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-native-config-listener-port (fn-native-operator-result-config result))
    0))

(defun fn-native-operator-result-run-tls-cert-octets (result)
  (declare (xargs :guard t))
  (if (and (fn-native-operator-result-run-planp result)
           (fn-native-config-tls-cert
            (fn-native-operator-result-config result)))
      (fn-record-string-octets
       (fn-native-config-tls-cert
        (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-tls-key-octets (result)
  (declare (xargs :guard t))
  (if (and (fn-native-operator-result-run-planp result)
           (fn-native-config-tls-key
            (fn-native-operator-result-config result)))
      (fn-record-string-octets
       (fn-native-config-tls-key
        (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-oncep (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-ncfg-nth 2 (fn-native-operator-result-arguments result))
    nil))

; The implicit-TLS listener (`[listener] tls_port', PRF-162): the port a
; served `run' opens beside the plaintext listener, or nil for none.  It is
; offered only when the host will load the TLS context the handshake needs
; (both certificate and key octets, which host/native/operator.lisp opens
; with fnn-tls-open-context), on a port of its own, and not for `run
; --once', which serves one client on the plaintext listener.  The
; connections it accepts run the STARTTLS session machine after its
; handshake (books/served-implicit-tls.lisp).
(defun fn-native-operator-result-run-implicit-tls-port (result)
  (declare (xargs :guard t))
  (let* ((c (fn-native-operator-result-config result))
         (port (fn-native-config-listener-tls-port c)))
    (if (and (fn-native-operator-result-run-planp result)
             (not (fn-native-operator-result-run-oncep result))
             (natp port) (< 0 port) (<= port 65535)
             (fn-ncfg-tls-port-okp port (fn-native-config-listener-port c)
                                   (fn-native-config-tls-cert c))
             (fn-native-operator-result-run-tls-cert-octets result)
             (fn-native-operator-result-run-tls-key-octets result))
        port
      nil)))

; KEYSTONE.  An implicit-TLS listener is offered only beside a loaded
; certificate and key, on a valid port that is not the plaintext one, for a
; served run.  The subject is the accessor host/native/operator.lisp reads
; (fn-native-operator-host-result-run-implicit-tls-port) to decide whether
; fnn-owner-run binds the second listener.
(defthm fn-native-operator-implicit-tls-listener-needs-its-certificate
  (let ((port (fn-native-operator-result-run-implicit-tls-port result)))
    (implies port
             (and (fn-native-operator-result-run-planp result)
                  (not (fn-native-operator-result-run-oncep result))
                  (fn-native-operator-result-run-tls-cert-octets result)
                  (fn-native-operator-result-run-tls-key-octets result)
                  (natp port) (< 0 port) (<= port 65535)
                  (not (equal port
                              (fn-native-operator-result-run-listener-port result))))))
  :hints (("Goal" :in-theory (e/d (fn-ncfg-tls-port-okp
                                   fn-native-operator-result-run-listener-port)
                                  (fn-native-operator-result-run-tls-cert-octets
                                   fn-native-operator-result-run-tls-key-octets
                                   fn-native-operator-result-run-oncep
                                   fn-native-operator-result-run-planp))))
  :rule-classes nil)

(defun fn-native-operator-result-run-max-connections (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-native-config-owner-max-connections
       (fn-native-operator-result-config result))
    0))

(defun fn-native-operator-result-run-auth-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-record-string-octets
       (fn-native-config-auth-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-auth-requiredp (result)
  (declare (xargs :guard t))
  (and (fn-native-operator-result-run-planp result)
       (fn-native-config-auth-requiredp
        (fn-native-operator-result-config result))
       t))

(defun fn-native-operator-result-run-auth-protected-onlyp (result)
  (declare (xargs :guard t))
  (and (fn-native-operator-result-run-planp result)
       (fn-native-config-auth-protected-onlyp
        (fn-native-operator-result-config result))
       t))

(defun fn-native-operator-result-run-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-run-posting-enabledp (result)
  (declare (xargs :guard t))
  (and (fn-native-operator-result-run-planp result)
       (fn-native-config-posting-enabledp
        (fn-native-operator-result-config result))))

; The service log the run plan names, or nil for stderr.  Only an admitted
; profile reaches a run plan, so the path is absolute
; (fn-native-config-log-pathp).
(defun fn-native-operator-result-run-log-path-octets (result)
  (declare (xargs :guard t))
  (if (and (fn-native-operator-result-run-planp result)
           (fn-native-config-log-path (fn-native-operator-result-config result)))
      (fn-record-string-octets
       (fn-native-config-log-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-post-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "post")))

(defun fn-native-operator-result-post-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-post-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-post-msgid-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-post-planp result)
      (fn-record-string-octets
       (fn-ncfg-nth 1 (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-result-post-payload-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-post-planp result)
      (fn-record-string-octets
       (fn-ncfg-nth 2 (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-post-group-octets (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (fn-record-string-octets (car groups))
            (fn-native-operator-post-group-octets (cdr groups)))
    nil))

(defun fn-native-operator-result-post-group-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-post-planp result)
      (fn-native-operator-post-group-octets
      (fn-ncfg-nth 3 (fn-native-operator-result-arguments result)))
    nil))

; -----------------------------------------------------------------------------
; `init': stand the configured store up through the operator.
;
; The plan carries the store root the configuration names and the groups the
; operator named.  Whether that store already exists is a physical question,
; so raw Lisp answers it -- but only by reporting which of the names below it
; found, and ACL2 turns that observation into the tagged outcome.  The one
; guarantee the observation buys is that no lock is taken to make it:
; `writer.lock' is one of the names, so a store a live owner holds is refused
; on its presence rather than on a failed flock.

(defconst *fn-nop-store-markers*
  '("config.json" "writer.lock" "allocation-frontier.json" "transactions"
    "config"))

(defun fn-nop-marker-octets (names)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (fn-record-string-octets (car names))
            (fn-nop-marker-octets (cdr names)))
    nil))

(defun fn-native-operator-init-marker-octets ()
  "The store entries whose presence means an initialised store is already there."
  (declare (xargs :guard t))
  (fn-nop-marker-octets *fn-nop-store-markers*))

(defun fn-native-operator-result-init-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "init")))

(defun fn-native-operator-result-init-store-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-init-planp result)
      (fn-record-string-octets
       (fn-native-config-store (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-init-group-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-init-planp result)
      (fn-native-operator-post-group-octets
       (fn-ncfg-second (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-result-init-profile (result)
  "The profile request (base and field overrides) an accepted init plan
writes, else nil."
  (declare (xargs :guard t))
  (if (fn-native-operator-result-init-planp result)
      (let ((profile (fn-ncfg-second
                      (fn-ncfg-rest (fn-native-operator-result-arguments result)))))
        (if (fn-bs-profile-requestp profile) profile nil))
    nil))

(defun fn-native-operator-result-rollback-path-octets (result)
  "The kept config.json path an accepted `store rollback-check' plan names."
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "store")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :rollback-check)
           (stringp (fn-ncfg-second (fn-native-operator-result-arguments result))))
      (fn-record-string-octets
       (fn-ncfg-second (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-result-upgrade-profile (result)
  "The profile request an accepted `store upgrade-profile' plan names, else nil."
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "store")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :upgrade-profile))
      (let ((profile (fn-ncfg-second (fn-native-operator-result-arguments result))))
        (if (fn-bs-profile-requestp profile) profile nil))
    nil))

(defun fn-native-operator-init-outcome (result observed)
  "The tagged outcome for one accepted init plan and one store observation.

OBSERVED is the sublist of `fn-native-operator-init-marker-octets' that raw
Lisp found beside the configured store root.  A non-empty observation is a
refusal: an existing store is adopted by `run' and repaired by `recover', and
this command creates one.  It is deliberately not an uncertainty -- nothing
was written -- and not a usage error, because the command line was well
formed and the operator asked for something the node declined to do."
  (declare (xargs :guard t))
  (cond ((not (fn-native-operator-result-init-planp result))
         (fn-nop-usage :not-an-init-plan "init"
                       (fn-native-operator-result-config result) nil))
        ((consp observed)
         (fn-nop-refused :store-exists "init"
                         (fn-native-operator-result-config result)
                         (fn-native-operator-result-arguments result)))
        (t (fn-nop-result :accepted :initialize "init"
                          (fn-native-operator-result-config result)
                          (fn-native-operator-result-arguments result)))))

(defun fn-native-operator-result-admin-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (or (equal (fn-native-operator-result-command result) "group")
           (equal (fn-native-operator-result-command result) "capacity")
           (equal (fn-native-operator-result-command result) "peer")
           (equal (fn-native-operator-result-command result) "bp-boundary")
           (equal (fn-native-operator-result-command result) "bp-route")
           (equal (fn-native-operator-result-command result) "policy")
           (equal (fn-native-operator-result-command result) "retention")
           (equal (fn-native-operator-result-command result) "control")
           (and (equal (fn-native-operator-result-command result) "account")
                (not (equal (fn-ncfg-first
                             (fn-native-operator-result-arguments result))
                            :account-invite))))))

;; PRF-164: the seconds of an accepted `account invite' plan, or nil.
(defun fn-native-operator-result-account-invite-seconds (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "account")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :account-invite))
      (fn-ncfg-second (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-admin-plan (result)
  "The exact ACL2 administrative plan; no raw argv reaches the executor."
  ; The arguments field is whatever the plan put there, so the total
  ; accessors of books/native-config read it: `car' of it cannot run under a
  ; verified guard, and these three read a result the host may hand back.
  (declare (xargs :guard t))
  (if (fn-native-operator-result-admin-planp result)
      (fn-ncfg-first (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-admin-argv (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-admin-planp result)
      (fn-ncfg-second (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-principal-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "principal")))

(defun fn-native-operator-result-principal-plan (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-principal-planp result)
      (fn-ncfg-first (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-principal-auth-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-principal-planp result)
      (fn-record-string-octets
       (fn-native-config-auth-path (fn-native-operator-result-config result)))
    nil))

; The store the configuration declares, whose writer lock tells the principal
; verb whether an owner is serving (PKT-102,
; fn-native-auth-admin-effect-word).
(defun fn-native-operator-result-principal-store-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-principal-planp result)
      (fn-record-string-octets
       (fn-native-config-store (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-peering-words (result)
  "The verb and words of an accepted `peer keygen|genesis|invite|accept|confirm'."
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "peer")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :peering))
      (fn-ncfg-rest (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-peering-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-peering-words result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-keys-msgid-octets (result)
  "The Message-ID of an accepted `keys redecide MSGID', as octets."
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "keys")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :keys)
           (stringp (fn-ncfg-third (fn-native-operator-result-arguments result))))
      (fn-record-string-octets
       (fn-ncfg-third (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-result-keys-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-keys-msgid-octets result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-native-action (result)
  "The only commands the current raw native module may execute by itself.

`run' and `post' retain normalized plans for the owner and local-control
callbacks.  Neither is translated into a direct Store call.  `init' is an
offline store action like `status' and `recover': it names the store the
configuration declares and the groups the operator named, and its refusal
when that store already exists is `fn-native-operator-init-outcome'."
  (declare (xargs :guard t))
  (if (not (equal (fn-native-operator-result-status result) :accepted))
      :none
    (cond ((equal (fn-native-operator-result-command result) "help") :help)
          ((equal (fn-native-operator-result-command result) "init") :init)
          ((equal (fn-native-operator-result-command result) "run") :run)
          ((equal (fn-native-operator-result-command result) "post") :post)
          ((equal (fn-native-operator-result-command result) "status") :status)
          ((equal (fn-native-operator-result-command result) "pins") :status)
          ((equal (fn-native-operator-result-command result) "health") :health)
          ((equal (fn-native-operator-result-command result) "obligations") :status)
          ((equal (fn-native-operator-result-command result) "recover") :recover)
          ((equal (fn-native-operator-result-command result) "store")
           (cond ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :compact)
                  :compact)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :checkpoint)
                  :checkpoint)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :reclaim)
                  :reclaim)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :reclaim-dry-run)
                  :reclaim-dry-run)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :needs-upgrade)
                  :needs-upgrade)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :rollback-check)
                  :rollback-check)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :rollback-snapshot)
                  :rollback-snapshot)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :inspect)
                  :inspect)
                 (t :upgrade-profile)))
          ((and (equal (fn-native-operator-result-command result) "peer")
                (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                       :peering))
           :peering)
          ((or (equal (fn-native-operator-result-command result) "group")
               (equal (fn-native-operator-result-command result) "capacity")
               (equal (fn-native-operator-result-command result) "peer")
               (equal (fn-native-operator-result-command result) "bp-boundary")
               (equal (fn-native-operator-result-command result) "bp-route")
               (equal (fn-native-operator-result-command result) "policy")
               (equal (fn-native-operator-result-command result) "retention")
           (equal (fn-native-operator-result-command result) "control")) :admin)
          ((and (equal (fn-native-operator-result-command result) "account")
                (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                       :account-invite))
           :account-invite)
          ((equal (fn-native-operator-result-command result) "account") :admin)
          ((equal (fn-native-operator-result-command result) "principal") :principal)
          ((equal (fn-native-operator-result-command result) "keys") :keys)
          ((equal (fn-native-operator-result-command result) "show") :show)
          ((equal (fn-native-operator-result-command result) "mission") :mission)
          (t :owner-required))))

; KEYSTONE (RFC 5536 s3.1.4 reserved names at `init').  The subject is
; `fn-native-operator-run', which host/native-operator-host.lisp:19 calls
; (`fn-native-operator-host-run').  An `init' naming a reserved group, in
; any position, is never an accepted plan, so `fnn-operator-dispatch-plan'
; (host/native/operator.lisp) emits the result and exits before
; `fnn-operator-execute-init' observes or creates anything.
(local (defthm fn-nop-some-reserved-when-member
  (implies (and (member-equal name names)
                (fn-native-admin-group-name-reservedp name))
           (fn-native-admin-some-group-name-reservedp names))))

(defthm fn-native-operator-run-refuses-a-reserved-init-group
  (implies (and (equal (car (fn-nop-argument-texts argv)) "init")
                (member-equal name (cdr (fn-nop-argument-texts argv)))
                (fn-native-admin-group-name-reservedp name))
           (not (equal (fn-native-operator-result-status
                        (fn-native-operator-run config argv))
                       :accepted)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-parse-command fn-nop-parse-init
                                   fn-nop-parse-init-plain
                                   fn-nop-usage fn-nop-refused fn-nop-result
                                   fn-native-operator-result-status)
                                  (fn-native-admin-group-name-reservedp
                                   fn-native-admin-some-group-name-reservedp
                                   fn-nop-parse-init-groups fn-nop-argument-texts
                                   fn-nop-parse-profile-flags
                                   fn-bs-profile-resolve
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep)))))

; KEYSTONE (M5, the operator entry to compaction).  The subject is
; `fn-native-operator-run' (host/native-operator-host.lisp calls it) and the
; projection `fn-native-operator-result-native-action' that
; `fnn-operator-dispatch-plan' (host/native/operator.lisp) dispatches on.
; An accepted `store compact' is the :compact action, and the :compact
; action arises from that argv and no other (a further word, another
; subcommand, another verb), so the raw host reaches `fnn-command-compact'
; only for the bare command.
(defthm fn-native-operator-run-store-compact-is-the-compact-action
  (implies (and (equal (fn-nop-argument-texts argv) '("store" "compact"))
                (equal (fn-native-operator-result-status
                        (fn-native-operator-run config argv))
                       :accepted))
           (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :compact))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-parse-command fn-nop-parse-store
                                   fn-nop-usage fn-nop-refused fn-nop-result
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-native-operator-result-native-action)
                                  (fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep)))))

(local
 (defthm fn-nop-result-accessors
   (and (equal (fn-native-operator-result-status (fn-nop-result s r c g a)) s)
        (equal (fn-native-operator-result-command (fn-nop-result s r c g a)) c)
        (equal (fn-native-operator-result-arguments (fn-nop-result s r c g a)) a))
   :hints (("Goal" :in-theory (enable fn-nop-result fn-native-operator-result-status
                                      fn-native-operator-result-command
                                      fn-native-operator-result-arguments)))))

; Which subcommand parser answers is visible in the result's command field.
(local
 (defthm fn-nop-parse-init-command
   (equal (fn-native-operator-result-command (fn-nop-parse-init w c)) "init")
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-init fn-nop-usage fn-nop-refused)
                                   (fn-nop-result fn-native-operator-result-command fn-nop-parse-init-groups fn-nop-parse-profile-flags fn-bs-profile-resolve fn-native-admin-some-group-name-reservedp))))))

(local
 (defthm fn-nop-parse-post-command
   (equal (fn-native-operator-result-command (fn-nop-parse-post w c)) "post")
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-post fn-nop-usage fn-nop-refused)
                                   (fn-nop-result fn-native-operator-result-command fn-nop-parse-post-aux fn-native-config-posting-enabledp))))))

(local
 (defthm fn-nop-parse-principal-command
   (equal (fn-native-operator-result-command (fn-nop-parse-principal a c)) "principal")
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-principal fn-nop-usage fn-nop-refused)
                                   (fn-nop-result fn-native-operator-result-command fn-native-auth-admin-parse-argv fn-native-auth-admin-plan-status fn-native-auth-admin-plan-reason))))))

(local
 (defthm fn-nop-parse-administration-command
   (equal (fn-native-operator-result-command (fn-nop-parse-administration command a c)) command)
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-administration fn-nop-usage fn-nop-refused)
                                   (fn-nop-result fn-native-operator-result-command fn-native-admin-plan fn-native-admin-result-status fn-native-admin-result-reason))))))

(local
 (defthm fn-nop-parse-store-command
   (equal (fn-native-operator-result-command (fn-nop-parse-store w c)) "store")
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-store fn-nop-usage fn-nop-refused)
                                   (fn-nop-result fn-native-operator-result-command fn-nop-parse-profile-flags fn-nop-profile-preset-word))))))

(local
 (defthm fn-nop-parse-store-compact-words
   (implies (and (equal (fn-native-operator-result-status (fn-nop-parse-store w c))
                        :accepted)
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-store w c)))
                        :compact))
            (equal w '("compact")))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)))))

(local
 (defthm fn-nop-parse-command-compact-words
   (implies (and (equal (fn-native-operator-result-status
                         (fn-nop-parse-command words config argv))
                        :accepted)
                 (equal (fn-native-operator-result-command
                         (fn-nop-parse-command words config argv))
                        "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-command words config argv)))
                        :compact))
            (equal words '("store" "compact")))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-command fn-nop-usage)
                                   (fn-nop-result
                                    fn-native-operator-result-status
                                    fn-native-operator-result-command
                                    fn-native-operator-result-arguments
                                    fn-nop-parse-init fn-nop-parse-post
                                    fn-nop-parse-principal
                                    fn-nop-parse-administration
                                    fn-nop-parse-store fn-nop-parse-run
                                    fn-nop-help-text fn-nop-help-subjectp))
            :use ((:instance fn-nop-parse-store-compact-words
                             (w (cdr words)) (c config)))))))

(local
 (defthm fn-nop-compact-action-shape
   (implies (equal (fn-native-operator-result-native-action result) :compact)
            (and (equal (fn-native-operator-result-status result) :accepted)
                 (equal (fn-native-operator-result-command result) "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                        :compact)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-native-operator-result-native-action)))))

(local
 (defthm fn-nop-native-action-of-unaccepted
   (implies (not (equal (fn-native-operator-result-status result) :accepted))
            (equal (fn-native-operator-result-native-action result) :none))
   :hints (("Goal" :in-theory (enable fn-native-operator-result-native-action)))))

(local
 (defthm fn-nop-parse-command-compact-action-words
   (implies (equal (fn-native-operator-result-native-action
                    (fn-nop-parse-command words config argv))
                   :compact)
            (equal words '("store" "compact")))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-nop-compact-action-shape
                                       fn-native-operator-result-native-action
                                       fn-nop-parse-command)
            :use ((:instance fn-nop-compact-action-shape
                             (result (fn-nop-parse-command words config argv)))
                  fn-nop-parse-command-compact-words)))))

(defthm fn-native-operator-run-compact-action-is-only-store-compact
  (implies (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :compact)
           (equal (fn-nop-argument-texts argv) '("store" "compact")))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-usage)
                                  (fn-nop-result
                                   fn-native-operator-result-native-action
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-nop-parse-command fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep))
           :use ((:instance fn-nop-parse-command-compact-action-words
                            (words (fn-nop-argument-texts argv))
                            (config (fn-ncfg-second (fn-native-config-load config)))
                            (argv argv))
                 (:instance fn-nop-parse-command-compact-action-words
                            (words (fn-nop-argument-texts argv))
                            (config nil) (argv argv))))))

; KEYSTONE (P3, the operator entry to the state checkpoint).  The same
; subject and projection as the compaction keystone above: an accepted
; `store checkpoint' is the :checkpoint action, and the :checkpoint action
; arises from that argv and no other, so the raw host reaches
; `fnn-command-state-checkpoint' only for the bare command.
(defthm fn-native-operator-run-store-checkpoint-is-the-checkpoint-action
  (implies (and (equal (fn-nop-argument-texts argv) '("store" "checkpoint"))
                (equal (fn-native-operator-result-status
                        (fn-native-operator-run config argv))
                       :accepted))
           (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :checkpoint))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-parse-command fn-nop-parse-store
                                   fn-nop-usage fn-nop-refused fn-nop-result
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-native-operator-result-native-action)
                                  (fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep)))))

(local
 (defthm fn-nop-parse-store-checkpoint-words
   (implies (and (equal (fn-native-operator-result-status (fn-nop-parse-store w c))
                        :accepted)
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-store w c)))
                        :checkpoint))
            (equal w '("checkpoint")))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)))))

(local
 (defthm fn-nop-parse-command-checkpoint-words
   (implies (and (equal (fn-native-operator-result-status
                         (fn-nop-parse-command words config argv))
                        :accepted)
                 (equal (fn-native-operator-result-command
                         (fn-nop-parse-command words config argv))
                        "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-command words config argv)))
                        :checkpoint))
            (equal words '("store" "checkpoint")))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-command fn-nop-usage)
                                   (fn-nop-result
                                    fn-native-operator-result-status
                                    fn-native-operator-result-command
                                    fn-native-operator-result-arguments
                                    fn-nop-parse-init fn-nop-parse-post
                                    fn-nop-parse-principal
                                    fn-nop-parse-administration
                                    fn-nop-parse-store fn-nop-parse-run
                                    fn-nop-help-text fn-nop-help-subjectp))
            :use ((:instance fn-nop-parse-store-checkpoint-words
                             (w (cdr words)) (c config)))))))

(local
 (defthm fn-nop-checkpoint-action-shape
   (implies (equal (fn-native-operator-result-native-action result) :checkpoint)
            (and (equal (fn-native-operator-result-status result) :accepted)
                 (equal (fn-native-operator-result-command result) "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                        :checkpoint)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-native-operator-result-native-action)))))

(local
 (defthm fn-nop-parse-command-checkpoint-action-words
   (implies (equal (fn-native-operator-result-native-action
                    (fn-nop-parse-command words config argv))
                   :checkpoint)
            (equal words '("store" "checkpoint")))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-nop-checkpoint-action-shape
                                       fn-native-operator-result-native-action
                                       fn-nop-parse-command)
            :use ((:instance fn-nop-checkpoint-action-shape
                             (result (fn-nop-parse-command words config argv)))
                  fn-nop-parse-command-checkpoint-words)))))

(defthm fn-native-operator-run-checkpoint-action-is-only-store-checkpoint
  (implies (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :checkpoint)
           (equal (fn-nop-argument-texts argv) '("store" "checkpoint")))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-usage)
                                  (fn-nop-result
                                   fn-native-operator-result-native-action
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-nop-parse-command fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep))
           :use ((:instance fn-nop-parse-command-checkpoint-action-words
                            (words (fn-nop-argument-texts argv))
                            (config (fn-ncfg-second (fn-native-config-load config)))
                            (argv argv))
                 (:instance fn-nop-parse-command-checkpoint-action-words
                            (words (fn-nop-argument-texts argv))
                            (config nil) (argv argv))))))

; KEYSTONE (STO-017, the operator entry to content reclamation).  The
; same subject and projection as the compaction keystone above: an
; accepted `store reclaim' is the :reclaim action, and the
; :reclaim action arises from that argv and no other, so the raw host
; reaches `fnn-command-reclaim' without --dry-run only for it.
(defthm fn-native-operator-run-store-reclaim-is-the-reclaim-action
  (implies (and (equal (fn-nop-argument-texts argv) '("store" "reclaim"))
                (equal (fn-native-operator-result-status
                        (fn-native-operator-run config argv))
                       :accepted))
           (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :reclaim))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-parse-command fn-nop-parse-store
                                   fn-nop-usage fn-nop-refused fn-nop-result
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-native-operator-result-native-action)
                                  (fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep)))))

(local
 (defthm fn-nop-parse-store-reclaim-words
   (implies (and (equal (fn-native-operator-result-status (fn-nop-parse-store w c))
                        :accepted)
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-store w c)))
                        :reclaim))
            (equal w '("reclaim")))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)))))

(local
 (defthm fn-nop-parse-command-reclaim-words
   (implies (and (equal (fn-native-operator-result-status
                         (fn-nop-parse-command words config argv))
                        :accepted)
                 (equal (fn-native-operator-result-command
                         (fn-nop-parse-command words config argv))
                        "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-command words config argv)))
                        :reclaim))
            (equal words '("store" "reclaim")))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-command fn-nop-usage)
                                   (fn-nop-result
                                    fn-native-operator-result-status
                                    fn-native-operator-result-command
                                    fn-native-operator-result-arguments
                                    fn-nop-parse-init fn-nop-parse-post
                                    fn-nop-parse-principal
                                    fn-nop-parse-administration
                                    fn-nop-parse-store fn-nop-parse-run
                                    fn-nop-help-text fn-nop-help-subjectp))
            :use ((:instance fn-nop-parse-store-reclaim-words
                             (w (cdr words)) (c config)))))))

(local
 (defthm fn-nop-reclaim-action-shape
   (implies (equal (fn-native-operator-result-native-action result) :reclaim)
            (and (equal (fn-native-operator-result-status result) :accepted)
                 (equal (fn-native-operator-result-command result) "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                        :reclaim)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-native-operator-result-native-action)))))

(local
 (defthm fn-nop-parse-command-reclaim-action-words
   (implies (equal (fn-native-operator-result-native-action
                    (fn-nop-parse-command words config argv))
                   :reclaim)
            (equal words '("store" "reclaim")))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-nop-reclaim-action-shape
                                       fn-native-operator-result-native-action
                                       fn-nop-parse-command)
            :use ((:instance fn-nop-reclaim-action-shape
                             (result (fn-nop-parse-command words config argv)))
                  fn-nop-parse-command-reclaim-words)))))

(defthm fn-native-operator-run-reclaim-action-is-only-store-reclaim
  (implies (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :reclaim)
           (equal (fn-nop-argument-texts argv) '("store" "reclaim")))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-usage)
                                  (fn-nop-result
                                   fn-native-operator-result-native-action
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-nop-parse-command fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep))
           :use ((:instance fn-nop-parse-command-reclaim-action-words
                            (words (fn-nop-argument-texts argv))
                            (config (fn-ncfg-second (fn-native-config-load config)))
                            (argv argv))
                 (:instance fn-nop-parse-command-reclaim-action-words
                            (words (fn-nop-argument-texts argv))
                            (config nil) (argv argv))))))

; KEYSTONE (STO-017, the operator entry to content reclamation).  The
; same subject and projection as the compaction keystone above: an
; accepted `store reclaim --dry-run' is the :reclaim-dry-run action, and the
; :reclaim-dry-run action arises from that argv and no other, so the raw host
; reaches `fnn-command-reclaim' with --dry-run only for it.
(defthm fn-native-operator-run-store-reclaim-dry-run-is-the-reclaim-dry-run-action
  (implies (and (equal (fn-nop-argument-texts argv) '("store" "reclaim" "--dry-run"))
                (equal (fn-native-operator-result-status
                        (fn-native-operator-run config argv))
                       :accepted))
           (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :reclaim-dry-run))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-parse-command fn-nop-parse-store
                                   fn-nop-usage fn-nop-refused fn-nop-result
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-native-operator-result-native-action)
                                  (fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep)))))

(local
 (defthm fn-nop-parse-store-reclaim-dry-run-words
   (implies (and (equal (fn-native-operator-result-status (fn-nop-parse-store w c))
                        :accepted)
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-store w c)))
                        :reclaim-dry-run))
            (equal w '("reclaim" "--dry-run")))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)))))

(local
 (defthm fn-nop-parse-command-reclaim-dry-run-words
   (implies (and (equal (fn-native-operator-result-status
                         (fn-nop-parse-command words config argv))
                        :accepted)
                 (equal (fn-native-operator-result-command
                         (fn-nop-parse-command words config argv))
                        "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-command words config argv)))
                        :reclaim-dry-run))
            (equal words '("store" "reclaim" "--dry-run")))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-command fn-nop-usage)
                                   (fn-nop-result
                                    fn-native-operator-result-status
                                    fn-native-operator-result-command
                                    fn-native-operator-result-arguments
                                    fn-nop-parse-init fn-nop-parse-post
                                    fn-nop-parse-principal
                                    fn-nop-parse-administration
                                    fn-nop-parse-store fn-nop-parse-run
                                    fn-nop-help-text fn-nop-help-subjectp))
            :use ((:instance fn-nop-parse-store-reclaim-dry-run-words
                             (w (cdr words)) (c config)))))))

(local
 (defthm fn-nop-reclaim-dry-run-action-shape
   (implies (equal (fn-native-operator-result-native-action result) :reclaim-dry-run)
            (and (equal (fn-native-operator-result-status result) :accepted)
                 (equal (fn-native-operator-result-command result) "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                        :reclaim-dry-run)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-native-operator-result-native-action)))))

(local
 (defthm fn-nop-parse-command-reclaim-dry-run-action-words
   (implies (equal (fn-native-operator-result-native-action
                    (fn-nop-parse-command words config argv))
                   :reclaim-dry-run)
            (equal words '("store" "reclaim" "--dry-run")))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-nop-reclaim-dry-run-action-shape
                                       fn-native-operator-result-native-action
                                       fn-nop-parse-command)
            :use ((:instance fn-nop-reclaim-dry-run-action-shape
                             (result (fn-nop-parse-command words config argv)))
                  fn-nop-parse-command-reclaim-dry-run-words)))))

(defthm fn-native-operator-run-reclaim-dry-run-action-is-only-store-reclaim-dry-run
  (implies (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :reclaim-dry-run)
           (equal (fn-nop-argument-texts argv) '("store" "reclaim" "--dry-run")))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-usage)
                                  (fn-nop-result
                                   fn-native-operator-result-native-action
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-arguments
                                   fn-nop-parse-command fn-nop-argument-texts
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp
                                   fn-native-config-operator-availablep))
           :use ((:instance fn-nop-parse-command-reclaim-dry-run-action-words
                            (words (fn-nop-argument-texts argv))
                            (config (fn-ncfg-second (fn-native-config-load config)))
                            (argv argv))
                 (:instance fn-nop-parse-command-reclaim-dry-run-action-words
                            (words (fn-nop-argument-texts argv))
                            (config nil) (argv argv))))))

; The status report the operator asked for (books/native-live-status.lisp
; renders it), the watch interval, and the control socket the running owner
; answers on.  `peer list' is the fourth kind, reached through its
; administrative query plan (`fn-native-operator-result-admin-plan').
(defun fn-native-operator-result-status-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (member-equal (fn-native-operator-result-command result)
                     '("status" "health" "pins" "obligations"))
       t))

(defun fn-native-operator-result-status-kind (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-status-planp result)
      (fn-ncfg-first (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-status-watch (result)
  (declare (xargs :guard t))
  (if (and (fn-native-operator-result-status-planp result)
           (equal (fn-ncfg-second (fn-native-operator-result-arguments result))
                  :watch))
      (fn-ncfg-third (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-status-control-path-octets (result)
  (declare (xargs :guard t))
  (if (or (fn-native-operator-result-status-planp result)
          (fn-native-operator-result-admin-planp result))
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

; PRF-112: the operator's [alerts] headroom_min_percent, the threshold of the
; health verdict's space-pressure state (books/native-health.lisp).
(defun fn-native-operator-result-health-min-percent (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (member-equal (fn-native-operator-result-command result) '("health" "run")))
      (nfix (fn-native-config-alerts-headroom-min-percent
             (fn-native-operator-result-config result)))
    0))

; PKT-096/PKT-097 projections the raw host reads.
(defun fn-native-operator-result-mission-octets (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "mission"))
      (fn-ncfg-third (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-mission-directory-octets (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "mission"))
      (fn-native-operator-post-group-octets
       (fn-ncfg-nth 3 (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-result-show-octets (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "show"))
      (fn-ncfg-second (fn-native-operator-result-arguments result))
    nil))

; -----------------------------------------------------------------------------
; HST-008 / PRF-130 part 1: "no store here" is a refusal, never a fault.
;
; Every accepted plan whose native action reads or writes an existing store
; is first checked against the same observation `init' uses: which of
; `*fn-nop-store-markers*' exist beside the configured store root (lstat
; only, no lock; host/native/operator.lisp `fnn-operator-init-observed').
; With none of them there is no store to open, and the outcome is the
; refusal :no-store (the refusal code 1, HST-009), not the host fault the
; open would otherwise raise ("missing store directory").  A partial store
; (some markers, e.g. an interrupted init) is not "no store": it proceeds to
; the open, which recovers or refuses it.

(defconst *fn-nop-store-actions*
  '(:run :post :status :health :recover :compact :checkpoint :reclaim
    :reclaim-dry-run :needs-upgrade :rollback-check :rollback-snapshot
    :upgrade-profile :admin :inspect
    :peering :principal :keys))

(defun fn-native-operator-result-needs-storep (result)
  "An accepted plan whose native action opens the configured store."
  (declare (xargs :guard t))
  (and (member-equal (fn-native-operator-result-native-action result)
                     *fn-nop-store-actions*)
       t))

(defun fn-native-operator-store-outcome (result observed)
  "RESULT unchanged, or the :no-store refusal when RESULT needs a store and
OBSERVED (the markers found beside the store root) is empty."
  (declare (xargs :guard t))
  (if (and (fn-native-operator-result-needs-storep result)
           (not (consp observed)))
      (fn-nop-refused :no-store
                      (fn-native-operator-result-command result)
                      (fn-native-operator-result-config result)
                      (fn-native-operator-result-arguments result))
    result))

; KEYSTONE PRF-130 part 1.  The subject is `fn-native-operator-store-outcome',
; which `fnn-operator-dispatch-plan' (host/native/operator.lisp) calls through
; `fn-native-operator-host-store-outcome' on every accepted plan before it
; executes the action.  For a plan that needs a store and an observation that
; found none of the store's entries, the outcome is a refusal named
; :no-store whose exit code is the refusal code 1 (HST-009; PKT-295): never
; accepted (so no action runs and no open is attempted), never the fault code
; 4, never the usage code 5, never the fenced code 3.
(local
 (defthm fn-nop-native-action-of-refused
   (equal (fn-native-operator-result-native-action (list :refused r c g a)) :none)
   :hints (("Goal" :in-theory '(fn-native-operator-result-native-action
                                fn-native-operator-result-status
                                fn-ncfg-first car-cons)))))

(defthm fn-native-operator-absent-store-is-refused
  (implies (and (fn-native-operator-result-needs-storep result)
                (not (consp observed)))
           (let ((outcome (fn-native-operator-store-outcome result observed)))
             (and (equal (fn-native-operator-result-status outcome) :refused)
                  (equal (fn-native-operator-result-reason outcome) :no-store)
                  (equal (fn-native-operator-exit-code outcome)
                         (fn-outcome-code :refused))
                  (equal (fn-native-operator-result-native-action outcome) :none))))
  :hints (("Goal" :in-theory '(fn-native-operator-store-outcome
                                fn-nop-refused fn-nop-result
                                fn-native-operator-result-status
                                fn-native-operator-result-reason
                                fn-native-operator-exit-code
                                fn-native-operator-outcome-class
                                fn-outcome-of-status
                                fn-ncfg-first fn-ncfg-second fn-ncfg-rest
                                (:e fn-native-operator-result-native-action)
                                fn-nop-native-action-of-refused
                                car-cons cdr-cons))))

; The converse half: a store that is there (any marker observed) or a plan
; that needs none is passed through untouched, so the check refuses nothing
; the store actions would have served.
(defthm fn-native-operator-store-outcome-passes-a-present-store
  (implies (or (consp observed)
               (not (fn-native-operator-result-needs-storep result)))
           (equal (fn-native-operator-store-outcome result observed) result))
  :hints (("Goal" :in-theory '(fn-native-operator-store-outcome))))

;  The line printed before a usage or refused result's tagged line: what the
; command accepts, or what to do.  ACL2's words; the host prints them.
(defun fn-native-operator-result-hint (result)
  (declare (xargs :guard t))
  (let ((status (fn-native-operator-result-status result))
        (reason (fn-native-operator-result-reason result))
        (command (fn-native-operator-result-command result)))
    (cond ((and (equal status :refused) (equal reason :no-store))
           "no store at the configured [store] path: this node was never initialized; run: fn operator CONFIG init GROUP... (a mission's fn.toml: init with no group)")
          ((and (equal status :usage) (equal reason :mission-fixes-profile))
           "under [ops] mission, init takes GROUP words only (none: the mission's default groups); the mission fixes the store profile. Raise a bound afterwards offline with: fn operator CONFIG store upgrade-profile --FIELD N (fields only rise; the presets are smaller than a mission's); or delete the mission line from fn.toml to choose a profile at init")
          ((and (equal status :usage) (fn-nop-help-subjectp command))
           (fn-nop-help-text command))
          (t nil))))

(defun fn-native-operator-result-snapshot-path-octets (result)
  "The snapshot store root an accepted `store rollback-check --snapshot' names."
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "store")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :rollback-snapshot)
           (stringp (fn-ncfg-second (fn-native-operator-result-arguments result))))
      (fn-record-string-octets
       (fn-ncfg-second (fn-native-operator-result-arguments result)))
    nil))

; -----------------------------------------------------------------------------
; What restoring a snapshot loses (mandate 5.6: "Restoring a pre-migration
; snapshot can lose later accepted articles; operational instructions must say
; so plainly").  The host (host/native/io.lisp `fnn-command-rollback-snapshot')
; acquires both stores under their shared writer locks, reads each one's
; committed history as the open reads it (`fnn-rollback-history': the selected
; pack's records, then the suffix files, the committed-history marker checked),
; and hands ACL2 the records one pair at a time.  An event is a committed
; record's exact octets.  The snapshot is an earlier state of this store only
; when its records are this store's first records; the loss is then every
; committed record after them.
;
; Until 2026-09-26 the host handed (SEQUENCE . FILE-LENGTH) pairs instead, and
; two histories whose records agree in number and length but not in content
; passed as one history (gpt-6's answers section 7).  Counters and lengths are not
; compared here at all: not as a filter, not as a count.

(defun fn-nop-history-prefixp (snap cur)
  (declare (xargs :guard t))
  (if (consp snap)
      (and (consp cur)
           (equal (car snap) (car cur))
           (fn-nop-history-prefixp (cdr snap) (cdr cur)))
    t))

(defun fn-nop-history-suffix (snap cur)
  (declare (xargs :guard t))
  (if (and (consp snap) (consp cur))
      (fn-nop-history-suffix (cdr snap) (cdr cur))
    cur))

(defun fn-native-operator-snapshot-loss (snap cur)
  "(:loses N) when SNAP's events are a prefix of CUR's, N the events committed
after it; else (:refused :snapshot-not-a-prefix)."
  (declare (xargs :guard t))
  (if (fn-nop-history-prefixp snap cur)
      (list :loses (len (fn-nop-history-suffix snap cur)))
    (list :refused :snapshot-not-a-prefix)))

(defthm fn-nop-history-suffix-len
  (implies (fn-nop-history-prefixp snap cur)
           (equal (len (fn-nop-history-suffix snap cur))
                  (- (len cur) (len snap)))))

(defthm fn-native-operator-snapshot-loss-counts-the-suffix
  (and (iff (equal (car (fn-native-operator-snapshot-loss snap cur)) :loses)
            (fn-nop-history-prefixp snap cur))
       (implies (fn-nop-history-prefixp snap cur)
                (equal (cadr (fn-native-operator-snapshot-loss snap cur))
                       (- (len cur) (len snap))))))

; The comparison the host drives: one call per snapshot record, with the
; store's record at the same position (CUR-PRESENT nil when the store has no
; record there), then the verdict over the store's record count.
(defun fn-native-operator-history-start ()
  (declare (xargs :guard t))
  (list :matching 0))

(defun fn-native-operator-history-step (acc snap-event cur-present cur-event)
  (declare (xargs :guard t))
  (if (and (equal (fn-ncfg-first acc) :matching)
           cur-present
           (equal snap-event cur-event))
      (list :matching (+ 1 (nfix (fn-ncfg-second acc))))
    (list :diverged)))

(defun fn-native-operator-history-verdict (acc ncur)
  (declare (xargs :guard t))
  (if (equal (fn-ncfg-first acc) :matching)
      (list :loses (nfix (- (nfix ncur) (nfix (fn-ncfg-second acc)))))
    (list :refused :snapshot-not-a-prefix)))

; The host's loop, as a function: `fnn-command-rollback-snapshot' calls
; `fn-native-operator-history-step' once per snapshot record in order, with
; the store's records consumed alongside, from
; `fn-native-operator-history-start', and then
; `fn-native-operator-history-verdict' with the store's record count: the
; composition the two theorems below are stated over.
(defun fn-nop-history-run (acc snap cur)
  (declare (xargs :guard t))
  (if (consp snap)
      (fn-nop-history-run (fn-native-operator-history-step
                           acc (car snap) (consp cur) (fn-ncfg-first cur))
                          (cdr snap) (fn-ncfg-rest cur))
    acc))

(local
 (defthm fn-nop-history-run-diverged
   (equal (fn-nop-history-run '(:diverged) snap cur)
          '(:diverged))))

(local
 (defun fn-nop-history-run-ind (k snap cur)
   (if (consp snap)
       (fn-nop-history-run-ind (+ 1 k) (cdr snap) (fn-ncfg-rest cur))
     (list k cur))))

(local
 (defthm fn-nop-history-run-matching
   (implies (natp k)
            (equal (fn-nop-history-run (list :matching k) snap cur)
                   (if (fn-nop-history-prefixp snap cur)
                       (list :matching (+ k (len snap)))
                     '(:diverged))))
   :hints (("Goal" :induct (fn-nop-history-run-ind k snap cur)
            :in-theory (enable fn-ncfg-rest)))))

(local
 (defthm fn-nop-history-prefixp-len
   (implies (fn-nop-history-prefixp snap cur)
            (<= (len snap) (len cur)))
   :rule-classes :linear))

; The streamed comparison is the list-level one: the host's calls compute
; `fn-native-operator-snapshot-loss' of the two record lists.
(defthm fn-native-operator-history-loss-is-snapshot-loss
  (equal (fn-native-operator-history-verdict
          (fn-nop-history-run (fn-native-operator-history-start) snap cur)
          (len cur))
         (fn-native-operator-snapshot-loss snap cur)))

(local
 (defthm fn-nop-history-prefixp-is-append
   (iff (fn-nop-history-prefixp snap cur)
        (equal (append snap (nthcdr (len snap) cur)) cur))))

(local
 (defthm fn-nop-history-suffix-is-nthcdr
   (implies (fn-nop-history-prefixp snap cur)
            (equal (fn-nop-history-suffix snap cur)
                   (nthcdr (len snap) cur)))))

; KEYSTONE (PRF-141, the rollback verb's history claim).  The subject is the
; composition `fnn-command-rollback-snapshot' (host/native/io.lisp) runs
; through `fn-native-operator-host-history-start', `-step' and `-verdict'
; over the two stores' committed records.  The verb answers :loses exactly when the store's history is the
; snapshot's records followed by more records, and the count it prints is the
; number of those later records: the ones restoring the snapshot throws away.
; Two histories that agree in record counts and lengths but differ in any
; record's octets are refused.
(defthm fn-native-operator-history-loss-is-ancestry
  (let ((verdict (fn-native-operator-history-verdict
                  (fn-nop-history-run (fn-native-operator-history-start) snap cur)
                  (len cur))))
    (and (iff (equal (car verdict) :loses)
              (equal (append snap (nthcdr (len snap) cur)) cur))
         (implies (equal (append snap (nthcdr (len snap) cur)) cur)
                  (equal (cadr verdict)
                         (len (nthcdr (len snap) cur)))))))

(defun fn-nop-nat-text (n)
  (declare (xargs :guard t))
  (coerce (explode-atom (nfix n) 10) 'string))

; The verb's two lines, ACL2's words: the count and the plain sentence the
; mandate asks the operator instructions to carry (5.6).
(defun fn-native-operator-snapshot-loss-report (verdict nsnap ncur)
  (declare (xargs :guard t))
  (if (equal (fn-ncfg-first verdict) :loses)
      (let ((n (fn-nop-nat-text (fn-ncfg-second verdict))))
        (concatenate 'string
                     "rollback snapshot loses transactions=" n
                     " snapshot-transactions=" (fn-nop-nat-text nsnap)
                     " store-transactions=" (fn-nop-nat-text ncur)
                     (coerce '(#\Newline) 'string)
                     "the snapshot's committed records are this store's first "
                     (fn-nop-nat-text nsnap)
                     ", compared record by record (packed records included); "
                     "restoring this snapshot loses every transaction committed after it: "
                     n
                     ", the articles accepted since it among them; the snapshot cannot give them back"))
    (concatenate 'string
                 "rollback snapshot refused snapshot-not-a-prefix"
                 (coerce '(#\Newline) 'string)
                 "this snapshot is not an earlier state of this store's history: "
                 "its committed records, compared record by record, are not this store's first records "
                 "(equal transaction counts or file sizes do not make them so); "
                 "restoring it would replace this history, not shorten it")))

; -----------------------------------------------------------------------------
; `store inspect MESSAGE-ID' (NNT-032, PRF-162): the operator's settling
; lookup.  The host opens the stopped store (the same exclusive open as
; `recover'), asks the store node whether it binds MESSAGE-ID
; (fn-store-sn-lookup-foundp, host/native/io.lisp fnn-bridge-lookup-found-p),
; and prints this report.  "accepted" means an article is stored under the
; Message-ID -- committed, whatever its visibility now (a cancel or a reclaim
; does not unbind it); "absent" means none is.  It does not compare the
; stored article with the client's copy: that is the re-send's question
; (D25), which a client that lost its posting right can no longer ask.

(defun fn-native-operator-result-inspect-msgid-octets (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "store")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :inspect)
           (stringp (fn-ncfg-second (fn-native-operator-result-arguments result))))
      (fn-record-string-octets
       (fn-ncfg-second (fn-native-operator-result-arguments result)))
    nil))

(defun fn-nop-octets-text (octets)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp octets) (fn-record-octets-string octets) ""))

; (EXIT-CODE VERDICT LINE).  FOUNDP is the store node's lookup; the line is
; the verdict word, the Message-ID and the sentence the verdict names.
(defun fn-nop-inspect-verdict (foundp)
  (declare (xargs :guard t))
  (if foundp :accepted :absent))

(defun fn-nop-inspect-line (verdict msgid)
  (declare (xargs :guard t))
  (if (equal verdict :accepted)
      (concatenate 'string "accepted " (if (stringp msgid) msgid "")
                   " an article is stored here under this Message-ID")
    (concatenate 'string "absent " (if (stringp msgid) msgid "")
                 " nothing is stored here under this Message-ID")))

(defun fn-native-operator-inspect-report (msgid-octets foundp)
  (declare (xargs :guard t))
  (let ((verdict (fn-nop-inspect-verdict foundp)))
    (list (if (equal verdict :accepted) 0 1)
          verdict
          (fn-nop-inspect-line verdict (fn-nop-octets-text msgid-octets)))))

(in-theory (disable fn-nop-inspect-line))

; KEYSTONE.  The report is the lookup: verdict :accepted and exit 0 exactly
; when the store binds the Message-ID, :absent and exit 1 exactly when it
; does not; the printed line is the verdict's.  The subject is the function
; host/native/io.lisp fnn-command-operator-inspect calls (through
; fn-native-operator-host-inspect-report) with the boolean
; fnn-bridge-lookup-found-p returned.
(defthm fn-native-operator-inspect-report-is-the-lookup
  (let ((report (fn-native-operator-inspect-report msgid-octets foundp)))
    (and (equal (car report) (if foundp 0 1))
         (equal (cadr report) (if foundp :accepted :absent))
         (equal (caddr report)
                (fn-nop-inspect-line (if foundp :accepted :absent)
                                     (fn-nop-octets-text msgid-octets))))))
