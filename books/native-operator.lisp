; fn: bounded native operator command grammar.
;
; This is a command-plan boundary, not a second storage or owner
; implementation.  It takes raw argv octet lists and the raw configuration
; bytes, asks books/native-config.lisp for the one normalized configuration,
; and returns a tagged plan.  A raw host may transport/print this result but
; may not supply defaults, select a command, or decide an outcome.

(in-package "ACL2")
(include-book "native-config")
(include-book "native-admin")
(include-book "native-auth-admin")

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

(defun fn-native-operator-exit-code (result)
  "The tagged result, not a raw host condition, owns the five CLI codes."
  (declare (xargs :guard t))
  (cond ((equal (fn-native-operator-result-status result) :accepted) 0)
        ((equal (fn-native-operator-result-status result) :refused) 1)
        ((equal (fn-native-operator-result-status result) :uncertain) 3)
        ((equal (fn-native-operator-result-status result) :fault) 4)
        ((equal (fn-native-operator-result-status result) :usage) 5)
        (t 4)))

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

; The store profile `init' writes (books/byte-store-frame.lisp
; `fn-bs-config-for-profile'): its transaction budget is fixed for the life of
; the store (books/store-budget.lisp).  Without `--profile' it is the
; 128-transaction :development profile; `--profile scale' is the
; 4096-transaction one.  Any other word is a usage error, never a default.
(defun fn-nop-init-profile-word (word)
  (declare (xargs :guard t))
  (cond ((equal word "development") :development)
        ((equal word "scale") :scale)
        (t nil)))

(defun fn-nop-parse-init (words config)
  (declare (xargs :guard t))
  (let* ((profilep (and (consp words) (equal (car words) "--profile")))
         (profile (if profilep
                      (fn-nop-init-profile-word (fn-ncfg-second words))
                    :development))
         (names (if profilep (fn-ncfg-rest (fn-ncfg-rest words)) words))
         (groups (fn-nop-parse-init-groups names nil)))
    (cond ((null profile)
           (fn-nop-usage :invalid-init-profile "init" config words))
          ((equal groups :bad)
           (fn-nop-usage :invalid-init-groups "init" config words))
          (t (fn-nop-result :accepted :plan "init" config
                            (list :init groups profile))))))

(defun fn-nop-help-subjectp (subject)
  (declare (xargs :guard t))
  (member-equal subject '("help" "init" "run" "post" "status" "recover" "group" "capacity" "peer" "bp-boundary" "policy" "principal")))

(defun fn-nop-help-text (subject)
  "Bounded operator help output, selected only from ACL2-normalized subjects."
  (declare (xargs :guard t))
  (cond ((equal subject "init")
         "usage: fn operator CONFIG init [--profile development|scale] GROUP [GROUP...]")
        ((equal subject "run") "usage: fn operator CONFIG run [--once]")
        ((equal subject "post")
         "usage: fn operator CONFIG post --message-id ID --payload PATH --group GROUP [--group GROUP]")
        ((equal subject "status") "usage: fn operator CONFIG status")
        ((equal subject "recover") "usage: fn operator CONFIG recover")
        ((equal subject "group") "usage: fn operator CONFIG group {create|retire} NAME")
        ((equal subject "capacity") "usage: fn operator CONFIG capacity DECIMAL-UINT32")
        ((equal subject "peer")
         "usage: fn operator CONFIG peer add NAME PATH HOST PORT INBOUND|- OUTBOUND|- SOURCE true|false | peer remove NAME | peer list")
        ((equal subject "bp-boundary")
         "usage: fn operator CONFIG bp-boundary add NAME PATH BP-EID PORT [INBOUND-GROUPS MAX-OCTETS MAX-INFLIGHT] (IPv4 loopback; the short form grants no inbound articles)")
        ((equal subject "policy")
         "usage: fn operator CONFIG policy set path-identity IDENTITY")
        ((equal subject "principal")
         "usage: fn operator CONFIG principal {list|set-password NAME [--principal HEX] [--posting|--no-posting]}")
        ((equal subject "help") "usage: fn operator CONFIG help [COMMAND]")
        (t "usage: fn operator CONFIG {help|init|run|post|status|recover|group|capacity|peer|bp-boundary|policy|principal}")))

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

(defun fn-nop-parse-administration (command argv config)
  "Delegate the exact bounded argv vector to the ACL2 durable-admin grammar."
  (declare (xargs :guard t))
  (let ((plan (fn-native-admin-plan argv)))
    (if (equal (fn-native-admin-result-status plan) :accepted)
        (fn-nop-result :accepted :plan command config (list plan argv))
      (fn-nop-usage (list :administration (fn-native-admin-result-reason plan))
                    command config argv))))

(defun fn-nop-parse-command (words config argv)
  "The accepted tag means a bounded command *plan* exists; no host effect ran."
  (declare (xargs :guard t))
  (if (not (consp words))
      (fn-nop-usage :missing-command nil config nil)
    (let ((command (car words)) (rest (cdr words)))
      (cond ((equal command "help")
             (if (or (null rest)
                     (and (equal (len rest) 1) (fn-nop-help-subjectp (car rest))))
                 (let ((subject (if (consp rest) (car rest) "help")))
                   (fn-nop-result :accepted :plan "help" config
                                  (list :help subject (fn-nop-help-text subject))))
               (fn-nop-usage :invalid-help "help" config rest)))
            ((equal command "run")
             (let ((arguments (fn-nop-parse-run rest nil)))
               (if (equal arguments :bad)
                   (fn-nop-usage :invalid-run-options "run" config rest)
                 (fn-nop-result :accepted :plan "run" config arguments))))
            ((equal command "init") (fn-nop-parse-init rest config))
            ((equal command "post") (fn-nop-parse-post rest config))
            ((equal command "status")
             (if (null rest)
                 (fn-nop-result :accepted :plan "status" config (list :status))
               (fn-nop-usage :unexpected-arguments "status" config rest)))
            ((equal command "recover")
             (if (null rest)
                 (fn-nop-result :accepted :plan "recover" config (list :recover))
               (fn-nop-usage :unexpected-arguments "recover" config rest)))
            ((or (equal command "group") (equal command "capacity")
                 (equal command "peer") (equal command "bp-boundary")
                 (equal command "policy"))
             (fn-nop-parse-administration command argv config))
            ((equal command "principal")
             (fn-nop-parse-principal argv config))
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
      (if (and (consp words) (equal (car words) "help"))
          (fn-nop-parse-command words nil argv-octets)
        (list :needs-config)))))

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
  "The store profile keyword an accepted init plan writes, else nil."
  (declare (xargs :guard t))
  (if (fn-native-operator-result-init-planp result)
      (let ((profile (fn-ncfg-second
                      (fn-ncfg-rest (fn-native-operator-result-arguments result)))))
        (if (member-equal profile '(:development :scale)) profile nil))
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
           (equal (fn-native-operator-result-command result) "policy"))))

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
          ((equal (fn-native-operator-result-command result) "recover") :recover)
          ((or (equal (fn-native-operator-result-command result) "group")
               (equal (fn-native-operator-result-command result) "capacity")
               (equal (fn-native-operator-result-command result) "peer")
               (equal (fn-native-operator-result-command result) "bp-boundary")
               (equal (fn-native-operator-result-command result) "policy")) :admin)
          ((equal (fn-native-operator-result-command result) "principal") :principal)
          (t :owner-required))))
