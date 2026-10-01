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
(include-book "native-config-paths")
(include-book "native-admin")
(include-book "accounts")
(include-book "native-auth-admin")
(include-book "native-retire")
(include-book "tls-self-signed")
(include-book "byte-store-frame")
(include-book "outcome-class")
; PKT-209: `control log' and `control evidence MESSAGE-ID'.
(include-book "control-evidence-grammar")

; PKT-867 (D27): no word count and no word length.  The kernel admits the
; argv (its ARG_MAX); the parse is one pass over it, and every field a word
; names is bounded where it is used (a group name by the record's name width,
; a path by the configuration's, a profile field by its codec width).  What
; reaches the running owner travels in one control frame, read under the
; profile's bound (books/native-control.lisp fn-nctrl-read-bound-for).
(defun fn-nop-argvp (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (and (consp (car argv))
           (fn-ncfg-ascii-octetsp (car argv))
           (fn-nop-argvp (cdr argv)))
    (null argv)))

(defun fn-nop-argument-texts-loop (argv acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp argv)
      (fn-nop-argument-texts-loop (cdr argv) (cons (fn-record-octets-string (car argv)) acc))
    (revappend acc nil)))

(defun fn-nop-argument-texts (argv)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp argv)
                  (cons (fn-record-octets-string (car argv))
                        (fn-nop-argument-texts (cdr argv)))
                nil)
       :exec (fn-nop-argument-texts-loop argv nil)))

(local
 (defthm fn-nop-argument-texts-loop-is-revappend
   (equal (fn-nop-argument-texts-loop argv acc)
          (revappend acc (fn-nop-argument-texts argv)))))

(verify-guards fn-nop-argument-texts)

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

;; PKT-657, PKT-575 (books/moderation-verbs.lisp): `moderation approve ID
;; --moderator LOGIN', `moderation reject ID --moderator LOGIN [--reason
;; TEXT]' and `article withdraw ID --reason TEXT' are one request to the
;; running owner (FNCT kind 21), planned as (:moderate OP LOGIN ID REASON),
;; each an octet list.  ID is a bracketed Message-ID; the owner decides the
;; rest (who moderates, what is held, what the configuration can carry).
(defun fn-nop-moderate-plan (command op id login reason config words)
  (declare (xargs :guard t))
  (if (and (fn-cevg-msgidp id)
           (or (equal op :withdraw) (fn-cfg-account-loginp login))
           (stringp reason))
      (fn-nop-result :accepted :plan command config
                     (list :moderate op
                           (if (stringp login) (fn-record-string-octets login) nil)
                           (fn-record-string-octets id)
                           (fn-record-string-octets reason)))
    (fn-nop-usage :moderation-verb command config words)))

(defun fn-nop-parse-moderate (command words config)
  (declare (xargs :guard t))
  (let ((verb (fn-ncfg-first words)) (rest (fn-ncfg-rest words)))
    (cond ((and (equal command "moderation") (equal verb "approve")
                (equal (len rest) 3) (equal (fn-ncfg-second rest) "--moderator"))
           (fn-nop-moderate-plan command :approve (fn-ncfg-first rest)
                                 (fn-ncfg-first (fn-ncfg-rest (fn-ncfg-rest rest)))
                                 "" config words))
          ((and (equal command "moderation") (equal verb "reject")
                (member-equal (len rest) '(3 5))
                (equal (fn-ncfg-second rest) "--moderator")
                (or (equal (len rest) 3)
                    (equal (fn-ncfg-first (nthcdr 3 (true-list-fix rest))) "--reason")))
           (fn-nop-moderate-plan command :reject (fn-ncfg-first rest)
                                 (fn-ncfg-first (fn-ncfg-rest (fn-ncfg-rest rest)))
                                 (if (equal (len rest) 5)
                                     (fn-ncfg-first (nthcdr 4 (true-list-fix rest)))
                                   "")
                                 config words))
          ((and (equal command "article") (equal verb "withdraw")
                (equal (len rest) 3) (equal (fn-ncfg-second rest) "--reason"))
           (fn-nop-moderate-plan command :withdraw (fn-ncfg-first rest) nil
                                 (fn-ncfg-first (fn-ncfg-rest (fn-ncfg-rest rest)))
                                 config words))
          (t (fn-nop-usage :moderation-verb command config words)))))

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

;  The store profile `init' writes and `store import' asks for
; (books/byte-store-frame.lisp, D27): the operator's fields.  A request is a
; base -- a preset word (`--profile development|scale|default' at init), the
; D27 defaults at init when none is named, the archive's profile at import
; -- and field overrides, one
; `--FIELD N' per field of `*fn-bs-profile-field-names*' (for example
; `--max-transactions 100000 --max-article-octets 20000').  N is a decimal
; natural of at most 20 digits (a frame natural, below 2^64); the relations
; between the fields are ACL2's (`fn-bs-profile-validp'), decided below at
; init and at the import.
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

; A flag's value: a decimal (every field of the format-10 profile).
(defun fn-nop-profile-flag-value (field text)
  (declare (xargs :guard t) (ignore field))
  (fn-nop-profile-decimal text))

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
  (cond ((equal name "small-community") (list :default (list (cons *fn-bs-pf-max-article-octets* 1048576) (cons *fn-bs-pf-max-groups-per-article* 8))))
        ((equal name "relay") (list :default (list (cons *fn-bs-pf-max-article-octets* 1048576) (cons *fn-bs-pf-max-groups-per-article* 16))))
        ((equal name "archive") (list :default (list (cons *fn-bs-pf-max-article-octets* 1048576) (cons *fn-bs-pf-max-groups-per-article* 16))))
        (t nil)))

; The groups a mission's `init' serves when the operator names none; only a
; small community has a default pair.
(defun fn-native-mission-default-groups (name)
  (declare (xargs :guard t))
  (if (equal name "small-community") '("local.general" "local.test") nil))

(defthm fn-native-mission-profiles-valid
  (implies (member-equal name *fn-ncfg-mission-names*)
           (fn-bs-profile-validp
            (fn-bs-profile-resolve (fn-native-mission-request name) nil)))
  :hints (("Goal" :in-theory (e/d ((:e fn-bs-profile-validp) (:e fn-bs-profile-resolve)
                                   (:e fn-native-mission-request))
                                  (fn-bs-profile-validp fn-bs-profile-resolve
                                   fn-native-mission-request)))))

;; PRF-171 (PKT-451 (C)): field 7, max-group-name-octets, governs the names
;; `init' creates, as it governs `group create' (books/store-capacity-config
;; `fn-cvec-native-admin-authorize').  Every name of NAMES is at most N octets.
(defun fn-nop-group-names-within (names n)
  (declare (xargs :guard t))
  (if (consp names)
      (and (<= (len (fn-record-string-octets (car names))) (nfix n))
           (fn-nop-group-names-within (cdr names) n))
    t))

; Row Q10b (PKT-596/690/691): `init''s sizing words, grammar words where
; the FN_INIT_* environment variables were.
; `--budget MB' names the memory budget, in MiB, init sizes the store for (a
; store made for the service's memory limit, or for another machine);
; `--largest' asks for the largest preset the budget holds instead of the
; conservative rung (books/heap-reservation.lisp fn-heap-init-decide decides
; both).  They stand among the profile flags, each at most once; MB is a
; decimal naming at least 1.  (BUDGET LARGEST REST): BUDGET the MiB or NIL,
; LARGEST T or NIL, REST the other words in order; :bad for a repeated word
; or a budget that is not a positive decimal.  Every other flag carries one
; value (the profile grammar), so a flag's value is never read as a word here.
(defun fn-nop-parse-init-sizing (words budget largest)
  (declare (xargs :guard t :measure (len words)))
  (cond ((atom words) (list budget largest nil))
        ((equal (car words) "--budget")
         (let ((mb (if (consp (cdr words)) (fn-nop-profile-decimal (cadr words)) nil)))
           (if (or budget (not (posp mb)))
               :bad
             (fn-nop-parse-init-sizing (cddr words) mb largest))))
        ((equal (car words) "--largest")
         (if largest :bad (fn-nop-parse-init-sizing (cdr words) budget t)))
        ((and (fn-nop-flag-wordp (car words)) (consp (cdr words)))
         (let ((r (fn-nop-parse-init-sizing (cddr words) budget largest)))
           (if (equal r :bad)
               :bad
             (list (car r) (cadr r)
                   (list* (car words) (cadr words) (caddr r))))))
        (t (list budget largest (true-list-fix words)))))

; The capacity fields (T, H and R): a request naming one over no named preset
; is sized from the development preset, not D27's defaults (row Q10b; the
; review's walk: `init --max-transactions 100000' took H = 1 TiB and asked a
; 10,493,234 MB reservation, PKT-582).  `--profile default' still names D27's.
(defun fn-nop-names-capacityp (overrides)
  (declare (xargs :guard t))
  (if (consp overrides)
      (or (and (consp (car overrides))
               (member-equal (caar overrides)
                             (list *fn-bs-pf-max-transactions*
                                   *fn-bs-pf-max-history-octets*
                                   *fn-bs-pf-max-record-octets*)))
          (fn-nop-names-capacityp (cdr overrides)))
    nil))

; The request `init' parses from its profile words: (REQUEST REST) or :bad,
; the base the preset named, else development when a capacity field is
; named, else D27's defaults (a capacity-free request heap-reservation sizes).
(defun fn-nop-parse-init-request (words)
  (declare (xargs :guard t))
  (let ((parsed (fn-nop-parse-profile-flags words nil nil nil)))
    (if (consp parsed)
        (let* ((request (car parsed))
               (base (fn-ncfg-first request))
               (overrides (fn-ncfg-second request)))
          (list (list (cond (base base)
                            ((fn-nop-names-capacityp overrides) :development)
                            (t :default))
                      overrides)
                (fn-ncfg-second parsed)))
      :bad)))

; The profile values REQUEST resolves to before its relations are judged:
; `fn-bs-profile-resolve''s own values (fn-nop-init-profile-values-resolve
; below), so the refusal can name the numbers the relation compared.
(defun fn-nop-init-profile-values (request)
  (declare (xargs :guard t))
  (if (not (fn-bs-profile-requestp request))
      :bad
    (let* ((base (fn-bs-config-for-profile (car request)))
           (values (if (null base) :bad
                     (fn-bs-profile-set-fields base (cadr request)))))
      (if (or (equal values :bad)
              (assoc-equal *fn-bs-pf-max-open-suffix* (cadr request)))
          values
        (fn-bs-profile-put
         *fn-bs-pf-max-open-suffix*
         (min (fn-bs-pf *fn-bs-pf-max-open-suffix* values)
              (fn-bs-pf *fn-bs-pf-max-transactions* values))
         values)))))

(defthm fn-nop-init-profile-values-resolve
  (equal (fn-bs-profile-resolve request nil)
         (let ((values (fn-nop-init-profile-values request)))
           (cond ((equal values :bad) (list :invalid :request))
                 ((fn-bs-profile-invalid-reason values)
                  (list :invalid (fn-bs-profile-invalid-reason values)))
                 (t values))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-profile-invalid-reason
                                      fn-bs-profile-set-fields fn-bs-profile-put
                                      fn-bs-pf fn-bs-config-for-profile))))

(in-theory (disable fn-nop-parse-init-sizing fn-nop-parse-init-request
                    fn-nop-init-profile-values fn-nop-names-capacityp))

(defun fn-nop-init-field-text (name i values)
  (declare (xargs :guard (and (stringp name) (natp i))))
  (concatenate 'string name " " (fn-acct-decimal-text (fn-bs-pf i values))))

(defthm fn-nop-init-field-text-stringp
  (stringp (fn-nop-init-field-text name i values))
  :rule-classes :type-prescription)

(defthm fn-nop-acct-decimal-text-stringp
  (stringp (fn-acct-decimal-text n))
  :rule-classes :type-prescription)

(in-theory (disable fn-nop-init-field-text))

; Row Q10b: a refused init profile names its numbers (the review's walk:
; `refused init max-history-octets-below-max-record-octets' named none) and,
; for the two relations an operator meets by raising one field, the value
; to pass.  WORDS are the refused init's words; NIL when they parse to no
; values (the usage line answers those).
(defun fn-nop-init-refusal-numbers (reason words)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (disable fn-nop-init-profile-values
                                          fn-nop-parse-init-request
                                          fn-nop-parse-init-sizing
                                          fn-bs-profile-invalid-reason
                                          fn-bs-pf fn-acct-decimal-text
                                          fn-record-encoded-octets-ceiling)))))
  (let* ((split (fn-nop-parse-init-sizing words nil nil))
         (parsed (if (consp split) (fn-nop-parse-init-request (caddr split)) :bad))
         (values (if (consp parsed) (fn-nop-init-profile-values (car parsed)) :bad)))
    (if (or (not (consp values))
            (not (fn-bs-profile-invalid-reason values)))
        nil
      (let ((tx (fn-nop-init-field-text "max-transactions" *fn-bs-pf-max-transactions* values))
            (h (fn-nop-init-field-text "max-history-octets" *fn-bs-pf-max-history-octets* values))
            (r (fn-nop-init-field-text "max-record-octets" *fn-bs-pf-max-record-octets* values))
            (a (fn-nop-init-field-text "max-article-octets" *fn-bs-pf-max-article-octets* values))
            (g (fn-nop-init-field-text "max-groups-per-article" *fn-bs-pf-max-groups-per-article* values))
            (k (fn-nop-init-field-text "max-open-suffix" *fn-bs-pf-max-open-suffix* values)))
        (cond ((equal reason :max-history-octets-below-max-record-octets)
               (concatenate 'string "init: " h " is below " r
                            "; pass --max-history-octets "
                            (fn-acct-decimal-text (fn-bs-pf *fn-bs-pf-max-record-octets* values))
                            " or more, or a smaller --max-record-octets"))
              ((equal reason :max-record-octets-below-the-article-record)
               (let ((need (fn-acct-decimal-text
                            (fn-record-encoded-octets-ceiling
                             (nfix (fn-bs-pf *fn-bs-pf-max-article-octets* values))
                             (nfix (fn-bs-pf *fn-bs-pf-max-groups-per-article* values))))))
                 (concatenate 'string "init: " r " is below " need
                              ", the record of one article at " a " in " g
                              " groups; pass --max-record-octets " need
                              " (and --max-history-octets at least that), or a smaller --max-article-octets or --max-groups-per-article")))
              (t (concatenate 'string "init: the profile refused: " tx ", " h ", " r
                              ", " a ", " g ", " k)))))))

(defun fn-nop-parse-init-plain (words config)
  (declare (xargs :guard t))
  (let* ((split (fn-nop-parse-init-sizing words nil nil))
         (parsed (if (consp split) (fn-nop-parse-init-request (caddr split)) :bad))
         (request (if (consp parsed) (car parsed) nil))
         (names (if (consp parsed) (fn-ncfg-second parsed) nil))
         ; The profile init will write, resolved over no store, or
         ; (:invalid REASON); the frame itself is encoded at the store.
         (profile (if (consp parsed) (fn-bs-profile-resolve request nil) nil))
         (groups (fn-nop-parse-init-groups names nil)))
    (cond ((not (consp split))
           (fn-nop-usage :invalid-init-budget "init" config words))
          ((not (consp parsed))
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
          ; The profile's field 7, by name.
          ((not (fn-nop-group-names-within
                 groups (fn-bs-profile-max-group-name-octets profile)))
           (fn-nop-refused :max-group-name-octets "init" config words))
          (t (fn-nop-result :accepted :plan "init" config
                            (list :init groups request
                                  (list (car split) (if (cadr split) :largest nil))))))))

;  KEYSTONE (PRF-171).  An accepted `init' plan creates no group whose name is
; longer than the max-group-name-octets of the profile it will write.  Host:
; host/native/operator.lisp's init arm runs this plan
; (`fn-native-operator-plan').
(defthm fn-nop-init-plain-groups-are-within-the-profile
  (let ((result (fn-nop-parse-init-plain words config)))
    (implies (equal (fn-native-operator-result-status result) :accepted)
             (fn-nop-group-names-within
              (cadr (nth 4 result))
              (fn-bs-profile-max-group-name-octets
               (fn-bs-profile-resolve (caddr (nth 4 result)) nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nop-parse-init-plain fn-nop-result
                                   fn-nop-refused fn-nop-usage
                                   fn-native-operator-result-status)
                                  (fn-nop-group-names-within
                                   fn-bs-profile-max-group-name-octets
                                   fn-bs-profile-resolve
                                   fn-nop-parse-profile-flags
                                   fn-nop-parse-init-groups
                                   fn-nop-some-flag-wordp
                                   fn-native-admin-some-group-name-reservedp)))))

;; PKT-708 (decided by the coordinator 2026-09-27): a mission's node files its
;; readers' own cancels, so its `init' also serves control.cancel, the group
;; a cancel is filed in (books/control-classify.lisp; RFC 5537 s5.3).  It is
;; added after the groups named, once (a mission with no groups named and
;; none by default, relay or archive, is still the usage error it was).  A plain `init' serves exactly the
;; groups its operator names (fn-nop-parse-init-groups: no second owner of
;; that choice).
(defun fn-nop-with-cancel-group (words)
  (declare (xargs :guard t))
  (if (or (atom words) (member-equal "control.cancel" (true-list-fix words)))
      (true-list-fix words)
    (append (true-list-fix words) (list "control.cancel"))))

;  `init' under a configuration that names a mission (`[ops] mission'): the
; mission fixes the profile, so a profile word is a usage error, and with no
; group named a small community serves its default pair; either way it
; serves control.cancel too (PKT-708).
(defun fn-nop-parse-init (words config)
  (declare (xargs :guard t))
  (let ((mission (fn-native-config-ops-mission config)))
    (if (and mission (fn-native-mission-request mission))
        (let* ((split (fn-nop-parse-init-sizing words nil nil))
               (names (if (consp split) (caddr split) nil))
               (groups (fn-nop-parse-init-groups
                        (fn-nop-with-cancel-group
                         (if (consp names) names (fn-native-mission-default-groups mission)))
                        nil)))
          ; Row Q10b: `--budget MB' names the machine, not the profile, so a
          ; mission's init takes it; `--largest' and every profile word are
          ; the mission's to fix.
          (cond ((not (consp split))
                 (fn-nop-usage :invalid-init-budget "init" config words))
                ((or (cadr split) (fn-nop-some-flag-wordp names))
                 (fn-nop-usage :mission-fixes-profile "init" config words))
                ((equal groups :bad)
                 (fn-nop-usage :invalid-init-groups "init" config words))
                ((fn-native-admin-some-group-name-reservedp words)
                 (fn-nop-refused :reserved-group-name "init" config words))
                (t (fn-nop-result :accepted :plan "init" config
                                  (list :init groups
                                        (fn-native-mission-request mission)
                                        (list (car split) nil))))))
      (fn-nop-parse-init-plain words config))))

;; The groups the parse answers are the words, in order.
(local
 (defthm fn-nop-member-of-ncfg-reverse-aux-acc
   (implies (member-equal x acc)
            (member-equal x (fn-ncfg-reverse-aux xs acc)))
   :hints (("Goal" :induct (fn-ncfg-reverse-aux xs acc)))))

(local
 (defthm fn-nop-member-of-ncfg-reverse-aux-xs
   (implies (member-equal x xs)
            (member-equal x (fn-ncfg-reverse-aux xs acc)))
   :hints (("Goal" :induct (fn-ncfg-reverse-aux xs acc)))))

(local
 (defthm fn-nop-parse-init-groups-keeps-its-words
   (implies (and (or (member-equal x words) (member-equal x acc))
                 (not (equal (fn-nop-parse-init-groups words acc) :bad)))
            (member-equal x (fn-nop-parse-init-groups words acc)))))

(local
 (defthm fn-nop-with-cancel-group-has-it
   (implies (consp words)
            (member-equal "control.cancel" (fn-nop-with-cancel-group words)))))

(local
 (defthm fn-nop-with-cancel-group-of-an-atom
   (implies (atom words)
            (equal (fn-nop-with-cancel-group words) nil))))

(local (in-theory (disable fn-nop-with-cancel-group)))

(local
 (defthm fn-nop-parse-with-cancel-keeps-it
   (implies (not (equal (fn-nop-parse-init-groups (fn-nop-with-cancel-group w) nil)
                        :bad))
            (member-equal "control.cancel"
                          (fn-nop-parse-init-groups (fn-nop-with-cancel-group w) nil)))
   :hints (("Goal" :cases ((consp w))
            :in-theory (disable fn-nop-parse-init-groups-keeps-its-words
                                fn-nop-with-cancel-group-has-it)
            :use ((:instance fn-nop-parse-init-groups-keeps-its-words
                             (x "control.cancel")
                             (words (fn-nop-with-cancel-group w)) (acc nil))
                  (:instance fn-nop-with-cancel-group-has-it (words w)))))))

;; KEYSTONE (PKT-708).  An accepted `init' under a mission serves
;; control.cancel, so a reader's own cancel is filed there
;; (fn-pa-filing-plan) with no `group create' first.  Host: host/native/
;; operator.lisp's init arm runs this plan (`fn-native-operator-plan').
(defthm fn-nop-mission-init-serves-control-cancel
  (let ((result (fn-nop-parse-init words config)))
    (implies (and (fn-native-config-ops-mission config)
                  (fn-native-mission-request (fn-native-config-ops-mission config))
                  (equal (fn-native-operator-result-status result) :accepted))
             (member-equal "control.cancel" (cadr (nth 4 result)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nop-result fn-nop-refused fn-nop-usage
                                   fn-native-operator-result-status)
                                  (fn-native-mission-request
                                   fn-native-mission-default-groups
                                   fn-nop-some-flag-wordp
                                   fn-native-admin-some-group-name-reservedp)))))

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

; `store export DIR' and `store import DIR [--FIELD N ...]' (D34, fresh
; deploys; books/store-export.lisp): the archive of a store's committed
; records and profile, and a fresh store's init from it plus the replay of
; those records.  DIR is an absolute path within the path bound.  The import's
; flags are field overrides over the archive's profile (base :current; no
; --profile), resolved at the import by `fn-bs-profile-resolve', not here.
; `store compact': the offline compaction (host/native/checkpoint.lisp
; `fnn-command-compact': a state checkpoint with the log rotated, then the
; covered segments dropped).  It takes no argument.
; `store checkpoint': publish the exact-state checkpoint (P3,
; books/store-checkpoint-open.lisp).  It takes no argument.
; `store reclaim [--dry-run | --recorded]': content reclamation's durable
; step (D13, STO-017, books/store-log-reclaim.lisp).  What it removes is
; `fn-lgr-decide-stream' at the store, not here; `--dry-run' writes nothing;
; `--recorded' reclaims at the instant the configuration records
; (books/reclaim-instant.lisp) and records none.
; A Message-ID as a command word: "<", printable US-ASCII, ">" (RFC 3977
; section 3.6), within the store's Message-ID bound (fn-record-msgidp).
(defun fn-nop-msgid-wordp (word)
  (declare (xargs :guard t))
  (and (stringp word)
       (fn-record-msgidp word)
       (<= 3 (length word))
       (equal (char word 0) #\<)
       (equal (char word (1- (length word))) #\>)))

(defun fn-nop-archive-pathp (word)
  (declare (xargs :guard t))
  (and (stringp word)
       (< 1 (length word))
       (<= (length word) *fn-ncfg-max-path*)
       (equal (char word 0) #\/)))

(defun fn-nop-parse-store (words config)
  (declare (xargs :guard t))
  (cond ; Row S3b (lane operability-7): `store export --status', the running
        ; owner's export in flight or its last outcome
        ; (books/owner-export-request.lisp fn-oex-status-word).
        ((and (consp words) (equal (car words) "export")
              (consp (cdr words)) (equal (cadr words) "--status")
              (null (cddr words)))
         (fn-nop-result :accepted :plan "store" config (list :export-status)))
        ((and (consp words) (equal (car words) "export")
              (consp (cdr words)) (null (cddr words))
              (fn-nop-archive-pathp (cadr words)))
         (fn-nop-result :accepted :plan "store" config
                        (list :export (cadr words))))
        ; S7a: read-only blessing of an already captured snapshot.  This
        ; action opens DIR, not the configured store, and never requests a copy.
        ((and (consp words) (equal (car words) "bless-snapshot")
              (consp (cdr words)) (null (cddr words))
              (fn-nop-archive-pathp (cadr words)))
         (fn-nop-result :accepted :plan "store" config
                        (list :bless-snapshot (cadr words))))
        ((and (consp words) (equal (car words) "import")
              (consp (cdr words))
              (fn-nop-archive-pathp (cadr words)))
         (let ((parsed (fn-nop-parse-profile-flags (cddr words) :current t nil)))
           (if (or (not (consp parsed)) (fn-ncfg-second parsed))
               (fn-nop-usage :invalid-store-profile "store" config words)
             (fn-nop-result :accepted :plan "store" config
                            (list :import (cadr words) (car parsed))))))
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
        ; Row S3d (lane operability-5): `store inspect --group GROUP', the
        ; group's memberships, article numbers to Message-IDs
        ; (books/owner-inspect-group.lisp fn-oig-report), over the stopped
        ; store or the running owner's archive.  GROUP as typed
        ; (fn-cevg-groupp): the report looks it up.
        ((and (consp words) (equal (car words) "inspect")
              (consp (cdr words)) (equal (cadr words) "--group")
              (consp (cddr words)) (null (cdddr words))
              (fn-cevg-groupp (caddr words)))
         (fn-nop-result :accepted :plan "store" config
                        (list :inspect-group (caddr words))))
        ((and (consp words) (equal (car words) "checkpoint") (null (cdr words)))
         (fn-nop-result :accepted :plan "store" config (list :checkpoint)))
        ((and (consp words) (equal (car words) "reclaim") (null (cdr words)))
         (fn-nop-result :accepted :plan "store" config (list :reclaim)))
        ((and (consp words) (equal (car words) "reclaim")
              (equal (cdr words) '("--dry-run")))
         (fn-nop-result :accepted :plan "store" config (list :reclaim-dry-run)))
        ; `store reclaim --recorded': the reclaim at the instant the
        ; configuration records (books/reclaim-instant.lisp, PKT-857).
        ((and (consp words) (equal (car words) "reclaim")
              (equal (cdr words) '("--recorded")))
         (fn-nop-result :accepted :plan "store" config (list :reclaim-recorded)))
        ; PKT-579: record the filesystem the store is on now
        ; (books/store-mount-identity.lisp fn-smid-rebind-plan), keeping the
        ; store's durability policy (PKT-648) or setting it.
        ((and (consp words) (equal (car words) "rebind-filesystem")
              (null (cdr words)))
         (fn-nop-result :accepted :plan "store" config
                        (list :rebind-filesystem nil)))
        ((and (consp words) (equal (car words) "rebind-filesystem")
              (equal (cdr words) '("--storage-require-durable" "on")))
         (fn-nop-result :accepted :plan "store" config
                        (list :rebind-filesystem 1)))
        ((and (consp words) (equal (car words) "rebind-filesystem")
              (equal (cdr words) '("--storage-require-durable" "off")))
         (fn-nop-result :accepted :plan "store" config
                        (list :rebind-filesystem 0)))
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
  (member-equal subject '("help" "init" "run" "post" "show" "mission" "status" "health" "pins" "obligations" "recover" "store" "group" "capacity" "peer" "bp-boundary" "bp-route" "policy" "control" "principal" "keys" "tls" "retention" "account" "motd" "moderation" "article" "consumer" "carry" "retire")))

(defun fn-nop-help-text (subject)
  "Bounded operator help output, selected only from ACL2-normalized subjects."
  (declare (xargs :guard t))
  (cond ((equal subject "init")
         "usage: fn operator CONFIG init [--budget MB] [--largest] [--profile development|scale|default] [--max-transactions N] [--max-history-octets N] [--max-record-octets N] [--max-article-octets N] [--max-groups-per-article N] [--max-group-name-octets N] [--max-open-suffix N] [--max-consumers N] [--max-bp-rows N] [--max-config-generations N] [--max-credentials N] [--max-policy-members N] [--max-control-clients N] GROUP [GROUP...]; under [ops] mission: init [--budget MB] [GROUP...] only (the mission fixes the profile; raise max-transactions, max-history-octets or max-article-octets later with policy set, on the running node)")
        ((equal subject "run") "usage: fn operator CONFIG run [--once]")
        ((equal subject "show")
         "usage: fn operator CONFIG show [TABLE KEY] (the normalized configuration as fn.toml, or one key's value)")
        ((equal subject "mission")
         "usage: fn operator NODE/fn.toml mission small-community|relay|archive [--host H] [--port P] [--tls-port P] [--tls-name NAME ...] (writes a new fn.toml; then init; with --tls-port or --tls-name the image makes a self-signed certificate and its key in NODE/tls/ naming each NAME, a DNS name or an IP address, default the --host address, valid 365 days; with --tls-port the node also serves NNTP over TLS on that port, STARTTLS always)")
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
        ((equal subject "recover") "usage: fn operator CONFIG recover [--repair truncate SEGMENT:OFFSET] (the repair only as a log-damaged refusal names it: the damaged segment is kept under quarantine/, then the log is truncated before the damage)")
        ((equal subject "store")
         "usage: fn operator CONFIG store {export ARCHIVE-DIR | export --status | bless-snapshot SNAPSHOT-DIR | import ARCHIVE-DIR [--FIELD N ...] | compact | checkpoint | reclaim [--dry-run | --recorded] | inspect MESSAGE-ID | inspect --group GROUP | rebind-filesystem [--storage-require-durable on|off]} (import and rebind-filesystem offline, refused while an owner runs; export, compact, checkpoint, reclaim and inspect answer on the running owner too; rebind-filesystem records the filesystem the store is on now, after a deliberate move or a restore; import makes a new store: the configured store must not exist, and the archive's profile, with any field raised, is the new store's)")
        ((equal subject "group") "usage: fn operator CONFIG group {create|retire} NAME | group describe NAME [TEXT ...] (LIST NEWSGROUPS shows TEXT; no TEXT clears it) | group policy NAME y|n | group authority NAME HEX|ungoverned | group moderate NAME --moderators LOGIN[,LOGIN...] [--queue QUEUE] [--submission ADDRESS] | group moderate NAME --off | group subscribe-default [NAME ...] (LIST SUBSCRIPTIONS recommends the NAMEs in order; none clears it)")
        ((equal subject "motd")
         "usage: fn operator CONFIG motd {set LINE [LINE ...] | clear} (LIST MOTD shows one LINE per argument, each at most 256 octets)")
        ((equal subject "capacity") "usage: fn operator CONFIG capacity DECIMAL-UINT32")
        ((equal subject "retention")
         "usage: fn operator CONFIG retention set {keep-forever | released-by-all-holders | release-after DAYS} (D13: the content-retention rule; keep-forever is the default) | retention expire {GROUP | *} {clear | [keep DAYS] [default DAYS] [purge DAYS] [octets N]} (Q14: a group's expiry policy; an Expires: header is honoured between keep and purge; `store reclaim' applies it)")
        ((equal subject "moderation")
         "usage: fn operator CONFIG moderation {list GROUP | approve MESSAGE-ID --moderator LOGIN | reject MESSAGE-ID --moderator LOGIN [--reason TEXT]} (list: the posts held for moderated GROUP in its queue, held, approved or rejected, from the running owner or offline from the store; approve posts the held article with Approved: LOGIN, reject withdraws its envelope; both need the running owner and a LOGIN that moderates the group)")
        ((equal subject "article")
         "usage: fn operator CONFIG article withdraw MESSAGE-ID --reason TEXT (withdraws the stored article under this node's own authority: a configuration record, then a cancel the node injects; needs the running owner)")
        ((equal subject "control")
         "usage: fn operator CONFIG control {grant PRINCIPAL-HEX cancel NAMESPACE | revoke PRINCIPAL-HEX cancel NAMESPACE | list | log | evidence MESSAGE-ID} (NAMESPACE is a group name or one ending in .*; spec peering 8; log lists the withdrawal records, evidence shows one article's decision context)")
        ((equal subject "peer")
         "usage: fn operator CONFIG peer set NAME [--host HOST] [--port PORT] [--take GROUPS|-] [--send GROUPS|-] [--streaming true|false] [--tls clear|starttls|implicit] [--server-name NAME|-] [--anchor PEM|-] [--login FILE|-] [--allow-clear true|false] [--principal HEX | --source-address IPV4] (changes the named fields of a peer, live; every other field and the pull, carries and budget settings stay) | peer login NAME LOGIN FILE (asks the password your friend gave you twice, writes FILE for NAME and sets it as NAME's login) | peer add NAME PATH HOST PORT INBOUND|- OUTBOUND|- source-address|principal VALUE [PROFILE ALLOW-CLEAR] STREAMING [starttls|implicit SERVER-NAME ANCHOR-PEM] | peer remove NAME | peer list | peer pull NAME SECONDS | peer catch-up NAME SECONDS | peer feed NAME pause|resume | peer budget NAME OCTETS COUNT | peer keygen KEYDIR | peer genesis KEYDIR | peer invite NAME GROUPS HOST PORT PATH KEYDIR OUT MY-HOST|- MY-PORT|- | peer accept FILE KEYDIR PATH REACHABLE|- OUT | peer confirm ACCEPTANCE INVITATION (KEYDIR, FILE and OUT absolute; peer add, set, remove, pull and feed apply to the running node; keygen makes a new KEYDIR with both key pairs and runs genesis; spec peering 9)")
        ((equal subject "bp-boundary")
         "usage: fn operator CONFIG bp-boundary add NAME PATH BP-EID PORT [INBOUND-GROUPS MAX-OCTETS MAX-INFLIGHT] [carries SOURCE-EID ...] (IPv4 loopback; the short form grants no inbound articles; carries lists the source EIDs this neighbour may relay, each judged under its own enrollment here)")
        ((equal subject "bp-route")
         "usage: fn operator CONFIG bp-route {add PATTERN BOUNDARY [PRIORITY] | remove PATTERN BOUNDARY} (PATTERN is a BP EID, or one ending in * for every EID with that prefix; the next hop of held transit, spec bp-node-machine 4.7)")
        ((equal subject "policy")
         "usage: fn operator CONFIG policy set KEY VALUE, KEY one of: path-identity IDENTITY | posting-policy bound-logins|open | complaints-to ADDR | anonymous none|open | exposure-connections N | exposure-per-address N | exposure-steps-per-second N | exposure-idle-seconds N | exposure-first-seconds N | exposure-auth-failures N | exposure-posts-per-minute N | exposure-trusted CIDR[,CIDR...]|none | relay-date-skew SECONDS | refused-offer-capacity N | relay-require-path 0|1 | log-batch-records N | log-batch-octets N | barrier-deadline-ms N | barrier-stall-ms N | clock-event-ms N | compress-min-octets N | disk-reserve-octets N | max-transactions N | max-history-octets N | max-article-octets N (each applies to a running node at once, the three store limits as their answer says: now, at the next start, or refused by name)")
        ((equal subject "principal")
         "usage: fn operator CONFIG principal {list | set-password NAME [--principal HEX] [--posting|--no-posting] | delete NAME | bind NAME HEX | unbind NAME} (the same logins as account set-password and account delete; set-password reads the password twice from the terminal or two lines of stdin; its last word says when it applies: applied (the running node took it), effective-at-next-start (no node running) or restart-required (fn.toml names no [control] path); bind and unbind apply to a running node at once)")
        ((equal subject "consumer")
         "usage: fn operator CONFIG consumer {bind NAME --account LOGIN | unbind NAME | show} (bind confines local consumer NAME to the groups LOGIN may read: its poll and ack then need LOGIN's password and serve only the events of a group LOGIN's access rule admits; unbind returns it to the operator's unrestricted consumer; show is the account list report; apply to a running node at once; spec consumer-progress Bound consumers)")
        ((equal subject "account")
         "usage: fn operator CONFIG account {invite [--expires SECONDS] | list | set-password LOGIN [--principal HEX] [--posting|--no-posting] | access {LOGIN|--anonymous} --read WILDMAT --post WILDMAT | access show | delete LOGIN} (invite prints one code, once, for a friend's XREDEEM; the node keeps only its digest; SECONDS defaults to 604800; list shows logins and principals, never codes, digests or verifiers, each access rule, and a code's expiry as a UTC time; set-password asks the password twice and writes LOGIN into auth.toml, which a redeemed account's own password then yields to; access sets the groups a login sees and may post to; delete removes a login auth.toml holds, else ends LOGIN's redeemed account: new logins as LOGIN are refused, its posts stay, and a redeemed login is never given out again; refused while a signing binding, a moderator role or a consumer binding names LOGIN; set-password and delete apply to a running node at once; spec nntp Invitation-code accounts, Group access)")
        ((equal subject "keys")
         "usage: fn operator CONFIG keys redecide MSGID (re-decide a stored key statement under the grants in force now; the running owner decides it over the control socket; refused when MSGID is no stored key statement or its change is already made; spec peering 7.4)")
        ((equal subject "tls")
         "usage: fn operator CONFIG tls reload | tls self-signed NAME [NAME ...] [--days N] (self-signed: the image makes a P-256 key and a certificate naming each NAME, a DNS name or an IP address, the first its subject, valid from an hour ago for N days, default 365, and writes them at tls_cert and tls_key; refused when either file exists; then run, or tls reload on a running node. reload: the running owner re-reads its tls_cert and tls_key and serves them to new connections; sessions already open keep theirs; refused by name, the old certificate still served, when the files do not load, the key does not match, the certificate is not valid now, or it drops a name the served one has)")
        ((equal subject "carry")
         "usage: fn operator CONFIG carry JOURNAL {list | inspect WORK | pause WORK|* | resume WORK|* | drop WORK [--abandon] REASON...} (the BP carry obligations in the FNWF workflow journal at the absolute path JOURNAL: list and inspect print each work's message, peer, status, Store pin, hold and last attempt; pause stops the requests for WORK (* every work) until resume; drop stops carrying WORK for REASON, final; the Store pin stays until the receipt releases it, or, with --abandon, the operator waives the obligation: the waiver (your uid, REASON) is durable and the Store pin is released now, refused unless the pin is held; the store must not be served)")
        ((equal subject "retire")
         "usage: fn operator CONFIG retire [--drain SECONDS] (the running node refuses new connections, stops pulling, lets its feeds drain for at most SECONDS (0 without --drain; at most 86400), prints per peer what stays undelivered and the obligation ledger, takes a final checkpoint and stops; what stays is released only by carry drop WORK --abandon on the stopped store)")
        ((equal subject "help") "usage: fn operator CONFIG help [COMMAND]")
        (t "usage: fn operator CONFIG {help|init|run|post|show|mission|status|health|pins|obligations|recover|store|group|capacity|retention|peer|bp-boundary|bp-route|policy|control|principal|keys|tls|account|motd|consumer|carry|retire} (fn operator CONFIG help COMMAND for one command's words; fn --version for the release and its source revision)")))

;; PRF-097: the peering verbs (specs/peering.md section 9).  Their words are
;; values and absolute paths; what the documents say, and whether they are
;; accepted, is books/peer-invite.lisp's, asked by host/native/peer-invite.lisp.
(defconst *fn-nop-peering-arity*
  '(("keygen" . 1) ("genesis" . 1) ("invite" . 9) ("accept" . 5) ("confirm" . 2)
    ; Row S5: `peer login NAME LOGIN FILE' writes the FNAUTH1 file from two
    ; password entries (books/peer-set.lisp fn-pset-login-file) and sets it
    ; as the peer's login (`peer set NAME --login FILE').
    ("login" . 3)))

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
        ((equal verb "login") (fn-nop-absolute-pathp (nth 2 args)))
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

; PRF-212: `tls reload'.  Whether the owner takes the new files is the
; owner's (books/tls-reload.lisp fn-tlsr-decide, asked by
; host/native/tls-reload.lisp over the control socket).
; Row Q10a: a name list books/tls-self-signed.lisp refuses, by the word the
; operator reads (mission and tls self-signed alike).
(defun fn-nop-self-signed-refusal-word (reason)
  (declare (xargs :guard t))
  (if (equal reason :common-name-length) :tls-common-name-length :tls-name))

; Row Q10a: `tls self-signed NAME [NAME ...] [--days N]' (NAMES-REV newest
; first; DAYS NIL until given).
(defun fn-nop-self-signed-words (words names-rev days)
  (declare (xargs :guard t :measure (len words)))
  (cond ((atom words) (list (fn-ncfg-reverse names-rev) days))
        ((equal (car words) "--days")
         (if (and (consp (cdr words)) (null days) (fn-nop-profile-decimal (cadr words)))
             (fn-nop-self-signed-words (cddr words) names-rev
                                       (fn-nop-profile-decimal (cadr words)))
           :bad))
        ((stringp (car words))
         (fn-nop-self-signed-words (cdr words) (cons (car words) names-rev) days))
        (t :bad)))

(defun fn-nop-parse-tls (words config)
  (declare (xargs :guard t))
  (cond ((and (equal (fn-ncfg-first words) "reload")
              (null (fn-ncfg-rest words)))
         (fn-nop-result :accepted :plan "tls" config (list :tls "reload")))
        ((equal (fn-ncfg-first words) "self-signed")
         (let ((parsed (fn-nop-self-signed-words (fn-ncfg-rest words) nil nil)))
           (if (or (equal parsed :bad) (atom (fn-ncfg-first parsed)))
               (fn-nop-usage :invalid-tls-command "tls" config words)
             (let* ((names (fn-ncfg-first parsed))
                    (days (or (fn-ncfg-second parsed) *fn-ssc-default-days*))
                    (names-refusal (fn-ssc-names-refusal names)))
               (cond (names-refusal
                      (fn-nop-refused (fn-nop-self-signed-refusal-word names-refusal)
                                      "tls" config words))
                     ((not (and (stringp (fn-native-config-tls-cert config))
                                (stringp (fn-native-config-tls-key config))))
                      (fn-nop-refused :no-tls-files "tls" config words))
                     (t (fn-nop-result :accepted :plan "tls" config
                                       (list :tls-self-signed names days))))))))
        (t (fn-nop-usage :invalid-tls-command "tls" config words))))

; PKT-869: `carry JOURNAL {list | inspect WORK | pause WORK|* | resume WORK|*
; | drop WORK REASON...}' over the FNWF workflow journal at the absolute path
; JOURNAL, beside the configured store (books/bp-carry-control.lisp decides
; each record; host/native/bp-obligation.lisp executes).  A drop's REASON is
; its words joined by one space.  `drop WORK --abandon REASON...' plans the
; verb :abandon, the operator's waiver (books/bp-carry-waiver.lisp, PRF-950).
(defun fn-nop-chars-onto (cs acc)
  (declare (xargs :guard (and (character-listp cs) (character-listp acc))))
  (if (consp cs) (fn-nop-chars-onto (cdr cs) (cons (car cs) acc)) acc))

(defthm fn-nop-chars-onto-character-listp
  (implies (and (character-listp cs) (character-listp acc))
           (character-listp (fn-nop-chars-onto cs acc))))

(defun fn-nop-join-words-loop (words acc)
  ; ACC is the joined characters so far, reversed: one pass, no append.
  (declare (xargs :guard (character-listp acc)))
  (if (consp words)
      (fn-nop-join-words-loop
       (cdr words)
       (if (stringp (car words))
           (fn-nop-chars-onto (coerce (car words) 'list)
                              (if acc (cons #\Space acc) nil))
         acc))
    (coerce (fn-nop-chars-onto acc nil) 'string)))

(defun fn-nop-parse-carry (words config)
  (declare (xargs :guard t))
  (let ((journal (fn-ncfg-first words))
        (verb (fn-ncfg-second words))
        (more (fn-ncfg-rest (fn-ncfg-rest words))))
    (cond ((not (fn-nop-archive-pathp journal))
           (fn-nop-usage :invalid-carry-journal "carry" config words))
          ((and (equal verb "list") (null more))
           (fn-nop-result :accepted :plan "carry" config (list :carry journal :list nil nil)))
          ((and (equal verb "inspect") (consp more) (null (cdr more))
                (stringp (car more)))
           (fn-nop-result :accepted :plan "carry" config
                          (list :carry journal :inspect (car more) nil)))
          ((and (member-equal verb '("pause" "resume")) (consp more) (null (cdr more))
                (stringp (car more)))
           (fn-nop-result :accepted :plan "carry" config
                          (list :carry journal (if (equal verb "pause") :pause :resume)
                                (car more) nil)))
          ; PRF-950: `drop WORK --abandon REASON...', the operator's waiver.
          ((and (equal verb "drop") (consp more) (stringp (car more))
                (consp (cdr more)) (equal (cadr more) "--abandon")
                (consp (cddr more)) (true-listp more))
           (fn-nop-result :accepted :plan "carry" config
                          (list :carry journal :abandon (car more)
                                (fn-nop-join-words-loop (cddr more) nil))))
          ((and (equal verb "drop") (consp more) (stringp (car more))
                (consp (cdr more)) (true-listp more)
                (not (equal (cadr more) "--abandon")))
           (fn-nop-result :accepted :plan "carry" config
                          (list :carry journal :drop (car more)
                                (fn-nop-join-words-loop (cdr more) nil))))
          (t (fn-nop-usage :invalid-carry-command "carry" config words)))))

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
                           :verb-not-grantable
                           ; Row S10: `policy set' refused by name.
                           :unknown-policy-key :policy-value-not-a-number))
           (fn-nop-refused (list :administration (fn-native-admin-result-reason plan))
                           command config argv))
          (t (fn-nop-usage (list :administration (fn-native-admin-result-reason plan))
                           command config argv)))))

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
        (fn-nop-result :accepted :plan "principal" config
                       (list plan
                             ; PRF-388 (PKT-560): for `bind|unbind', the
                             ; `account bind|unbind' plan the host runs when
                             ; the credential file does not hold the login.
                             ; Row S6: for `delete', the `account delete'
                             ; plan, the same way.
                             (if (member-equal (fn-native-auth-admin-action-kind plan)
                                               '(:bind :delete))
                                 (fn-nop-parse-administration
                                  "account"
                                  (cons (fn-record-string-octets "account")
                                        (fn-ncfg-rest argv))
                                  config)
                               nil)))
      (fn-nop-usage (list :principal (fn-native-auth-admin-plan-reason plan))
                    "principal" config (fn-ncfg-rest argv)))))

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
        ;; PRF-222: `account access show' and `account access LOGIN|--anonymous
        ;; --read WILDMAT --post WILDMAT' (books/native-admin.lisp).
        ((equal (fn-ncfg-first words) "access")
         (fn-nop-parse-administration "account" argv config))
        ;; Row S6 (one account system): `account set-password LOGIN' and
        ;; `account delete LOGIN' are the credential file's plans
        ;; (books/native-auth-admin.lisp); a login the file does not hold
        ;; is deleted by public-node-2's `account delete' record
        ;; (books/native-admin.lisp), the plan's second argument.
        ((or (equal (fn-ncfg-first words) "set-password")
             (equal (fn-ncfg-first words) "delete"))
         (fn-nop-parse-principal argv config))
        ;; PKT-597: `account hash LOGIN' prints the posting-account value an
        ;; article posted under LOGIN carries (books/injection-info-policy.lisp
        ;; fn-ipp-account-hash): the host reads the node secret, ACL2
        ;; computes the value.  Nothing is written.
        ((and (equal (fn-ncfg-first words) "hash")
              (fn-ipp-login-wordp (fn-ncfg-second words))
              (null (fn-ncfg-rest (fn-ncfg-rest words))))
         (fn-nop-result :accepted :plan "account" config
                        (list :account-hash (fn-ncfg-second words))))
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
                   ; Row S3: on a stopped store `status' reads the checkpoint
                   ; header (books/owner-maintenance-request.lisp); `--replay'
                   ; asks for the report over the replayed log.
                   ((and (equal (fn-ncfg-first rest) "--replay")
                         (null (fn-ncfg-rest rest)))
                    (fn-nop-result :accepted :plan "status" config
                                   (list :status :replay)))
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
            ; Row S9: `retire [--drain SECONDS]' (books/native-retire.lisp
            ; decides the window; a value past its bound is refused by name).
            ((equal command "retire")
             (cond ((or (null rest)
                        (and (equal (fn-ncfg-first rest) "--drain")
                             (consp (cdr rest)) (null (cddr rest))))
                    (let ((plan (fn-nret-plan
                                 (if (null rest)
                                     0
                                   (let ((n (fn-nop-profile-decimal (fn-ncfg-second rest))))
                                     (if (natp n) n :not-a-number))))))
                      (if (equal (fn-ncfg-first plan) :accepted)
                          (fn-nop-result :accepted :plan "retire" config
                                         (list :retire (fn-ncfg-second plan)))
                        (fn-nop-refused (list :retire (fn-ncfg-second plan))
                                        "retire" config rest))))
                   (t (fn-nop-usage :unexpected-arguments "retire" config rest))))
            ((or (equal command "pins") (equal command "obligations"))
             (if (null rest)
                 (fn-nop-result :accepted :plan command config
                                (list (if (equal command "pins") :pins :obligations)))
               (fn-nop-usage :unexpected-arguments command config rest)))
            ((equal command "recover")
             ; Lane log-corruption: `recover --repair truncate SEGMENT:OFFSET',
             ; the operator's confirmation of the one repair a log-damaged
             ; refusal names (books/store-log-damage.lisp admits it only for
             ; exactly that damage).
             (cond ((null rest)
                    (fn-nop-result :accepted :plan "recover" config (list :recover)))
                   ((and (equal (fn-ncfg-first rest) "--repair")
                         (equal (fn-ncfg-second rest) "truncate")
                         (stringp (fn-ncfg-nth 2 rest))
                         (null (fn-ncfg-rest (fn-ncfg-rest (fn-ncfg-rest rest)))))
                    (fn-nop-result :accepted :plan "recover" config
                                   (list :recover (fn-ncfg-nth 2 rest))))
                   (t (fn-nop-usage :unexpected-arguments "recover" config rest))))
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
            ; PKT-209 (PRF-185): `control log' and `control evidence MSGID'
            ; are status reports (books/control-evidence-grammar.lisp), not
            ; administrative plans; every other `control' verb is.
            ((and (equal command "control")
                  (equal (fn-ncfg-first (fn-cevg-parse rest)) :kind))
             (fn-nop-result :accepted :plan "control" config
                            (list (fn-ncfg-second (fn-cevg-parse rest)))))
            ((and (equal command "control")
                  (equal (fn-ncfg-first (fn-cevg-parse rest)) :usage))
             (fn-nop-usage (list :control-report (fn-ncfg-second (fn-cevg-parse rest)))
                           "control" config rest))
            ; PKT-657, PKT-575: the owner's moderation and withdrawal verbs.
            ((and (equal command "moderation")
                  (member-equal (fn-ncfg-first rest) '("approve" "reject")))
             (fn-nop-parse-moderate command rest config))
            ((equal command "article") (fn-nop-parse-moderate command rest config))
            ; PKT-657: `moderation list GROUP' is a status report too.
            ((and (equal command "moderation")
                  (equal (fn-ncfg-first (fn-cevg-moderation-parse rest)) :kind))
             (fn-nop-result :accepted :plan "moderation" config
                            (list (fn-ncfg-second (fn-cevg-moderation-parse rest)))))
            ((equal command "moderation")
             (fn-nop-usage (list :moderation-report
                                 (fn-ncfg-second (fn-cevg-moderation-parse rest)))
                           "moderation" config rest))
            ((or (equal command "group") (equal command "capacity")
                 (equal command "peer") (equal command "bp-boundary")
                 (equal command "bp-route") (equal command "policy")
                 (equal command "control") (equal command "retention")
                 (equal command "motd") (equal command "consumer"))
             (fn-nop-parse-administration command argv config))
            ((equal command "principal")
             (fn-nop-parse-principal argv config))
            ((equal command "keys") (fn-nop-parse-keys rest config))
            ((equal command "carry") (fn-nop-parse-carry rest config))
            ((equal command "tls") (fn-nop-parse-tls rest config))
            ((equal command "account") (fn-nop-parse-account rest argv config))
            (t (fn-nop-usage :unsupported-command command config rest))))))

(defun fn-native-operator-command-preflight (argv-octets)
  "Parse only the config-free command boundary.

The distinguished `(:needs-config)' result directs the raw boundary to read a
configuration file.  Every other result is the ordinary tagged operator result,
so malformed argv and help syntax remain ACL2-owned before any host file I/O."
  (declare (xargs :guard t))
  (if (or (not (true-listp argv-octets))
          (not (fn-nop-argvp argv-octets)))
      (fn-nop-usage :argv-malformed nil nil nil)
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
; Row Q10a: `--tls-port P' and each `--tls-name NAME' (NAMES-REV, newest
; first).
(defun fn-nop-mission-options (words host port tls-port names-rev)
  (declare (xargs :guard t :measure (len words)))
  (cond ((atom words) (list host port tls-port (fn-ncfg-reverse names-rev)))
        ((and (equal (car words) "--host") (consp (cdr words)) (stringp (cadr words)))
         (fn-nop-mission-options (cddr words) (cadr words) port tls-port names-rev))
        ((and (equal (car words) "--port") (consp (cdr words))
              (fn-nop-profile-decimal (cadr words)))
         (fn-nop-mission-options (cddr words) host (fn-nop-profile-decimal (cadr words))
                                 tls-port names-rev))
        ((and (equal (car words) "--tls-port") (consp (cdr words))
              (fn-nop-profile-decimal (cadr words)))
         (fn-nop-mission-options (cddr words) host port (fn-nop-profile-decimal (cadr words))
                                 names-rev))
        ((and (equal (car words) "--tls-name") (consp (cdr words)) (stringp (cadr words)))
         (fn-nop-mission-options (cddr words) host port tls-port
                                 (cons (cadr words) names-rev)))
        (t :bad)))

; The request for the pair a mission makes: NIL without --tls-port or
; --tls-name (a mission without TLS words makes no pair; `tls self-signed'
; makes one later), else
; (NAMES DAYS CERT-PATH KEY-PATH), the paths the absolute octets of the files
; the configuration names (tls/cert.pem and tls/key.pem beside fn.toml).
(defun fn-nop-mission-self-signed (node host tls-port names)
  (declare (xargs :guard t))
  (and (or tls-port (consp names))
       (list (if (consp names) names (list host))
             *fn-ssc-default-days*
             (fn-record-string-octets (fn-ncfg-join-path node "/tls/cert.pem"))
             (fn-record-string-octets (fn-ncfg-join-path node "/tls/key.pem")))))


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
            (not (fn-nop-argvp argv-octets))
            (not (equal (fn-ncfg-first words) "mission"))
            (not (consp (fn-ncfg-rest words)))
            (not (fn-ncfg-printablep path-octets))
            (not (true-listp path-octets)))
        (fn-nop-usage :invalid-mission "mission" nil nil)
      (let ((options (fn-nop-mission-options (fn-ncfg-rest (fn-ncfg-rest words))
                                             *fn-ncfg-default-listener-host*
                                             *fn-ncfg-default-listener-port*
                                             nil nil))
            (node (fn-record-octets-string
                   (fn-ncfg-reverse (fn-nop-dirname-rev (fn-ncfg-reverse path-octets)))))
            (name (fn-ncfg-second words)))
        (if (equal options :bad)
            (fn-nop-usage :invalid-mission-options "mission" nil (fn-ncfg-rest words))
          (let* ((self-signed (fn-nop-mission-self-signed node (fn-ncfg-first options)
                                                          (fn-ncfg-third options)
                                                          (fn-ncfg-nth 3 options)))
                 (names-refusal (and self-signed
                                     (fn-ssc-names-refusal (fn-ncfg-first self-signed))))
                 (plan (fn-native-mission-plan name node (fn-ncfg-first options)
                                               (fn-ncfg-second options)
                                               (fn-ncfg-third options))))
            (cond ((not (equal (fn-ncfg-first plan) :accepted))
                   (fn-nop-refused (fn-ncfg-second plan) "mission" nil (fn-ncfg-rest words)))
                  (names-refusal
                   (fn-nop-refused (fn-nop-self-signed-refusal-word names-refusal)
                                   "mission" nil (fn-ncfg-rest words)))
                  (t (fn-nop-result :accepted :plan "mission" nil
                                    (list :mission name
                                          (fn-ncfg-third plan)
                                          (fn-native-mission-directories node)
                                          self-signed))))))))))

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

;; Row S8: the operator entry the host calls.  CWD is the host's working
;; directory and CONFIG-PATH the fn.toml path as given (octet lists); the
;; configuration's relative paths are resolved under fn.toml's directory
;; (books/native-config-paths.lisp, KEYSTONE
;; fn-ncpath-config-octets-load-the-resolved-configuration) before the
;; command is planned, and a resolved path past the path bound is refused by
;; name.
(defun fn-native-operator-run-at (cwd config-path config-octets argv-octets)
  (declare (xargs :guard t))
  (let ((octets (fn-ncpath-config-octets config-octets
                                         (fn-ncpath-base cwd config-path))))
    (if (equal octets :bad)
        (fn-nop-usage (list :configuration :resolved-path-bounds) nil nil nil)
      (fn-native-operator-run octets argv-octets))))

(defun fn-native-operator-result-run-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "run")))

(defun fn-native-operator-result-run-cold-resources (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      (fn-native-config-cold-resources (fn-native-operator-result-config result))
    nil))

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

; PRF-211 (NNT-043): the owner a run installs is bounded one past the width
; of a limit row, so the connection capacity is the `exposure-connections'
; row the operator sets (books/public-exposure.lisp
; fn-exp-open-refuses-exactly-at-the-capacity), not fn.toml's fixed 32
; (fn-native-config-owner-max-connections, which no run reads now).
(defun fn-native-operator-result-run-max-connections (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-run-planp result)
      *fn-exp-owner-connection-bound*
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

; The moderation request (books/moderation-verbs.lisp): OP LOGIN ID REASON,
; and the control socket it goes to.
(defun fn-native-operator-result-moderate-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (member-equal (fn-native-operator-result-command result)
                     '("moderation" "article"))
       (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
              :moderate)
       t))

(defun fn-native-operator-result-moderate-request (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-moderate-planp result)
      (fn-ncfg-rest (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-moderate-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-moderate-planp result)
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

(defun fn-native-operator-post-group-octets-loop (groups acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp groups)
      (fn-native-operator-post-group-octets-loop (cdr groups) (cons (fn-record-string-octets (car groups)) acc))
    (revappend acc nil)))

(defun fn-native-operator-post-group-octets (groups)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp groups)
                  (cons (fn-record-string-octets (car groups))
                        (fn-native-operator-post-group-octets (cdr groups)))
                nil)
       :exec (fn-native-operator-post-group-octets-loop groups nil)))

(local
 (defthm fn-native-operator-post-group-octets-loop-is-revappend
   (equal (fn-native-operator-post-group-octets-loop groups acc)
          (revappend acc (fn-native-operator-post-group-octets groups)))))

(verify-guards fn-native-operator-post-group-octets)

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

(defun fn-native-operator-result-config-mission (result)
  "The mission an accepted plan's configuration names (the durability policy
of the store `init' or `store import' makes, books/store-mount-identity.lisp
fn-smid-init-policy), else nil."
  (declare (xargs :guard t))
  (if (equal (fn-native-operator-result-status result) :accepted)
      (fn-native-config-ops-mission (fn-native-operator-result-config result))
    nil))

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

; Row Q10b: the sizing words an accepted init plan carries, for the host to
; hand fn-heap-init-decide: the budget `--budget MB' named (MiB) or NIL, and
; :largest for `--largest' or NIL (conservative).
(defun fn-native-operator-result-init-budget (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-init-planp result)
      (let ((mb (fn-ncfg-first (fn-ncfg-nth 3 (fn-native-operator-result-arguments result)))))
        (if (posp mb) mb nil))
    nil))

(defun fn-native-operator-result-init-sizing (result)
  (declare (xargs :guard t))
  (if (and (fn-native-operator-result-init-planp result)
           (equal (fn-ncfg-second (fn-ncfg-nth 3 (fn-native-operator-result-arguments result)))
                  :largest))
      :largest
    nil))

(defun fn-nop-store-plan-word (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "store"))
      (fn-ncfg-first (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-archive-path-octets (result)
  "The archive directory an accepted `store export' or `store import' plan
names, as octets, else nil."
  (declare (xargs :guard t))
  (if (and (member-equal (fn-nop-store-plan-word result) '(:export :import :bless-snapshot))
           (stringp (fn-ncfg-second (fn-native-operator-result-arguments result))))
      (fn-record-string-octets
       (fn-ncfg-second (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-result-rebind-policy (result)
  "The durability policy an accepted `store rebind-filesystem' plan sets (1
or 0), or nil to keep the store's."
  (declare (xargs :guard t))
  (if (and (equal (fn-nop-store-plan-word result) :rebind-filesystem)
           (member-equal (fn-ncfg-second (fn-native-operator-result-arguments result))
                         '(0 1)))
      (fn-ncfg-second (fn-native-operator-result-arguments result))
    nil))

(defun fn-native-operator-result-import-request (result)
  "The field overrides an accepted `store import' plan names over the
archive's profile (a request with base :current), else nil."
  (declare (xargs :guard t))
  (if (equal (fn-nop-store-plan-word result) :import)
      (let ((request (fn-ncfg-first
                      (fn-ncfg-rest
                       (fn-ncfg-rest (fn-native-operator-result-arguments result))))))
        (if (fn-bs-profile-requestp request) request nil))
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
           (equal (fn-native-operator-result-command result) "motd")
           (equal (fn-native-operator-result-command result) "consumer")
           (and (equal (fn-native-operator-result-command result) "account")
                (not (member-equal (fn-ncfg-first
                                    (fn-native-operator-result-arguments result))
                                   '(:account-invite :account-hash)))))))

;; PKT-597: the login of an accepted `account hash' plan, or nil.
(defun fn-native-operator-result-account-hash-login (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "account")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :account-hash))
      (fn-ncfg-second (fn-native-operator-result-arguments result))
    nil))

;; PKT-786: the credential file an accepted `account hash' plan reads (the
;; configuration's auth path), or nil.
(defun fn-native-operator-result-account-hash-auth-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-account-hash-login result)
      (fn-record-string-octets
       (fn-native-config-auth-path (fn-native-operator-result-config result)))
    nil))

;; PKT-786: the account a login posts under.  The served path keys the
;; posting-account value by the session's subject (books/served.lisp
;; fn-served-account): the principal of the credential the connection's
;; pinned table finds for the login, the credential file's rows first, then
;; the redeemed accounts' (books/nntp-auth.lisp fn-auth-config-with-accounts).
;; The operator reads the credential file; a login the file does not hold is
;; an invitation-code account, live or deleted (a deleted login is never given
;; out again), whose principal is its local principal (fn-auth-account-cred).
(defun fn-nop-login-principal (login creds)
  (declare (xargs :guard t))
  (let ((cred (fn-auth-find-cred login creds)))
    (if cred (fn-auth-cred-principal cred) (fn-acct-local-principal login))))

;; The credential file's rows as the owner's bounded load reads them (the
;; policy flags do not change the rows: fn-nop-auth-file-creds-of-any-policy).
(defun fn-nop-auth-file-creds (octets presentp max-credentials)
  (declare (xargs :guard t))
  (let ((loaded (fn-native-auth-load octets presentp nil nil nil max-credentials)))
    (if (equal (fn-native-auth-result-status loaded) :accepted)
        (fn-auth-config-creds (fn-native-auth-result-config loaded))
      :refused)))

;; The host-called subject of `account hash LOGIN' (host/native-operator-
;; host.lisp fn-native-operator-host-account-hash-text): the posting-account
;; value of LOGIN's account under SECRET, or nil when the credential file is
;; one the owner's load refuses.
(defun fn-nop-account-hash (secret login octets presentp max-credentials)
  (declare (xargs :guard t))
  (let ((creds (fn-nop-auth-file-creds octets presentp max-credentials)))
    (if (equal creds :refused)
        nil
      (fn-ipp-account-hash secret
                           (fn-nop-login-principal (fn-ipp-octets login) creds)))))

(local (defthm fn-nop-auth-configp-of-make-config
  (implies (and (booleanp a) (booleanp b) (booleanp c))
           (equal (fn-auth-configp (fn-auth-make-config a b c creds))
                  (fn-auth-cred-listp creds)))
  :hints (("Goal" :in-theory (e/d (fn-auth-configp) (fn-auth-cred-listp))))))

(defthm fn-nop-auth-file-creds-of-any-policy
  (implies (equal (fn-native-auth-result-status
                   (fn-native-auth-load octets presentp requiredp protected-onlyp
                                        tls-availablep max-credentials))
                  :accepted)
           (equal (fn-nop-auth-file-creds octets presentp max-credentials)
                  (fn-auth-config-creds
                   (fn-native-auth-result-config
                    (fn-native-auth-load octets presentp requiredp protected-onlyp
                                         tls-availablep max-credentials)))))
  :hints (("Goal" :in-theory (e/d (fn-native-auth-load) (fn-auth-configp fn-auth-make-config fn-native-auth-parse-lines fn-ncfg-lines))))
  :rule-classes nil)

(local (defthm fn-nop-find-cred-of-append
  (implies (fn-auth-cred-listp a)
           (equal (fn-auth-find-cred name (append a b))
                  (or (fn-auth-find-cred name a) (fn-auth-find-cred name b))))
  :hints (("Goal" :in-theory (e/d (fn-auth-find-cred fn-auth-cred-listp) (fn-auth-credp))))))

(local (defthm fn-nop-account-cred-principal-is-its-names
  (equal (fn-auth-cred-principal (fn-auth-account-cred row))
         (fn-acct-local-principal (fn-auth-cred-name (fn-auth-account-cred row))))
  :hints (("Goal" :in-theory (e/d (fn-auth-account-cred) (fn-acct-local-principal))))))
(local (defthm fn-nop-find-cred-of-account-creds
  (implies (fn-auth-find-cred name (fn-auth-account-creds rows))
           (equal (fn-auth-cred-principal
                   (fn-auth-find-cred name (fn-auth-account-creds rows)))
                  (fn-acct-local-principal name)))
  :hints (("Goal" :in-theory (e/d (fn-auth-find-cred fn-auth-account-creds)
                                  (fn-auth-credp fn-auth-account-cred fn-acct-local-principal))))))

(local (defthm fn-nop-configp-has-a-cred-list
  (implies (fn-auth-configp x) (fn-auth-cred-listp (fn-auth-config-creds x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-configp) (fn-auth-cred-listp))))))
(defthm fn-nop-login-principal-is-the-served-tables
  (implies (and (fn-auth-configp acfg)
                (fn-auth-find-cred login (fn-auth-config-creds
                                          (fn-auth-config-with-accounts acfg v))))
           (equal (fn-nop-login-principal login (fn-auth-config-creds acfg))
                  (fn-auth-cred-principal
                   (fn-auth-find-cred login (fn-auth-config-creds
                                             (fn-auth-config-with-accounts acfg v))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-config-with-accounts)
                                  (fn-auth-configp fn-auth-find-cred fn-auth-account-creds
                                   fn-acct-local-principal))))
  :rule-classes nil)

(local (defthm fn-nop-a-cred-list-is-not-refused
  (implies (fn-auth-cred-listp x) (not (equal x :refused)))
  :rule-classes :forward-chaining))

; KEYSTONE (PKT-786): the value `account hash LOGIN' prints is the value an
; article posted by LOGIN carries.  Whatever policy flags the owner loaded the
; credential file under, when the connection's pinned table (the file's rows,
; then the redeemed accounts' of any configuration value V) finds LOGIN, the
; operator's value is the posting-account value of that credential's
; principal: the session subject books/served.lisp fn-served-account records
; as the submission's account, which books/injection-info-params.lisp
; fn-ipp-injected-octets hashes.  Teeth: tests/acl2/injection-info-params-tests.lisp.
(defthm fn-nop-account-hash-is-the-served-account-value
  (implies (and (equal (fn-native-auth-result-status
                        (fn-native-auth-load octets presentp requiredp protected-onlyp
                                             tls-availablep max-credentials))
                       :accepted)
                (equal acfg (fn-native-auth-result-config
                             (fn-native-auth-load octets presentp requiredp protected-onlyp
                                                  tls-availablep max-credentials)))
                (fn-auth-find-cred (fn-ipp-octets login)
                                   (fn-auth-config-creds
                                    (fn-auth-config-with-accounts acfg v))))
           (equal (fn-nop-account-hash secret login octets presentp max-credentials)
                  (fn-pa-account-value
                   secret
                   (fn-ipp-octets
                    (fn-auth-cred-principal
                     (fn-auth-find-cred (fn-ipp-octets login)
                                        (fn-auth-config-creds
                                         (fn-auth-config-with-accounts acfg v))))))))
  :hints (("Goal" :use ((:instance fn-nop-auth-file-creds-of-any-policy)
                        (:instance fn-native-auth-load-accepted-is-config
                                   (protected protected-onlyp) (tls tls-availablep))
                        (:instance fn-nop-login-principal-is-the-served-tables
                                   (login (fn-ipp-octets login))))
           :in-theory (e/d (fn-ipp-account-hash)
                           (fn-native-auth-load-accepted-is-config
                            fn-nop-auth-file-creds fn-nop-login-principal
                            fn-native-auth-load fn-auth-configp
                            fn-auth-config-with-accounts fn-auth-find-cred
                            fn-pa-account-value fn-ipp-octets))))
  :rule-classes nil)

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

; PRF-388 (PKT-560): the operator result the host dispatches when the
; credential file answered that it does not hold the login of `principal
; bind|unbind' (books/native-auth-admin.lisp fn-native-auth-admin-bind's
; :account): the `account bind|unbind' plan of the same words.
(defun fn-native-operator-result-principal-account-result (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-principal-planp result)
      (fn-ncfg-second (fn-native-operator-result-arguments result))
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

; The control socket the principal verb asks a running owner to republish
; the credential file's login bindings through (PKT-221, request 14).
(defun fn-native-operator-result-principal-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-principal-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
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

; PKT-869: the accepted `carry' plan's fields: (JOURNAL VERB WORK REASON).
(defun fn-native-operator-result-carry-fields (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "carry")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result)) :carry))
      (fn-ncfg-rest (fn-native-operator-result-arguments result))
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

(defun fn-native-operator-result-tls-control-path-octets (result)
  "The control socket an accepted `tls reload' asks, as octets."
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "tls")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :tls))
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
          ((equal (fn-native-operator-result-command result) "retire") :retire)
          ((and (member-equal (fn-native-operator-result-command result)
                              '("control" "moderation"))
                (fn-cevg-kindp (fn-ncfg-first
                                (fn-native-operator-result-arguments result))))
           :status)
          ((and (member-equal (fn-native-operator-result-command result)
                              '("moderation" "article"))
                (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                       :moderate))
           :moderate)
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
                         :reclaim-recorded)
                  :reclaim-recorded)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :export)
                  :export)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :export-status)
                  :export-status)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :bless-snapshot)
                  :bless-snapshot)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :import)
                  :import)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :inspect)
                  :inspect)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :inspect-group)
                  :inspect-group)
                 ((equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                         :rebind-filesystem)
                  :rebind-filesystem)
                 (t :none)))
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
               (equal (fn-native-operator-result-command result) "motd")
               (equal (fn-native-operator-result-command result) "consumer")
           (equal (fn-native-operator-result-command result) "control")) :admin)
          ((and (equal (fn-native-operator-result-command result) "account")
                (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                       :account-invite))
           :account-invite)
          ((and (equal (fn-native-operator-result-command result) "account")
                (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                       :account-hash))
           :account-hash)
          ((equal (fn-native-operator-result-command result) "account") :admin)
          ((equal (fn-native-operator-result-command result) "principal") :principal)
          ((equal (fn-native-operator-result-command result) "keys") :keys)
          ((equal (fn-native-operator-result-command result) "carry") :carry)
          ((and (equal (fn-native-operator-result-command result) "tls")
                (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                       :tls-self-signed))
           :tls-self-signed)
          ((equal (fn-native-operator-result-command result) "tls") :tls)
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
                                   (fn-nop-result fn-native-operator-result-command fn-nop-parse-init-groups fn-nop-parse-profile-flags fn-bs-profile-resolve fn-native-admin-some-group-name-reservedp fn-nop-group-names-within fn-bs-profile-max-group-name-octets))))))

(local
 (defthm fn-nop-parse-post-command
   (equal (fn-native-operator-result-command (fn-nop-parse-post w c)) "post")
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-post fn-nop-usage fn-nop-refused)
                                   (fn-nop-result fn-native-operator-result-command fn-nop-parse-post-aux fn-native-config-posting-enabledp))))))

(local
 (defthm fn-nop-parse-principal-command
   (equal (fn-native-operator-result-command (fn-nop-parse-principal a c)) "principal")
   ; The account plan is an argument, never opened: 2.8M steps opened, 740 closed.
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-principal fn-nop-usage fn-nop-refused)
                                   (fn-nop-result fn-native-operator-result-command fn-native-auth-admin-parse-argv fn-native-auth-admin-plan-status fn-native-auth-admin-plan-reason fn-nop-parse-administration fn-native-auth-admin-action-kind))))))

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

; An accepted `store' plan is the store parser's plan over the words after
; "store" (one expansion of fn-nop-parse-command, shared by the five
; store-verb lemmas below: each alone cost 659,470 prover steps).
(local
 (defthm fn-nop-parse-command-store-is-parse-store
   (implies (and (equal (fn-native-operator-result-status
                         (fn-nop-parse-command words config argv))
                        :accepted)
                 (equal (fn-native-operator-result-command
                         (fn-nop-parse-command words config argv))
                        "store"))
            (and (consp words) (equal (car words) "store")
                 (equal (fn-nop-parse-command words config argv)
                        (fn-nop-parse-store (cdr words) config))))
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
                                    fn-nop-help-text fn-nop-help-subjectp
                                    fn-nop-profile-decimal))))))

(local
 (defthm fn-nop-parse-store-compact-words
   (implies (and (equal (fn-native-operator-result-status (fn-nop-parse-store w c))
                        :accepted)
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-store w c)))
                        :compact))
            (equal w '("compact")))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)
                                   (fn-nop-parse-profile-flags))))))

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
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-nop-parse-command-store-is-parse-store
                  (:instance fn-nop-parse-store-compact-words (w (cdr words)) (c config)))))))

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
                                   fn-native-config-operator-availablep
                                   fn-nntp-response-text-true-listp fn-cp-idp true-listp
                                   fn-nntp-article-idp-is-consp fn-nntp-response-textp
                                   fn-cp-id-length-bound fn-nntp-clean-line-is-response-text))
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
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)
                                   (fn-nop-parse-profile-flags))))))

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
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-nop-parse-command-store-is-parse-store
                  (:instance fn-nop-parse-store-checkpoint-words (w (cdr words)) (c config)))))))

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
                                   fn-native-config-operator-availablep
                                   fn-nntp-response-text-true-listp fn-cp-idp true-listp
                                   fn-nntp-article-idp-is-consp fn-nntp-response-textp
                                   fn-cp-id-length-bound fn-nntp-clean-line-is-response-text))
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
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)
                                   (fn-nop-parse-profile-flags))))))

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
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-nop-parse-command-store-is-parse-store
                  (:instance fn-nop-parse-store-reclaim-words (w (cdr words)) (c config)))))))

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
                                   fn-native-config-operator-availablep
                                   fn-nntp-response-text-true-listp fn-cp-idp true-listp
                                   fn-nntp-article-idp-is-consp fn-nntp-response-textp
                                   fn-cp-id-length-bound fn-nntp-clean-line-is-response-text))
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
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)
                                   (fn-nop-parse-profile-flags))))))

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
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-nop-parse-command-store-is-parse-store
                  (:instance fn-nop-parse-store-reclaim-dry-run-words (w (cdr words)) (c config)))))))

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
                                   fn-native-config-operator-availablep
                                   fn-nntp-response-text-true-listp fn-cp-idp true-listp
                                   fn-nntp-article-idp-is-consp fn-nntp-response-textp
                                   fn-cp-id-length-bound fn-nntp-clean-line-is-response-text))
           :use ((:instance fn-nop-parse-command-reclaim-dry-run-action-words
                            (words (fn-nop-argument-texts argv))
                            (config (fn-ncfg-second (fn-native-config-load config)))
                            (argv argv))
                 (:instance fn-nop-parse-command-reclaim-dry-run-action-words
                            (words (fn-nop-argument-texts argv))
                            (config nil) (argv argv))))))

; KEYSTONE (STO-017, the operator entry to content reclamation).  The
; same subject and projection as the compaction keystone above: an
; accepted `store reclaim --recorded' is the :reclaim-recorded action, and the
; :reclaim-recorded action arises from that argv and no other, so the raw host
; reaches `fnn-command-reclaim' with --recorded only for it.
(defthm fn-native-operator-run-store-reclaim-recorded-is-the-reclaim-recorded-action
  (implies (and (equal (fn-nop-argument-texts argv) '("store" "reclaim" "--recorded"))
                (equal (fn-native-operator-result-status
                        (fn-native-operator-run config argv))
                       :accepted))
           (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :reclaim-recorded))
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
 (defthm fn-nop-parse-store-reclaim-recorded-words
   (implies (and (equal (fn-native-operator-result-status (fn-nop-parse-store w c))
                        :accepted)
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-store w c)))
                        :reclaim-recorded))
            (equal w '("reclaim" "--recorded")))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-nop-parse-store fn-nop-usage fn-nop-result
                                      fn-native-operator-result-status
                                      fn-native-operator-result-arguments)
                                   (fn-nop-parse-profile-flags))))))

(local
 (defthm fn-nop-parse-command-reclaim-recorded-words
   (implies (and (equal (fn-native-operator-result-status
                         (fn-nop-parse-command words config argv))
                        :accepted)
                 (equal (fn-native-operator-result-command
                         (fn-nop-parse-command words config argv))
                        "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments
                                        (fn-nop-parse-command words config argv)))
                        :reclaim-recorded))
            (equal words '("store" "reclaim" "--recorded")))
   :rule-classes nil
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-nop-parse-command-store-is-parse-store
                  (:instance fn-nop-parse-store-reclaim-recorded-words (w (cdr words)) (c config)))))))

(local
 (defthm fn-nop-reclaim-recorded-action-shape
   (implies (equal (fn-native-operator-result-native-action result) :reclaim-recorded)
            (and (equal (fn-native-operator-result-status result) :accepted)
                 (equal (fn-native-operator-result-command result) "store")
                 (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                        :reclaim-recorded)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-native-operator-result-native-action)))))

(local
 (defthm fn-nop-parse-command-reclaim-recorded-action-words
   (implies (equal (fn-native-operator-result-native-action
                    (fn-nop-parse-command words config argv))
                   :reclaim-recorded)
            (equal words '("store" "reclaim" "--recorded")))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-nop-reclaim-recorded-action-shape
                                       fn-native-operator-result-native-action
                                       fn-nop-parse-command)
            :use ((:instance fn-nop-reclaim-recorded-action-shape
                             (result (fn-nop-parse-command words config argv)))
                  fn-nop-parse-command-reclaim-recorded-words)))))

(defthm fn-native-operator-run-reclaim-recorded-action-is-only-store-reclaim-recorded
  (implies (equal (fn-native-operator-result-native-action
                   (fn-native-operator-run config argv))
                  :reclaim-recorded)
           (equal (fn-nop-argument-texts argv) '("store" "reclaim" "--recorded")))
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
                                   fn-native-config-operator-availablep
                                   fn-nntp-response-text-true-listp fn-cp-idp true-listp
                                   fn-nntp-article-idp-is-consp fn-nntp-response-textp
                                   fn-cp-id-length-bound fn-nntp-clean-line-is-response-text))
           :use ((:instance fn-nop-parse-command-reclaim-recorded-action-words
                            (words (fn-nop-argument-texts argv))
                            (config (fn-ncfg-second (fn-native-config-load config)))
                            (argv argv))
                 (:instance fn-nop-parse-command-reclaim-recorded-action-words
                            (words (fn-nop-argument-texts argv))
                            (config nil) (argv argv))))))

; The status report the operator asked for (books/native-live-status.lisp
; renders it), the watch interval, and the control socket the running owner
; answers on.  `peer list' is the fourth kind, reached through its
; administrative query plan (`fn-native-operator-result-admin-plan').
(defun fn-native-operator-result-status-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (or (member-equal (fn-native-operator-result-command result)
                         '("status" "health" "pins" "obligations"))
           ;; PKT-209: `control log', `control evidence MSGID'.
           (and (member-equal (fn-native-operator-result-command result)
                              '("control" "moderation"))
                (fn-cevg-kindp (fn-ncfg-first
                                (fn-native-operator-result-arguments result)))))
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

; PKT-868: `store compact' and `store checkpoint' on a running owner are a
; request for its publication (books/owner-compact-request.lisp), sent as
; the administrative vector below over its control socket; with no owner
; they run offline as before.  The route is the administrative one: ACL2's
; liveness decision (fn-native-control-liveness-decides) over the socket and
; the store lock, the offline executor only when no owner holds the lock.
(defun fn-native-operator-result-compaction-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "store")
       (member-equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                     '(:compact :checkpoint))
       t))

(defun fn-native-operator-result-compaction-argv (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-compaction-planp result)
      (list (fn-record-string-octets "compaction") (fn-record-string-octets "request"))
    nil))

(defun fn-native-operator-result-compaction-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-compaction-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

;; Row S9: `retire' is a request to the running owner, sent as
;; books/native-retire.lisp's vector over the control socket.
(defun fn-native-operator-result-retire-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "retire")
       (equal (fn-ncfg-first (fn-native-operator-result-arguments result)) :retire)
       t))

(defun fn-native-operator-result-retire-argv (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-retire-planp result)
      (fn-nret-request-argv (fn-ncfg-second (fn-native-operator-result-arguments result)))
    nil))

(defun fn-native-operator-result-retire-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-retire-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

;; Q16 (lane online-reclaim): `store reclaim' on a running owner is a
;; request for the owner's reclaim pass (books/owner-reclaim.lisp), sent as
;; the administrative vector below over the same route as the compaction
;; request; with no owner it runs offline as before.  The second word names
;; the mode: "request" (record the instant, then reclaim), "recorded" (the
;; configuration's recorded instant), "dry-run" (decide, write nothing).
(defun fn-native-operator-result-reclaim-planp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-status result) :accepted)
       (equal (fn-native-operator-result-command result) "store")
       (member-equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                     '(:reclaim :reclaim-dry-run :reclaim-recorded))
       t))

(defun fn-native-operator-result-reclaim-argv (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-reclaim-planp result)
      (list (fn-record-string-octets "reclaim")
            (fn-record-string-octets
             (let ((action (fn-ncfg-first (fn-native-operator-result-arguments result))))
               (cond ((equal action :reclaim-dry-run) "dry-run")
                     ((equal action :reclaim-recorded) "recorded")
                     (t "request")))))
    nil))

(defun fn-native-operator-result-reclaim-control-path-octets (result)
  (declare (xargs :guard t))
  (if (fn-native-operator-result-reclaim-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-result-status-control-path-octets (result)
  (declare (xargs :guard t))
  (if (or (fn-native-operator-result-status-planp result)
          (fn-native-operator-result-admin-planp result))
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

; friend-path-2: the service log `status' and `health' read the last run
; line from when no owner runs (books/native-health.lisp fn-nh-last-run), or
; nil when the configuration names none (stderr).
(defun fn-native-operator-result-status-log-path-octets (result)
  (declare (xargs :guard t))
  (if (and (or (fn-native-operator-result-status-planp result)
               (fn-native-operator-result-admin-planp result))
           (fn-native-config-log-path (fn-native-operator-result-config result)))
      (fn-record-string-octets
       (fn-native-config-log-path (fn-native-operator-result-config result)))
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

; Row Q10a: the self-signed pair an accepted `mission --tls-port' or `tls
; self-signed' asks the image to make: (NAMES DAYS CERT-PATH KEY-PATH), the
; paths as octets, or NIL.
(defun fn-native-operator-result-self-signed (result)
  (declare (xargs :guard t))
  (cond ((not (equal (fn-native-operator-result-status result) :accepted)) nil)
        ((equal (fn-native-operator-result-command result) "mission")
         (fn-ncfg-nth 4 (fn-native-operator-result-arguments result)))
        ((and (equal (fn-native-operator-result-command result) "tls")
              (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                     :tls-self-signed))
         (let ((config (fn-native-operator-result-config result)))
           (list (fn-ncfg-second (fn-native-operator-result-arguments result))
                 (fn-ncfg-third (fn-native-operator-result-arguments result))
                 (fn-record-string-octets (fn-native-config-tls-cert config))
                 (fn-record-string-octets (fn-native-config-tls-key config)))))
        (t nil)))

; The host's lstat of the two files: an existing one is refused by name
; (`exists'); the image never overwrites a certificate or a key.
(defun fn-native-operator-self-signed-outcome (result cert-exists key-exists)
  (declare (xargs :guard t))
  (if (and (fn-native-operator-result-self-signed result) (or cert-exists key-exists))
      (fn-nop-refused :exists (fn-native-operator-result-command result)
                      (fn-native-operator-result-config result) nil)
    result))

;   The refusal the image's pair answered with (a fn-ssc-plan word such as
;   :clock, or :spki / :signature / :key from the host's octets), by name.
(defun fn-native-operator-self-signed-refused (result reason)
  (declare (xargs :guard t))
  (fn-nop-refused (if (member-equal reason '(:no-names :name :common-name-length :clock :days
                                             :serial :spki :too-long :body :signature :key))
                      reason
                    :self-signed)
                  (fn-native-operator-result-command result)
                  (fn-native-operator-result-config result) nil))

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
    :reclaim-dry-run :reclaim-recorded :export :export-status :admin :inspect
    :inspect-group
    :peering :principal :keys :tls :carry))

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

; -----------------------------------------------------------------------------
; The control socket's path at `run' (lane ops-fixes).  A Unix socket's
; address holds its path in sun_path: 108 octets on Linux, 104 on OpenBSD
; and Darwin, each with a terminating NUL, so 103 octets is the longest
; control path every supported platform binds whole.  A longer path was
; bound truncated (SBCL copies the prefix that fits), and the owner then
; faulted at its own start with ENOENT on the full path (exit 4,
; tests.test_native_heap_from_profile on a deep scratch tree).  The run is
; refused by name before anything opens: :control-path-too-long, exit 1.
; The clients that connect to the path need no check: with no owner bound
; there, their connect fails before submission and names no-owner
; (books/native-control-reason.lisp fn-native-control-transport-word).

(defconst *fn-nop-control-path-max-octets* 103)

(defun fn-native-operator-control-path-too-longp (result)
  (declare (xargs :guard t))
  (and (equal (fn-native-operator-result-native-action result) :run)
       (< *fn-nop-control-path-max-octets*
          (len (fn-record-string-octets
                (fn-native-config-control-path
                 (fn-native-operator-result-config result)))))))

(defun fn-native-operator-control-outcome (result)
  "RESULT unchanged, or the :control-path-too-long refusal of a `run' whose
control path no supported platform binds whole."
  (declare (xargs :guard t))
  (if (fn-native-operator-control-path-too-longp result)
      (fn-nop-refused :control-path-too-long
                      (fn-native-operator-result-command result)
                      (fn-native-operator-result-config result)
                      (fn-native-operator-result-arguments result))
    result))

; KEYSTONE.  The subject is `fn-native-operator-control-outcome', which
; `fnn-operator-store-outcome' (host/native/operator.lisp) calls through
; `fn-native-operator-host-control-outcome' on every plan, after the
; store's outcome and before any action executes: a run whose control path
; is too long is refused by name with the refusal code, and nothing runs;
; every other plan passes through unchanged.
(defthm fn-native-operator-long-control-path-is-refused
  (implies (fn-native-operator-control-path-too-longp result)
           (let ((outcome (fn-native-operator-control-outcome result)))
             (and (equal (fn-native-operator-result-status outcome) :refused)
                  (equal (fn-native-operator-result-reason outcome)
                         :control-path-too-long)
                  (equal (fn-native-operator-exit-code outcome)
                         (fn-outcome-code :refused))
                  (equal (fn-native-operator-result-native-action outcome) :none))))
  :hints (("Goal" :in-theory '(fn-native-operator-control-outcome
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

(defthm fn-native-operator-control-outcome-passes-a-bindable-path
  (implies (not (fn-native-operator-control-path-too-longp result))
           (equal (fn-native-operator-control-outcome result) result))
  :hints (("Goal" :in-theory '(fn-native-operator-control-outcome))))

;  The line printed before a usage or refused result's tagged line: what the
; command accepts, or what to do.  ACL2's words; the host prints them.
(defun fn-native-operator-result-hint (result)
  (declare (xargs :guard t))
  (let ((status (fn-native-operator-result-status result))
        (reason (fn-native-operator-result-reason result))
        (command (fn-native-operator-result-command result)))
    (cond ; Row S10: `policy set KEY VALUE' refused by name, with what it takes.
          ((and (equal status :refused)
                (equal reason (list :administration :unknown-policy-key)))
           "policy set: no key by that name; the keys are path-identity, posting-policy, exposure-connections, exposure-per-address, exposure-steps-per-second, exposure-idle-seconds, exposure-first-seconds, exposure-auth-failures, exposure-posts-per-minute, relay-date-skew, refused-offer-capacity, relay-require-path, max-transactions, max-history-octets, max-article-octets (docs/operator.md)")
          ((and (equal status :refused)
                (equal reason (list :administration :policy-value-not-a-number)))
           "policy set: that key takes a decimal count (digits only); run: fn operator CONFIG policy set KEY N")
          ((and (equal status :refused) (equal reason :control-path-too-long))
           "the control socket path ([control] path, else the [store] path with /control.sock) is longer than 103 octets, which a Unix socket cannot bind on every platform; set a shorter [control] path in fn.toml")
          ((and (equal status :refused) (equal reason :no-store))
           "no store at the configured [store] path: this node was never initialized; run: fn operator CONFIG init GROUP... (a mission's fn.toml: init with no group)")
          ((and (equal status :usage) (equal reason :mission-fixes-profile))
           "under [ops] mission, init takes GROUP words only (none: the mission's default groups); the mission fixes the store profile. To raise a bound later: fn operator CONFIG policy set max-transactions|max-history-octets|max-article-octets N; or delete the mission line from fn.toml to choose a profile at init")
          ; Row Q10b: init's budget word, and a refused profile's numbers.
          ((and (equal status :usage) (equal reason :invalid-init-budget))
           "init: --budget takes the memory budget in MiB (a decimal, at least 1) and --largest takes no value; each at most once (fn operator CONFIG init [--budget MB] [--largest] ...)")
          ((and (equal status :refused) (equal command "init")
                (fn-nop-init-refusal-numbers
                 reason (fn-native-operator-result-arguments result)))
           (fn-nop-init-refusal-numbers
            reason (fn-native-operator-result-arguments result)))
          ((and (equal status :usage) (fn-nop-help-subjectp command))
           (fn-nop-help-text command))
          (t nil))))

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

; Row S3d: the group `store inspect --group GROUP' names, or nil.
(defun fn-native-operator-result-inspect-group (result)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-operator-result-status result) :accepted)
           (equal (fn-native-operator-result-command result) "store")
           (equal (fn-ncfg-first (fn-native-operator-result-arguments result))
                  :inspect-group)
           (stringp (fn-ncfg-second (fn-native-operator-result-arguments result))))
      (fn-ncfg-second (fn-native-operator-result-arguments result))
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
