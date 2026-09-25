; fn: the offline store-profile upgrade (M5).
;
; A store's profile (books/byte-store-frame.lisp, `config.json', an FNSM
; frame) bounds the work of opening the store before any configuration record
; is replayed, so it cannot be raised by a configuration record
; (books/store-budget.lisp, "Why the budget is fixed at init").  It CAN be
; raised offline: with no owner running, the one metadata file is replaced by
; a frame whose every bound is at least the old one.  This book is the ACL2
; half of that step:
;
;   * `fn-profile-upgradep' OLD NEW: OLD is a profile a store runs under
;     (format 8, or format 7 through its translation), NEW is a valid
;     format-8 profile (`fn-bs-profile-validp', the relations, not a table),
;     NEW is not OLD, and none of its twelve fields is smaller.  The format 7
;     to 8 step is the case NEW = the translation of OLD.
;   * `fn-profile-upgrade-verdict' CURRENT TARGET: what the operator verb
;     (host/native/io.lisp `fnn-command-upgrade-profile') does, decided here:
;     the octets to write, or the refusal and its reason.  TARGET is a preset
;     word or the operator's request (base and field overrides).  Same
;     profile is refused (`:same-profile'), an invalid one by the relation it
;     fails, a smaller one (`:not-an-upgrade' and the field); nothing is
;     written for any refusal.
;   * The monotonicity of every profile-dependent gate the host consults when
;     it opens or publishes into a store, over the functions it calls:
;       - the transaction namespace observation, `fn-profile-txn-observation'
;         (host/store-host.lisp `fn-store-txn-observation-selected', called
;         from host/native/io.lisp `fnn-transaction-files' with field 4);
;       - the aggregate replay bound, `fn-profile-replay-within-boundp'
;         (host/store-host.lisp `fn-store-profile-replay-within-bound', called
;         per record from host/native/io.lisp `fnn-durable-records');
;       - the publication admissibility `fn-bs-publication-admissiblep'
;         (host/native/io.lisp `fnn-publish') and the budget and verdict of
;         books/store-budget.lisp that the owner and `store post' consult.
;     Replay itself (`fn-store-sn-recover' through `fnn-bridge-recover')
;     takes no profile argument: it is a function of the record list, the
;     frontier and the configuration records, none of which the upgrade
;     writes.  So a store the old profile admits is admitted by the new one
;     with the same observation, and replays to the same state.
;
; The byte program the verb runs, and its crash theorem, are
; books/byte-store-profile-program.lisp.
(in-package "ACL2")
(include-book "store-budget")
(include-book "byte-store-txn-name")
(local (include-book "frame-invariants"))
(local (include-book "cbor-invariants"))

; -----------------------------------------------------------------------------
; The upgrade relation

(defun fn-profile-bound (n values)
  "Field N of the profile a store runs under, as a natural (2..13)."
  (declare (xargs :guard (natp n)))
  (fn-bs-profile-field n values))

; NEW is an upgrade of OLD: OLD is a profile a store runs under (format 8, or
; format 7 through its translation), NEW is a valid format-8 profile, NEW is
; not OLD, and no field of NEW is smaller than the same field of OLD.  The
; formats need no clause: every valid profile has the format-8 and frontier
; format texts.  A format-7 OLD and its own translation satisfy it (every
; field equal, the lists different): that is the format 7 to 8 step.
(defun fn-profile-upgradep (old new)
  (declare (xargs :guard t))
  (and (fn-bs-profile-admittedp old)
       (fn-bs-profile-validp new)
       (not (equal old new))
       (<= (fn-profile-bound 2 old) (fn-profile-bound 2 new))
       (<= (fn-profile-bound 3 old) (fn-profile-bound 3 new))
       (<= (fn-profile-bound 4 old) (fn-profile-bound 4 new))
       (<= (fn-profile-bound 5 old) (fn-profile-bound 5 new))
       (<= (fn-profile-bound 6 old) (fn-profile-bound 6 new))
       (<= (fn-profile-bound 7 old) (fn-profile-bound 7 new))
       (<= (fn-profile-bound 8 old) (fn-profile-bound 8 new))
       (<= (fn-profile-bound 9 old) (fn-profile-bound 9 new))
       (<= (fn-profile-bound 10 old) (fn-profile-bound 10 new))
       (<= (fn-profile-bound 11 old) (fn-profile-bound 11 new))
       (<= (fn-profile-bound 12 old) (fn-profile-bound 12 new))
       (<= (fn-profile-bound 13 old) (fn-profile-bound 13 new))))

; The first field NEW makes smaller than OLD, by its operator name, or NIL.
(defun fn-profile-shrunk-field (old new names)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((entry (car names)))
        (if (and (consp entry) (natp (car entry))
                 (< (fn-profile-bound (car entry) new)
                    (fn-profile-bound (car entry) old)))
            (cdr entry)
          (fn-profile-shrunk-field old new (cdr names))))
    nil))

; -----------------------------------------------------------------------------
; The open gates, as the host calls them

; The transaction-namespace observation: at most MAXIMUM names (the profile's
; max_transactions, host/native/io.lisp `fnn-transaction-files'), then ACL2's
; name grammar and sequence binding.
(defun fn-profile-txn-observation (names maximum selected-lower)
  (declare (xargs :guard t))
  (if (and (natp maximum) (natp selected-lower) (true-listp names)
           (<= (len names) maximum))
      (fn-bs-txn-observation-selected names selected-lower)
    :invalid))

; The aggregate replay input: at most the profile's max_history_octets.
(defun fn-profile-replay-within-boundp (profile aggregate)
  (declare (xargs :guard t))
  (and (fn-bs-profile-admittedp profile)
       (natp aggregate)
       (<= aggregate (fn-bs-profile-max-history-octets profile))))

; -----------------------------------------------------------------------------
; Keystones: every gate is monotone in the upgrade

(local (in-theory (disable fn-bs-txn-observation-selected)))

(local
 (defthm fn-profile-validp-is-admitted
   (implies (fn-bs-profile-validp values)
            (fn-bs-profile-admittedp values))
   :hints (("Goal" :in-theory (enable fn-bs-profile-admittedp)))))

; The shape facts the keystones spend, stated once so that no keystone opens
; the profile relations or the upgrade relation.
(local
 (defthm fn-profile-upgradep-facts
   (implies (fn-profile-upgradep old new)
            (and (fn-bs-profile-admittedp old)
                 (fn-bs-profile-admittedp new)
                 (<= (fn-bs-profile-max-transactions old)
                     (fn-bs-profile-max-transactions new))
                 (<= (fn-bs-profile-max-history-octets old)
                     (fn-bs-profile-max-history-octets new))
                 (<= (fn-bs-profile-record-ceiling old)
                     (fn-bs-profile-record-ceiling new))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (fn-profile-upgradep fn-profile-bound
                                    fn-bs-profile-max-transactions
                                    fn-bs-profile-max-history-octets
                                    fn-bs-profile-max-record-octets
                                    fn-bs-profile-record-ceiling)
                                   (fn-bs-profile-admittedp
                                    fn-bs-profile-validp
                                    fn-bs-profile-field))))))

(local
 (defthm fn-profile-max-transactions-natural
   (natp (fn-bs-profile-max-transactions x))
   :rule-classes :type-prescription))
(local
 (defthm fn-profile-max-history-octets-natural
   (natp (fn-bs-profile-max-history-octets x))
   :rule-classes :type-prescription))
(local
 (defthm fn-profile-record-ceiling-natural
   (natp (fn-bs-profile-record-ceiling x))
   :rule-classes :type-prescription))

(local (in-theory (disable fn-profile-upgradep fn-bs-profile-admittedp
                           fn-bs-profile-validp
                           fn-bs-profile-max-transactions
                           fn-bs-profile-max-history-octets
                           fn-bs-profile-record-ceiling)))

; The observation a store's namespace gave under the old profile is the
; observation it gives under the new one: same pairs, same lower bound.
(defthm fn-profile-upgrade-keeps-txn-observation
  (implies (and (fn-profile-upgradep old new)
                (not (equal (fn-profile-txn-observation
                             names (fn-bs-profile-max-transactions old)
                             selected-lower)
                            :invalid)))
           (equal (fn-profile-txn-observation
                   names (fn-bs-profile-max-transactions new) selected-lower)
                  (fn-profile-txn-observation
                   names (fn-bs-profile-max-transactions old) selected-lower))))

(defthm fn-profile-upgrade-keeps-replay-bound
  (implies (and (fn-profile-upgradep old new)
                (fn-profile-replay-within-boundp old aggregate))
           (fn-profile-replay-within-boundp new aggregate)))

(defthm fn-profile-upgrade-keeps-publication-admissibility
  (implies (and (fn-profile-upgradep old new)
                (fn-bs-publication-admissiblep old used octets))
           (fn-bs-publication-admissiblep new used octets)))

(defthm fn-profile-upgrade-budget-grows
  (implies (fn-profile-upgradep old new)
           (<= (fn-sbud-budget old kind) (fn-sbud-budget new kind)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sbud-budget))))

; The owner's and `store post''s verdict for one more record: whatever the old
; profile admitted in a Store state, the new profile admits in that state --
; the count gate and the history-octet gate both.
(defthm fn-profile-upgrade-keeps-verdict
  (implies (and (fn-profile-upgradep old new)
                (equal (fn-sbud-verdict old kind s) :admissible))
           (equal (fn-sbud-verdict new kind s) :admissible))
  :hints (("Goal" :use fn-profile-upgrade-budget-grows
           :in-theory (enable fn-sbud-verdict fn-sbud-verdict-at))))

(local (in-theory (enable fn-bs-profile-validp)))

; -----------------------------------------------------------------------------
; The frame the verb writes, and the budget after reopen

(local
 (defthm fn-profile-octet-list-is-true-list
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-profile-seal-octet-listp
   (implies (fn-frame-inputp magic version kind payload max-payload)
            (fn-cbor-octet-listp (fn-frame-seal magic version kind payload)))
   :hints (("Goal"
            :use ((:instance fn-frame-digestp-of-fn-frame-digest
                             (octets (fn-frame-protected magic version kind payload)))
                  (:instance fn-cbor-u32-bytes-are-octets (n (len payload))))
            :in-theory (e/d (fn-frame-seal fn-frame-encode fn-frame-protected
                             fn-frame-header fn-frame-inputp fn-frame-magicp
                             fn-frame-digestp fn-cbor-octet-listp-append)
                            (fn-frame-digestp-of-fn-frame-digest
                             fn-cbor-u32-bytes-are-octets))))))

(local
 (defthm fn-profile-fields-round-trip
   (implies (fn-bs-profile-validp values)
            (equal (fn-frame-fields-parse
                    *fn-bs-meta-profile-spec*
                    (fn-frame-fields-octets *fn-bs-meta-profile-spec* values))
                   (fn-frame-parse-ok values nil)))
   :hints (("Goal" :use ((:instance fn-bs-profile-validp-facts)
                         (:instance fn-frame-fields-parse-of-octets
                                    (specs *fn-bs-meta-profile-spec*)))
            :in-theory (disable fn-bs-profile-validp-facts
                                fn-frame-fields-parse-of-octets
                                fn-bs-profile-validp)))))

; The metadata codec's round trip for EVERY valid profile: what `init' and
; the verb write is what the next open decodes (under A-CRYPTO, through
; fn-frame-open-of-seal).
(defthm fn-bs-config-decode-of-encode
  (implies (fn-bs-profile-validp values)
           (equal (fn-bs-config-decode (fn-bs-config-encode values))
                  values))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-open-of-seal
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bs-meta-profile-spec* values))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-profile-seal-octet-listp
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bs-meta-profile-spec* values))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-bs-profile-frame-inputp)
                 (:instance fn-profile-fields-round-trip))
           :in-theory (e/d (fn-bs-config-decode fn-bs-config-encode
                            fn-bs-meta-frame-okp fn-frame-inputp)
                           (fn-frame-open-of-seal fn-profile-seal-octet-listp
                            fn-bs-profile-frame-inputp
                            fn-profile-fields-round-trip
                            fn-bs-profile-validp)))))

; The profile the verb is asked for: a preset word (the developer entry and
; the old operator form), or a request (base . overrides) resolved over the
; store's CURRENT profile.
(defun fn-profile-upgrade-target (current target)
  (declare (xargs :guard t))
  (fn-bs-profile-resolve (if (symbolp target) (list target nil) target)
                         current))

; What the operator verb does.  CURRENT is the profile ACL2 decoded from the
; store's config.json at open; TARGET the preset word or request the operator
; named.
;   (:upgrade OCTETS OLD-BUDGET NEW-BUDGET)   write OCTETS as config.json
;   (:refused REASON [FIELD])                  write nothing
(defun fn-profile-upgrade-verdict (current target)
  (declare (xargs :guard t))
  (let ((new (fn-profile-upgrade-target current target)))
    (cond ((not (fn-bs-profile-admittedp current))
           (list :refused :invalid-current-profile))
          ((and (consp new) (equal (car new) :invalid))
           (list :refused (if (or (atom (cdr new))
                                  (equal (cadr new) :request))
                              :unknown-profile
                            (cadr new))))
          ((equal current new) (list :refused :same-profile))
          ((not (fn-profile-upgradep current new))
           (list :refused :not-an-upgrade
                 (fn-profile-shrunk-field current new
                                          *fn-bs-profile-field-names*)))
          (t (list :upgrade (fn-bs-config-encode new)
                   (fn-sbud-budget current :article)
                   (fn-sbud-budget new :article))))))

(local
 (defthm fn-profile-resolve-valid-unless-invalid
   (implies (not (equal (car (fn-bs-profile-resolve request current))
                        :invalid))
            (fn-bs-profile-validp (fn-bs-profile-resolve request current)))
   :hints (("Goal" :in-theory (e/d (fn-bs-profile-resolve)
                                   (fn-bs-profile-set-fields
                                    fn-bs-profile-put
                                    fn-bs-profile-invalid-reason))))))

; The verb writes only upgrades: an :upgrade verdict's octets decode, at the
; next open, to the profile the operator asked for, and that profile is an
; upgrade of the one the store had.
(defthm fn-profile-upgrade-verdict-writes-only-upgrades
  (implies (equal (car (fn-profile-upgrade-verdict current target)) :upgrade)
           (and (equal (fn-bs-config-decode
                        (cadr (fn-profile-upgrade-verdict current target)))
                       (fn-profile-upgrade-target current target))
                (fn-profile-upgradep
                 current
                 (fn-bs-config-decode
                  (cadr (fn-profile-upgrade-verdict current target))))))
  :hints (("Goal" :use ((:instance fn-profile-resolve-valid-unless-invalid
                                   (request (if (symbolp target)
                                                (list target nil)
                                              target))))
           :in-theory (e/d (fn-profile-upgrade-target)
                           (fn-profile-upgradep fn-bs-config-encode
                            fn-bs-config-decode fn-bs-profile-resolve
                            fn-bs-profile-validp fn-bs-profile-admittedp
                            fn-profile-shrunk-field
                            (:e fn-bs-config-encode)
                            (:e fn-bs-config-decode))))))

; The budget after the upgrade: the owner is handed the profile the next open
; decodes (host/native/owner.lisp `fnn-owner-install', which installs
; `fnn-store-config'), so its budget is `fn-sbud-budget' of the new profile.
(defthm fn-profile-upgrade-budget-after-reopen
  (implies (equal (car (fn-profile-upgrade-verdict current target)) :upgrade)
           (equal (fn-sbud-budget
                   (fn-bs-config-decode
                    (cadr (fn-profile-upgrade-verdict current target)))
                   kind)
                  (fn-sbud-budget (fn-profile-upgrade-target current target)
                                  kind)))
  :hints (("Goal" :use fn-profile-upgrade-verdict-writes-only-upgrades
           :in-theory (disable fn-profile-upgrade-verdict fn-sbud-budget
                               fn-bs-config-decode fn-profile-upgradep
                               fn-profile-upgrade-target))))

; The format 7 to 8 step.  A store whose profile is one of the two format-7
; tuples is upgraded, with no field given, to its format-8 translation: the
; verdict writes that translation, which is an upgrade of the store's
; profile, keeps every bound the store ran under, and so keeps the budget of
; every kind.
(local
 (defthm fn-profile-of-format-7-translation
   (implies (fn-bs-meta-format-7-valuesp current)
            (equal (fn-bs-profile-of (fn-bs-profile-from-format-7 current))
                   (fn-bs-profile-of current)))
   :hints (("Goal" :in-theory (enable fn-bs-meta-format-7-valuesp)))))

(local
 (defthm fn-profile-budget-reads-the-profile-of
   (implies (equal (fn-bs-profile-of a) (fn-bs-profile-of b))
            (equal (fn-sbud-budget a kind) (fn-sbud-budget b kind)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sbud-budget fn-bs-profile-admittedp
                                    fn-bs-profile-record-ceiling
                                    fn-bs-profile-max-record-octets
                                    fn-bs-profile-max-transactions
                                    fn-bs-profile-field)
                                   (fn-bs-profile-of fn-bs-profile-validp
                                    fn-store-publication-ceiling))))))

(defthm fn-profile-upgrade-format-7-to-8
  (implies (fn-bs-meta-format-7-valuesp current)
           (and (fn-profile-upgradep current (fn-bs-profile-from-format-7 current))
                (equal (fn-profile-upgrade-verdict current '(:current nil))
                       (list :upgrade
                             (fn-bs-config-encode
                              (fn-bs-profile-from-format-7 current))
                             (fn-sbud-budget current :article)
                             (fn-sbud-budget current :article)))
                (equal (fn-sbud-budget (fn-bs-profile-from-format-7 current) kind)
                       (fn-sbud-budget current kind))))
  :hints (("Goal" :use ((:instance fn-profile-budget-reads-the-profile-of
                                   (a (fn-bs-profile-from-format-7 current))
                                   (b current)))
           :in-theory (union-theories
                       '(fn-bs-meta-format-7-valuesp
                         fn-profile-upgrade-verdict
                         (:e fn-profile-upgrade-target)
                         (:e fn-bs-profile-admittedp)
                         (:e fn-profile-upgradep)
                         (:e fn-bs-profile-from-format-7)
                         (:e fn-sbud-budget)
                         (:e fn-bs-profile-of)
                         (:e fn-profile-shrunk-field))
                       (theory 'minimal-theory)))))

; The deployed case, as ground facts: development to scale is an upgrade,
; with budgets 128 and 4096; development to development is the same profile;
; scale to development shrinks max_transactions.
(defthm fn-profile-upgrade-development-to-scale
  (and (equal (car (fn-profile-upgrade-verdict
                    *fn-bs-profile-development* :scale))
              :upgrade)
       (equal (cddr (fn-profile-upgrade-verdict
                     *fn-bs-profile-development* :scale))
              '(128 4096))
       (equal (fn-profile-upgrade-verdict
               *fn-bs-profile-development* :development)
              '(:refused :same-profile))
       (equal (fn-profile-upgrade-verdict
               *fn-bs-profile-scale* :development)
              '(:refused :not-an-upgrade "max-transactions")))
  :hints (("Goal" :in-theory (disable fn-bs-config-encode
                                      (:e fn-bs-config-encode)
                                      (:e fn-profile-upgrade-verdict)))))

; The profile word of the developer `store ROOT upgrade-profile WORD' entry,
; as octets; the operator entry parses words and flags in
; books/native-operator.lisp `fn-nop-parse-profile-request'.
(defun fn-profile-word-octets (octets)
  (declare (xargs :guard t))
  (cond ((equal octets '(100 101 118 101 108 111 112 109 101 110 116)) :development)
        ((equal octets '(115 99 97 108 101)) :scale)
        (t nil)))

(in-theory (disable fn-profile-upgradep fn-profile-txn-observation
                    fn-profile-replay-within-boundp fn-profile-upgrade-verdict
                    fn-profile-upgrade-target))
