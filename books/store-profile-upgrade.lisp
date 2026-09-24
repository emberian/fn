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
;   * `fn-profile-upgradep' OLD NEW: NEW is a named profile of the same format
;     and frontier format as OLD, is not OLD, and none of its bounds is
;     smaller (capacity, payload, aggregate replay, transaction count, and the
;     per-record ceiling the last two imply).
;   * `fn-profile-upgrade-verdict' CURRENT TARGET: what the operator verb
;     (host/native/io.lisp `fnn-command-upgrade-profile') does, decided here:
;     the octets to write, or the refusal and its reason.  Same profile is
;     refused (`:same-profile'), a smaller or differently formatted one is
;     refused (`:not-an-upgrade'); nothing is written for either.
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
  "Field N of a profile read as a natural (fields 1..4 are frame naturals)."
  (declare (xargs :guard (natp n)))
  (nfix (fn-bs-meta-nth n values)))

(defun fn-profile-upgradep (old new)
  (declare (xargs :guard t))
  (and (fn-bs-meta-config-valuesp old)
       (fn-bs-meta-config-valuesp new)
       (not (equal old new))
       ; same record format and same frontier format
       (equal (fn-bs-meta-nth 0 new) (fn-bs-meta-nth 0 old))
       (equal (fn-bs-meta-nth 5 new) (fn-bs-meta-nth 5 old))
       ; no bound smaller
       (<= (fn-profile-bound 1 old) (fn-profile-bound 1 new))
       (<= (fn-profile-bound 2 old) (fn-profile-bound 2 new))
       (<= (fn-profile-bound 3 old) (fn-profile-bound 3 new))
       (<= (fn-profile-bound 4 old) (fn-profile-bound 4 new))
       (<= (fn-bs-profile-record-ceiling old)
           (fn-bs-profile-record-ceiling new))))

; -----------------------------------------------------------------------------
; The open gates, as the host calls them

; The transaction-namespace observation: at most MAXIMUM names (field 4 of the
; profile, host/native/io.lisp `fnn-transaction-files'), then ACL2's name
; grammar and sequence binding.
(defun fn-profile-txn-observation (names maximum selected-lower)
  (declare (xargs :guard t))
  (if (and (natp maximum) (natp selected-lower) (true-listp names)
           (<= (len names) maximum))
      (fn-bs-txn-observation-selected names selected-lower)
    :invalid))

; The aggregate replay input: at most field 3 of the profile.
(defun fn-profile-replay-within-boundp (profile aggregate)
  (declare (xargs :guard t))
  (and (fn-bs-meta-config-valuesp profile)
       (natp aggregate)
       (<= aggregate (fn-profile-bound 3 profile))))

; -----------------------------------------------------------------------------
; Keystones: every gate is monotone in the upgrade

(local (in-theory (disable fn-bs-txn-observation-selected)))

; The shape facts the keystones spend, stated once so that no keystone opens
; the profile table or the upgrade relation.
(local
 (defthm fn-profile-named-values-facts
   (implies (fn-bs-meta-config-valuesp x)
            (and (natp (fn-bs-meta-nth 1 x)) (natp (fn-bs-meta-nth 2 x))
                 (natp (fn-bs-meta-nth 3 x)) (natp (fn-bs-meta-nth 4 x))
                 (fn-bs-profile-aggregate-covers-recordsp x)))
   :hints (("Goal" :in-theory (enable fn-bs-meta-config-valuesp)))))

(local
 (defthm fn-profile-upgradep-facts
   (implies (fn-profile-upgradep old new)
            (and (fn-bs-meta-config-valuesp old)
                 (fn-bs-meta-config-valuesp new)
                 (natp (fn-bs-meta-nth 3 old)) (natp (fn-bs-meta-nth 4 old))
                 (natp (fn-bs-meta-nth 3 new)) (natp (fn-bs-meta-nth 4 new))
                 (<= (fn-bs-meta-nth 3 old) (fn-bs-meta-nth 3 new))
                 (<= (fn-bs-meta-nth 4 old) (fn-bs-meta-nth 4 new))
                 (<= (fn-bs-profile-record-ceiling old)
                     (fn-bs-profile-record-ceiling new))))
   :rule-classes :forward-chaining
   :hints (("Goal" :use ((:instance fn-profile-named-values-facts (x old))
                         (:instance fn-profile-named-values-facts (x new)))
            :in-theory (e/d (fn-profile-upgradep)
                            (fn-bs-meta-config-valuesp fn-profile-named-values-facts
                             fn-bs-profile-record-ceiling
                             fn-bs-profile-aggregate-covers-recordsp))))))

(local (in-theory (disable fn-profile-upgradep fn-bs-meta-config-valuesp
                           fn-bs-profile-record-ceiling
                           fn-bs-profile-aggregate-covers-recordsp)))

; The observation a store's namespace gave under the old profile is the
; observation it gives under the new one: same pairs, same lower bound.
(defthm fn-profile-upgrade-keeps-txn-observation
  (implies (and (fn-profile-upgradep old new)
                (not (equal (fn-profile-txn-observation
                             names (fn-bs-meta-nth 4 old) selected-lower)
                            :invalid)))
           (equal (fn-profile-txn-observation
                   names (fn-bs-meta-nth 4 new) selected-lower)
                  (fn-profile-txn-observation
                   names (fn-bs-meta-nth 4 old) selected-lower))))

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
; profile admitted in a Store state, the new profile admits in that state.
(defthm fn-profile-upgrade-keeps-verdict
  (implies (and (fn-profile-upgradep old new)
                (equal (fn-sbud-verdict old kind s) :admissible))
           (equal (fn-sbud-verdict new kind s) :admissible))
  :hints (("Goal" :use fn-profile-upgrade-budget-grows
           :in-theory (enable fn-sbud-verdict))))

(local (in-theory (enable fn-bs-meta-config-valuesp
                          fn-bs-profile-record-ceiling
                          fn-bs-profile-aggregate-covers-recordsp)))

; -----------------------------------------------------------------------------
; The frame the verb writes, and the budget after reopen

(local
 (defthm fn-profile-config-frame-input
   (implies (fn-bs-meta-config-valuesp values)
            (fn-frame-inputp *fn-bs-meta-magic* *fn-bs-meta-version*
                             *fn-bs-meta-config-kind*
                             (fn-frame-fields-octets *fn-bs-meta-config-spec* values)
                             *fn-bs-meta-max-config-payload*))
   :hints (("Goal" :in-theory (enable fn-bs-meta-config-valuesp)))))

(local
 (defthm fn-profile-config-fields-round-trip
   (implies (fn-bs-meta-config-valuesp values)
            (equal (fn-frame-fields-parse
                    *fn-bs-meta-config-spec*
                    (fn-frame-fields-octets *fn-bs-meta-config-spec* values))
                   (fn-frame-parse-ok values nil)))
   :hints (("Goal" :in-theory (enable fn-bs-meta-config-valuesp)))))

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

; The metadata codec's round trip for a named profile: what the verb writes
; is what the next open decodes (under A-CRYPTO, through fn-frame-open-of-seal).
(defthm fn-bs-config-decode-of-encode
  (implies (fn-bs-meta-config-valuesp values)
           (equal (fn-bs-config-decode (fn-bs-config-encode values))
                  values))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-open-of-seal
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bs-meta-config-spec* values))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-profile-seal-octet-listp
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bs-meta-config-spec* values))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-profile-config-frame-input))
           :in-theory (e/d (fn-bs-config-decode fn-bs-config-encode
                            fn-bs-meta-frame-okp fn-frame-inputp)
                           (fn-frame-open-of-seal fn-profile-seal-octet-listp
                            fn-profile-config-frame-input
                            fn-bs-meta-config-valuesp)))))

; What the operator verb does.  CURRENT is the profile ACL2 decoded from the
; store's config.json at open; TARGET the profile word the operator named.
;   (:upgrade OCTETS OLD-BUDGET NEW-BUDGET)   write OCTETS as config.json
;   (:refused REASON)                          write nothing
(defun fn-profile-upgrade-verdict (current target)
  (declare (xargs :guard t))
  (let ((new (fn-bs-config-for-profile target)))
    (cond ((not (fn-bs-meta-config-valuesp current))
           (list :refused :invalid-current-profile))
          ((null new) (list :refused :unknown-profile))
          ((equal current new) (list :refused :same-profile))
          ((not (fn-profile-upgradep current new))
           (list :refused :not-an-upgrade))
          (t (list :upgrade (fn-bs-config-encode new)
                   (fn-sbud-budget current :article)
                   (fn-sbud-budget new :article))))))

; The verb writes only upgrades: an :upgrade verdict's octets decode, at the
; next open, to the profile the operator named, and that profile is an
; upgrade of the one the store had.
(defthm fn-profile-upgrade-verdict-writes-only-upgrades
  (implies (equal (car (fn-profile-upgrade-verdict current target)) :upgrade)
           (and (equal (fn-bs-config-decode
                        (cadr (fn-profile-upgrade-verdict current target)))
                       (fn-bs-config-for-profile target))
                (fn-profile-upgradep
                 current
                 (fn-bs-config-decode
                  (cadr (fn-profile-upgrade-verdict current target))))))
  :hints (("Goal" :in-theory (disable fn-profile-upgradep fn-bs-config-encode
                                      fn-bs-config-decode
                                      (:e fn-bs-config-encode)
                                      (:e fn-bs-config-decode)))))

; The budget after the upgrade: the owner is handed the profile the next open
; decodes (host/native/owner.lisp `fnn-owner-install', which installs
; `fnn-store-config'), so its budget is `fn-sbud-budget' of the new profile.
(defthm fn-profile-upgrade-budget-after-reopen
  (implies (equal (car (fn-profile-upgrade-verdict current target)) :upgrade)
           (equal (fn-sbud-budget
                   (fn-bs-config-decode
                    (cadr (fn-profile-upgrade-verdict current target)))
                   kind)
                  (fn-sbud-budget (fn-bs-config-for-profile target) kind)))
  :hints (("Goal" :use fn-profile-upgrade-verdict-writes-only-upgrades
           :in-theory (disable fn-profile-upgrade-verdict fn-sbud-budget
                               fn-bs-config-decode fn-profile-upgradep))))

; The deployed case, as ground facts: development to scale is the one upgrade
; from development, with budgets 128 and 4096; development to development is
; the same profile.
(defthm fn-profile-upgrade-development-to-scale
  (and (equal (car (fn-profile-upgrade-verdict
                    *fn-bs-meta-development-values* :scale))
              :upgrade)
       (equal (cddr (fn-profile-upgrade-verdict
                     *fn-bs-meta-development-values* :scale))
              '(128 4096))
       (equal (fn-profile-upgrade-verdict
               *fn-bs-meta-development-values* :development)
              '(:refused :same-profile))
       (equal (fn-profile-upgrade-verdict
               *fn-bs-meta-scale-values* :development)
              '(:refused :not-an-upgrade)))
  :hints (("Goal" :in-theory (disable fn-bs-config-encode
                                      (:e fn-bs-config-encode)
                                      (:e fn-profile-upgrade-verdict)))))

; The profile word of the developer `store ROOT upgrade-profile WORD' entry,
; as octets; the operator entry parses the same two words in
; books/native-operator.lisp `fn-nop-init-profile-word'.
(defun fn-profile-word-octets (octets)
  (declare (xargs :guard t))
  (cond ((equal octets '(100 101 118 101 108 111 112 109 101 110 116)) :development)
        ((equal octets '(115 99 97 108 101)) :scale)
        (t nil)))

(in-theory (disable fn-profile-upgradep fn-profile-txn-observation
                    fn-profile-replay-within-boundp fn-profile-upgrade-verdict))
