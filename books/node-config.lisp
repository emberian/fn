; fn: the configured node (packet R3 of specs/reconfiguration.md).
;
; `fn-cnode' pairs a `fn-node' state with its `(generation value)'
; configuration and carries, as recognizer conjuncts rather than per-operation
; checks, the coherence the design's section 1.6 asks for.  Two tables, one
; equality each:
;
;   * the acceptance state's group list IS the allocation DOMAIN: every name
;     the configuration history ever created, retired or not
;     (`fn-cfg-group-all-names').  `fn-nexts-for-p' keys the watermarks on
;     exactly that list and `fn-articlep' binds every article's groups inside
;     it, so a retired name that left the list would lose its watermark and
;     unbind its articles.  Keeping the name is what makes NNT-006
;     ("watermarks survive removal and restart") structural;
;   * the SERVED table is the configuration's live names at the current
;     generation (`fn-cfg-group-names'), a subset of the domain.  Admission
;     checks the served table here, in `fn-cnode-selection-servedp', which is
;     also the predicate the host calls;
;   * the retention ledger's capacity IS the configuration's capacity.
;
; `books/acceptance', `books/node' and `books/replay' are untouched and every
; statement of theirs still holds of the node inside: each transition below
; lifts the node transition and re-establishes the two equalities.
; `fn-cnode-apply-config' is the configuration transition; it is admissible
; only on an idle node and only when `books/config' admits the record against
; the node's real reservation total and RFC 3977 section 3.1's initial-line
; ceiling, which `books/nntp-syntax' owns and this book cites once.

(in-package "ACL2")
(include-book "node-invariants")
(include-book "config-invariants")
(include-book "config-records")
(include-book "nntp-syntax")
(include-book "records-seam")

; A record passed to `fn-replay-apply-record' must be a true list; records'
; opacity withdrew that fact (board, convergence 2026-09-19), and
; `fn-record-uint32p' is withdrawn under the codec vocabulary.
(local (in-theory (enable fn-record-record-vocabulary
                          fn-record-shape-vocabulary
                          fn-acceptance-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The record

(defun fn-cnode-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))
(defun fn-cnode-node (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-cnode-node)
(defun fn-cnode-config (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-cnode-config)
(defun fn-cnode-make (node config)
  (declare (xargs :guard t))
  (list node config))

(defthm fn-cnode-shapep-of-fn-cnode-make
  (fn-cnode-shapep (fn-cnode-make node config)))
(defthm fn-cnode-node-of-fn-cnode-make
  (equal (fn-cnode-node (fn-cnode-make node config)) node))
(defthm fn-cnode-config-of-fn-cnode-make
  (equal (fn-cnode-config (fn-cnode-make node config)) config))

(defthm fn-cnode-shapep-forward-shape
  (implies (fn-cnode-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-cnode-accessors-forward-consp
  (and (implies (fn-cnode-node x) (consp x))
       (implies (fn-cnode-config x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-cnode-node x) (consp x))
                                    :trigger-terms ((fn-cnode-node x)))
                 (:forward-chaining :corollary (implies (fn-cnode-config x) (consp x))
                                    :trigger-terms ((fn-cnode-config x)))))

(in-theory (disable (:d fn-cnode-shapep) (:d fn-cnode-node)
                    (:d fn-cnode-config) (:d fn-cnode-make)))

; -----------------------------------------------------------------------------
; The two tables of a configuration, and the one ceiling this book cites

(defun fn-cnode-served-of (config)
  ; The served table: the live names at the configuration's generation.
  (declare (xargs :guard t))
  (fn-cfg-group-names (fn-cfg-value config) (fn-cfg-generation config)))

(defun fn-cnode-domain-of (config)
  ; The allocation domain: every name the history ever created.
  (declare (xargs :guard t))
  (fn-cfg-group-all-names (fn-cfg-groups (fn-cfg-value config))))

(defun fn-cnode-served (cn)
  (declare (xargs :guard t))
  (fn-cnode-served-of (fn-cnode-config cn)))

(defun fn-cnode-domain (cn)
  (declare (xargs :guard t))
  (fn-cnode-domain-of (fn-cnode-config cn)))

(defun fn-cnode-selection-servedp (config groups)
  ; The predicate admission and the host both call: every named group is
  ; served at this configuration's generation.
  (declare (xargs :guard t))
  (fn-subsetp groups (fn-cnode-served-of config)))

(defun fn-cnode-line-ceiling ()
  ; RFC 3977 section 3.1's initial line, cited from its one owner.
  (declare (xargs :guard t))
  *fn-nntp-max-initial-line-octets*)

; -----------------------------------------------------------------------------
; The recognizer: a carried invariant

(defun fn-cnode-statep (cn)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-cnode-shapep cn)
       (fn-node-statep (fn-cnode-node cn))
       (fn-cfgp (fn-cnode-config cn))
       (equal (fn-state-groups (fn-node-acceptance (fn-cnode-node cn)))
              (fn-cnode-domain cn))
       (equal (fn-retain-capacity (fn-node-retention (fn-cnode-node cn)))
              (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn))))))

(defthm fn-cnode-statep-forward-shape
  (implies (fn-cnode-statep cn) (and (consp cn) (true-listp cn)))
  :rule-classes :forward-chaining)

(verify-guards fn-cnode-statep)

; -----------------------------------------------------------------------------
; The initial configured node

(defun fn-cnode-initial (config)
  (declare (xargs :guard t))
  (fn-cnode-make (fn-node-initial-state (fn-cnode-domain-of config)
                                        (fn-cfg-capacity (fn-cfg-value config)))
                 config))

; The bridge from the configuration's typed names to acceptance's list
; vocabulary: a group entry's name is a group name, hence a string, and the
; configuration's own no-duplicates predicate is acceptance's.
(local (defthm fn-cnode-group-listp-names-are-strings
  (implies (fn-cfg-group-listp es)
           (fn-string-listp (fn-cfg-group-all-names es)))
  :hints (("Goal" :in-theory (enable fn-cfg-group-listp fn-cfg-group-all-names
                                     fn-cfg-group-entryp)))))

(local (defthm fn-cnode-member-namep-is-member
  (iff (fn-cfg-member-namep name names) (member-equal name names))
  :hints (("Goal" :in-theory (enable fn-cfg-member-namep)))))

(local (defthm fn-cnode-no-duplicate-namesp-is-no-duplicatesp
  (implies (fn-cfg-no-duplicate-namesp names) (fn-no-duplicatesp names))
  :hints (("Goal" :in-theory (enable fn-cfg-no-duplicate-namesp)))))

(local (defthm fn-cnode-cfgp-domain-facts
  (implies (fn-cfgp config)
           (and (fn-string-listp (fn-cnode-domain-of config))
                (fn-no-duplicatesp (fn-cnode-domain-of config))
                (natp (fn-cfg-capacity (fn-cfg-value config)))))
  :hints (("Goal" :in-theory (enable fn-cfgp fn-cfg-valuep)))))

(defthm fn-cnode-initial-is-state
  (implies (fn-cfgp config)
           (fn-cnode-statep (fn-cnode-initial config)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep fn-node-initial-state
                                   fn-initial-state fn-retain-initial-state)
                                  (fn-cnode-domain-of))
           :use ((:instance fn-node-initial-state-is-state
                            (groups (fn-cnode-domain-of config))
                            (capacity (fn-cfg-capacity (fn-cfg-value config))))
                 (:instance fn-cnode-cfgp-domain-facts)))))

; The default configuration record reproduces the former compiled table: the
; configured node's acceptance state on that record is exactly the old
; `fn-initial-state' of the two experimental groups.  A ground witness cited by
; name, and the compatibility statement for every includer of
; `fn-initial-state' that has not moved yet.
(defthm fn-cnode-initial-of-the-default-record-is-fn-initial-state-of-its-groups
  (equal (fn-node-acceptance
          (fn-cnode-node
           (fn-cnode-initial
            (fn-config-replay 0 (fn-cnode-line-ceiling)
                              (list *fn-cfg-default-record*)))))
         (fn-initial-state '("fn.letters" "fn.test")))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Lifted article transitions.  Each keeps the configuration and, under the
; carried invariant, both coherence equalities.

(defun fn-cnode-prepare (cn cfg-gen generation msgid payload groups
                            obligation-id subject evidence charge)
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil))
  (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
      cn
    (if (or (not (equal cfg-gen (fn-cfg-generation (fn-cnode-config cn))))
            (not (fn-cnode-selection-servedp (fn-cnode-config cn) groups)))
        cn
      (let ((next (fn-node-prepare (fn-cnode-node cn) generation msgid
                                   payload groups obligation-id subject
                                   evidence charge)))
        (if (equal next (fn-cnode-node cn))
            cn
          (fn-cnode-make next (fn-cnode-config cn)))))))

(defun fn-cnode-complete (cn txid generation completion-status)
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil))
  (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
      cn
    (let ((next (fn-node-complete (fn-cnode-node cn) txid generation
                                  completion-status)))
      (if (equal next (fn-cnode-node cn))
          cn
        (fn-cnode-make next (fn-cnode-config cn))))))

(defun fn-cnode-recover (cn txid generation recovery-result)
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil))
  (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
      cn
    (let ((next (fn-node-recover (fn-cnode-node cn) txid generation
                                 recovery-result)))
      (if (equal next (fn-cnode-node cn))
          cn
        (fn-cnode-make next (fn-cnode-config cn))))))

(verify-guards fn-cnode-prepare
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))
(verify-guards fn-cnode-complete
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))
(verify-guards fn-cnode-recover
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))

; The node transitions keep the group list and the capacity.  Stated over the
; node so the configured transitions below inherit them; proof vocabulary.

(local (in-theory (enable fn-node-statep fn-node-stagep fn-node-prepare
                          fn-node-complete fn-node-recover
                          fn-node-pending-matchesp
                          fn-accept-prepare fn-accept-complete fn-accept-recover
                          fn-install-pending fn-clear-pending
                          fn-retain-admit)))

(defthm fn-cnode-node-prepare-keeps-groups-and-capacity
  (and (equal (fn-state-groups
               (fn-node-acceptance
                (fn-node-prepare s generation msgid payload groups
                                 obligation-id subject evidence charge)))
              (fn-state-groups (fn-node-acceptance s)))
       (equal (fn-retain-capacity
               (fn-node-retention
                (fn-node-prepare s generation msgid payload groups
                                 obligation-id subject evidence charge)))
              (fn-retain-capacity (fn-node-retention s)))))

(defthm fn-cnode-node-complete-keeps-groups-and-capacity
  (implies (fn-node-statep s)
           (and (equal (fn-state-groups
                        (fn-node-acceptance
                         (fn-node-complete s txid generation completion-status)))
                       (fn-state-groups (fn-node-acceptance s)))
                (equal (fn-retain-capacity
                        (fn-node-retention
                         (fn-node-complete s txid generation completion-status)))
                       (fn-retain-capacity (fn-node-retention s))))))

(defthm fn-cnode-node-recover-keeps-groups-and-capacity
  (implies (fn-node-statep s)
           (and (equal (fn-state-groups
                        (fn-node-acceptance
                         (fn-node-recover s txid generation recovery-result)))
                       (fn-state-groups (fn-node-acceptance s)))
                (equal (fn-retain-capacity
                        (fn-node-retention
                         (fn-node-recover s txid generation recovery-result)))
                       (fn-retain-capacity (fn-node-retention s))))))

; When prepare stages, the pending article carries exactly the offered groups.
(defthm fn-cnode-node-prepare-stages-the-offered-groups
  (implies (not (equal (fn-node-prepare s generation msgid payload groups
                                        obligation-id subject evidence charge)
                       s))
           (equal (fn-pending-groups
                   (fn-state-pending
                    (fn-node-acceptance
                     (fn-node-prepare s generation msgid payload groups
                                      obligation-id subject evidence charge))))
                  groups)))

; A matching stage's retention (fn-retain-admit of the committed ledger) keeps
; the capacity, and installing a pending article keeps the group list.
(defthm fn-cnode-matching-stage-keeps-capacity
  (implies (fn-node-pending-matchesp s txid generation)
           (equal (fn-retain-capacity
                   (fn-node-stage-retention (fn-node-stage s)))
                  (fn-retain-capacity (fn-node-retention s)))))

(defthm fn-cnode-install-pending-keeps-groups
  (equal (fn-state-groups (fn-install-pending s)) (fn-state-groups s)))

(local (in-theory (disable fn-node-statep fn-node-stagep fn-node-prepare
                           fn-node-complete fn-node-recover
                           fn-node-pending-matchesp
                           fn-accept-prepare fn-accept-complete fn-accept-recover
                           fn-install-pending fn-clear-pending
                           fn-retain-admit)))

(defthm fn-cnode-prepare-preserves-state
  (implies (fn-cnode-statep cn)
           (fn-cnode-statep
            (fn-cnode-prepare cn cfg-gen generation msgid payload groups
                              obligation-id subject evidence charge)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep fn-cnode-prepare)
                                  (fn-node-statep)))))

(defthm fn-cnode-complete-preserves-state
  (implies (fn-cnode-statep cn)
           (fn-cnode-statep (fn-cnode-complete cn txid generation completion-status)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep fn-cnode-complete)
                                  (fn-node-statep)))))

(defthm fn-cnode-recover-preserves-state
  (implies (fn-cnode-statep cn)
           (fn-cnode-statep (fn-cnode-recover cn txid generation recovery-result)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep fn-cnode-recover)
                                  (fn-node-statep)))))

; An untrusted article never changes the configuration (architecture.md).
(defthm fn-cnode-article-transitions-never-change-config
  (and (equal (fn-cnode-config
               (fn-cnode-prepare cn cfg-gen generation msgid payload groups
                                 obligation-id subject evidence charge))
              (fn-cnode-config cn))
       (equal (fn-cnode-config (fn-cnode-complete cn txid generation status))
              (fn-cnode-config cn))
       (equal (fn-cnode-config (fn-cnode-recover cn txid generation result))
              (fn-cnode-config cn)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-prepare fn-cnode-complete
                                   fn-cnode-recover)
                                  (fn-cnode-statep fn-node-prepare
                                   fn-node-complete fn-node-recover)))))

; KEYSTONE.  An article is staged only into groups the pinned configuration
; serves: when prepare stages, the caller's pin is the node's generation and
; the pending article's groups are the offered groups, every one served.
(defthm fn-cnode-prepare-stages-only-served-groups
  (implies (and (fn-cnode-statep cn)
                (not (equal (fn-cnode-prepare cn cfg-gen generation msgid payload
                                              groups obligation-id subject
                                              evidence charge)
                            cn)))
           (and (equal cfg-gen (fn-cfg-generation (fn-cnode-config cn)))
                (fn-subsetp groups (fn-cnode-served cn))
                (equal (fn-pending-groups
                        (fn-state-pending
                         (fn-node-acceptance
                          (fn-cnode-node
                           (fn-cnode-prepare cn cfg-gen generation msgid payload
                                             groups obligation-id subject
                                             evidence charge)))))
                       groups)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cnode-prepare fn-cnode-selection-servedp)
                                  (fn-cnode-statep fn-cnode-served-of
                                   fn-node-prepare)))))

; -----------------------------------------------------------------------------
; The configuration transition

(defun fn-cnode-extend-nexts (names nexts)
  ; The watermark list for a (possibly grown) domain: every name keeps the
  ; watermark it has, a name new to the list starts at 1.
  (declare (xargs :guard t))
  (if (consp names)
      (cons (cons (car names)
                  (let ((n (fn-next-number (car names) nexts)))
                    (if (posp n) n 1)))
            (fn-cnode-extend-nexts (cdr names) nexts))
    nil))

(defun fn-cnode-record-acceptablep (cn record ceiling)
  ; `books/config' admits the record against the node's REAL reservation
  ; total; and no transaction is staged (the design's :group-staged).
  (declare (xargs :guard t))
  (and (fn-cfg-record-acceptablep (fn-cnode-config cn) record
                                  (fn-retain-reserved
                                   (fn-node-retention (fn-cnode-node cn)))
                                  ceiling)
       (null (fn-node-stage (fn-cnode-node cn)))))

(defun fn-cnode-apply-config (cn record ceiling)
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil))
  (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
      cn
    (if (not (fn-cnode-record-acceptablep cn record ceiling))
        cn
      (let* ((node (fn-cnode-node cn))
             (acc (fn-node-acceptance node))
             (ret (fn-node-retention node))
             (config (fn-cfg-apply-record (fn-cnode-config cn) record))
             (domain (fn-cnode-domain-of config)))
        (fn-cnode-make
         (fn-node-make-state
          (fn-make-state domain
                         (fn-cnode-extend-nexts domain (fn-state-nexts acc))
                         (fn-state-articles acc)
                         (fn-state-next-txid acc)
                         nil nil)
          (fn-retain-make-state (fn-cfg-capacity (fn-cfg-value config))
                                (fn-retain-reserved ret)
                                (fn-retain-pins ret)
                                (fn-retain-releases ret))
          nil
          (fn-node-bindings node))
         config)))))

(verify-guards fn-cnode-apply-config)

; Refusal changes nothing: the same fact `fn-cfg-inadmissible-record-is-not-
; applied' states for the configuration fold.  -by-definition; not a rule.
(defthm fn-cnode-inadmissible-config-changes-nothing
  (implies (not (fn-cnode-record-acceptablep cn record ceiling))
           (equal (fn-cnode-apply-config cn record ceiling) cn))
  :rule-classes nil)

; --- vocabulary for the preservation proof ---------------------------------

(local (defthm fn-cnode-extend-nexts-for-p
  (fn-nexts-for-p names (fn-cnode-extend-nexts names nexts))))

(local (defthm fn-cnode-next-number-of-extend-nexts
  (implies (member-equal name names)
           (equal (fn-next-number name (fn-cnode-extend-nexts names nexts))
                  (let ((n (fn-next-number name nexts)))
                    (if (posp n) n 1))))))

; Hypothesis order matters: the rewriter binds `b' from the second subset
; fact in the context (an induction hypothesis) and then rewrites the first.
(local (defthm fn-cnode-subsetp-transitive
  (implies (and (fn-subsetp b c) (fn-subsetp a b))
           (fn-subsetp a c))
  :hints (("Goal" :induct (fn-subsetp a b)))))

(local (defthm fn-cnode-memberships-below-extend
  (implies (and (fn-memberships-below-nextsp ms nexts)
                (fn-membership-listp gs ms)
                (fn-subsetp gs names)
                (fn-subsetp gs dom)
                (fn-nexts-for-p dom nexts))
           (fn-memberships-below-nextsp ms (fn-cnode-extend-nexts names nexts)))
  :hints (("Goal" :induct (fn-membership-listp gs ms)))))

(local (defthm fn-cnode-articles-below-extend
  (implies (and (fn-articles-below-nextsp arts nexts)
                (fn-article-listp dom arts)
                (fn-subsetp dom names)
                (fn-nexts-for-p dom nexts))
           (fn-articles-below-nextsp arts (fn-cnode-extend-nexts names nexts)))
  :hints (("Goal" :induct (fn-article-listp dom arts)
           :in-theory (enable fn-articlep)))))

(local (defthm fn-cnode-article-listp-monotone
  (implies (and (fn-article-listp dom arts)
                (fn-subsetp dom names))
           (fn-article-listp names arts))
  :hints (("Goal" :induct (fn-article-listp dom arts)
           :in-theory (enable fn-articlep)))))

; The domain only grows: retirement keeps every name, creation appends or
; revives in place.
(local (defthm fn-cnode-retire-keeps-all-names
  (equal (fn-cfg-group-all-names (fn-cfg-groups-retire es gen name))
         (fn-cfg-group-all-names es))
  :hints (("Goal" :in-theory (enable fn-cfg-groups-retire
                                     fn-cfg-group-all-names)))))

(local (defthm fn-cnode-create-grows-all-names
  (fn-subsetp (fn-cfg-group-all-names es)
              (fn-cfg-group-all-names
               (fn-cfg-groups-create es gen stamp name policy)))
  :hints (("Goal" :in-theory (enable fn-cfg-groups-create
                                     fn-cfg-group-all-names)))))

(local (defthm fn-cnode-apply-delta-grows-all-names
  (fn-subsetp (fn-cfg-group-all-names (fn-cfg-groups v))
              (fn-cfg-group-all-names
               (fn-cfg-groups (fn-cfg-apply-delta v gen stamp d))))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-set-groups)))))

(local (defthm fn-cnode-apply-grows-all-names
  (fn-subsetp (fn-cfg-group-all-names (fn-cfg-groups v))
              (fn-cfg-group-all-names
               (fn-cfg-groups (fn-cfg-apply v gen stamp deltas))))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (e/d (fn-cfg-apply) (fn-cfg-apply-delta))))))

; Admissibility keeps the reservation total inside the capacity: a
; set-capacity below it is :capacity-below-reserved, every other delta keeps
; the capacity.
(local (defthm fn-cnode-apply-delta-capacity
  (implies (and (natp reserved)
                (<= reserved (fn-cfg-capacity v))
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (<= reserved (fn-cfg-capacity (fn-cfg-apply-delta v gen stamp d))))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-set-groups
                                     fn-cfg-delta-reason)))))

(local (defthm fn-cnode-apply-capacity
  (implies (and (natp reserved)
                (<= reserved (fn-cfg-capacity v))
                (fn-cfg-admissiblep v gen stamp reserved ceiling deltas))
           (<= reserved (fn-cfg-capacity (fn-cfg-apply v gen stamp deltas))))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (e/d (fn-cfg-apply fn-cfg-admissiblep
                            fn-cfg-admissible-reason)
                           (fn-cfg-apply-delta fn-cfg-delta-reason))))))

(local (defthm fn-cnode-apply-record-domain-and-capacity
  (implies (and (fn-cfgp cfg)
                (natp reserved)
                (<= reserved (fn-cfg-capacity (fn-cfg-value cfg)))
                (fn-cfg-record-acceptablep cfg r reserved ceiling))
           (and (fn-subsetp (fn-cnode-domain-of cfg)
                            (fn-cnode-domain-of (fn-cfg-apply-record cfg r)))
                (<= reserved
                    (fn-cfg-capacity (fn-cfg-value (fn-cfg-apply-record cfg r))))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-record fn-cfg-record-acceptablep)
                                  (fn-cfg-apply fn-cfg-admissiblep))))))

(local (in-theory (disable fn-cnode-domain-of)))

(defthm fn-cnode-apply-config-preserves-state
  (implies (fn-cnode-statep cn)
           (fn-cnode-statep (fn-cnode-apply-config cn record ceiling)))
  :hints (("Goal"
           :in-theory (e/d (fn-cnode-statep fn-node-statep fn-statep
                            fn-retain-statep)
                           (fn-cfg-apply-record fn-cfg-record-acceptablep
                            fn-cfgp fn-cfg-valuep fn-cnode-extend-nexts
                            fn-article-listp fn-articles-below-nextsp
                            fn-node-articles-have-archive-bindingsp))
           :use ((:instance fn-cnode-apply-record-domain-and-capacity
                            (cfg (fn-cnode-config cn))
                            (r record)
                            (reserved (fn-retain-reserved
                                       (fn-node-retention (fn-cnode-node cn)))))
                 (:instance fn-cnode-cfgp-domain-facts
                            (config (fn-cfg-apply-record (fn-cnode-config cn)
                                                         record)))))))

; KEYSTONE.  A group retired at generation g keeps its watermark and every
; article already bound: the configuration transition leaves the article list
; untouched, the domain never shrinks, and every name already in the domain
; (a retired one included) keeps its exact watermark.
(defthm fn-cnode-apply-config-keeps-watermarks-and-articles
  (implies (and (fn-cnode-statep cn)
                (fn-cnode-record-acceptablep cn record ceiling))
           (let ((next (fn-cnode-apply-config cn record ceiling)))
             (and (equal (fn-state-articles (fn-node-acceptance (fn-cnode-node next)))
                         (fn-state-articles (fn-node-acceptance (fn-cnode-node cn))))
                  (fn-subsetp (fn-cnode-domain cn) (fn-cnode-domain next))
                  (implies (member-equal name (fn-cnode-domain cn))
                           (equal (fn-next-number
                                   name (fn-state-nexts (fn-node-acceptance (fn-cnode-node next))))
                                  (fn-next-number
                                   name (fn-state-nexts (fn-node-acceptance (fn-cnode-node cn)))))))))
  :hints (("Goal"
           :in-theory (e/d (fn-cnode-statep fn-node-statep fn-statep)
                           (fn-cfg-apply-record fn-cfg-record-acceptablep
                            fn-cfgp fn-cfg-valuep fn-cnode-extend-nexts
                            fn-article-listp fn-articles-below-nextsp
                            fn-node-articles-have-archive-bindingsp
                            fn-retain-statep))
           :use ((:instance fn-cnode-apply-record-domain-and-capacity
                            (cfg (fn-cnode-config cn))
                            (r record)
                            (reserved (fn-retain-reserved
                                       (fn-node-retention (fn-cnode-node cn)))))
                 (:instance fn-member-of-subset
                            (xs (fn-cnode-domain cn))
                            (ys (fn-cnode-domain-of
                                 (fn-cfg-apply-record (fn-cnode-config cn) record)))
                            (x name))
                 (:instance fn-next-positive
                            (configured (fn-cnode-domain cn))
                            (nexts (fn-state-nexts (fn-node-acceptance (fn-cnode-node cn))))
                            (group name))))))

(defthm fn-cnode-apply-config-bumps-the-generation
  (implies (fn-cnode-record-acceptablep cn record ceiling)
           (equal (fn-cfg-generation (fn-cnode-config (fn-cnode-apply-config cn record ceiling)))
                  (if (fn-cnode-statep cn)
                      (+ 1 (fn-cfg-generation (fn-cnode-config cn)))
                    (fn-cfg-generation (fn-cnode-config cn)))))
  :hints (("Goal" :in-theory (disable fn-cfg-apply-record fn-cfg-record-acceptablep
                                      fn-cnode-statep))))

; -----------------------------------------------------------------------------
; Replay over the two-kind stream

(defun fn-cnode-apply-record (cn record)
  ; One article record: served-table admission, then the node machine's own
  ; replay step.  NIL is a refusal, never a partial state.
  (declare (xargs :guard (and (fn-cnode-statep cn) (fn-record-p record))
                  :verify-guards nil))
  (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
      nil
    (if (not (fn-cnode-selection-servedp (fn-cnode-config cn)
                                         (fn-record-groups record)))
        nil
      (let ((next (fn-replay-apply-record (fn-cnode-node cn) record)))
        (if (mbe :logic (not (fn-node-statep next)) :exec (not (consp next)))
            nil
          (fn-cnode-make next (fn-cnode-config cn)))))))

; `fn-store-event-p' is withdrawn on export (books/store-events); this
; conjecture needs it to reach the used lemma's hypothesis, and its three
; statement kind recognizers stay closed so the statement codec does not
; unfold on every branch (books/config-records carries the same pair).
(verify-guards fn-cnode-apply-record
  :hints (("Goal" :use ((:instance fn-replay-apply-record-statep-iff-consp
                                   (node (fn-cnode-node cn))))
           ;; `fn-record-p' closed as well: the conjecture has it as a
           ;; hypothesis, and that literal is the disjunct of
           ;; `fn-store-event-p' the used lemma needs.  Open, the record codec
           ;; split the goal 743 ways, 3.3 s
           ;; (planning/evidence/misc-books-cost-2026-09-23.md).
           :in-theory (e/d (fn-cnode-statep fn-store-event-p)
                           (fn-stxe-p fn-stxk-p fn-stxa-p fn-record-p
                            fn-store-retention-event-p
                            fn-node-statep fn-replay-apply-record)))))

(local (defthm fn-cnode-advance-keeps-groups
  (equal (fn-state-groups
          (fn-node-acceptance (fn-replay-advance-txid node recorded-txid)))
         (fn-state-groups (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

; Definition bridge for the release-record replay arm.  Release changes the
; reservation and evidence lists but carries the configured capacity exactly.
(local
 (defthm fn-cnode-retain-release-keeps-capacity-by-definition
   (equal (fn-retain-capacity
           (fn-retain-release retention id subject kind evidence))
          (fn-retain-capacity retention))
   :hints (("Goal" :in-theory (enable fn-retain-release)))))

(local
 (defthm fn-cnode-retain-admit-keeps-capacity-by-definition
   (equal (fn-retain-capacity
           (fn-retain-admit retention id subject kind evidence charge))
          (fn-retain-capacity retention))
   :hints (("Goal" :in-theory (enable fn-retain-admit)))))

(local (defthm fn-cnode-replay-apply-record-keeps-groups-and-capacity
  (implies (and (fn-node-statep node)
                (consp (fn-replay-apply-record node record)))
           (and (equal (fn-state-groups
                        (fn-node-acceptance (fn-replay-apply-record node record)))
                       (fn-state-groups (fn-node-acceptance node)))
                (equal (fn-retain-capacity
                        (fn-node-retention (fn-replay-apply-record node record)))
                       (fn-retain-capacity (fn-node-retention node)))))
  ;; The event recognizers and the composite decoder stay closed: the three
  ;; arms need only their kind test as a literal.  Open, they and the
  ;; retention arm's release test split `Goal' 1 536 ways, 6.8 s
  ;; (planning/evidence/misc-books-cost-2026-09-23.md).
  :hints (("Goal"
           :in-theory (e/d (fn-replay-apply-record)
                           (fn-node-prepare fn-node-complete
                            fn-node-pending-matchesp
                            fn-replay-advance-txid
                            fn-record-record-vocabulary
                            fn-record-shape-vocabulary
                            fn-stxa-p fn-stxe-p fn-stxk-p
                            fn-store-retention-event-p
                            fn-replay-composite-record))))))

(defthm fn-cnode-apply-record-keeps-config
  (implies (consp (fn-cnode-apply-record cn record))
           (equal (fn-cnode-config (fn-cnode-apply-record cn record))
                  (fn-cnode-config cn)))
  :hints (("Goal" :in-theory (disable fn-cnode-statep fn-replay-apply-record
                                      fn-node-statep))))

(defthm fn-cnode-apply-record-preserves-state
  (implies (and (fn-cnode-statep cn)
                (consp (fn-cnode-apply-record cn record)))
           (fn-cnode-statep (fn-cnode-apply-record cn record)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep)
                                  (fn-node-statep fn-replay-apply-record)))))

(defthm fn-cnode-apply-record-statep-iff-consp
  (implies (fn-cnode-statep cn)
           (iff (fn-cnode-statep (fn-cnode-apply-record cn record))
                (consp (fn-cnode-apply-record cn record))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep)
                                  (fn-node-statep fn-replay-apply-record
                                   fn-cnode-apply-record-preserves-state))
           :use fn-cnode-apply-record-preserves-state)))

(defun fn-cnode-replay-loop (cn ceiling js expected)
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil
                  :measure (len js)))
  (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
      (fn-replay-fault cn expected :invalid-initial-node)
    (if (consp js)
        (let ((j (car js)))
          (if (not (fn-jrec-p j))
              (fn-replay-fault cn expected :invalid-record)
            (if (not (equal (fn-jrec-sequence j) expected))
                (fn-replay-fault cn expected :sequence)
              (if (equal (fn-jrec-kind j) :config)
                  (if (not (fn-cnode-record-acceptablep cn (fn-jrec-body j) ceiling))
                      (fn-replay-fault cn expected :config-refusal)
                    (fn-cnode-replay-loop
                     (fn-cnode-apply-config cn (fn-jrec-body j) ceiling)
                     ceiling (cdr js) (1+ expected)))
                (let ((next (fn-cnode-apply-record cn (fn-jrec-body j))))
                  (if (mbe :logic (not (fn-cnode-statep next))
                           :exec (not (consp next)))
                      (fn-replay-fault cn expected :node-refusal)
                    (fn-cnode-replay-loop next ceiling (cdr js) (1+ expected))))))))
      (if (null js)
          (fn-replay-ok cn expected)
        (fn-replay-fault cn expected :improper-record-list)))))

(verify-guards fn-cnode-replay-loop
  :hints (("Goal"
           :use ((:instance fn-cnode-apply-record-statep-iff-consp
                            (record (fn-jrec-body (car js)))))
           :in-theory (e/d (fn-jrec-p)
                           (fn-cnode-statep fn-cnode-apply-record
                            fn-cnode-apply-config fn-cnode-record-acceptablep)))))

(defun fn-cnode-config-jrecs (records)
  ; A configuration-only history as the two-kind stream.
  (declare (xargs :guard t))
  (if (consp records)
      (cons (fn-jrec-make :config (fn-cfg-record-sequence (car records))
                          (car records))
            (fn-cnode-config-jrecs (cdr records)))
    nil))

(defun fn-cnode-replay (js)
  ; The entry point: the empty configuration, the ceiling cited once.
  (declare (xargs :guard t :verify-guards nil))
  (let ((cn (fn-cnode-initial (fn-cfg-initial))))
    (if (fn-cnode-statep cn)
        (fn-cnode-replay-loop cn (fn-cnode-line-ceiling) js 0)
      (fn-replay-fault cn 0 :invalid-initial-node))))

(verify-guards fn-cnode-replay)

(defun fn-cnode-config-replay (records)
  ; What the host replays at open: the configuration history alone.
  (declare (xargs :guard t))
  (fn-cnode-replay (fn-cnode-config-jrecs records)))

; KEYSTONE.  Replay is a fold: the result over a history split anywhere is
; the result of resuming from the prefix's result, which is what makes a
; resumed recovery deterministic.
(defthm fn-cnode-replay-loop-splits-at-any-prefix
  (implies (true-listp a)
           (equal (fn-cnode-replay-loop cn ceiling (append a b) expected)
                  (let ((mid (fn-cnode-replay-loop cn ceiling a expected)))
                    (if (equal (fn-replay-result-kind mid) :ok)
                        (fn-cnode-replay-loop (fn-replay-result-node mid) ceiling b
                                              (fn-replay-result-sequence mid))
                      mid))))
  :hints (("Goal" :induct (fn-cnode-replay-loop cn ceiling a expected)
           :in-theory (e/d (fn-cnode-replay-loop)
                           (fn-cnode-statep fn-cnode-apply-record
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-jrec-p)))))

; The generation never goes down along a replay: a configuration record bumps
; it by one, an article record leaves it alone, a fault stops at the last
; good node.
(defthm fn-cnode-replay-loop-generation-is-monotone
  (<= (fn-cfg-generation (fn-cnode-config cn))
      (fn-cfg-generation
       (fn-cnode-config
        (fn-replay-result-node (fn-cnode-replay-loop cn ceiling js expected)))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cnode-replay-loop cn ceiling js expected)
           :in-theory (e/d (fn-cnode-replay-loop)
                           (fn-cnode-statep fn-cnode-apply-record
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-jrec-p)))))

; KEYSTONE (STO-004).  The generation recovered from a prefix of the history
; is at most the generation the whole history reaches.  `<=', never `=': an
; unacknowledged reconfiguration in the lost tail may be absent.
(defthm fn-cnode-recovered-generation-is-at-most-the-live-generation
  (implies (true-listp a)
           (<= (fn-cfg-generation
                (fn-cnode-config
                 (fn-replay-result-node (fn-cnode-replay-loop cn ceiling a expected))))
               (fn-cfg-generation
                (fn-cnode-config
                 (fn-replay-result-node
                  (fn-cnode-replay-loop cn ceiling (append a b) expected))))))
  :hints (("Goal" :use fn-cnode-replay-loop-splits-at-any-prefix
           :in-theory (disable fn-cnode-replay-loop
                               fn-cnode-replay-loop-splits-at-any-prefix))))

; -----------------------------------------------------------------------------
; Export theory.  Keystones and record lemmas stay enabled; the recognizer,
; the tables, the transitions and the loop are proof vocabulary.

(deftheory fn-cnode-vocabulary
  '((:d fn-cnode-served-of) (:d fn-cnode-domain-of) (:d fn-cnode-served)
    (:d fn-cnode-domain) (:d fn-cnode-selection-servedp)
    (:d fn-cnode-line-ceiling) (:d fn-cnode-statep) (:d fn-cnode-initial)
    (:d fn-cnode-prepare) (:d fn-cnode-complete) (:d fn-cnode-recover)
    (:d fn-cnode-extend-nexts) (:d fn-cnode-record-acceptablep)
    (:d fn-cnode-apply-config) (:d fn-cnode-apply-record)
    (:d fn-cnode-replay-loop) (:d fn-cnode-config-jrecs) (:d fn-cnode-replay)
    (:d fn-cnode-config-replay)
    fn-cnode-node-prepare-keeps-groups-and-capacity
    fn-cnode-node-complete-keeps-groups-and-capacity
    fn-cnode-node-recover-keeps-groups-and-capacity
    fn-cnode-apply-config-bumps-the-generation))

(in-theory (disable fn-cnode-vocabulary))
