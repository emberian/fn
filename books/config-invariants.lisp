; fn: what configuration replay preserves.
;
; Five properties, each of which a reconfiguration design has to earn before
; the node may carry a configuration at all:
;
;   1. replay is a fold          -- splitting a record history at any prefix
;                                   gives the same configuration, which is what
;                                   "replay is deterministic" has to mean for a
;                                   recovery that resumes from a crash image;
;   2. the generation counts configuration records, not journal records;
;   3. retirement never deletes: a retired group keeps its entry, its creation
;      stamp and its local-number watermark, and re-creating the name resumes
;      the numbering (NNT-006, made structural);
;   4. an admissible change preserves the value's typed invariant, so a
;      configuration can never name a bound the codec cannot represent;
;   5. a crash image is a prefix, so the recovered generation is at most the
;      live one (STO-004's `<=', never `=').
;
; Nothing here is a claim about the node: the node transition is proposed in
; planning/lanes/HANDOFF-w4-config-records.md and belongs to the store cluster.

(in-package "ACL2")
(include-book "config")

(local (in-theory (enable fn-cfg-vocabulary)))

; -----------------------------------------------------------------------------
; The floor is well typed

(defthm fn-cfg-empty-value-is-a-value
  (fn-cfg-valuep (fn-cfg-empty-value)))

(defthm fn-cfg-initial-is-a-configuration
  (fn-cfgp (fn-cfg-initial)))

(defthm fn-cfg-initial-serves-no-group
  (equal (fn-cfg-group-names (fn-cfg-value (fn-cfg-initial)) gen) nil))

; -----------------------------------------------------------------------------
; 3.  Retirement never deletes

(defthm fn-cfg-groups-retire-keeps-the-length
  (equal (len (fn-cfg-groups-retire es gen name)) (len es)))

(defthm fn-cfg-groups-retire-keeps-the-names
  (equal (fn-cfg-group-all-names (fn-cfg-groups-retire es gen name))
         (fn-cfg-group-all-names es)))

(defthm fn-cfg-groups-retire-keeps-the-watermark
  (implies (consp (fn-cfg-group-find es name))
           (and (consp (fn-cfg-group-find
                        (fn-cfg-groups-retire es gen name) name))
                (equal (fn-cfg-group-next
                        (fn-cfg-group-find
                         (fn-cfg-groups-retire es gen name) name))
                       (fn-cfg-group-next (fn-cfg-group-find es name)))
                (equal (fn-cfg-group-created-stamp
                        (fn-cfg-group-find
                         (fn-cfg-groups-retire es gen name) name))
                       (fn-cfg-group-created-stamp
                        (fn-cfg-group-find es name))))))

(defthm fn-cfg-groups-create-resumes-the-watermark
  ; Re-creating a retired name revives the entry in place and keeps its
  ; retained next-number, rather than appending a second entry.
  (implies (consp (fn-cfg-group-find es name))
           (and (equal (len (fn-cfg-groups-create es gen stamp name policy))
                       (len es))
                (equal (fn-cfg-group-next
                        (fn-cfg-group-find
                         (fn-cfg-groups-create es gen stamp name policy)
                         name))
                       (fn-cfg-group-next (fn-cfg-group-find es name))))))

(defthm fn-cfg-groups-create-keeps-the-names-or-adds-one
  ; Over a group list only: `fn-cfg-group-find' answers `nil' both for "no such
  ; name" and for a found non-cons entry, so on `es' = (nil) with `name' nil
  ; the creation replaces in place while the right-hand side appends.
  (implies (fn-cfg-group-listp es)
           (equal (fn-cfg-group-all-names (fn-cfg-groups-create es gen stamp
                                                                name policy))
                  (if (consp (fn-cfg-group-find es name))
                      (fn-cfg-group-all-names es)
                    (append (fn-cfg-group-all-names es) (list name))))))

; -----------------------------------------------------------------------------
; 4.  An admissible change preserves the typed value

(defthm fn-cfg-group-find-is-a-member-or-nil
  (implies (and (fn-cfg-group-listp es) (consp (fn-cfg-group-find es name)))
           (fn-cfg-group-entryp (fn-cfg-group-find es name))))

(defthm fn-cfg-groups-retire-preserves-group-listp
  ; The retired entry must be live at `gen': an entry retired before its own
  ; creation generation is not a group entry (created-gen <= retired-gen), so
  ; the statement without this hypothesis is false.  The hypothesis is exactly
  ; `fn-cfg-group-livep' opened, which is what admissibility checks.
  (implies (and (fn-cfg-group-listp es) (fn-record-uint32p gen)
                (fn-cfg-entry-livep (fn-cfg-group-find es name) gen))
           (fn-cfg-group-listp (fn-cfg-groups-retire es gen name))))

(defthm fn-cfg-groups-create-preserves-group-listp
  (implies (and (fn-cfg-group-listp es)
                (fn-record-group-namep name)
                (fn-record-uint32p gen)
                (fn-cfg-stampp stamp)
                (fn-cfg-labelp policy))
           (fn-cfg-group-listp
            (fn-cfg-groups-create es gen stamp name policy))))

(local (defthm fn-cfg-member-namep-of-append
  (equal (fn-cfg-member-namep x (append a b))
         (or (fn-cfg-member-namep x a) (fn-cfg-member-namep x b)))))

(defthm fn-cfg-no-duplicates-of-append-one
  (implies (and (fn-cfg-no-duplicate-namesp names)
                (not (fn-cfg-member-namep name names)))
           (fn-cfg-no-duplicate-namesp (append names (list name)))))

(defthm fn-cfg-group-find-nil-means-not-a-name
  ; Over a group list, for the same reason as the creation lemma above.
  (implies (and (fn-cfg-group-listp es)
                (not (consp (fn-cfg-group-find es name))))
           (not (fn-cfg-member-namep name (fn-cfg-group-all-names es)))))

(local (defthm fn-cfg-create-adds-no-other-name
  (implies (and (not (fn-cfg-member-namep x (fn-cfg-group-all-names es)))
                (not (equal x name)))
           (not (fn-cfg-member-namep
                 x (fn-cfg-group-all-names
                    (fn-cfg-groups-create es gen stamp name policy)))))))

(defthm fn-cfg-groups-create-preserves-no-duplicates
  (implies (fn-cfg-no-duplicate-namesp (fn-cfg-group-all-names es))
           (fn-cfg-no-duplicate-namesp
            (fn-cfg-group-all-names
             (fn-cfg-groups-create es gen stamp name policy)))))

(defthm fn-cfg-groups-retire-preserves-no-duplicates
  (implies (fn-cfg-no-duplicate-namesp (fn-cfg-group-all-names es))
           (fn-cfg-no-duplicate-namesp
            (fn-cfg-group-all-names (fn-cfg-groups-retire es gen name)))))

(defthm fn-cfg-row-upsert-preserves-row-listp
  (implies (and (fn-cfg-row-listp rows) (fn-cfg-rowp row))
           (fn-cfg-row-listp (fn-cfg-row-upsert rows row))))

(defthm fn-cfg-row-upsert-preserves-limits-withinp
  (implies (and (fn-cfg-limits-withinp rows)
                (<= (nfix (fn-cfg-limit-value row))
                    (fn-cfg-limit-ceiling (fn-cfg-limit-slot row))))
           (fn-cfg-limits-withinp (fn-cfg-row-upsert rows row))))

(defthm fn-cfg-row-replace-key-preserves-row-listp
  (implies (and (fn-cfg-row-listp rows) (fn-cfg-rowp row))
           (fn-cfg-row-listp (fn-cfg-row-replace-key rows row))))

(defthm fn-cfg-row-replace-key-looks-up-the-row
  (equal (fn-cfg-row-lookup (fn-cfg-row-replace-key rows row) (fn-cfg-row-a row))
         row)
  :hints (("Goal" :in-theory (enable fn-cfg-row-replace-key fn-cfg-row-lookup))))

; KEYSTONE (a policy slot holds the value set last).  Over
; fn-cfg-apply-delta, the configuration fold every policy record goes
; through: after a :set-policy delta for SLOT with value ID, the policy read
; for SLOT is ID, whatever was set before.  Teeth: tests/acl2/config-tests.lisp
; (bound-logins then open reads open; upsert, the old fold, reads the first).
; It has no hypothesis, so it has no must-fail.
(defthm fn-cfg-set-policy-sets-the-policy
  (equal (fn-cfg-policy (fn-cfg-apply-delta v gen stamp (fn-cfg-set-policy slot id))
                        slot)
         id)
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-delta fn-cfg-set-policy fn-cfg-policy)
                                  (fn-cfg-row-replace-key-looks-up-the-row
                                   fn-cfg-row-replace-key fn-cfg-row-lookup))
           :use ((:instance fn-cfg-row-replace-key-looks-up-the-row
                            (rows (fn-cfg-policies v))
                            (row (fn-cfg-row-make slot id "" 0)))))))

; The two peer arms (:set-peer, :remove-peer) rebuild the peers slot from a
; keyed selection and the delta's rows; both stay row lists.  Local: no
; `append'-backchaining rule leaves this book.
(local (defthm fn-cfg-rows-without-key-is-row-listp
  (implies (fn-cfg-row-listp rows)
           (fn-cfg-row-listp (fn-cfg-rows-without-key rows a)))))
(local (defthm fn-cfg-row-listp-of-append
  (implies (and (fn-cfg-row-listp a) (fn-cfg-row-listp b))
           (fn-cfg-row-listp (append a b)))))

;; C2: the authorities slot stays a row list under a grant and a revoke.
(local (defthm fn-cfg-rows-without-pair-is-row-listp
  (implies (fn-cfg-row-listp rows)
           (fn-cfg-row-listp (fn-cfg-rows-without-pair rows a b)))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-without-pair)))))
(local (defthm fn-cfg-grant-verb-is-a-label
  (implies (and (fn-cfg-row-listp rows) (consp rows))
           (fn-cfg-labelp (fn-cfg-grant-verb rows)))
  :hints (("Goal" :in-theory (enable fn-cfg-grant-verb fn-cfg-ag-car)))))
(local (defthm fn-cfg-grant-verb-of-nil-is-nil
  (implies (not (consp rows))
           (equal (fn-cfg-grant-verb rows) nil))
  :hints (("Goal" :in-theory (enable fn-cfg-grant-verb fn-cfg-ag-car
                                     fn-cfg-row-c)))))

(defthm fn-cfg-apply-delta-preserves-valuep
  ; `fn-record-uint32p' is opened for the `:set-limit' arm (`nfix' of a
  ; uint32 is itself); `fn-record-string-octets' is kept closed so a label
  ; stays the opaque term `fn-cfg-labelp' names rather than splitting on
  ; `stringp' through `coerce'.
  (implies (and (fn-cfg-valuep v)
                (fn-cfg-deltap d)
                (fn-record-uint32p gen)
                (fn-cfg-stampp stamp)
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (fn-cfg-valuep (fn-cfg-apply-delta v gen stamp d)))
  :hints (("Goal" :in-theory (e/d (fn-record-uint32p)
                                  (fn-record-string-octets)))))

(defthm fn-cfg-apply-preserves-valuep
  (implies (and (fn-cfg-valuep v)
                (fn-cfg-delta-listp deltas)
                (fn-record-uint32p gen)
                (fn-cfg-stampp stamp)
                (fn-cfg-admissiblep v gen stamp reserved ceiling deltas))
           (fn-cfg-valuep (fn-cfg-apply v gen stamp deltas)))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (disable fn-cfg-apply-delta fn-cfg-delta-reason
                               fn-cfg-valuep fn-cfg-deltap))))

(defthm fn-cfg-apply-record-is-a-configuration
  (implies (and (fn-cfgp cfg)
                (fn-cfg-record-acceptablep cfg r reserved ceiling))
           (fn-cfgp (fn-cfg-apply-record cfg r)))
  :hints (("Goal" :in-theory (disable fn-cfg-apply fn-cfg-admissiblep
                                      fn-cfg-valuep))))

(defthm fn-config-replay-loop-result-is-typed
  (implies (fn-cfgp cfg)
           (or (equal (fn-config-replay-loop cfg reserved ceiling records)
                      :fault)
               (fn-cfgp (fn-config-replay-loop cfg reserved ceiling records))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling records)
           :in-theory (disable fn-cfg-apply-record fn-cfgp
                               fn-cfg-record-acceptablep))))

(defthm fn-config-replay-result-is-typed
  (or (equal (fn-config-replay reserved ceiling records) :fault)
      (fn-cfgp (fn-config-replay reserved ceiling records)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-config-replay-loop-result-is-typed
                            (cfg (fn-cfg-initial))))
           :in-theory (disable fn-cfgp fn-config-replay-loop
                               fn-cfg-initial))))

; -----------------------------------------------------------------------------
; 1.  Replay is a fold

(defthm fn-config-replay-loop-splits-at-any-prefix
  ; What "replay is deterministic" has to mean operationally: a recovery that
  ; resumes after a prefix reaches the same configuration as one that replays
  ; the whole history in a single pass.
  (implies (and (true-listp a)
                (not (equal (fn-config-replay-loop cfg reserved ceiling a)
                            :fault)))
           (equal (fn-config-replay-loop cfg reserved ceiling (append a b))
                  (fn-config-replay-loop
                   (fn-config-replay-loop cfg reserved ceiling a)
                   reserved ceiling b)))
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling a)
           :in-theory (disable fn-cfg-apply-record
                               fn-cfg-record-acceptablep))))

; -----------------------------------------------------------------------------
; 2.  The generation counts configuration records

(defthm fn-cfg-apply-record-bumps-the-generation-by-one
  (implies (fn-cfg-record-acceptablep cfg r reserved ceiling)
           (equal (fn-cfg-generation (fn-cfg-apply-record cfg r))
                  (+ 1 (fn-cfg-generation cfg))))
  :hints (("Goal" :in-theory (disable fn-cfg-apply fn-cfg-admissiblep
                                      fn-cfg-recordp fn-cfgp))))

(defthm fn-config-replay-loop-generation-counts-records
  ; The starting generation must be a number: on the empty history the loop
  ; returns `cfg' itself, and `(+ g 0)' is not `g' for a non-numeric `g'.
  ; `fn-config-replay' starts from generation 0, which is what the entry-point
  ; keystone below instantiates.
  (implies (and (acl2-numberp (fn-cfg-generation cfg))
                (not (equal (fn-config-replay-loop cfg reserved ceiling
                                                   records)
                            :fault)))
           (equal (fn-cfg-generation
                   (fn-config-replay-loop cfg reserved ceiling records))
                  (+ (fn-cfg-generation cfg) (len records))))
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling records)
           :in-theory (disable fn-cfg-apply-record
                               fn-cfg-record-acceptablep))))

(defthm fn-config-replay-generation-counts-config-records
  ; A thousand posts leave the generation where it was: only a configuration
  ; record advances it, and each one advances it by exactly one.
  (implies (not (equal (fn-config-replay reserved ceiling records) :fault))
           (equal (fn-cfg-generation
                   (fn-config-replay reserved ceiling records))
                  (len records)))
  :hints (("Goal"
           :use ((:instance fn-config-replay-loop-generation-counts-records
                            (cfg (fn-cfg-initial))))
           :in-theory (disable fn-config-replay-loop
                               fn-config-replay-loop-generation-counts-records))))

; -----------------------------------------------------------------------------
; 5.  Recovery is `<=', never `='

(defun fn-cfg-take (n xs)
  ; A crash image is a prefix of the committed history; per STO-004 an
  ; unacknowledged tail may be absent.  Total.
  (declare (xargs :guard t))
  (if (not (posp n))
      nil
    (if (consp xs)
        (cons (car xs) (fn-cfg-take (- n 1) (cdr xs)))
      nil)))

(defthm fn-cfg-take-is-a-true-list
  (true-listp (fn-cfg-take n xs)))

(defthm fn-cfg-take-length-is-at-most
  (<= (len (fn-cfg-take n xs)) (len xs))
  :rule-classes :linear)

(defthm fn-cfg-recovered-generation-is-at-most-the-live-generation
  ; STO-004: the recovered generation is at most the live one.  The equality
  ; direction is NOT available and is not claimed: an unacknowledged
  ; reconfiguration at the tail of the image may be absent.
  (implies (and (not (equal (fn-config-replay reserved ceiling records)
                            :fault))
                (not (equal (fn-config-replay reserved ceiling
                                              (fn-cfg-take n records))
                            :fault)))
           (<= (fn-cfg-generation
                (fn-config-replay reserved ceiling (fn-cfg-take n records)))
               (fn-cfg-generation
                (fn-config-replay reserved ceiling records))))
  :hints (("Goal"
           :use ((:instance fn-config-replay-generation-counts-config-records)
                 (:instance fn-config-replay-generation-counts-config-records
                            (records (fn-cfg-take n records))))
           :in-theory (disable fn-config-replay fn-cfg-take
                               fn-config-replay-generation-counts-config-records))))

; -----------------------------------------------------------------------------
; Inadmissibility changes nothing.
;
; The refusal direction of atomicity: a record whose delta list is not
; admissible on the replayed value leaves the configuration exactly as it was,
; because the loop faults rather than applying a prefix of the list.

(defthm fn-cfg-inadmissible-record-is-not-applied
  (implies (not (fn-cfg-record-acceptablep cfg r reserved ceiling))
           (equal (fn-config-replay-loop cfg reserved ceiling (cons r rest))
                  :fault)))

; -----------------------------------------------------------------------------
; Export theory.
;
; Keystones stay enabled: the five properties above, the typed-floor lemmas and
; the retirement/creation watermark facts.  The component preservation lemmas
; are proof vocabulary for a book that extends the transition.

(deftheory fn-cfg-invariants-vocabulary
  '(fn-cfg-group-find-is-a-member-or-nil
    fn-cfg-groups-retire-preserves-group-listp
    fn-cfg-groups-create-preserves-group-listp
    fn-cfg-no-duplicates-of-append-one
    fn-cfg-group-find-nil-means-not-a-name
    fn-cfg-groups-create-preserves-no-duplicates
    fn-cfg-groups-retire-preserves-no-duplicates
    fn-cfg-row-upsert-preserves-row-listp
    fn-cfg-row-upsert-preserves-limits-withinp
    fn-cfg-row-replace-key-preserves-row-listp
    fn-cfg-apply-delta-preserves-valuep
    fn-cfg-groups-retire-keeps-the-names
    fn-cfg-groups-create-keeps-the-names-or-adds-one
    (:d fn-cfg-take)))

(in-theory (disable fn-cfg-group-find-is-a-member-or-nil
             fn-cfg-groups-retire-preserves-group-listp
             fn-cfg-groups-create-preserves-group-listp
             fn-cfg-no-duplicates-of-append-one
             fn-cfg-group-find-nil-means-not-a-name
             fn-cfg-groups-create-preserves-no-duplicates
             fn-cfg-groups-retire-preserves-no-duplicates
             fn-cfg-row-upsert-preserves-row-listp
             fn-cfg-row-upsert-preserves-limits-withinp
             fn-cfg-row-replace-key-preserves-row-listp
             fn-cfg-apply-delta-preserves-valuep
             fn-cfg-groups-retire-keeps-the-names
             fn-cfg-groups-create-keeps-the-names-or-adds-one
             (:d fn-cfg-take)))
