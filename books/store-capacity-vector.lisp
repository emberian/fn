; fn: the Store's capacity as a resource vector (PRF-138, STO-020).
;
; gpt-6's review of wave 2 (planning/review-2026-09-26-gpt6-wave2.md, section
; 3): "committed use + in-flight reservations + completion/maintenance debt
; <= admitted capacity", with the components kept apart, and admission never
; consuming the last resource its own promise needs.  This book states that
; vector over the values the owner carries and proves it is a maintained
; invariant: established at init, preserved by every admitted record of every
; kind, and by reclaim (the profile is written once, at init: D34).
;
; The components, and where each is bounded:
;
;   transactions  the Store's transaction namespace, one `%020d.txn' per
;                 committed record, bounded by the profile's T for the life of
;                 the store (compaction and reclaim keep the count:
;                 `fn-sbud-used-names-the-transaction-namespace').
;   history       the committed record octets (unframed, the sum the open
;                 path counts: `fn-sbud-record-octets'), bounded by H.
;   completion    DEBT, the forward undertakings the Store holds open.  Each
;   debt          :undertake record pins a :forward obligation whose
;                 discharge is a :release record (books/store-node-retention,
;                 `fn-snrt-retention-of-apply-retention-event'), so an
;                 accepted undertaking is a promise to write one more record.
;   maintenance   one more :release record for the maintenance release
;                 (PRF-129, books/store-maintenance-reserve).
;   charge        the retention ledger's reserved charge against its
;                 capacity.  It is pre-paid: a pin's charge includes the
;                 permanent unit of its own release record, and a release
;                 never raises the reserved charge
;                 (`fn-cvec-release-never-raises-the-charge').
;   configuration the configuration namespace's generations, bounded by the
;   generations   profile's max-config-generations.  The operator's content
;                 release (`retention set') is a configuration record, so
;                 every other configuration record leaves the last
;                 generation to it (`fn-cvec-config-generations').
;   workspace     disk.  Compaction and reclamation write no Store record;
;                 their state checkpoint is checked against the free octets
;                 the host observes (books/owner-checkpoint-writer.lisp
;                 `fn-ockp-decide', through books/store-checkpoint-arena-
;                 writer.lisp `fn-scka-publication-setup').  That
;                 observation is not ownership: ENVIRONMENTAL ASSUMPTION, no
;                 concurrent writer takes the observed space before the
;                 checkpoint is written.  The promise is "refused or
;                 uncertain, never torn", not "completes"; a checkpoint
;                 write that fails at EIO/ENOSPC over the log has no native
;                 case yet (the pack publication's EIO cuts went with the
;                 pack layer).
;
; The vector's reservation: the profile's gate admits DEBT + 1 release
; records after the committed state, one after another
; (`fn-cvec-roomp').  With no open undertaking it is exactly PRF-129's
; reservation (`fn-cvec-roomp-without-debt-is-the-reserve'); the gate
; (`fn-cvec-verdict-at') differs from PRF-129's only for :undertake, which
; must leave room for its own release as well
; (`fn-cvec-verdict-without-debt-is-the-reserve-gate').
;
; Host calls: host/owner-host.lisp `fn-owner-publication-verdict' (every
; served non-article record, BP admission's retention included) answers
; `fn-cvec-verdict-at'; `fn-owner-prepare' and `fn-owner-prepare-buffer'
; (the served POST and the BP transit) hand `fn-cvec-article-budget-for' to
; `fn-pcar-sbud-prepare'; the debt they pass is `fn-cvec-debt-extend' of the
; owner's carried (K . DEBT) over the committed records, the same carriage
; as the octets (`fn-owner-record-octets').  host/store-node-host.lisp
; `fn-store-sn-publication-verdict' and `fn-store-sn-article-verdict' (the
; developer `store post') answer `fn-cvec-verdict-at' and
; `fn-cvec-article-verdict-at'; `fn-store-cfg-native-admin-authorize' hands
; `fn-cvec-config-generations' to `fn-native-admin-publication-authorize'.
(in-package "ACL2")
(include-book "store-maintenance-reserve")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(local (in-theory (disable fn-sbud-budget-is-the-profile-admissibility
                           fn-bs-publication-admissiblep fn-bs-profile-validp
                           fn-bs-profile-of fn-bs-profile-admittedp
                           fn-bs-profile-max-history-octets
                           fn-sbud-article-figure fn-sbud-article-gate-figure)))

; -----------------------------------------------------------------------------
; Completion debt over the committed records

(defun fn-cvec-debt-step (kind debt)
  "The open undertakings after one committed record of KIND."
  (declare (xargs :guard t))
  (cond ((equal kind :undertake) (+ 1 (nfix debt)))
        ((equal kind :release) (nfix (- (nfix debt) 1)))
        (t (nfix debt))))

(defun fn-cvec-debt-from (debt records)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-cvec-debt-from (fn-cvec-debt-step (fn-store-event-kind (car records))
                                            debt)
                         (cdr records))
    (nfix debt)))

(defun fn-cvec-record-debt (records)
  "The completion debt of a committed record list."
  (declare (xargs :guard t))
  (fn-cvec-debt-from 0 records))

; The owner carries CACHE = (K . DEBT), the debt of the first K committed
; records, and extends it by the records committed since, as it carries the
; octets (`fn-sbud-bytes-extend').
(defun fn-cvec-debt-cache-validp (cache records)
  (declare (xargs :guard (true-listp records)))
  (and (consp cache) (natp (car cache)) (<= (car cache) (len records))
       (equal (cdr cache) (fn-cvec-record-debt (take (car cache) records)))))

(defun fn-cvec-debt-extend (cache records)
  (declare (xargs :guard (true-listp records)))
  (if (and (consp cache) (natp (car cache)) (natp (cdr cache))
           (<= (car cache) (len records)))
      (fn-cvec-debt-from (cdr cache) (nthcdr (car cache) records))
    (fn-cvec-record-debt records)))

(local
 (defthm fn-cvec-debt-from-append
   (equal (fn-cvec-debt-from d (append x y))
          (fn-cvec-debt-from (fn-cvec-debt-from d x) y))))

(local
 (defthm fn-cvec-debt-from-of-nfix
   (equal (fn-cvec-debt-from (nfix d) x) (fn-cvec-debt-from d x))))

(local
 (defthm fn-cvec-take-nthcdr-append
   (implies (and (natp k) (<= k (len x)))
            (equal (append (take k x) (nthcdr k x)) x))))

; KEYSTONE (the carried debt is the history's debt).
(defthm fn-cvec-debt-extend-is-the-record-debt
  (implies (fn-cvec-debt-cache-validp cache records)
           (equal (fn-cvec-debt-extend cache records)
                  (fn-cvec-record-debt records)))
  :hints (("Goal" :use ((:instance fn-cvec-debt-from-append
                                   (d 0) (x (take (car cache) records))
                                   (y (nthcdr (car cache) records))))
           :in-theory (disable fn-cvec-debt-from-append))))

(local
 (defthm fn-cvec-debt-from-take-len
   (equal (fn-cvec-debt-from d (take (len x) x))
          (fn-cvec-debt-from d x))
   :hints (("Goal" :induct (fn-cvec-debt-from d x)))))

(defthm fn-cvec-full-debt-cache-is-valid
  (fn-cvec-debt-cache-validp (cons (len records) (fn-cvec-record-debt records))
                             records))

; -----------------------------------------------------------------------------
; The debt is the ledger's open forward obligations
;
; An :undertake record's replay admits a :forward pin, a :release record's
; removes the :forward pin it matches (`fn-snrt-retention-of-apply-retention-event').
; Over the ledger functions those are one more and one fewer open forward
; obligation.

(defun fn-cvec-forward-count (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (+ (if (and (consp (car pins))
                  (equal (fn-retain-obligation-kind (car pins)) :forward))
             1 0)
         (fn-cvec-forward-count (cdr pins)))
    0))

(defthm fn-cvec-admit-forward-adds-one-debt
  (implies (fn-retain-admissiblep s id subject :forward evidence charge)
           (equal (fn-cvec-forward-count
                   (fn-retain-pins (fn-retain-admit s id subject :forward
                                                    evidence charge)))
                  (+ 1 (fn-cvec-forward-count (fn-retain-pins s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-retain-admit) (fn-retain-admissiblep)))))

(local
 (defthm fn-cvec-forward-count-of-remove-found
   (implies (and (consp (fn-retain-find-id id pins))
                 (equal (fn-retain-obligation-kind (fn-retain-find-id id pins))
                        :forward))
            (equal (fn-cvec-forward-count (fn-retain-remove-id id pins))
                   (+ -1 (fn-cvec-forward-count pins))))))

(defthm fn-cvec-release-forward-removes-one-debt
  (let ((pin (fn-retain-find-id id (fn-retain-pins s))))
    (implies (and (fn-retain-statep s)
                  (fn-retain-matching-releasep pin id subject :forward evidence))
             (equal (fn-cvec-forward-count
                     (fn-retain-pins (fn-retain-release s id subject :forward
                                                        evidence)))
                    (+ -1 (fn-cvec-forward-count (fn-retain-pins s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-retain-release
                                     fn-retain-matching-releasep))))

; The charge component is pre-paid: a release never raises the reserved
; charge (each pin's charge is positive and includes its release unit).
(local
 (defthm fn-cvec-find-is-obligation
   (implies (and (fn-retain-obligation-listp pins)
                 (consp (fn-retain-find-id id pins)))
            (fn-retain-obligationp (fn-retain-find-id id pins)))))

(defthm fn-cvec-release-never-raises-the-charge
  (implies (fn-retain-statep s)
           (<= (fn-retain-reserved (fn-retain-release s id subject kind evidence))
               (fn-retain-reserved s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-retain-release)
           :expand ((fn-retain-statep s)
                    (fn-retain-obligationp
                     (fn-retain-find-id id (fn-retain-pins s))))
           :use ((:instance fn-cvec-find-is-obligation
                            (pins (fn-retain-pins s)))))))

; -----------------------------------------------------------------------------
; The reservation

(defun fn-cvec-roomp (profile used bytes-used debt)
  "The capacity vector holds: after the committed USED records and BYTES-USED
octets, the profile's gate admits DEBT + 1 release records in turn (one per
open undertaking and the maintenance release)."
  (declare (xargs :guard t))
  (and (natp used) (natp bytes-used)
       (fn-smr-roomp profile (+ used (nfix debt))
                     (+ bytes-used (* (nfix debt) (fn-smr-reserve-octets))))))

(defun fn-cvec-verdict-at (profile kind used bytes-used debt)
  "The publication verdict for one more record of KIND at DEBT open
undertakings.  A release is the profile's gate (it discharges a debt or
consumes the maintenance release); every other kind is admitted only if the
vector holds after it at its worst case, its own promise included."
  (declare (xargs :guard t))
  (if (equal kind :release)
      (fn-sbud-verdict-at profile kind used bytes-used)
    (if (and (equal (fn-sbud-verdict-at profile kind used bytes-used) :admissible)
             (fn-cvec-roomp profile (+ 1 (nfix used))
                            (+ (nfix bytes-used)
                               (fn-store-publication-ceiling kind))
                            (fn-cvec-debt-step kind debt)))
        :admissible
      :unaffordable)))

;; THE ACCEPTED-STATEMENT FIGURE: a composite's stored charge is its
;; encoding (`fn-sbud-row-octets'), so its gate charges the kind's publication
;; ceiling; the article it carries pays its memberships and header in the
;; memory equation (memory landing 3+4, RULINGS 2026-10-09 21:50).
(defun fn-cvec-statement-figure (group-count)
  (declare (xargs :guard t) (ignore group-count))
  (fn-store-publication-ceiling :accepted-statement))

(defun fn-cvec-statement-verdict-at (profile used bytes-used group-count debt)
  "The publication verdict for one accepted-statement composite whose article
is filed in GROUP-COUNT groups: the kind's count gate, the history gate and
the capacity vector at the composite's figure."
  (declare (xargs :guard t))
  (if (and (fn-sbud-admitp (fn-sbud-budget profile :accepted-statement) used)
           (fn-bs-history-admissiblep profile bytes-used
                                      (fn-cvec-statement-figure group-count))
           (fn-cvec-roomp profile (+ 1 (nfix used))
                          (+ (nfix bytes-used)
                             (fn-cvec-statement-figure group-count))
                          debt))
      :admissible
    :unaffordable))

(defun fn-cvec-article-verdict-at (profile used bytes-used payload-length
                                           group-count debt)
  (declare (xargs :guard t))
  (if (and (equal (fn-sbud-article-verdict-at profile used bytes-used
                                              payload-length group-count)
                  :admissible)
           (fn-cvec-roomp profile (+ 1 (nfix used))
                          (+ (nfix bytes-used)
                             (fn-sbud-article-gate-figure payload-length group-count))
                          debt))
      :admissible
    :unaffordable))

(defun fn-cvec-article-budget (profile used bytes-used payload-length
                                       group-count debt)
  (declare (xargs :guard t))
  (if (fn-cvec-roomp profile (+ 1 (nfix used))
                     (+ (nfix bytes-used)
                        (fn-sbud-article-gate-figure payload-length group-count))
                     debt)
      (fn-sbud-article-budget profile bytes-used payload-length group-count)
    0))

(defun fn-cvec-article-budget-for (profile used bytes-used record debt)
  (declare (xargs :guard t))
  (fn-cvec-article-budget profile used bytes-used
                          (len (fn-record-payload record))
                          (len (fn-record-groups record)) debt))

; THE TWO RESOURCES (lane m1-durable-2, 2026-10-04: Mini's condition for
; leaving segment rotation out of 6.6.0, "the history budget refuses by
; name").  The article's admission asks two resources, and each has two
; tests:
;
;   transactions  the count gate (one more record under T) and the vector's
;                 transaction reservation (DEBT + 1 release records after
;                 it, under T): `fn-cvec-article-transactions-admitp'.
;   history       the history gate (the article's figure within H after
;                 the committed octets) and the vector's octet reservation
;                 (DEBT + 1 release ceilings after it, within H):
;                 `fn-cvec-article-history-admitp'.
;
; The vector's own refusal is split between them: near H it is the octet
; reservation that refuses first, a band of (DEBT + 1) x 4096 octets in
; which the history gate alone still admits.  A word that called that band
; `unaffordable' would name H only some of the time.  The budget the
; served prepare is handed admits exactly when both resources do
; (`fn-cvec-article-budget-for-admits-exactly-both-sides').
(defun fn-cvec-article-transactions-admitp (profile used debt)
  (declare (xargs :guard t))
  (and (fn-sbud-admitp (fn-sbud-budget profile :article) used)
       (fn-sbud-admitp (fn-sbud-budget profile :release)
                       (+ 1 (nfix used) (nfix debt)))))

(defun fn-cvec-article-history-admitp (profile bytes-used figure debt)
  (declare (xargs :guard t))
  (and (fn-bs-history-admissiblep profile bytes-used figure)
       (fn-bs-history-admissiblep
        profile
        (+ (nfix bytes-used) (nfix figure)
           (* (nfix debt) (fn-smr-reserve-octets)))
        (fn-smr-reserve-octets))))

; The word the host reports for the served POST's prepare.  The prepare
; answers :unaffordable whenever its budget does not admit one more record;
; this names which resource refused, in this precedence:
;
;   1. the transactions refuse                         :unaffordable (T)
;   2. the history refuses                             :history-exhausted (H)
;   3. otherwise (no budget refusal the host can hand)  :unaffordable
;
; Any other word is passed through.  T first: a store out of transactions
; is full whatever its octets, and only compaction-free growth of T helps.
; The owner's memory gate names its own refusal (:memory) after these two
; (books/admission-memory.lisp, K-ADMIT).  KEYSTONES
; `fn-cvec-article-refusal-word-names-the-history',
; `fn-cvec-article-refusal-word-keeps-unaffordable-for-the-transactions' and,
; under the budget the host handed,
; `fn-cvec-article-refusal-word-under-the-budget-names-the-resource' (case 3
; unreachable).  The host line: host/owner-host.lisp `fn-owner-prepare' and
; `fn-owner-prepare-buffer', over the word `fn-pout-prepare-article'
; answered and the same count, octets, record and debt the budget was
; decided from.
(defun fn-cvec-article-refusal-word (word profile used bytes-used record debt)
  (declare (xargs :guard t))
  (let ((p (len (fn-record-payload record)))
        (k (len (fn-record-groups record))))
    (cond ((not (equal word :unaffordable)) word)
          ((not (fn-cvec-article-transactions-admitp profile used debt))
           :unaffordable)
          ((not (fn-cvec-article-history-admitp
                 profile bytes-used (fn-sbud-article-gate-figure p k) debt))
           :history-exhausted)
          (t :unaffordable))))

; The developer `store post' names its refusal as the served path does: its
; verdict (`fn-cvec-article-verdict-at', host/store-node-host.lisp
; `fn-store-sn-article-verdict-word') refused, and the word is the resource
; that refused, in the served word's precedence: the transactions
; (:unaffordable), the history (:history-exhausted).  KEYSTONE
; `fn-cvec-article-verdict-word-names-the-resource' (the last arm is
; unreachable).
(defun fn-cvec-article-verdict-word (profile used bytes-used payload-length
                                             group-count debt)
  (declare (xargs :guard t))
  (cond ((equal (fn-cvec-article-verdict-at profile used bytes-used
                                            payload-length group-count debt)
                :admissible)
         :admissible)
        ((not (fn-cvec-article-transactions-admitp profile used debt))
         :unaffordable)
        ((not (fn-cvec-article-history-admitp
               profile bytes-used
               (fn-sbud-article-gate-figure payload-length group-count) debt))
         :history-exhausted)
        (t :unaffordable)))

; The word admits exactly what the verdict admits.
(defthm fn-cvec-article-verdict-word-by-definition
  (let ((word (fn-cvec-article-verdict-word profile used bytes-used
                                            payload-length group-count debt)))
    (and (iff (equal word :admissible)
              (equal (fn-cvec-article-verdict-at profile used bytes-used
                                                 payload-length group-count debt)
                     :admissible))
         (member-equal word '(:admissible :history-exhausted :unaffordable))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cvec-article-verdict-word
                               fn-cvec-article-verdict-at
                               member-equal (:e member-equal)))))

; What `status' prints: the octets and transactions the vector reserves at
; DEBT, and whether the committed state has them.
(defun fn-cvec-report (profile used bytes-used debt)
  (declare (xargs :guard t))
  (list (* (+ 1 (nfix debt)) (fn-smr-reserve-octets))
        (+ 1 (nfix debt))
        (nfix debt)
        (if (fn-cvec-roomp profile used bytes-used debt) :held :short)))

; -----------------------------------------------------------------------------
; Keystones

(local (in-theory (e/d (fn-smr-roomp fn-sbud-verdict-at fn-sbud-admitp
                        fn-bs-history-admissiblep)
                       (fn-sbud-budget))))

(defthm fn-cvec-roomp-naturals
  (implies (fn-cvec-roomp profile used bytes-used debt)
           (and (natp used) (natp bytes-used)))
  :rule-classes :forward-chaining)

(defthm fn-cvec-roomp-without-debt-is-the-reserve
  (implies (and (natp used) (natp bytes-used))
           (equal (fn-cvec-roomp profile used bytes-used 0)
                  (fn-smr-roomp profile used bytes-used))))

(defthm fn-cvec-verdict-without-debt-is-the-reserve-gate
  (implies (and (natp used) (natp bytes-used)
                (not (equal kind :undertake)))
           (equal (fn-cvec-verdict-at profile kind used bytes-used 0)
                  (fn-smr-verdict-at profile kind used bytes-used)))
  :hints (("Goal" :in-theory (enable fn-smr-verdict-at))))

(defthm fn-cvec-roomp-antitone-in-octets
  (implies (and (fn-cvec-roomp profile used b debt)
                (natp b2) (<= b2 b))
           (fn-cvec-roomp profile used b2 debt))
  :rule-classes nil)

; Where the vector holds, the committed octets are within H and the committed
; count below T: the bounds the open path checks.
(defthm fn-cvec-roomp-is-within-the-profile
  (implies (fn-cvec-roomp profile used b debt)
           (and (fn-profile-replay-within-boundp profile (nfix b))
                (< (nfix used)
                   (fn-bs-profile-max-transactions profile))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-profile-replay-within-boundp
                                     fn-sbud-budget
                                     fn-bs-publication-admissiblep))))

;  KEYSTONE (full never means a promise it cannot discharge).  Where the vector
; holds at DEBT, every one of the DEBT releases and the maintenance release is
; admitted by the profile's gate in turn: the J-th, after J releases of at
; most the release ceiling each, whatever their order.
(defthm fn-cvec-roomp-discharges-every-debt
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (natp j) (<= j (nfix debt))
                (natp b2)
                (<= b2 (+ bytes-used (* j (fn-smr-reserve-octets)))))
           (equal (fn-cvec-verdict-at profile :release (+ used j) b2 debt)
                  :admissible))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sbud-budget
                                     fn-bs-publication-admissiblep))))

;  KEYSTONE (an admitted record keeps the vector).  A record of a kind other
; than the release, admitted at (USED, BYTES-USED, DEBT) and within its
; kind's worst case, leaves the vector holding at the next committed state,
; the debt its own undertaking adds included.
(defthm fn-cvec-admission-keeps-the-vector
  (implies (and (equal (fn-cvec-verdict-at profile kind used bytes-used debt)
                       :admissible)
                (not (equal kind :release))
                (natp octets)
                (<= octets (fn-store-publication-ceiling kind)))
           (fn-cvec-roomp profile (+ 1 used) (+ bytes-used octets)
                          (fn-cvec-debt-step kind debt)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-publication-admissiblep)
                                  (fn-store-publication-ceiling)))))

;  KEYSTONE (an admitted composite keeps the vector at its stored charge).
; An accepted-statement composite admitted at (USED, BYTES-USED, DEBT) for
; GROUP-COUNT groups, whose stored charge is within its figure, leaves the
; vector holding at the next committed state.
(defthm fn-cvec-statement-admission-keeps-the-vector
  (implies (and (equal (fn-cvec-statement-verdict-at profile used bytes-used
                                                     group-count debt)
                       :admissible)
                (natp used) (natp bytes-used) (natp debt)
                (natp octets)
                (<= octets (fn-cvec-statement-figure group-count)))
           (fn-cvec-roomp profile (+ 1 used) (+ bytes-used octets)
                          (fn-cvec-debt-step :accepted-statement debt)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-roomp-antitone-in-octets
                                   (used (+ 1 (nfix used)))
                                   (b (+ (nfix bytes-used)
                                         (fn-cvec-statement-figure group-count)))
                                   (b2 (+ bytes-used octets))))
           :in-theory (e/d (fn-cvec-statement-verdict-at)
                           (fn-cvec-roomp fn-cvec-statement-figure
                            fn-store-publication-ceiling)))))

;  KEYSTONE (the composite's charge and its figure).  A retained
; accepted-statement row's stored charge is its encoding, so it is within the
; figure its gate charges exactly when its encoding is within the kind's
; publication ceiling, whatever its group count.  The admission's runtime
; check is the charge against the figure (fn-cvec-record-admittedp).
(defthm fn-cvec-statement-row-within-its-figure
  (implies (and (fn-hstxa-p row)
                (<= (len (fn-store-event-encode (fn-hstxa-stxa row)))
                    (fn-store-publication-ceiling :accepted-statement)))
           (<= (fn-sbud-row-octets row)
               (fn-cvec-statement-figure (fn-sbud-row-memberships row))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-row-octets fn-cvec-statement-figure)
                                  (fn-store-event-encode fn-store-publication-ceiling
                                   fn-held-p fn-hstxa-stxa)))))

(defthm fn-cvec-statement-row-within-its-figure-has-its-encoding
  (implies (and (fn-hstxa-p row)
                (<= (fn-sbud-row-octets row)
                    (fn-cvec-statement-figure (fn-sbud-row-memberships row))))
           (<= (len (fn-store-event-encode (fn-hstxa-stxa row)))
               (fn-store-publication-ceiling :accepted-statement)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-row-octets fn-cvec-statement-figure)
                                  (fn-store-event-encode fn-store-publication-ceiling
                                   fn-held-p fn-hstxa-stxa)))))

;  KEYSTONE (a release discharges a debt and keeps the vector).  Where the
; vector holds with at least one open undertaking, a release record of at
; most the release ceiling leaves it holding with one fewer.
(defthm fn-cvec-release-keeps-the-vector
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (posp debt)
                (natp octets)
                (<= octets (fn-smr-reserve-octets)))
           (fn-cvec-roomp profile (+ 1 used) (+ bytes-used octets)
                          (fn-cvec-debt-step :release debt)))
  :rule-classes nil)


;  KEYSTONE (the served article prepare keeps the vector).
(defthm fn-cvec-prepare-keeps-the-vector
  (implies (and (not (equal (fn-sbud-prepare
                             oc record
                             (fn-cvec-article-budget-for
                              profile (fn-sbud-used (fn-sbud-oc-store oc))
                              bytes-used record debt))
                            oc)))
           (and (fn-cvec-roomp profile
                               (+ 1 (fn-sbud-used (fn-sbud-oc-store oc)))
                               (+ bytes-used (len (fn-record-payload record)))
                               debt)
                (fn-profile-replay-within-boundp
                 profile (+ bytes-used (len (fn-record-payload record))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-roomp-antitone-in-octets
                                   (used (+ 1 (fn-sbud-used (fn-sbud-oc-store oc))))
                                   (b (+ bytes-used
                                         (fn-sbud-article-gate-figure
                                          (len (fn-record-payload record))
                                          (len (fn-record-groups record)))))
                                   (b2 (+ bytes-used (len (fn-record-payload record)))))
                        (:instance fn-sbud-prepare-under-article-budget-keeps-history
                                   (bytes-used bytes-used)))
           :in-theory (e/d (fn-sbud-prepare fn-cvec-article-budget-for
                            fn-cvec-article-budget fn-sbud-article-budget-for
                            fn-sbud-article-budget fn-sbud-article-gate-figure)
                           (fn-cvec-roomp fn-smr-roomp
                            fn-opc-prepare fn-sbud-used
                            fn-profile-replay-within-boundp)))))

;  KEYSTONE (the developer `store post' keeps the vector).
(defthm fn-cvec-article-verdict-keeps-the-vector
  (implies (and (equal (fn-cvec-article-verdict-at profile used bytes-used
                                                   payload-length group-count
                                                   debt)
                       :admissible)
                (<= (len (fn-record-payload record)) (nfix payload-length)))
           (fn-cvec-roomp profile (+ 1 used)
                          (+ bytes-used (len (fn-record-payload record)))
                          debt))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-roomp-antitone-in-octets
                                   (used (+ 1 used))
                                   (b (+ bytes-used (fn-sbud-article-gate-figure
                                                     payload-length group-count)))
                                   (b2 (+ bytes-used (len (fn-record-payload record))))))
           :in-theory (e/d (fn-cvec-article-verdict-at fn-sbud-article-verdict-at
                            fn-sbud-article-gate-figure)
                           (fn-cvec-roomp fn-smr-roomp)))))


;  KEYSTONE (the vector holds from init).
(defthm fn-cvec-admitted-profile-starts-held
  (implies (fn-bs-profile-admittedp profile)
           (fn-cvec-roomp profile 0 0 0))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-smr-admitted-profile-starts-reserved))
           :in-theory (disable fn-smr-roomp fn-sbud-verdict-at))))

; -----------------------------------------------------------------------------
; The composed statement
;
; A history is admitted from (USED, BYTES-USED, DEBT) when each record, at the
; state its prefix leaves, is admitted by the gate the host calls for its
; kind and is within the figure that gate charged.  For an article that is
; the article gate at its own payload and group counts, and the figure bounds
; the record whose charge fits u32 at every producer width (PRF-126,
; `fn-sbud-article-figure-bounds-the-producer-record'; the producers that
; establish the premise are PRF-123's).  For every other kind it is the kind's
; publication ceiling, which the record's own codec bound must meet: a
; premise here, not a proof that every producer meets it (the signed
; composite and peer-carried producers are outside PRF-123/126).  A release
; is admitted only against an open undertaking.

;
; A retained article is a HELD row (records-flip): kind :article is exactly
; `fn-held-p' (books/store-events.lisp `fn-store-event-kind'), its payload
; position is a handle, and its payload length is the facts' octets the
; intern decided from the bytes it sealed (`fn-sbud-row-octets'; stated over
; the arena in books/store-budget-stored.lisp).  The host's article gate
; (`fn-cvec-article-budget-for') is asked of the WIRE record at the POST,
; whose payload length the intern copies into those facts
; (`fn-cvec-intern-row-payload-length' in the test book's witness).  Before
; this restatement the arm asked `fn-record-p' of the history row, which no
; retained article satisfies (`fn-cvec-wire-record-is-no-article-row'):
; every history with an article was unadmitted and the keystones below said
; nothing about one.
(defun fn-cvec-row-payload-length (row)
  (declare (xargs :guard t :verify-guards nil))
  (nfix (fn-hf-octets (fn-held-facts row))))

(defun fn-cvec-record-figure (record)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (fn-store-event-kind record)))
    (cond ((equal kind :article)
           (fn-sbud-article-gate-figure (fn-cvec-row-payload-length record)
                                   (len (fn-record-groups record))))
          ((equal kind :accepted-statement)
           (fn-cvec-statement-figure (fn-sbud-row-memberships record)))
          (t (fn-store-publication-ceiling kind)))))

(defun fn-cvec-record-admittedp (profile used bytes-used debt record)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (fn-store-event-kind record)))
    (cond ((equal kind :article)
           (and (fn-held-p record)
                (equal (fn-cvec-article-verdict-at
                        profile used bytes-used (fn-cvec-row-payload-length record)
                        (len (fn-record-groups record)) debt)
                       :admissible)))
          ((equal kind :accepted-statement)
           (and (equal (fn-cvec-statement-verdict-at
                        profile used bytes-used (fn-sbud-row-memberships record)
                        debt)
                       :admissible)
                (<= (fn-sbud-row-octets record)
                    (fn-cvec-statement-figure
                     (fn-sbud-row-memberships record)))))
          (t
           (and (equal (fn-cvec-verdict-at profile kind used bytes-used debt)
                       :admissible)
                (or (not (equal kind :release)) (posp debt))
                (<= (fn-sbud-row-octets record)
                    (fn-store-publication-ceiling kind)))))))

; The arm the restatement replaced could not fire: a wire record is never a
; row of kind :article.
(defthm fn-cvec-wire-record-is-no-article-row
  (implies (fn-record-p record)
           (not (equal (fn-store-event-kind record) :article)))
  :hints (("Goal" :use ((:instance fn-held-p-forward-shape (x record)))
           :in-theory (e/d (fn-store-event-kind fn-record-p fn-record-shapep fn-held-shapep
                            fn-store-retention-event-p fn-th-topic-eventp fn-th-local-admin-eventp)
                           (fn-held-p)))))

(defun fn-cvec-history-admittedp (profile used bytes-used debt records)
  (declare (xargs :guard t :verify-guards nil :measure (len records)))
  (if (consp records)
      (let ((rest (fn-cvec-history-admittedp
                   profile (+ 1 (nfix used))
                   (+ (nfix bytes-used)
                      (fn-sbud-row-octets (car records)))
                   (fn-cvec-debt-step (fn-store-event-kind (car records)) debt)
                   (cdr records))))
        (and (fn-cvec-record-admittedp profile used bytes-used debt
                                       (car records))
             rest))
    t))

(local (in-theory (disable fn-smr-roomp fn-sbud-verdict-at fn-sbud-admitp
                           fn-bs-history-admissiblep)))

(local
 (defthm fn-cvec-roomp-of-nfix-debt
   (equal (fn-cvec-roomp profile used b (nfix d))
          (fn-cvec-roomp profile used b d))))


;  A held row stores its payload length, the figure it was charged at.
(local
 (defthm fn-cvec-held-row-octets
   (implies (fn-held-p record)
            (equal (fn-sbud-row-octets record)
                   (fn-cvec-row-payload-length record)))
   :hints (("Goal" :in-theory (enable fn-sbud-row-octets)))))

; A held row's charge, its payload, is the figure its article was charged at.
(defthm fn-cvec-held-row-within-its-figure
  (equal (fn-sbud-article-gate-figure (fn-cvec-row-payload-length record) group-count)
         (fn-cvec-row-payload-length record))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sbud-article-gate-figure fn-cvec-row-payload-length))))

; The article verdict at a held row's payload length keeps the vector at the
; octets the row stores.
(defthm fn-cvec-article-verdict-keeps-the-vector-for-a-held-row
  (implies (equal (fn-cvec-article-verdict-at profile used bytes-used
                                              (fn-cvec-row-payload-length record)
                                              group-count debt)
                  :admissible)
           (fn-cvec-roomp profile (+ 1 used)
                          (+ bytes-used (fn-cvec-row-payload-length record))
                          debt))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cvec-article-verdict-at fn-sbud-article-verdict-at
                                   fn-sbud-article-gate-figure fn-cvec-row-payload-length
                                   fn-sbud-admitp fn-bs-history-admissiblep)
                                  (fn-cvec-roomp fn-smr-roomp fn-sbud-budget)))))

; One committed record of any kind keeps the vector, at a natural debt.
(local
(defthm fn-cvec-record-keeps-the-vector-at-a-natural-debt
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (natp debt)
                (fn-cvec-record-admittedp profile used bytes-used debt record))
           (fn-cvec-roomp profile (+ 1 used)
                          (+ bytes-used (fn-sbud-row-octets record))
                          (fn-cvec-debt-step (fn-store-event-kind record) debt)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cvec-article-verdict-keeps-the-vector-for-a-held-row
                            (group-count (len (fn-record-groups record))))
                 (:instance fn-cvec-release-keeps-the-vector
                            (octets (fn-sbud-row-octets record)))
                 (:instance fn-cvec-statement-admission-keeps-the-vector
                            (group-count (fn-sbud-row-memberships record))
                            (octets (fn-sbud-row-octets record)))
                 (:instance fn-cvec-admission-keeps-the-vector
                            (kind (fn-store-event-kind record))
                            (octets (fn-sbud-row-octets record))))
           :in-theory (e/d (fn-cvec-record-admittedp fn-cvec-debt-step)
                           (fn-cvec-roomp fn-cvec-verdict-at
                            fn-cvec-statement-verdict-at fn-cvec-statement-figure
                            fn-sbud-row-memberships
                            fn-cvec-article-verdict-at fn-cvec-row-payload-length
                            fn-store-event-kind fn-store-event-encode
                            fn-store-publication-ceiling fn-held-p
                            fn-sbud-held-heap-charge fn-sbud-row-octets))))))

; Every reader of the debt fixes it (fn-cvec-roomp, fn-cvec-debt-step, the
; verdicts through fn-cvec-roomp; a release asks posp), so a debt that is not
; a natural reads as 0 everywhere and the natural-debt hypothesis is
; redundant (PKT-362, PKT-776: it had no removal witness because it has no
; work to do).
(local
 (defthm fn-cvec-roomp-of-non-natp-debt
   (implies (not (natp d))
            (equal (fn-cvec-roomp profile used b d)
                   (fn-cvec-roomp profile used b 0)))))

(local
 (defthm fn-cvec-debt-step-of-non-natp
   (implies (not (natp debt))
            (equal (fn-cvec-debt-step kind debt) (fn-cvec-debt-step kind 0)))))

(local
 (defthm fn-cvec-record-admittedp-of-non-natp-debt
   (implies (not (natp debt))
            (equal (fn-cvec-record-admittedp profile used bytes-used debt record)
                   (fn-cvec-record-admittedp profile used bytes-used 0 record)))
   :hints (("Goal"
            :in-theory (union-theories
                        '(fn-cvec-record-admittedp fn-cvec-article-verdict-at
                          fn-cvec-statement-verdict-at fn-cvec-verdict-at
                          fn-cvec-roomp-of-non-natp-debt fn-cvec-debt-step-of-non-natp
                          posp natp (:executable-counterpart natp)
                          (:executable-counterpart posp))
                        (theory 'minimal-theory))))))

;  KEYSTONE (one committed record of any kind keeps the vector).
(defthm fn-cvec-record-keeps-the-vector
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (fn-cvec-record-admittedp profile used bytes-used debt record))
           (fn-cvec-roomp profile (+ 1 used)
                          (+ bytes-used (fn-sbud-row-octets record))
                          (fn-cvec-debt-step (fn-store-event-kind record) debt)))
  :rule-classes nil
  :hints (("Goal" :cases ((natp debt))
           :use ((:instance fn-cvec-record-keeps-the-vector-at-a-natural-debt)
                 (:instance fn-cvec-record-keeps-the-vector-at-a-natural-debt (debt 0)))
           :in-theory (union-theories '(fn-cvec-record-admittedp-of-non-natp-debt
                                        fn-cvec-debt-step-of-non-natp
                                        fn-cvec-roomp-of-non-natp-debt
                                        (:executable-counterpart natp))
                                      (theory 'minimal-theory)))))

;  The vector part of the composed statement, by induction over the history.
(local
 (defun fn-cvec-history-induction (used bytes-used debt records)
   (declare (xargs :measure (len records)))
   (if (consp records)
       (fn-cvec-history-induction
        (+ 1 used) (+ bytes-used (fn-sbud-row-octets (car records)))
        (fn-cvec-debt-step (fn-store-event-kind (car records)) debt)
        (cdr records))
     (list used bytes-used debt))))

(local
 (defthm fn-cvec-history-admittedp-of-cons
   (implies (consp records)
            (equal (fn-cvec-history-admittedp profile used bytes-used debt records)
                   (and (fn-cvec-record-admittedp profile used bytes-used debt
                                                  (car records))
                        (fn-cvec-history-admittedp
                         profile (+ 1 (nfix used))
                         (+ (nfix bytes-used)
                            (fn-sbud-row-octets (car records)))
                         (fn-cvec-debt-step (fn-store-event-kind (car records))
                                            debt)
                         (cdr records)))))
   :hints (("Goal" :expand ((fn-cvec-history-admittedp profile used bytes-used
                                                        debt records))
            :in-theory (disable fn-cvec-history-admittedp
                                fn-cvec-record-admittedp fn-cvec-debt-step
                                fn-store-event-kind fn-store-event-encode)))))

(local
 (defthm fn-cvec-record-octets-of-cons
   (implies (consp records)
            (equal (fn-sbud-record-octets records)
                   (+ (fn-sbud-row-octets (car records))
                      (fn-sbud-record-octets (cdr records)))))
   :hints (("Goal" :expand ((fn-sbud-record-octets records))
            :in-theory (disable fn-sbud-record-octets fn-store-event-encode)))))

(local
 (defthm fn-cvec-record-octets-of-atom
   (implies (not (consp records))
            (equal (fn-sbud-record-octets records) 0))
   :hints (("Goal" :expand ((fn-sbud-record-octets records))
            :in-theory (disable fn-sbud-record-octets fn-store-event-encode)))))

(local
 (defthm fn-cvec-debt-from-of-cons
   (implies (consp records)
            (equal (fn-cvec-debt-from debt records)
                   (fn-cvec-debt-from
                    (fn-cvec-debt-step (fn-store-event-kind (car records)) debt)
                    (cdr records))))))

(local
 (defthm fn-cvec-debt-from-of-atom
   (implies (not (consp records))
            (equal (fn-cvec-debt-from debt records) (nfix debt)))))

(local
 (defthm fn-cvec-debt-step-natural
   (natp (fn-cvec-debt-step kind debt))
   :rule-classes :type-prescription))

(local
 (defthm fn-cvec-record-step
   (implies (and (fn-cvec-roomp profile used bytes-used debt)
                 (natp debt)
                 (fn-cvec-record-admittedp profile used bytes-used debt record))
            (fn-cvec-roomp profile (+ 1 used)
                           (+ bytes-used (fn-sbud-row-octets record))
                           (fn-cvec-debt-step (fn-store-event-kind record) debt)))
   :hints (("Goal" :use fn-cvec-record-keeps-the-vector-at-a-natural-debt
            :in-theory (disable fn-cvec-roomp fn-cvec-record-admittedp
                                fn-cvec-debt-step fn-store-event-kind
                                fn-store-event-encode)))))

(local
 (defthm fn-cvec-admitted-history-keeps-roomp
   (implies (and (fn-cvec-roomp profile used bytes-used debt)
                 (natp debt)
                 (fn-cvec-history-admittedp profile used bytes-used debt records))
            (fn-cvec-roomp profile (+ used (len records))
                           (+ bytes-used (fn-sbud-record-octets records))
                           (fn-cvec-debt-from debt records)))
   :hints (("Goal" :induct (fn-cvec-history-induction used bytes-used debt records)
            :in-theory (disable fn-cvec-history-admittedp fn-sbud-record-octets
                                fn-cvec-debt-from fn-cvec-roomp
                                fn-cvec-record-admittedp fn-cvec-debt-step
                                fn-store-event-kind fn-store-event-encode)))))

;  The composed statement (PRF-138) at a natural debt.  From a state where the vector
; holds, a history of mixed record kinds each admitted by the host-called gate
; of its kind leaves the vector holding at the committed count, the ACTUAL
; committed record octets (`fn-sbud-record-octets', the unframed sum the open
; path counts) and the history's debt; so the history is within H and below
; T, which is what the selected open path admits.
(local
(defthm fn-cvec-admitted-history-keeps-the-vector-at-a-natural-debt
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (natp debt)
                (fn-cvec-history-admittedp profile used bytes-used debt records))
           (and (fn-cvec-roomp profile (+ used (len records))
                               (+ bytes-used (fn-sbud-record-octets records))
                               (fn-cvec-debt-from debt records))
                (fn-profile-replay-within-boundp
                 profile (+ bytes-used (fn-sbud-record-octets records)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-admitted-history-keeps-roomp)
                        (:instance fn-cvec-roomp-is-within-the-profile
                                   (used (+ used (len records)))
                                   (b (+ bytes-used (fn-sbud-record-octets records)))
                                   (debt (fn-cvec-debt-from debt records))))
           :in-theory (disable fn-cvec-roomp fn-cvec-history-admittedp
                               fn-profile-replay-within-boundp)))))

;  KEYSTONE (the composed statement, PRF-138), at any debt: the reads fix it.
(local
 (defthm fn-cvec-debt-from-of-non-natp
   (implies (not (natp debt))
            (equal (fn-cvec-debt-from debt records)
                   (fn-cvec-debt-from 0 records)))
   :hints (("Goal" :expand ((fn-cvec-debt-from debt records)
                            (fn-cvec-debt-from 0 records))
            :in-theory (union-theories '(fn-cvec-debt-step-of-non-natp nfix natp
                                         (:executable-counterpart nfix))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-cvec-history-admittedp-of-non-natp
   (implies (not (natp debt))
            (equal (fn-cvec-history-admittedp profile used bytes-used debt records)
                   (fn-cvec-history-admittedp profile used bytes-used 0 records)))
   :hints (("Goal" :expand ((fn-cvec-history-admittedp profile used bytes-used debt records)
                            (fn-cvec-history-admittedp profile used bytes-used 0 records))
            :in-theory (union-theories '(fn-cvec-debt-step-of-non-natp
                                         fn-cvec-record-admittedp-of-non-natp-debt)
                                       (theory 'minimal-theory))))))

(defthm fn-cvec-admitted-history-keeps-the-vector
  (implies (and (fn-cvec-roomp profile used bytes-used debt)
                (fn-cvec-history-admittedp profile used bytes-used debt records))
           (and (fn-cvec-roomp profile (+ used (len records))
                               (+ bytes-used (fn-sbud-record-octets records))
                               (fn-cvec-debt-from debt records))
                (fn-profile-replay-within-boundp
                 profile (+ bytes-used (fn-sbud-record-octets records)))))
  :rule-classes nil
  :hints (("Goal" :cases ((natp debt))
           :use ((:instance fn-cvec-admitted-history-keeps-the-vector-at-a-natural-debt)
                 (:instance fn-cvec-admitted-history-keeps-the-vector-at-a-natural-debt
                            (debt 0)))
           :in-theory (union-theories '(fn-cvec-history-admittedp-of-non-natp
                                        fn-cvec-debt-from-of-non-natp
                                        fn-cvec-roomp-of-non-natp-debt
                                        (:executable-counterpart natp))
                                      (theory 'minimal-theory)))))

;  KEYSTONE (from init).  A store initialised under an admitted profile whose
; history each record of which the host-called gate admitted is within H and
; below T, and holds the vector at its history's debt.
(defthm fn-cvec-admitted-history-from-init
  (implies (and (fn-bs-profile-admittedp profile)
                (fn-cvec-history-admittedp profile 0 0 0 records))
           (and (fn-cvec-roomp profile (len records)
                               (fn-sbud-record-octets records)
                               (fn-cvec-record-debt records))
                (fn-profile-replay-within-boundp
                 profile (fn-sbud-record-octets records))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cvec-admitted-profile-starts-held)
                        (:instance fn-cvec-admitted-history-keeps-the-vector
                                   (used 0) (bytes-used 0) (debt 0)))
           :in-theory (disable fn-cvec-roomp fn-cvec-history-admittedp))))

(in-theory (disable fn-cvec-roomp fn-cvec-verdict-at fn-cvec-article-verdict-at
                    fn-cvec-article-transactions-admitp
                    fn-cvec-article-history-admitp
                    fn-cvec-statement-verdict-at fn-cvec-statement-figure
                    fn-cvec-article-budget fn-cvec-article-budget-for
                    fn-cvec-report fn-cvec-debt-extend fn-cvec-record-debt
                    fn-cvec-history-admittedp
                    fn-cvec-record-admittedp fn-cvec-record-figure
                    fn-cvec-row-payload-length))

; -----------------------------------------------------------------------------
; The two resources (lane m1-durable-2)

; The vector at one more record is its transaction reservation and its octet
; reservation.
(defthm fn-cvec-roomp-is-the-two-sides
  (implies (and (natp used) (natp bytes-used))
           (equal (fn-cvec-roomp profile (+ 1 used) (+ bytes-used figure) debt)
                  (and (fn-sbud-admitp (fn-sbud-budget profile :release)
                                       (+ 1 used (nfix debt)))
                       (fn-bs-history-admissiblep
                        profile
                        (+ bytes-used figure (* (nfix debt) (fn-smr-reserve-octets)))
                        (fn-smr-reserve-octets))
                       (natp (+ bytes-used figure)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cvec-roomp fn-smr-roomp fn-sbud-verdict-at) (fn-smr-reserve-octets fn-sbud-verdict-is-the-count-and-history-admissibility fn-sbud-budget-is-the-profile-admissibility fn-sbud-admitp fn-bs-history-admissiblep fn-sbud-budget)))))

; The budget the served prepare is handed (`fn-cvec-article-budget-for')
; admits one more record exactly when both resources admit it at the gate
; figure.  So the prepare's :unaffordable is one of them refusing.
(defthm fn-cvec-article-budget-for-admits-exactly-both-sides
  (let ((p (len (fn-record-payload record)))
        (k (len (fn-record-groups record))))
    (iff (fn-sbud-admitp (fn-cvec-article-budget-for profile used bytes-used
                                                     record debt)
                         used)
         (and (fn-cvec-article-transactions-admitp profile used debt)
              (fn-cvec-article-history-admitp
               profile bytes-used (fn-sbud-article-gate-figure p k) debt))))
  :hints (("Goal" :use ((:instance fn-cvec-roomp-is-the-two-sides
                                   (used (nfix used)) (bytes-used (nfix bytes-used))
                                   (figure (fn-sbud-article-gate-figure
                                            (len (fn-record-payload record))
                                            (len (fn-record-groups record))))))
           :in-theory (e/d (fn-cvec-article-budget-for fn-cvec-article-budget
                            fn-sbud-article-budget
                            fn-cvec-article-transactions-admitp
                            fn-cvec-article-history-admitp fn-sbud-admitp
                            fn-bs-history-admissiblep)
                           (fn-smr-reserve-octets fn-cvec-roomp
                            fn-sbud-verdict-is-the-count-and-history-admissibility
                            fn-sbud-budget-is-the-profile-admissibility
                            fn-sbud-budget fn-sbud-article-gate-figure)))))

; The developer `store post''s verdict admits exactly when both resources do.
(defthm fn-cvec-article-verdict-admits-exactly-both-sides
  (iff (equal (fn-cvec-article-verdict-at profile used bytes-used payload-length
                                          group-count debt)
              :admissible)
       (and (fn-cvec-article-transactions-admitp profile used debt)
            (fn-cvec-article-history-admitp
             profile bytes-used
             (fn-sbud-article-gate-figure payload-length group-count) debt)))
  :hints (("Goal" :use ((:instance fn-cvec-roomp-is-the-two-sides
                                   (used (nfix used)) (bytes-used (nfix bytes-used))
                                   (figure (fn-sbud-article-gate-figure
                                            payload-length group-count))))
           :in-theory (e/d (fn-cvec-article-verdict-at fn-sbud-article-verdict-at
                            fn-cvec-article-transactions-admitp
                            fn-cvec-article-history-admitp fn-sbud-admitp
                            fn-bs-history-admissiblep)
                           (fn-smr-reserve-octets fn-cvec-roomp
                            fn-sbud-verdict-is-the-count-and-history-admissibility
                            fn-sbud-budget-is-the-profile-admissibility
                            fn-sbud-budget fn-sbud-article-gate-figure)))))

; -----------------------------------------------------------------------------
; KEYSTONE (the history budget refuses by name).  The word the host reports
; is :history-exhausted exactly when the prepare answered :unaffordable, the
; transactions admit the article (the count gate and the vector's
; transaction reservation), the history does not at the article's gate
; figure (the history gate or the vector's octet reservation).
(defthm fn-cvec-article-refusal-word-names-the-history
  (let ((p (len (fn-record-payload record)))
        (k (len (fn-record-groups record))))
    (equal (equal (fn-cvec-article-refusal-word word profile used
                                                bytes-used record debt)
                  :history-exhausted)
           (or (equal word :history-exhausted)
               (and (equal word :unaffordable)
                    (fn-cvec-article-transactions-admitp profile used debt)
                    (not (fn-cvec-article-history-admitp
                          profile bytes-used (fn-sbud-article-gate-figure p k)
                          debt))))))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-cvec-article-transactions-admitp
                                   fn-cvec-article-history-admitp
                                   fn-sbud-article-gate-figure)))))

; KEYSTONE (completeness: :unaffordable is left only to T).  The word stays
; :unaffordable exactly when the transactions refuse, or the history admits
; (which the host's budget never refuses: below).
(defthm fn-cvec-article-refusal-word-keeps-unaffordable-for-the-transactions
  (let ((p (len (fn-record-payload record)))
        (k (len (fn-record-groups record))))
    (equal (equal (fn-cvec-article-refusal-word word profile used
                                                bytes-used record debt)
                  :unaffordable)
           (and (equal word :unaffordable)
                (or (not (fn-cvec-article-transactions-admitp profile used debt))
                    (fn-cvec-article-history-admitp
                     profile bytes-used (fn-sbud-article-gate-figure p k) debt)))))
  :hints (("Goal" :use ((:instance fn-cvec-article-budget-for-admits-exactly-both-sides))
           :in-theory (e/d (fn-sbud-admitp fn-cvec-article-budget-for)
                           (fn-cvec-article-budget-for-admits-exactly-both-sides
                            fn-cvec-article-transactions-admitp
                            fn-cvec-article-history-admitp
                            fn-cvec-article-budget
                            fn-cvec-roomp fn-sbud-budget
                            fn-bs-history-admissiblep
                            fn-sbud-article-gate-figure)))))

; KEYSTONE (under the host's budget, the word names the resource).  When the
; budget the host handed does not admit one more record (the only way the
; prepare answers :unaffordable), the word is :unaffordable exactly when the
; transactions refuse, and :history-exhausted exactly when the transactions
; admit and the history refuses.
(defthm fn-cvec-article-refusal-word-under-the-budget-names-the-resource
  (let ((p (len (fn-record-payload record)))
        (k (len (fn-record-groups record)))
        (word2 (fn-cvec-article-refusal-word :unaffordable profile used
                                             bytes-used record debt)))
    (implies (and (natp used)
                  (not (fn-sbud-admitp (fn-cvec-article-budget-for
                                        profile used bytes-used record debt)
                                       used)))
             (and (member-equal word2 '(:unaffordable :history-exhausted))
                  (iff (equal word2 :unaffordable)
                       (not (fn-cvec-article-transactions-admitp profile used debt)))
                  (iff (equal word2 :history-exhausted)
                       (and (fn-cvec-article-transactions-admitp profile used debt)
                            (not (fn-cvec-article-history-admitp
                                  profile bytes-used
                                  (fn-sbud-article-gate-figure p k) debt)))))))
  :hints (("Goal" :use ((:instance fn-cvec-article-budget-for-admits-exactly-both-sides)
                        (:instance fn-cvec-article-refusal-word-keeps-unaffordable-for-the-transactions
                                   (word :unaffordable)))
           :in-theory (e/d ()
                           (fn-cvec-article-budget-for-admits-exactly-both-sides
                            fn-cvec-article-refusal-word-keeps-unaffordable-for-the-transactions
                            fn-cvec-article-transactions-admitp
                            fn-cvec-article-history-admitp
                            fn-cvec-article-budget-for fn-sbud-admitp
                            fn-sbud-article-gate-figure)))))

; KEYSTONE (the developer `store post' names the resource the same way).
(defthm fn-cvec-article-verdict-word-names-the-resource
  (let ((word (fn-cvec-article-verdict-word profile used bytes-used
                                            payload-length group-count debt))
        (tx (fn-cvec-article-transactions-admitp profile used debt))
        (hx (fn-cvec-article-history-admitp
             profile bytes-used
             (fn-sbud-article-gate-figure payload-length group-count) debt)))
    (and (member-equal word '(:admissible :history-exhausted :unaffordable))
         (iff (equal word :admissible) (and tx hx))
         (iff (equal word :unaffordable) (not tx))
         (iff (equal word :history-exhausted)
              (and tx (not hx)))))
  :hints (("Goal" :use ((:instance fn-cvec-article-verdict-admits-exactly-both-sides))
           :in-theory (e/d (fn-cvec-article-verdict-word)
                           (fn-cvec-article-verdict-admits-exactly-both-sides
                            fn-cvec-article-verdict-at
                            fn-cvec-article-transactions-admitp
                            fn-cvec-article-history-admitp
                            fn-cvec-roomp fn-sbud-admitp fn-sbud-budget
                            fn-bs-history-admissiblep
                            fn-sbud-article-gate-figure)))))
