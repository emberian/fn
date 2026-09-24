; fn: the Store's transaction budget, decided by the served prepare (M5).
;
; Where the budget comes from.  A store's persisted profile
; (books/byte-store-frame.lisp, `*fn-bs-meta-development-values*' and
; `*fn-bs-meta-scale-values*') is written once by `init' and decoded by
; `fn-bs-config-decode' at every open.  Its fifth field is the transaction
; budget: 128 for :development, 4096 for :scale.  The owner hands the
; decoded values back to ACL2 once, at open (host/owner-host.lisp
; `fn-owner-install-profile'), and every later decision reads that carried
; value; no host constant and no host count enters it.
;
; Why the budget is fixed at init.  The profile bounds the work of opening the
; store BEFORE any configuration record is replayed: the transaction
; namespace is enumerated with the budget as its readdir bound
; (host/native/io.lisp `fnn-transaction-files') and the aggregate replay input
; is the profile's `max_recovery_record_bytes'.  A configuration record lives
; inside that bounded input, so it cannot raise the bound that admits it.
; Changing the budget is therefore an offline step (a re-init, or a profile
; upgrade that replaces the one metadata file while no owner runs), never a
; served event; `fn-ocl-publish' does not carry it.  The retention charge
; capacity, by contrast, IS a configuration record (`operator capacity').
;
; Who decides.  `fn-sbud-prepare' (books/owner-store-budget.lisp) is the function `fn-owner-prepare'
; (host/owner-host.lisp) installs for an article: at or over the budget it
; returns the configured owner unchanged, below it it is `fn-opc-prepare'.
; The count it compares is the committed record list of the file kernel the
; owner already carries, `fn-sbud-used', never the host's counter.
(in-package "ACL2")
(include-book "byte-store-frame")
(include-book "store-events")
(include-book "store-node")

; -----------------------------------------------------------------------------
; The count, the budget and the verdict

(defun fn-sbud-used (s)
  "Committed transactions of the Store state S: its file kernel's records."
  (declare (xargs :guard t))
  (len (fn-sf-records (fn-sn-files s))))

(defun fn-sbud-budget (profile kind)
  "Transactions the persisted PROFILE admits for a record of KIND; 0 when the
profile is not one of the named profiles, does not cover its own aggregate,
or cannot hold KIND's worst-case encoded record."
  (declare (xargs :guard t))
  (if (and (fn-bs-meta-config-valuesp profile)
           (fn-bs-profile-aggregate-covers-recordsp profile)
           (<= (fn-store-publication-ceiling kind)
               (fn-bs-profile-record-ceiling profile)))
      (nfix (fn-bs-meta-nth 4 profile))
    0))

(defun fn-sbud-admitp (budget used)
  (declare (xargs :guard t))
  (and (natp budget) (natp used) (< used budget)))

(defun fn-sbud-verdict (profile kind s)
  "The owner's publication verdict for one more record of KIND."
  (declare (xargs :guard t))
  (if (fn-sbud-admitp (fn-sbud-budget profile kind) (fn-sbud-used s))
      :admissible
    :unaffordable))

; The operator's headroom: transactions used and budgeted, and the retention
; ledger's reserved charge and capacity (4096-octet pages plus one unit per
; record, `fn-charge-for-payload').
(defun fn-sbud-headroom (profile s)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-sbud-used s)
        (fn-sbud-budget profile :article)
        (fn-retain-reserved (fn-node-retention (fn-sn-node s)))
        (fn-retain-capacity (fn-node-retention (fn-sn-node s)))))

; -----------------------------------------------------------------------------
; Keystones

(local
 (defthm fn-sbud-profile-budget-natp
   (implies (fn-bs-meta-config-valuesp profile)
            (natp (fn-bs-meta-nth 4 profile)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-bs-meta-config-valuesp)))))

; The carried budget is the persisted profile's admissibility, the check the
; host used to ask with its own count (fn-store-publication-admissibility).
(defthm fn-sbud-budget-is-the-profile-admissibility
  (iff (fn-sbud-admitp (fn-sbud-budget profile kind) used)
       (fn-bs-publication-admissiblep
        profile used (fn-store-publication-ceiling kind)))
  :hints (("Goal" :in-theory (disable fn-bs-meta-config-valuesp
                                      fn-bs-profile-record-ceiling
                                      fn-bs-profile-aggregate-covers-recordsp
                                      fn-store-publication-ceiling))))

; The two named profiles' article budgets, from their persisted values.
(defthm fn-sbud-named-profile-article-budgets
  (and (equal (fn-sbud-budget (fn-bs-config-for-profile :development) :article)
              128)
       (equal (fn-sbud-budget (fn-bs-config-for-profile :scale) :article)
              4096)))

; -----------------------------------------------------------------------------
; The count is the store's transaction namespace

(defun fn-sbud-sequences (records)
  (declare (xargs :guard t))
  (if (consp records)
      (cons (fn-store-event-sequence (car records))
            (fn-sbud-sequences (cdr records)))
    nil))

(defun fn-sbud-iota (start n)
  (declare (xargs :guard (and (natp start) (natp n))))
  (if (zp n) nil (cons start (fn-sbud-iota (1+ start) (1- n)))))

(local
 (defthm fn-sbud-record-list-sequences
   (implies (fn-sf-record-listp records sequence lower frontier)
            (equal (fn-sbud-sequences records)
                   (fn-sbud-iota sequence (len records))))
   :hints (("Goal" :in-theory (enable fn-sf-record-listp)))))

; A well-formed file kernel's committed records are numbered 0 .. used-1:
; the transaction namespace the host enumerates at open (one
; `%020d.txn' per sequence) has exactly `fn-sbud-used' names, and the next
; staged record takes sequence `fn-sbud-used' (fn-sf-candidatep).
(defthm fn-sbud-used-names-the-transaction-namespace
  (implies (fn-sf-statep (fn-sn-files s))
           (equal (fn-sbud-sequences (fn-sf-records (fn-sn-files s)))
                  (fn-sbud-iota 0 (fn-sbud-used s))))
  :hints (("Goal" :in-theory (enable fn-sf-statep))))

(defthm fn-sbud-candidate-takes-sequence-used
  (implies (fn-sf-candidatep record (fn-sf-records (fn-sn-files s)) frontier)
           (equal (fn-store-event-sequence record) (fn-sbud-used s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sf-candidatep))))

(in-theory (disable fn-sbud-used fn-sbud-budget fn-sbud-verdict
                    fn-sbud-headroom))
