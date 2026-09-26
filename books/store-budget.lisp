; fn: the Store's transaction budget, decided by the served prepare (M5).
;
; Where the budget comes from.  A store's persisted profile
; (books/byte-store-frame.lisp, format 8: the operator's fields, validated by
; `fn-bs-profile-validp') is written by `init' and decoded by
; `fn-bs-config-decode' at every open.  Its max_transactions field T is the
; transaction budget and its max_history_octets field H bounds the committed
; record octets (128 and 24 MiB for :development, 4096 and 768 MiB for
; :scale, 2^32-1 and 1 TiB by default).  The owner hands the
; decoded values back to ACL2 once, at open (host/owner-host.lisp
; `fn-owner-install-profile'), and every later decision reads that carried
; value; no host constant and no host count enters it.
;
; Why the budget is fixed at init.  The profile bounds the work of opening the
; store BEFORE any configuration record is replayed: the transaction
; namespace is enumerated with the budget as its readdir bound
; (host/native/io.lisp `fnn-transaction-files') and the aggregate replay input
; is the profile's max_history_octets.  A configuration record lives
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
(include-book "consumer-event-index-store-invariants")

; -----------------------------------------------------------------------------
; The count, the budget and the verdict

(defun fn-sbud-used (s)
  "Committed transactions of the Store state S: its file kernel's records."
  (declare (xargs :guard t))
  (len (fn-sf-records (fn-sn-files s))))

(defun fn-sbud-budget (profile kind)
  "Transactions the persisted PROFILE admits for a record of KIND: its
max_transactions field; 0 when the profile is not admitted or its record
ceiling cannot hold KIND's worst-case encoded record."
  (declare (xargs :guard t))
  (if (and (fn-bs-profile-admittedp profile)
           (<= (fn-store-publication-ceiling kind)
               (fn-bs-profile-record-ceiling profile)))
      (fn-bs-profile-max-transactions profile)
    0))

(defun fn-sbud-admitp (budget used)
  (declare (xargs :guard t))
  (and (natp budget) (natp used) (< used budget)))

; The committed record octets: the sum of the encoded lengths of the file
; kernel's records, counted exactly as `fn-sbud-used' counts the records.
(defun fn-sbud-record-octets (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (+ (len (fn-store-event-encode (car records)))
         (fn-sbud-record-octets (cdr records)))
    0))

(defun fn-sbud-bytes-used (s)
  "Committed record octets of the Store state S."
  (declare (xargs :guard t :verify-guards nil))
  (fn-sbud-record-octets (fn-sf-records (fn-sn-files s))))

(defun fn-sbud-verdict-at (profile kind used bytes-used)
  "The publication verdict for one more record of KIND, given the committed
count USED and committed record octets BYTES-USED: the count is below the
budget and the kind's worst-case record fits the history bound."
  (declare (xargs :guard t))
  (if (and (fn-sbud-admitp (fn-sbud-budget profile kind) used)
           (fn-bs-history-admissiblep profile bytes-used
                                      (fn-store-publication-ceiling kind)))
      :admissible
    :unaffordable))

(defun fn-sbud-verdict (profile kind s)
  "The owner's publication verdict for one more record of KIND."
  (declare (xargs :guard t :verify-guards nil))
  (fn-sbud-verdict-at profile kind (fn-sbud-used s) (fn-sbud-bytes-used s)))

; The operator's headroom: transactions used and budgeted, record octets used
; and the history bound, and the retention ledger's reserved charge and
; capacity (4096-octet pages plus one unit per record, `fn-charge-for-payload').
; BYTES-USED is the committed record octets; the served owner passes its
; carried sum (`fn-sbud-bytes-extend', below), every other caller
; `fn-sbud-bytes-used'.
(defun fn-sbud-headroom-at (profile s bytes-used)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-sbud-used s)
        (fn-sbud-budget profile :article)
        bytes-used
        (fn-bs-profile-max-history-octets profile)
        (fn-retain-reserved (fn-node-retention (fn-sn-node s)))
        (fn-retain-capacity (fn-node-retention (fn-sn-node s)))))

(defun fn-sbud-headroom (profile s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sbud-headroom-at profile s (fn-sbud-bytes-used s)))

; -----------------------------------------------------------------------------
; The carried record-octet sum
;
; The served owner asks the verdict per article.  Re-encoding every committed
; record for it would be a whole-state walk per command, so the owner carries
; CACHE = (K . SUM), the record octets of the first K committed records, and
; extends it by the records committed since (host/owner-host.lisp
; `fn-owner-publication-verdict').  Committed records are immutable within
; one owner process; the owner resets the cache when it installs a profile
; at open.

(defun fn-sbud-octets-cache-validp (cache records)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp cache) (natp (car cache)) (<= (car cache) (len records))
       (equal (cdr cache) (fn-sbud-record-octets (take (car cache) records)))))

(defun fn-sbud-bytes-extend (cache records)
  "The record octets of RECORDS from CACHE: the cached sum plus the records
past its count; a full walk when CACHE is not a (K . SUM) pair within RECORDS."
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp cache) (natp (car cache)) (natp (cdr cache))
           (<= (car cache) (len records)))
      (+ (cdr cache) (fn-sbud-record-octets (nthcdr (car cache) records)))
    (fn-sbud-record-octets records)))

; -----------------------------------------------------------------------------
; Keystones

(local
 (defthm fn-sbud-record-octets-split
   (equal (fn-sbud-record-octets records)
          (+ (fn-sbud-record-octets (take k records))
             (fn-sbud-record-octets (nthcdr k records))))
   :rule-classes nil
   :hints (("Goal" :induct (nthcdr k records)
            :in-theory (e/d (take nthcdr) (fn-store-event-encode))))))

; KEYSTONE (the carried sum is the kernel's).  From a cache that is the
; record octets of a prefix of the committed records, the carried extension
; is exactly the committed record octets `fn-sbud-bytes-used' counts.
(defthm fn-sbud-bytes-used-is-kernel-sum
  (implies (fn-sbud-octets-cache-validp cache (fn-sf-records (fn-sn-files s)))
           (equal (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))
                  (fn-sbud-bytes-used s)))
  :hints (("Goal" :use ((:instance fn-sbud-record-octets-split
                                   (records (fn-sf-records (fn-sn-files s)))
                                   (k (car cache))))
           :in-theory (e/d (fn-sbud-octets-cache-validp fn-sbud-bytes-extend
                            fn-sbud-bytes-used)
                           (fn-sbud-record-octets take nthcdr
                            fn-store-event-encode)))))

; The cache the owner keeps after a verdict, the count and sum of every
; committed record, is valid for the committed records it was taken from.
(defthm fn-sbud-full-cache-is-valid
  (implies (true-listp records)
           (fn-sbud-octets-cache-validp
            (cons (len records) (fn-sbud-record-octets records))
            records))
  :hints (("Goal" :in-theory (enable fn-sbud-octets-cache-validp))))

; The carried budget is the persisted profile's admissibility, the check the
; host used to ask with its own count (fn-store-publication-admissibility).
(defthm fn-sbud-budget-is-the-profile-admissibility
  (iff (fn-sbud-admitp (fn-sbud-budget profile kind) used)
       (fn-bs-publication-admissiblep
        profile used (fn-store-publication-ceiling kind)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-budget fn-sbud-admitp
                                   fn-bs-publication-admissiblep)
                                  (fn-bs-profile-admittedp
                                   fn-bs-profile-record-ceiling
                                   fn-bs-profile-max-transactions
                                   fn-store-publication-ceiling)))))

;  KEYSTONE (the verdict is the profile's two gates).  One more record of
; KIND is admissible exactly when the count gate the host asserts at publish
; (`fn-bs-publication-admissiblep': fewer than T committed, the kind's
; worst-case record within R) and the history gate (`fn-bs-history-admissiblep':
; the committed record octets plus that record within H) both admit it.
(defthm fn-sbud-verdict-is-the-count-and-history-admissibility
  (equal (fn-sbud-verdict-at profile kind used bytes-used)
         (if (and (fn-bs-publication-admissiblep
                   profile used (fn-store-publication-ceiling kind))
                  (fn-bs-history-admissiblep
                   profile bytes-used (fn-store-publication-ceiling kind)))
             :admissible
           :unaffordable))
  :hints (("Goal" :use ((:instance fn-sbud-budget-is-the-profile-admissibility))
           :in-theory (e/d (fn-sbud-verdict-at)
                           (fn-sbud-budget-is-the-profile-admissibility
                            fn-sbud-admitp fn-sbud-budget
                            fn-bs-publication-admissiblep
                            fn-bs-history-admissiblep)))))

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

(in-theory (disable fn-sbud-used fn-sbud-budget fn-sbud-verdict fn-sbud-verdict-at
                    fn-sbud-headroom fn-sbud-headroom-at fn-sbud-bytes-used fn-sbud-record-octets
                    fn-sbud-bytes-extend fn-sbud-octets-cache-validp))

; -----------------------------------------------------------------------------
; The maintained figures (PRF-180, lane hot-path-scans-2)
;
; The served owner asks the count and the committed record octets on every
; POST (the verdict, the prepare's budget) and at every status, health and
; headroom answer.  `fn-sbud-used' is `len' of the history and
; `fn-sbud-bytes-extend' walks `len' and `nthcdr' of it; both are the logical
; model and stay so.  What the host calls instead reads the Store's derived
; event index (books/consumer-event-index.lisp), which every host-called open
; builds from the history it read and `fn-sn-io''s record-directory append
; extends by the appended event -- the maintained relation `fn-ceis-indexedp',
; proved of every owner the host reaches with no hypothesis
; (books/owner-store-indexed.lisp `fn-osi-live-owner-store-is-indexed'):
;
;   the COUNT is the index's count, which `fn-cei-put' adds one to
;   (`fn-sbud-count', constant work);
;
;   the OCTETS are the host's (K . SUM) cache advanced over sequences
;   K .. count-1 by `fn-cei-get' (a fixed-depth lookup, constant-bounded in
;   the history) and each such record's encoded length (`fn-sbud-bytes-carried').
;   The index holds the committed event object itself, not its length; the
;   length is taken from that event, so a POST encodes the one record it
;   committed since the last query, never the history.  The length is NOT
;   recorded beside the event at the append: that would evaluate the
;   constrained record encoder inside a Store transition, which defconst
;   evaluation cannot run (record §3 of hot-path-scans-2026-09-26).
;
; Why a named function and not `mbe' inside `fn-sbud-used': an `:exec' that
; reads the index is equal to the `len' only under the relation, so the guard
; would have to carry `fn-ceis-indexedp', and a guard is evaluated when the
; :program host calls the function -- a full rebuild of the index per call.
; So the host calls `fn-sbud-count' and the theorems below equate it with
; `fn-sbud-used' under the relation, the pattern of books/owner-prepare-carried.

(defun fn-sbud-count (s)
  "Committed transactions of the Store state S, read from its derived event
index: equal to `fn-sbud-used' under `fn-ceis-indexedp'."
  (declare (xargs :guard t))
  (fn-cei-count (fn-sn-event-index s)))

; KEYSTONE (the count).  Under the maintained relation the carried count is
; the committed record count.
(defthm fn-sbud-count-is-used
  (implies (fn-ceis-indexedp s)
           (equal (fn-sbud-count s) (fn-sbud-used s)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-count fn-sbud-used fn-ceis-indexedp)
                                  (fn-cei-correspondencep)))))

; The committed octets of the records at sequences K .. COUNT-1 of INDEX,
; added to SUM: one index lookup and one record's encoded length per step.
(defun fn-sbud-octets-advance (k count sum index)
  (declare (xargs :guard (and (natp k) (natp count) (acl2-numberp sum))
                  :measure (nfix (- (nfix count) (nfix k)))
                  :verify-guards nil))
  (if (and (natp k) (natp count) (< k count))
      (fn-sbud-octets-advance
       (1+ k) count
       (+ sum (len (fn-store-event-encode (fn-cei-get k index))))
       index)
    sum))

; The committed record octets of S from the carried CACHE = (K . SUM): the
; records past K read through the index; the fold when CACHE is not a
; (K . SUM) within the carried count, or the count is past the index's
; uint32 sequence space (a history no well-formed kernel holds: its txids
; are below the uint32 allocator frontier).
(defun fn-sbud-bytes-carried (cache s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((count (fn-sbud-count s)))
    (if (and (consp cache) (natp (car cache)) (natp (cdr cache))
             (<= (car cache) count)
             (<= count (1+ *fn-cbor-max-uint*)))
        (fn-sbud-octets-advance (car cache) count (cdr cache)
                                (fn-sn-event-index s))
      (fn-sbud-bytes-used s))))

;; The lookup without a true-list premise: the index is built from the
;; conses of the history alone, so the history's final cdr is irrelevant.
(local
 (defthm fn-sbud-build-aux-of-true-list-fix
   (equal (fn-cei-build-aux (true-list-fix events) sequence index)
          (fn-cei-build-aux events sequence index))
   :hints (("Goal" :induct (fn-cei-build-aux events sequence index)
            :in-theory (disable fn-cei-put)))))

(defthm fn-sbud-lookup-of-correspondence
  (implies (and (fn-cei-correspondencep index events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp k) (< k (len events)))
           (equal (fn-cei-get k index) (nth k events)))
  :hints (("Goal" :use ((:instance fn-cei-correspondence-lookup
                                   (events (true-list-fix events))
                                   (sequence k)))
           :in-theory (e/d (fn-cei-correspondencep fn-cei-build fn-cp-uintp)
                           (fn-cei-correspondence-lookup fn-cei-get
                            fn-cei-build-aux)))))

(local
 (defthm fn-sbud-record-octets-of-nthcdr-step
   (implies (and (natp k) (< k (len records)))
            (equal (fn-sbud-record-octets (nthcdr k records))
                   (+ (len (fn-store-event-encode (nth k records)))
                      (fn-sbud-record-octets (nthcdr (1+ k) records)))))
   :hints (("Goal" :induct (nthcdr k records)
            :in-theory (e/d (fn-sbud-record-octets nthcdr nth)
                            (fn-store-event-encode))))))

(local
 (defthm fn-sbud-record-octets-of-nthcdr-len
   (implies (and (natp k) (<= (len records) k))
            (equal (fn-sbud-record-octets (nthcdr k records)) 0))
   :hints (("Goal" :induct (nthcdr k records)
            :in-theory (e/d (fn-sbud-record-octets nthcdr)
                            (fn-store-event-encode))))))

; The advance over a corresponding index is the fold over the suffix.
(defthm fn-sbud-octets-advance-is-the-suffix-fold
  (implies (and (fn-cei-correspondencep index events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp k) (<= k (len events)) (acl2-numberp sum))
           (equal (fn-sbud-octets-advance k (len events) sum index)
                  (+ sum (fn-sbud-record-octets (nthcdr k events)))))
  :hints (("Goal" :induct (fn-sbud-octets-advance k (len events) sum index)
           :in-theory (e/d (fn-sbud-octets-advance fn-cp-uintp)
                           (fn-store-event-encode fn-cei-correspondencep
                            fn-cei-get fn-sbud-record-octets)))))

; KEYSTONE (the carried octets).  Under the maintained relation, from a
; cache that is the record octets of a prefix of the committed records, the
; carried figure is the fold `fn-sbud-bytes-used'.
(defthm fn-sbud-bytes-carried-is-the-fold
  (implies (and (fn-ceis-indexedp s)
                (fn-sbud-octets-cache-validp cache (fn-sf-records (fn-sn-files s))))
           (equal (fn-sbud-bytes-carried cache s)
                  (fn-sbud-bytes-used s)))
  :hints (("Goal" :use ((:instance fn-sbud-octets-advance-is-the-suffix-fold
                                   (index (fn-sn-event-index s))
                                   (events (fn-sf-records (fn-sn-files s)))
                                   (k (car cache)) (sum (cdr cache)))
                        (:instance fn-sbud-bytes-used-is-kernel-sum))
           :in-theory (e/d (fn-sbud-bytes-carried fn-sbud-octets-cache-validp
                            fn-sbud-bytes-extend fn-ceis-indexedp fn-sbud-used)
                           (fn-sbud-octets-advance fn-sbud-record-octets
                            fn-sbud-count fn-cei-correspondencep
                            fn-sbud-octets-advance-is-the-suffix-fold
                            fn-sbud-bytes-used-is-kernel-sum
                            fn-store-event-encode take nthcdr)))))

; The cache the owner keeps after a query, (COUNT . OCTETS), stays valid as
; the history only grows: a prefix's sum is the same prefix's sum of a longer
; list.
(local
 (defthm fn-sbud-take-of-append
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))
   :hints (("Goal" :induct (nthcdr k a) :in-theory (enable take nthcdr)))))

(defthm fn-sbud-octets-cache-valid-after-commit
  (implies (fn-sbud-octets-cache-validp cache records)
           (fn-sbud-octets-cache-validp cache (append records more)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-octets-cache-validp)
                                  (fn-sbud-record-octets)))))

(defthm fn-sbud-empty-cache-is-valid
  (fn-sbud-octets-cache-validp (cons 0 0) records)
  :hints (("Goal" :in-theory (enable fn-sbud-octets-cache-validp
                                     fn-sbud-record-octets))))

; The operator's headroom over the carried count: `fn-sbud-headroom-at' with
; the count read from the index.
(defun fn-sbud-headroom-carried (profile s bytes-used)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-sbud-count s)
        (fn-sbud-budget profile :article)
        bytes-used
        (fn-bs-profile-max-history-octets profile)
        (fn-retain-reserved (fn-node-retention (fn-sn-node s)))
        (fn-retain-capacity (fn-node-retention (fn-sn-node s)))))

(defthm fn-sbud-headroom-carried-is-headroom-at
  (implies (fn-ceis-indexedp s)
           (equal (fn-sbud-headroom-carried profile s bytes-used)
                  (fn-sbud-headroom-at profile s bytes-used)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-headroom-carried fn-sbud-headroom-at)
                                  (fn-sbud-count fn-sbud-used)))))

(in-theory (disable fn-sbud-count fn-sbud-octets-advance fn-sbud-bytes-carried
                    fn-sbud-headroom-carried))
