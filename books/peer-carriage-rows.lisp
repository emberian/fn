; fn: a peer boundary's opaque-carriage budget as typed configuration rows
; (PRF-099; review 2026-09-24, gpt-6 direction: "Permit [unknown-author
; carriage] only under an explicit peer/group/byte policy").
;
; A boundary that carries principals this node has not enrolled (D23, the
; `carries-principal' rows books/peer-authored-accept.lisp reads) holds their
; articles against a budget of its own: two rows of the peer's configuration
; group whose natural slot is typed by the row recognizer (`fn-cfg-rowp':
; uint32), not a decimal string,
;
;   (name "carried-budget-charge" "" CHARGE)   ; Store charge units
;   (name "carried-budget-count"  "" COUNT)    ; carried articles
;
; CHARGE is in the Store's own resource unit, the one the retention capacity
; and the quotas use (`fn-charge-for-payload', books/identity.lisp: one unit
; per started 4096-octet page plus one), so the row width is the capacity's
; width and never caps below a store the operator can write (D27).  The
; operator's verb takes octets and rounds down to whole pages
; (books/native-admin-peer.lisp `peer budget NAME OCTETS COUNT').  A peer
; with no budget rows has no budget, and the carried arm then admits nothing
; (books/peer-carriage.lisp `fn-pcb-admission').
;
; This book is the rows alone (config only), so the operator's parser and the
; acceptance decision read one spelling.  It also owns the merge that lets a
; boundary's carried list and budget change across requests: the operator's
; argv bound stays a per-request work bound (D27) and a list longer than one
; request grows by `peer carries NAME HEX ...' requests.
(in-package "ACL2")
(include-book "config")

(defconst *fn-pcb-charge-slot* "carried-budget-charge")
(defconst *fn-pcb-count-slot* "carried-budget-count")

; The natural of the first row whose slot is SLOT, or nil.
(defun fn-pcb-slot-natural (slot rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-b (car rows)) slot)
          (if (natp (fn-cfg-row-n (car rows))) (fn-cfg-row-n (car rows)) nil)
        (fn-pcb-slot-natural slot (cdr rows)))
    nil))

(defun fn-pcb-budgetp (budget)
  (declare (xargs :guard t))
  (and (true-listp budget) (equal (len budget) 2)
       (natp (car budget)) (natp (cadr budget))))

; (CHARGE COUNT) when both rows are present, else nil: no budget.
(defun fn-pcb-budget-of-rows (rows)
  (declare (xargs :guard t))
  (let ((charge (fn-pcb-slot-natural *fn-pcb-charge-slot* rows))
        (count (fn-pcb-slot-natural *fn-pcb-count-slot* rows)))
    (if (and (natp charge) (natp count)) (list charge count) nil)))

; The delivering boundary's budget: its rows in the configured peer table.
(defun fn-pcb-peer-budget (peer peers)
  (declare (xargs :guard t))
  (fn-pcb-budget-of-rows (fn-cfg-rows-with-key peers peer)))

(defthm fn-pcb-peer-budget-is-typed-or-absent
  (let ((b (fn-pcb-peer-budget peer peers)))
    (or (null b) (fn-pcb-budgetp b)))
  :rule-classes nil)

(defun fn-pcb-budget-rows (name charge count)
  (declare (xargs :guard t))
  (list (fn-cfg-row-make name *fn-pcb-charge-slot* "" charge)
        (fn-cfg-row-make name *fn-pcb-count-slot* "" count)))

; -----------------------------------------------------------------------------
; Growing a boundary's rows across requests.  NEW replaces the existing
; budget rows when it carries a budget slot, and appends every row not
; already present; nothing else of the peer's group changes.

; The peer's NEWNEWS pull interval in seconds (PRF-100, books/peer-pull.lisp;
; `peer pull NAME SECONDS').  Single-valued like the budget rows, so a new
; interval supersedes the old one on extension.
(defconst *fn-pcb-pull-interval-slot* "pull-interval")

; How many consecutive complete rounds an id the peer lists but answers 430
; holds the pull cursor (PRF-165, books/peer-pull.lisp; `peer pull NAME
; SECONDS ROUNDS').  Single-valued; absent means the book's policy default.
(defconst *fn-pcb-pull-unavailable-slot* "pull-unavailable-rounds")

(defun fn-pcb-budget-slotp (slot)
  ; The single-valued slots: a new row replaces the old one on extension.
  (declare (xargs :guard t))
  (or (equal slot *fn-pcb-charge-slot*) (equal slot *fn-pcb-count-slot*)
      (equal slot *fn-pcb-pull-interval-slot*)
      (equal slot *fn-pcb-pull-unavailable-slot*)))

(defun fn-pcb-slot-memberp (slot rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (equal (fn-cfg-row-b (car rows)) slot)
          (fn-pcb-slot-memberp slot (cdr rows)))
    nil))

(defun fn-pcb-row-supersededp (row new)
  (declare (xargs :guard t))
  (or (and (member-equal row (if (true-listp new) new nil)) t)
      (and (fn-pcb-budget-slotp (fn-cfg-row-b row))
           (fn-pcb-slot-memberp (fn-cfg-row-b row) new))))

(defun fn-pcb-kept-rows (existing new)
  (declare (xargs :guard t))
  (if (consp existing)
      (if (fn-pcb-row-supersededp (car existing) new)
          (fn-pcb-kept-rows (cdr existing) new)
        (cons (car existing) (fn-pcb-kept-rows (cdr existing) new)))
    nil))

(defun fn-pcb-extend-rows (existing new)
  (declare (xargs :guard t))
  (append (fn-pcb-kept-rows existing new) (if (true-listp new) new nil)))

; The (:set-peer NAME ROWS) delta that extends NAME's group in PEERS by NEW,
; or nil when PEERS has no such peer (an extension never creates a peer).
(defun fn-pcb-extend-delta (name new peers)
  (declare (xargs :guard t))
  (let ((existing (fn-cfg-rows-with-key peers name)))
    (if (and (consp existing) (consp new))
        (fn-cfg-set-peer name (fn-pcb-extend-rows existing new))
      nil)))

; -----------------------------------------------------------------------------
; The admission theorem for the operator's budget rows.

(local (defthm fn-pcb-slot-natural-of-append
  (equal (fn-pcb-slot-natural slot (append a b))
         (if (fn-pcb-slot-memberp slot a)
             (fn-pcb-slot-natural slot a)
           (fn-pcb-slot-natural slot b)))))

(local (defthm fn-pcb-kept-rows-drop-new-budget-slots
  (implies (and (fn-pcb-budget-slotp slot) (fn-pcb-slot-memberp slot new))
           (not (fn-pcb-slot-memberp slot (fn-pcb-kept-rows existing new))))))

; KEYSTONE (the budget rows mean what the operator wrote).  Whatever rows the
; boundary had, extending them by `fn-pcb-budget-rows' makes the budget
; reader answer exactly (CHARGE COUNT).
(defthm fn-pcb-budget-after-extension
  (implies (and (natp charge) (natp count))
           (equal (fn-pcb-budget-of-rows
                   (fn-pcb-extend-rows existing
                                       (fn-pcb-budget-rows name charge count)))
                  (list charge count))))

(local (in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-without-key
                          fn-cfg-rows-keyed-p)))

(local (defthm fn-pcb-rows-with-key-of-append
  (equal (fn-cfg-rows-with-key (append a b) k)
         (append (fn-cfg-rows-with-key a k) (fn-cfg-rows-with-key b k)))))

(local (defthm fn-pcb-rows-with-key-of-without-key
  (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows k) k) nil)))

(local (defthm fn-pcb-kept-rows-of-keyed
  (implies (fn-cfg-rows-keyed-p existing k)
           (fn-cfg-rows-keyed-p (fn-pcb-kept-rows existing new) k))))

(local (defthm fn-pcb-rows-keyed-of-append
  (equal (fn-cfg-rows-keyed-p (append a b) k)
         (and (fn-cfg-rows-keyed-p a k) (fn-cfg-rows-keyed-p b k)))))

(local (defthm fn-pcb-rows-with-key-is-keyed
  (fn-cfg-rows-keyed-p (fn-cfg-rows-with-key rows k) k)))

(local (defthm fn-pcb-rows-with-key-when-keyed
  (implies (and (fn-cfg-rows-keyed-p rows k) (true-listp rows))
           (equal (fn-cfg-rows-with-key rows k) rows))))

(local (defthm fn-pcb-budget-rows-keyed
  (fn-cfg-rows-keyed-p (fn-pcb-budget-rows name charge count) name)))

(local (defthm fn-pcb-true-listp-of-kept-rows
  (true-listp (fn-pcb-kept-rows existing new))))

(local
(defthm fn-pcb-rows-with-key-of-extend-rows
  (implies (and (fn-cfg-rows-keyed-p existing k)
                (fn-cfg-rows-keyed-p new k))
           (equal (fn-cfg-rows-with-key (fn-pcb-extend-rows existing new) k)
                  (fn-pcb-extend-rows existing new)))
  :hints (("Goal" :in-theory (enable fn-pcb-extend-rows)))))

; KEYSTONE (over the configuration the owner publishes).  When the named
; boundary exists, applying the extension delta with the operator's budget
; rows leaves exactly that budget under the boundary's name.
(defthm fn-pcb-peer-budget-after-extend-delta
  (implies (and (natp charge) (natp count)
                (consp (fn-cfg-rows-with-key (fn-cfg-peers v) name)))
           (equal (fn-pcb-peer-budget
                   name
                   (fn-cfg-peers
                    (fn-cfg-apply-delta
                     v gen stamp
                     (fn-pcb-extend-delta name
                                          (fn-pcb-budget-rows name charge count)
                                          (fn-cfg-peers v)))))
                  (list charge count)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-delta fn-cfg-set-peer)
                                  (fn-pcb-budget-of-rows fn-pcb-extend-rows
                                   fn-pcb-budget-rows))
           :use ((:instance fn-pcb-budget-after-extension
                            (existing (fn-cfg-rows-with-key (fn-cfg-peers v)
                                                            name)))))))

; -----------------------------------------------------------------------------
; The incremental extension (D27, PRF-171; PKT-436's default).  The record an
; extension publishes carries only the rows it changes: (:add-peer-rows NAME
; NEW), then, when NEW supersedes a single-valued slot the group already
; holds, (:remove-peer-rows NAME GONE) with exactly those superseded rows.
; `*fn-cfg-max-rows*' is then a work bound on one request's delta, and the
; peer's group grows past it across requests.  `fn-pcb-extend-delta' (the
; whole group as one :set-peer) stays the logical model; the theorem below
; equates the two, so every keystone stated over it holds of what the host
; publishes.

; The rows of EXISTING a single-valued slot of NEW supersedes, other than
; rows NEW itself carries (those the add already leaves in place).
(defun fn-pcb-slot-superseded-rows (existing new)
  (declare (xargs :guard t))
  (if (consp existing)
      (if (and (not (member-equal (car existing) (if (true-listp new) new nil)))
               (fn-pcb-budget-slotp (fn-cfg-row-b (car existing)))
               (fn-pcb-slot-memberp (fn-cfg-row-b (car existing)) new))
          (cons (car existing)
                (fn-pcb-slot-superseded-rows (cdr existing) new))
        (fn-pcb-slot-superseded-rows (cdr existing) new))
    nil))

; The deltas that extend NAME's group in PEERS by NEW, or nil when PEERS has
; no such peer (an extension never creates a peer).  Host:
; books/native-admin.lisp `fn-native-admin-plan-deltas-over', called from
; host/native-admin-host.lisp `fn-native-admin-host-owner-reconfigure' and
; `fn-native-admin-host-apply'.
(defun fn-pcb-extend-deltas (name new peers)
  (declare (xargs :guard t))
  (let ((existing (fn-cfg-rows-with-key peers name)))
    (if (and (consp existing) (consp new))
        (let ((gone (fn-pcb-slot-superseded-rows existing new)))
          (cons (fn-cfg-add-peer-rows name new)
                (if (consp gone)
                    (list (fn-cfg-remove-peer-rows name gone))
                  nil)))
      nil)))

(local (in-theory (enable fn-cfg-rows-without-members fn-cfg-rows-within
                          fn-pcb-kept-rows fn-pcb-extend-rows
                          fn-pcb-row-supersededp)))

(local (defthm fn-pcb-without-members-of-append
  (equal (fn-cfg-rows-without-members (append a b) d)
         (append (fn-cfg-rows-without-members a d)
                 (fn-cfg-rows-without-members b d)))))

(local (defthm fn-pcb-member-of-superseded
  (iff (member-equal e (fn-pcb-slot-superseded-rows existing new))
       (and (member-equal e existing)
            (not (member-equal e (if (true-listp new) new nil)))
            (fn-pcb-budget-slotp (fn-cfg-row-b e))
            (fn-pcb-slot-memberp (fn-cfg-row-b e) new)))
  :hints (("Goal" :induct (fn-pcb-slot-superseded-rows existing new)
           :in-theory (disable fn-pcb-budget-slotp fn-pcb-slot-memberp)))))

(local (defthm fn-pcb-true-listp-of-superseded
  (true-listp (fn-pcb-slot-superseded-rows existing new))))

(local (defthm fn-pcb-without-superseded-of-new-part
  (implies (and (true-listp new) (true-listp xs) (subsetp-equal xs new))
           (equal (fn-cfg-rows-without-members
                   xs (fn-pcb-slot-superseded-rows existing new))
                  xs))))

(local (defthm fn-pcb-without-superseded-of-kept-part
  (implies (and (true-listp new) (subsetp-equal xs existing))
           (equal (fn-cfg-rows-without-members
                   (fn-cfg-rows-without-members xs new)
                   (fn-pcb-slot-superseded-rows existing new))
                  (fn-pcb-kept-rows xs new)))))

(local (defthm fn-pcb-subsetp-equal-of-cons
  (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(local (defthm fn-pcb-subsetp-equal-refl
  (subsetp-equal x x)))

(local (defthm fn-pcb-without-members-of-atom
  (implies (and (true-listp rows) (not (consp d)))
           (equal (fn-cfg-rows-without-members rows d) rows))))

(local (defthm fn-pcb-without-members-is-kept-when-nothing-superseded
  (implies (and (true-listp new)
                (not (consp (fn-pcb-slot-superseded-rows existing new))))
           (equal (fn-cfg-rows-without-members existing new)
                  (fn-pcb-kept-rows existing new)))
  :hints (("Goal" :use ((:instance fn-pcb-without-superseded-of-kept-part
                                   (xs existing)))
           :in-theory (disable fn-pcb-without-superseded-of-kept-part)))))

(local (defthm fn-pcb-without-members-keyed
  (implies (fn-cfg-rows-keyed-p rows k)
           (fn-cfg-rows-keyed-p (fn-cfg-rows-without-members rows d) k))))

(local (defthm fn-pcb-without-key-of-keyed
  (implies (fn-cfg-rows-keyed-p rows k)
           (equal (fn-cfg-rows-without-key rows k) nil))))

(local (defthm fn-pcb-without-key-idempotent
  (equal (fn-cfg-rows-without-key (fn-cfg-rows-without-key rows k) k)
         (fn-cfg-rows-without-key rows k))))

(local (defthm fn-pcb-without-key-of-append
  (equal (fn-cfg-rows-without-key (append a b) k)
         (append (fn-cfg-rows-without-key a k)
                 (fn-cfg-rows-without-key b k)))))

(local (defthm fn-pcb-true-listp-of-without-members
  (true-listp (fn-cfg-rows-without-members rows d))))

(local (defthm fn-pcb-true-listp-of-with-key
  (true-listp (fn-cfg-rows-with-key rows k))))

(local (defthm fn-pcb-extend-deltas-apply-when-extending
  (implies (and (true-listp new)
                (fn-cfg-rows-keyed-p new name)
                (fn-pcb-extend-delta name new (fn-cfg-peers v)))
           (equal (fn-cfg-apply v gen stamp
                                (fn-pcb-extend-deltas name new (fn-cfg-peers v)))
                  (fn-cfg-apply-delta v gen stamp
                                      (fn-pcb-extend-delta name new
                                                           (fn-cfg-peers v)))))
  :hints (("Goal" :in-theory (enable fn-cfg-apply fn-cfg-apply-delta
                                     fn-cfg-set-peer fn-cfg-add-peer-rows
                                     fn-cfg-remove-peer-rows)))))

(local (defthm fn-pcb-apply-delta-of-nil
  (equal (fn-cfg-apply-delta v gen stamp nil) v)
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-delta-kind
                                     fn-cfg-ag-car)))))

; KEYSTONE (the incremental record is the whole-group extension).  Applying
; the deltas the host publishes leaves exactly the configuration value the
; single :set-peer of the extended group leaves (and, for a peer that does
; not exist, both leave the value alone), so the budget keystone
; `fn-pcb-peer-budget-after-extend-delta' and every theorem over
; `fn-pcb-extend-delta' hold of the published record.
(defthm fn-pcb-extend-deltas-apply-as-the-extend-delta
  (implies (and (true-listp new)
                (fn-cfg-rows-keyed-p new name))
           (equal (fn-cfg-apply v gen stamp
                                (fn-pcb-extend-deltas name new (fn-cfg-peers v)))
                  (fn-cfg-apply-delta v gen stamp
                                      (fn-pcb-extend-delta name new
                                                           (fn-cfg-peers v)))))
  :hints (("Goal" :use fn-pcb-extend-deltas-apply-when-extending
           :in-theory (e/d (fn-pcb-extend-deltas fn-pcb-extend-delta
                                                 fn-cfg-apply)
                           (fn-pcb-extend-deltas-apply-when-extending
                            fn-cfg-apply-delta)))))

;; The work bound and the data it no longer caps (PRF-171).  Subject:
;; `fn-cfg-delta-reason' and `fn-cfg-apply-delta', which the live owner runs
;; through `fn-ocfg-step' (host/owner-host.lisp's reconfiguration) and the
;; replay through `fn-cfg-record-acceptablep' / `fn-cfg-apply-record'
;; (host/store-node-host.lisp `fn-store-cfg-peer-delta-record' admits the
;; record by the same predicate).

; KEYSTONE (the per-request work bound, exactly).  An :add-peer-rows delta
; for a peer that exists, with keyed rows, is refused exactly when it
; carries more than `*fn-cfg-max-rows*' rows, and admitted otherwise.  The
; bound is on the delta, not on the peer.
(defthm fn-cfg-add-peer-rows-refuses-exactly-past-the-work-bound
  (implies (and (fn-cfg-labelp name)
                (fn-cfg-row-listp rows)
                (consp rows)
                (fn-cfg-rows-keyed-p rows name)
                (consp (fn-cfg-rows-with-key (fn-cfg-peers v) name)))
           (equal (fn-cfg-delta-reason v gen stamp reserved ceiling
                                       (fn-cfg-add-peer-rows name rows))
                  (if (< *fn-cfg-max-rows* (len rows)) :malformed-delta nil)))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason fn-cfg-deltap
                                     fn-cfg-add-peer-rows))))

; KEYSTONE (the group grows by the delta's rows).  After an :add-peer-rows
; the peer's group is its old group, less the rows the delta repeats,
; followed by the delta's rows: nothing bounds the group but the records
; that built it.
(defthm fn-cfg-add-peer-rows-extends-the-group
  (implies (and (true-listp rows) (fn-cfg-rows-keyed-p rows name))
           (equal (fn-cfg-rows-with-key
                   (fn-cfg-peers (fn-cfg-apply-delta
                                  v gen stamp (fn-cfg-add-peer-rows name rows)))
                   name)
                  (append (fn-cfg-rows-without-members
                           (fn-cfg-rows-with-key (fn-cfg-peers v) name) rows)
                          rows)))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-add-peer-rows))))

(local (defthm fn-pcb-len-of-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-pcb-len-without-members
  (<= (len (fn-cfg-rows-without-members rows d)) (len rows))
  :rule-classes :linear))

(local (defthm fn-pcb-len-without-and-with-key
  (equal (+ (len (fn-cfg-rows-without-key rows k))
            (len (fn-cfg-rows-with-key rows k)))
         (len rows))
  :rule-classes :linear))

(local (defthm fn-pcb-len-without-key
  (<= (len (fn-cfg-rows-without-key rows k)) (len rows))
  :rule-classes :linear))

; KEYSTONE (one delta's work).  Whatever the delta, the peers slot grows by
; at most `*fn-cfg-max-rows*' rows; a record of at most `*fn-cfg-max-deltas*'
; deltas (`fn-cfg-recordp') by at most their product.  With the profile's
; configuration generations (`fn-cvec-config-publication-keeps-the-release-
; generation', books/store-capacity-config.lisp) that is the bound on the
; table; no constant bounds one peer's group.
(defthm fn-cfg-apply-delta-adds-at-most-the-work-bound
  (implies (fn-cfg-deltap d)
           (<= (len (fn-cfg-peers (fn-cfg-apply-delta v gen stamp d)))
               (+ (len (fn-cfg-peers v)) *fn-cfg-max-rows*)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-delta fn-cfg-deltap fn-cfg-set-groups)
                                  (fn-cfg-labelp fn-record-uint32p
                                   fn-cfg-row-listp)))))

(defthm fn-cfg-apply-adds-at-most-the-work-bound
  (implies (fn-cfg-delta-listp deltas)
           (<= (len (fn-cfg-peers (fn-cfg-apply v gen stamp deltas)))
               (+ (len (fn-cfg-peers v)) (* *fn-cfg-max-rows* (len deltas)))))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (e/d (fn-cfg-apply fn-cfg-delta-listp)
                           (fn-cfg-apply-delta fn-cfg-deltap)))))

(in-theory (disable fn-pcb-slot-natural fn-pcb-budget-of-rows
                    fn-pcb-kept-rows fn-pcb-extend-rows
                    fn-pcb-slot-superseded-rows fn-pcb-extend-deltas))
