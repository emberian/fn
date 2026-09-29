; fn: the store's group table as a lookup between a name and a small code.
;
; The compiled group list `*fn-store-groups*` and its hand-bumped version id
; are gone (packet R4 of specs/reconfiguration.md): a store's group table is
; its configuration record history (`books/config`, `books/node-config`),
; replayed at open, and the node carries it as the acceptance state's
; allocation domain.  What stays here is the one thing the bridge needs from a
; table it is handed: the mapping between a group name and its zero-based
; position, in both directions, and the theorems that the two directions are
; inverse.  A code is a name's position in the domain list, which creation
; only ever appends to, so a code is stable across retirement and revival.

(in-package "ACL2")
(include-book "cbor")
(include-book "rev-onto")

; The format id is encoded with the CBOR primitives, opened locally here.
(local (in-theory (enable fn-cbor-codec-vocabulary)))

; The durable store's configuration format.  A store records this string and
; a host refuses to open one whose format it does not recognise, so a store
; written under an earlier set of decisions is rejected by its configuration
; rather than read with today's meaning.  Format 6 writes ACL2-owned FNSM
; metadata frames.  Older JSON metadata remains in place and needs explicit
; offline migration; merely opening a new-format store never rewrites it.
; "fn-store-experiment-7".  Format 6 remains readable through the physical
; metadata profile, but a new store is never created under its smaller record
; ceiling.
(defconst *fn-store-format-id*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109
    101 110 116 45 55))

(defun fn-store-group-name (code groups)
  ; The group at a zero-based code, or nil.
  (declare (xargs :guard (and (natp code) (true-listp groups))))
  (if (consp groups)
      (if (zp code)
          (car groups)
        (fn-store-group-name (- code 1) (cdr groups)))
    nil))

; Executes by a loop (lane depth-debt, PRF-919): its depth was the length of
; operator data (D27: no fixed cap), one control-stack frame per element.
(defun fn-store-group-code-in-loop (name groups i)
  (declare (xargs :guard (and (true-listp groups) (natp i))))
  (if (consp groups)
      (if (equal name (car groups))
          i
        (fn-store-group-code-in-loop name (cdr groups) (+ 1 i)))
    nil))

(defun fn-store-group-code-in (name groups)
  ; The zero-based code of a group, or nil.
  (declare (xargs :guard (true-listp groups) :verify-guards nil))
  (mbe :logic (if (consp groups)
                  (if (equal name (car groups))
                      0
                    (let ((rest (fn-store-group-code-in name (cdr groups))))
                      (if (null rest) nil (+ 1 rest))))
                nil)
       :exec (fn-store-group-code-in-loop name groups 0)))

(defthm fn-store-group-code-in-loop-is-plus
  (implies (natp i)
           (equal (fn-store-group-code-in-loop name groups i)
                  (let ((r (fn-store-group-code-in name groups)))
                    (if r (+ i r) nil)))))

(verify-guards fn-store-group-code-in)

; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element (an article's Newsgroups list: header
; content, no fixed cap).  The right fold runs from the left over the reversed
; list; the base is the recursion's, decided by the list's final tail.
(defun fn-store-groups-from-codes-step (groups x rest)
  (declare (xargs :guard (and (true-listp groups)
                              (or (equal rest :bad) (true-listp rest)))))
  (let ((group (if (natp x) (fn-store-group-name x groups) nil)))
    (if group
        (if (or (equal rest :bad) (member-equal group rest))
            :bad
          (cons group rest))
      :bad)))

(defun fn-store-groups-from-codes-loop (rev groups acc)
  (declare (xargs :guard (and (true-listp groups)
                              (or (equal acc :bad) (true-listp acc)))))
  (if (consp rev)
      (fn-store-groups-from-codes-loop (cdr rev) groups (fn-store-groups-from-codes-step groups (car rev) acc))
    acc))

(defun fn-store-groups-from-codes (codes groups)
  ; A code list becomes a distinct group list from the table, or :bad.
  ; Duplicate and unknown codes are refused here rather than deeper in the
  ; model.
  (declare (xargs :guard (true-listp groups) :verify-guards nil))
  (mbe :logic
   (if (consp codes)
      (let ((group (if (natp (car codes))
                       (fn-store-group-name (car codes) groups)
                     nil)))
        (if group
            (let ((rest (fn-store-groups-from-codes (cdr codes) groups)))
              (if (or (equal rest :bad) (member-equal group rest))
                  :bad
                (cons group rest)))
          :bad))
    (if (null codes) nil :bad))
   :exec (fn-store-groups-from-codes-loop (fn-ag-rev-onto codes nil) groups
                      (if (true-listp codes) nil :bad))))

(defthm fn-store-groups-from-codes-loop-of-rev-onto
  (equal (fn-store-groups-from-codes-loop (fn-ag-rev-onto codes zs) groups (if (true-listp codes) nil :bad))
         (fn-store-groups-from-codes-loop zs groups (fn-store-groups-from-codes codes groups)))
  :hints (("Goal" :induct (fn-ag-rev-onto codes zs)
                  :in-theory (disable fn-store-group-name))))

(verify-guards fn-store-groups-from-codes
  :hints (("Goal" :use ((:instance fn-store-groups-from-codes-loop-of-rev-onto (zs nil)))
                  :in-theory (disable fn-store-groups-from-codes-loop-of-rev-onto))))

; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element (an article's Newsgroups list: header
; content, no fixed cap).  The right fold runs from the left over the reversed
; list; the base is the recursion's, decided by the list's final tail.
(defun fn-store-codes-from-groups-step (groups x rest)
  (declare (xargs :guard (and (true-listp groups)
                              (or (equal rest :bad) (true-listp rest)))))
  (let ((code (fn-store-group-code-in x groups)))
    (if (null code)
        :bad
      (if (or (equal rest :bad) (member-equal code rest))
          :bad
        (cons code rest)))))

(defun fn-store-codes-from-groups-loop (rev groups acc)
  (declare (xargs :guard (and (true-listp groups)
                              (or (equal acc :bad) (true-listp acc)))))
  (if (consp rev)
      (fn-store-codes-from-groups-loop (cdr rev) groups (fn-store-codes-from-groups-step groups (car rev) acc))
    acc))

(defun fn-store-codes-from-groups (names groups)
  ; The inverse direction the Python boundary needs: names to codes, or :bad.
  (declare (xargs :guard (true-listp groups) :verify-guards nil))
  (mbe :logic
   (if (consp names)
      (let ((code (fn-store-group-code-in (car names) groups)))
        (if (null code)
            :bad
          (let ((rest (fn-store-codes-from-groups (cdr names) groups)))
            (if (or (equal rest :bad) (member-equal code rest))
                :bad
              (cons code rest)))))
    (if (null names) nil :bad))
   :exec (fn-store-codes-from-groups-loop (fn-ag-rev-onto names nil) groups
                      (if (true-listp names) nil :bad))))

(defthm fn-store-codes-from-groups-loop-of-rev-onto
  (equal (fn-store-codes-from-groups-loop (fn-ag-rev-onto names zs) groups (if (true-listp names) nil :bad))
         (fn-store-codes-from-groups-loop zs groups (fn-store-codes-from-groups names groups)))
  :hints (("Goal" :induct (fn-ag-rev-onto names zs)
                  :in-theory (disable fn-store-group-code-in))))

(verify-guards fn-store-codes-from-groups
  :hints (("Goal" :use ((:instance fn-store-codes-from-groups-loop-of-rev-onto (zs nil)))
                  :in-theory (disable fn-store-codes-from-groups-loop-of-rev-onto))))

; -----------------------------------------------------------------------------
; The two directions are inverse

; The general facts, by induction over the table, and then the two entry
; points as instances of them.

(defthm fn-store-group-code-in-natp
  (implies (fn-store-group-code-in name groups)
           (natp (fn-store-group-code-in name groups))))

(defthm fn-store-group-name-of-code-in
  (implies (fn-store-group-code-in name groups)
           (equal (fn-store-group-name
                   (fn-store-group-code-in name groups) groups)
                  name))
  :hints (("Goal" :induct (fn-store-group-code-in name groups))))

(defthm fn-store-group-name-is-a-member
  (implies (fn-store-group-name code groups)
           (member-equal (fn-store-group-name code groups) groups))
  :hints (("Goal" :induct (fn-store-group-name code groups))))

(defthm fn-store-group-code-in-of-name
  (implies (and (natp code)
                (no-duplicatesp-equal groups)
                (fn-store-group-name code groups))
           (equal (fn-store-group-code-in
                   (fn-store-group-name code groups) groups)
                  code))
  :hints (("Goal" :induct (fn-store-group-name code groups))))

; A code names one group: two names with the same code are the same name.
; With the compiled table this was decided by evaluation; over a table
; parameter it is the inversion lemma applied to both names.
(defthm fn-store-group-code-in-is-injective
  (implies (and (fn-store-group-code-in a groups)
                (fn-store-group-code-in b groups))
           (iff (equal (fn-store-group-code-in a groups)
                       (fn-store-group-code-in b groups))
                (equal a b)))
  :hints (("Goal" :use ((:instance fn-store-group-name-of-code-in (name a))
                        (:instance fn-store-group-name-of-code-in (name b)))
           :in-theory (disable fn-store-group-name-of-code-in))))

; Membership of a name list transfers to membership of its code list, which
; is what turns "no duplicate codes" into "no duplicate names" and back.
(defthm fn-store-codes-from-groups-member
  (implies (not (equal (fn-store-codes-from-groups names groups) :bad))
           (iff (member-equal name names)
                (and (fn-store-group-code-in name groups)
                     (member-equal (fn-store-group-code-in name groups)
                                   (fn-store-codes-from-groups names groups)))))
  :hints (("Goal" :induct (fn-store-codes-from-groups names groups))))

; Over a table parameter the inversion needs one hypothesis the compiled
; table made invisible: a NIL entry is a name whose code round-trips to NIL,
; which `fn-store-groups-from-codes' reads as "unknown".  A configured domain
; never holds NIL (`fn-record-group-namep' is a string); the tooth is in
; tests/acl2/config-tests.lisp.
(defthm fn-store-codes-from-groups-inverts
  (implies (and (true-listp names)
                (not (member-equal nil names))
                (not (equal (fn-store-codes-from-groups names groups) :bad)))
           (equal (fn-store-groups-from-codes
                   (fn-store-codes-from-groups names groups) groups)
                  names)))

; -----------------------------------------------------------------------------
; Export theory.
;
; The keystones are the two inversions between a group name and its code.
; The membership and type facts are proof vocabulary.

(deftheory fn-store-config-vocabulary
  '(fn-store-group-code-in-natp fn-store-group-name-of-code-in
    fn-store-group-name-is-a-member fn-store-group-code-in-is-injective
    fn-store-codes-from-groups-member))

(in-theory (disable fn-store-config-vocabulary))
