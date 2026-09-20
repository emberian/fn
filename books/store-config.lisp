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

; The format id is encoded with the CBOR primitives, opened locally here.
(local (in-theory (enable fn-cbor-codec-vocabulary)))

; The durable store's configuration format.  A store records this string and
; a host refuses to open one whose format it does not recognise, so a store
; written under an earlier set of decisions is rejected by its configuration
; rather than read with today's meaning.  Format 5 is the first written under
; the v1 content identity profile (`books/identity.lisp`); a store written
; under the pre-v1 `"sha256:"`/`"archive:"` derivation is format 4 and is
; refused at open.
; "fn-store-experiment-5"
(defconst *fn-store-format-id*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109
    101 110 116 45 53))

(defun fn-store-group-name (code groups)
  ; The group at a zero-based code, or nil.
  (declare (xargs :guard (and (natp code) (true-listp groups))))
  (if (consp groups)
      (if (zp code)
          (car groups)
        (fn-store-group-name (- code 1) (cdr groups)))
    nil))

(defun fn-store-group-code-in (name groups)
  ; The zero-based code of a group, or nil.
  (declare (xargs :guard (true-listp groups)))
  (if (consp groups)
      (if (equal name (car groups))
          0
        (let ((rest (fn-store-group-code-in name (cdr groups))))
          (if (null rest) nil (+ 1 rest))))
    nil))

(defun fn-store-groups-from-codes (codes groups)
  ; A code list becomes a distinct group list from the table, or :bad.
  ; Duplicate and unknown codes are refused here rather than deeper in the
  ; model.
  (declare (xargs :guard (true-listp groups)))
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
    (if (null codes) nil :bad)))

(defun fn-store-codes-from-groups (names groups)
  ; The inverse direction the Python boundary needs: names to codes, or :bad.
  (declare (xargs :guard (true-listp groups)))
  (if (consp names)
      (let ((code (fn-store-group-code-in (car names) groups)))
        (if (null code)
            :bad
          (let ((rest (fn-store-codes-from-groups (cdr names) groups)))
            (if (or (equal rest :bad) (member-equal code rest))
                :bad
              (cons code rest)))))
    (if (null names) nil :bad)))

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
