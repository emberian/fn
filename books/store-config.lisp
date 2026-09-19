; fn: the store's configured group table, in one place.
;
; The list of carried newsgroups and the mapping between a group name and the
; small integer code the bridge passes existed in four hand-synchronised
; copies: `tools/run_store.py`'s `DEFAULT_CONFIG["groups"]` and `group_codes`,
; `host/store-host.lisp`, `host/bp-ingress-host.lisp` and
; `host/reader-host.lisp`.  This book is the single source.  The code is the
; group's position in the list, so the two directions are inverse by
; construction rather than by a second table, and the theorems below say so.
;
; The table is a local configuration choice, not an RFC or protocol fact.
; `*fn-store-group-table-id*` names this version of it so a durable store can
; record which table it was written under without copying the names.

(in-package "ACL2")
(include-book "cbor")

(defconst *fn-store-groups* '("fn.letters" "fn.test"))

; "fn-store-groups-1"
(defconst *fn-store-group-table-id*
  '(102 110 45 115 116 111 114 101 45 103 114 111 117 112 115 45 49))

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

(defun fn-store-group-code (code)
  ; The host's existing entry point, now a lookup in the one table.
  (declare (xargs :guard t))
  (if (natp code) (fn-store-group-name code *fn-store-groups*) nil))

(defun fn-store-group-of-name (name)
  (declare (xargs :guard t))
  (fn-store-group-code-in name *fn-store-groups*))

(defun fn-store-groups-from-codes (codes)
  ; A code list becomes a distinct, configured group list, or :bad.  Duplicate
  ; and unknown codes are refused here rather than deeper in the model.
  (declare (xargs :guard t))
  (if (consp codes)
      (let ((group (fn-store-group-code (car codes))))
        (if group
            (let ((rest (fn-store-groups-from-codes (cdr codes))))
              (if (or (equal rest :bad) (member-equal group rest))
                  :bad
                (cons group rest)))
          :bad))
    (if (null codes) nil :bad)))

(defun fn-store-codes-from-groups (names)
  ; The inverse direction the Python boundary needs: names to codes, or :bad.
  (declare (xargs :guard t))
  (if (consp names)
      (let ((code (fn-store-group-of-name (car names))))
        (if (null code)
            :bad
          (let ((rest (fn-store-codes-from-groups (cdr names))))
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

(defthm fn-store-group-code-of-name
  (implies (fn-store-group-of-name name)
           (equal (fn-store-group-code (fn-store-group-of-name name)) name))
  :hints (("Goal" :in-theory (e/d (fn-store-group-of-name fn-store-group-code)
                                  (fn-store-group-name-of-code-in))
           :use ((:instance fn-store-group-name-of-code-in
                            (groups *fn-store-groups*))))))

(defthm fn-store-group-name-of-code
  (implies (fn-store-group-code code)
           (equal (fn-store-group-of-name (fn-store-group-code code)) code))
  :hints (("Goal" :in-theory (e/d (fn-store-group-of-name fn-store-group-code)
                                  (fn-store-group-code-in-of-name))
           :use ((:instance fn-store-group-code-in-of-name
                            (groups *fn-store-groups*))))))

; Membership of a name list transfers to membership of its code list, which
; is what turns "no duplicate codes" into "no duplicate names" and back.
(defthm fn-store-codes-from-groups-member
  (implies (not (equal (fn-store-codes-from-groups names) :bad))
           (iff (member-equal name names)
                (and (fn-store-group-of-name name)
                     (member-equal (fn-store-group-of-name name)
                                   (fn-store-codes-from-groups names)))))
  :hints (("Goal" :induct (fn-store-codes-from-groups names))))

(defthm fn-store-codes-from-groups-inverts
  (implies (and (true-listp names)
                (not (equal (fn-store-codes-from-groups names) :bad)))
           (equal (fn-store-groups-from-codes
                   (fn-store-codes-from-groups names))
                  names)))
