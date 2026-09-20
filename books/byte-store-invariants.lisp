; fn: well-formedness, fences and crash-image bounds of the byte-level
; storage model (crash model v2, §1.7 and the P1 keystones).
;
; Three groups of theorems, each proved from byte-store's definitions with
; no platform fact:
;
;   * K0 (model well-formedness).  fn-bs-statep is preserved by every
;     syscall for every outcome, by both fences, and by every admissible
;     crash.  The proofs are what forced the two extra fn-bs-statep
;     conjuncts recorded in byte-store.lisp.
;   * The fence lemmas.  A completed fence drains exactly the pending set it
;     names and nothing else: fn-bs-fence-file-drains-exactly-its-inode,
;     fn-bs-fence-dir-drains-exactly-its-directory, and the two
;     -touches-only- theorems.  A failed fence discards its set, so a later
;     successful fence of the same inode changes nothing durable
;     (fn-bs-refence-after-error-fences-nothing: fsyncgate).
;   * Crash images are bounded by the durable state and the pending set.
;     The lose-everything image (no choice) IS the durable state and is
;     admissible; every admissible image agrees with the durable state on
;     every fenced inode and every quiet directory
;     (fn-bs-crash-keeps-fenced-content, fn-bs-crash-keeps-quiet-directory);
;     and a directory entry of any admissible image is its durable value or
;     the target of one of its pending operations, never a third thing
;     (fn-bs-crash-entry-is-old-or-a-pending-target).
;
; The spec's fn-bs-crash-invents-nothing and fn-bs-tear-touches-only-its-
; inode are the same statement as fn-bs-crash-keeps-fenced-content
; (fn-bs-fencedp unfolds to their hypothesis; the spec's `ino' in the latter
; is unused), so they are not separate events here.  The spec's
; fn-bs-statep hypotheses on these contracts are unnecessary and dropped;
; the test book shows each remaining hypothesis is not.
;
; OPEN (recorded, not weakened): fn-bs-view-is-an-admissible-image.  Its
; splice-composition obligation is DISCHARGED here (fn-bs-splice-composition)
; and its witness choice list is admissible (fn-bs-view-choices-are-choices);
; what remains is the per-piece index arithmetic, stated exactly at that
; theorem's place below, together with the model defect the attempt found:
; a zero-length pending write tore into no pieces while applying as a
; zero-extension, so fn-bs-statep now carries fn-bs-writes-nonemptyp.  With
; it, the non-degenerate witness of fn-assume-crash-tearp.  K1, K2 and K3 are
; in books/byte-store-scan.lisp.
;
; The two named assumptions of the design's §3.6 are the encapsulates at the
; end.  They belong in books/assumptions.lisp; that book is owned by the
; hygiene lane (P7), and this book proposes the move rather than editing it.

(in-package "ACL2")
(include-book "byte-store")
(include-book "frame")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-bs-statep fn-bs-view fn-bs-lookup fn-bs-content
                          fn-bs-names fn-bs-durable-content fn-bs-durable-entry
                          fn-bs-fence-file fn-bs-fence-dir fn-bs-fencedp
                          fn-bs-dir-quietp fn-bs-crash
                          fn-bs-create fn-bs-write fn-bs-fsync-file
                          fn-bs-fsync-dir fn-bs-link fn-bs-rename
                          fn-bs-unlink fn-bs-mkdir fn-bs-read)))

; -----------------------------------------------------------------------------
; Alist vocabulary.  Keys of every table are keywords, strings or naturals,
; never NIL, which is what the -same lemmas need.

(defthm fn-bs-inode-tablep-implies-alistp
  (implies (fn-bs-inode-tablep x) (alistp x)))
(defthm fn-bs-entriesp-implies-alistp
  (implies (fn-bs-entriesp x) (alistp x)))
(defthm fn-bs-dir-tablep-implies-alistp
  (implies (fn-bs-dir-tablep x) (alistp x)))
(defthm fn-bs-op-listp-implies-true-listp
  (implies (fn-bs-op-listp x) (true-listp x)))

(defthm fn-bs-alistp-of-put-assoc
  (implies (alistp a) (alistp (fn-bs-put-assoc k v a))))

(defthm fn-bs-assoc-of-put-assoc-same
  (implies k
           (equal (assoc-equal k (fn-bs-put-assoc k v a)) (cons k v))))
(defthm fn-bs-assoc-of-put-assoc-other
  (implies (not (equal j k))
           (equal (assoc-equal j (fn-bs-put-assoc k v a)) (assoc-equal j a))))
(defthm fn-bs-assoc-of-del-assoc-same
  (implies k
           (equal (assoc-equal k (fn-bs-del-assoc k a)) nil)))
(defthm fn-bs-assoc-of-del-assoc-other
  (implies (not (equal j k))
           (equal (assoc-equal j (fn-bs-del-assoc k a)) (assoc-equal j a))))
(defthm fn-bs-assoc-of-put-assoc-iff
  (implies (alistp a)
           (iff (assoc-equal j (fn-bs-put-assoc k v a))
                (or (equal j k) (assoc-equal j a)))))

(defthm fn-bs-inode-tablep-content-is-octets
  (implies (fn-bs-inode-tablep x)
           (fn-cbor-octet-listp (cdr (assoc-equal k x)))))
(defthm fn-bs-inode-tablep-keys-are-inos
  (implies (and (fn-bs-inode-tablep x) (assoc-equal k x))
           (natp k)))
(defthm fn-bs-put-assoc-preserves-inode-tablep
  (implies (and (fn-bs-inode-tablep x) (fn-bs-inop k) (fn-cbor-octet-listp v))
           (fn-bs-inode-tablep (fn-bs-put-assoc k v x))))

(defthm fn-bs-dir-tablep-entries-are-entries
  (implies (fn-bs-dir-tablep x) (fn-bs-entriesp (cdr (assoc-equal k x)))))
(defthm fn-bs-put-assoc-preserves-entriesp
  (implies (and (fn-bs-entriesp x) (fn-bs-namep k) (fn-bs-entry-valuep v))
           (fn-bs-entriesp (fn-bs-put-assoc k v x))))
(defthm fn-bs-del-assoc-preserves-entriesp
  (implies (fn-bs-entriesp x) (fn-bs-entriesp (fn-bs-del-assoc k x))))
(defthm fn-bs-put-assoc-preserves-dir-tablep
  (implies (and (fn-bs-dir-tablep x) (fn-bs-dir-idp k) (fn-bs-entriesp v))
           (fn-bs-dir-tablep (fn-bs-put-assoc k v x))))

(defthm fn-bs-keys-belowp-bounds-known-key
  (implies (and (fn-bs-keys-belowp x n) (assoc-equal k x))
           (< k n)))
(defthm fn-bs-keys-belowp-excludes-bound
  (implies (fn-bs-keys-belowp x n)
           (not (assoc-equal n x))))
(defthm fn-bs-keys-belowp-monotone
  (implies (and (fn-bs-keys-belowp x n) (natp m) (<= n m))
           (fn-bs-keys-belowp x m)))
(defthm fn-bs-put-assoc-preserves-keys-belowp
  (implies (and (fn-bs-keys-belowp x n) (natp n) (natp k) (< k n))
           (fn-bs-keys-belowp (fn-bs-put-assoc k v x) n)))

; -----------------------------------------------------------------------------
; Octet vocabulary.

(defthm fn-bs-zeros-are-octets
  (fn-cbor-octet-listp (fn-bs-zeros n)))
(defthm fn-bs-take-is-true-list
  (true-listp (fn-bs-take n xs)))
(defthm fn-bs-take-of-octets-are-octets
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-bs-take n xs))))
(defthm fn-bs-nthcdr-of-octets-are-octets
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (nthcdr n xs))))
(defthm fn-bs-splice-of-octets-are-octets
  (implies (and (fn-cbor-octet-listp old) (fn-cbor-octet-listp octets))
           (fn-cbor-octet-listp (fn-bs-splice old offset octets))))

; -----------------------------------------------------------------------------
; Applying operations splits into the writes (inodes) and the entry
; operations (dirs); the two halves never touch each other.

(defun fn-bs-apply-writes (inodes ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (fn-bs-apply-writes
       (if (equal (car (car ops)) :write)
           (fn-bs-put-assoc (nth 1 (car ops))
                            (fn-bs-splice (cdr (assoc-equal (nth 1 (car ops)) inodes))
                                          (nth 2 (car ops)) (nth 3 (car ops)))
                            inodes)
         inodes)
       (cdr ops))
    inodes))

(defun fn-bs-apply-entries (dirs ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (fn-bs-apply-entries
       (let ((op (car ops)))
         (cond ((equal (car op) :set-entry)
                (fn-bs-put-assoc (nth 1 op)
                                 (fn-bs-put-assoc (nth 2 op) (nth 3 op)
                                                  (cdr (assoc-equal (nth 1 op) dirs)))
                                 dirs))
               ((equal (car op) :del-entry)
                (fn-bs-put-assoc (nth 1 op)
                                 (fn-bs-del-assoc (nth 2 op)
                                                  (cdr (assoc-equal (nth 1 op) dirs)))
                                 dirs))
               (t dirs)))
       (cdr ops))
    dirs))

(local (in-theory (disable fn-bs-splice)))

(defthm fn-bs-apply-ops-inodes-are-apply-writes
  (equal (mv-nth 0 (fn-bs-apply-ops inodes dirs ops))
         (fn-bs-apply-writes inodes ops))
  :hints (("Goal" :induct (fn-bs-apply-ops inodes dirs ops))))
(defthm fn-bs-apply-ops-dirs-are-apply-entries
  (equal (mv-nth 1 (fn-bs-apply-ops inodes dirs ops))
         (fn-bs-apply-entries dirs ops))
  :hints (("Goal" :induct (fn-bs-apply-ops inodes dirs ops))))

(defthm fn-bs-apply-writes-of-append
  (equal (fn-bs-apply-writes inodes (append a b))
         (fn-bs-apply-writes (fn-bs-apply-writes inodes a) b)))
(defthm fn-bs-apply-entries-of-append
  (equal (fn-bs-apply-entries dirs (append a b))
         (fn-bs-apply-entries (fn-bs-apply-entries dirs a) b)))
(defthm fn-bs-ops-for-ino-of-append
  (equal (fn-bs-ops-for-ino (append a b) ino)
         (append (fn-bs-ops-for-ino a ino) (fn-bs-ops-for-ino b ino))))
(defthm fn-bs-ops-for-dir-of-append
  (equal (fn-bs-ops-for-dir (append a b) dir)
         (append (fn-bs-ops-for-dir a dir) (fn-bs-ops-for-dir b dir))))
(defthm fn-bs-op-listp-of-append
  (implies (true-listp a)
           (equal (fn-bs-op-listp (append a b))
                  (and (fn-bs-op-listp a) (fn-bs-op-listp b)))))
(defthm fn-bs-writes-knownp-of-append
  (equal (fn-bs-writes-knownp (append a b) inodes)
         (and (fn-bs-writes-knownp a inodes) (fn-bs-writes-knownp b inodes))))

; Quiet objects are untouched.
(defthm fn-bs-apply-writes-keeps-quiet-ino
  (implies (not (fn-bs-ops-for-ino ops ino))
           (equal (assoc-equal ino (fn-bs-apply-writes inodes ops))
                  (assoc-equal ino inodes))))
(defthm fn-bs-apply-entries-keeps-quiet-dir
  (implies (not (fn-bs-ops-for-dir ops dir))
           (equal (assoc-equal dir (fn-bs-apply-entries dirs ops))
                  (assoc-equal dir dirs))))

; The selectors of a fence.
(defthm fn-bs-ops-for-ino-of-ops-not-for-ino
  (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-ino ops ino) ino) nil))
(defthm fn-bs-ops-not-for-ino-idempotent
  (equal (fn-bs-ops-not-for-ino (fn-bs-ops-not-for-ino ops ino) ino)
         (fn-bs-ops-not-for-ino ops ino)))
(defthm fn-bs-ops-for-dir-of-ops-not-for-dir
  (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-dir ops dir) dir) nil))
(defthm fn-bs-ops-not-for-dir-idempotent
  (equal (fn-bs-ops-not-for-dir (fn-bs-ops-not-for-dir ops dir) dir)
         (fn-bs-ops-not-for-dir ops dir)))
(defthm fn-bs-ops-for-ino-of-ops-for-ino-other
  (implies (not (equal other ino))
           (equal (fn-bs-ops-for-ino (fn-bs-ops-for-ino ops ino) other) nil)))
(defthm fn-bs-ops-for-dir-of-ops-for-dir-other
  (implies (not (equal other dir))
           (equal (fn-bs-ops-for-dir (fn-bs-ops-for-dir ops dir) other) nil)))
(defthm fn-bs-ops-for-dir-of-ops-for-ino
  (equal (fn-bs-ops-for-dir (fn-bs-ops-for-ino ops ino) dir) nil))
(defthm fn-bs-ops-for-ino-of-ops-for-dir
  (equal (fn-bs-ops-for-ino (fn-bs-ops-for-dir ops dir) ino) nil))
(defthm fn-bs-apply-entries-of-ops-for-ino
  (equal (fn-bs-apply-entries dirs (fn-bs-ops-for-ino ops ino)) dirs))
(defthm fn-bs-apply-writes-of-ops-for-dir
  (equal (fn-bs-apply-writes inodes (fn-bs-ops-for-dir ops dir)) inodes))

(defthm fn-bs-op-listp-of-ops-for-ino
  (implies (fn-bs-op-listp ops) (fn-bs-op-listp (fn-bs-ops-for-ino ops ino))))
(defthm fn-bs-op-listp-of-ops-not-for-ino
  (implies (fn-bs-op-listp ops) (fn-bs-op-listp (fn-bs-ops-not-for-ino ops ino))))
(defthm fn-bs-op-listp-of-ops-for-dir
  (implies (fn-bs-op-listp ops) (fn-bs-op-listp (fn-bs-ops-for-dir ops dir))))
(defthm fn-bs-op-listp-of-ops-not-for-dir
  (implies (fn-bs-op-listp ops) (fn-bs-op-listp (fn-bs-ops-not-for-dir ops dir))))
(defthm fn-bs-writes-knownp-of-ops-for-ino
  (implies (fn-bs-writes-knownp ops inodes)
           (fn-bs-writes-knownp (fn-bs-ops-for-ino ops ino) inodes)))
(defthm fn-bs-writes-knownp-of-ops-not-for-ino
  (implies (fn-bs-writes-knownp ops inodes)
           (fn-bs-writes-knownp (fn-bs-ops-not-for-ino ops ino) inodes)))
(defthm fn-bs-writes-knownp-of-ops-for-dir
  (implies (fn-bs-writes-knownp ops inodes)
           (fn-bs-writes-knownp (fn-bs-ops-for-dir ops dir) inodes)))
(defthm fn-bs-writes-knownp-of-ops-not-for-dir
  (implies (fn-bs-writes-knownp ops inodes)
           (fn-bs-writes-knownp (fn-bs-ops-not-for-dir ops dir) inodes)))
(defthm fn-bs-writes-knownp-of-put-assoc
  (implies (and (fn-bs-writes-knownp ops inodes) (alistp inodes))
           (fn-bs-writes-knownp ops (fn-bs-put-assoc k v inodes))))
(defthm fn-bs-writes-knownp-of-cons
  (implies (and (fn-bs-writes-knownp ops inodes) (consp x))
           (fn-bs-writes-knownp ops (cons x inodes))))
(defthm fn-bs-writes-knownp-of-apply-writes
  (implies (and (fn-bs-writes-knownp ops inodes) (alistp inodes))
           (fn-bs-writes-knownp ops (fn-bs-apply-writes inodes ops2)))
  :hints (("Goal" :induct (fn-bs-apply-writes inodes ops2))))

; The same eight facts for the non-empty-write conjunct of fn-bs-statep.
; Every selector list is a sublist or a projection of the pending list, and
; a torn piece of a non-empty write is non-empty, so nothing here is more
; than an induction.
(defthm fn-bs-writes-nonemptyp-of-append
  (equal (fn-bs-writes-nonemptyp (append a b))
         (and (fn-bs-writes-nonemptyp a) (fn-bs-writes-nonemptyp b))))
(defthm fn-bs-writes-nonemptyp-of-ops-for-ino
  (implies (fn-bs-writes-nonemptyp ops)
           (fn-bs-writes-nonemptyp (fn-bs-ops-for-ino ops ino))))
(defthm fn-bs-writes-nonemptyp-of-ops-not-for-ino
  (implies (fn-bs-writes-nonemptyp ops)
           (fn-bs-writes-nonemptyp (fn-bs-ops-not-for-ino ops ino))))
(defthm fn-bs-writes-nonemptyp-of-ops-for-dir
  (implies (fn-bs-writes-nonemptyp ops)
           (fn-bs-writes-nonemptyp (fn-bs-ops-for-dir ops dir))))
(defthm fn-bs-writes-nonemptyp-of-ops-not-for-dir
  (implies (fn-bs-writes-nonemptyp ops)
           (fn-bs-writes-nonemptyp (fn-bs-ops-not-for-dir ops dir))))
(defthm fn-bs-writes-nonemptyp-of-cons-write
  (implies (and (fn-bs-writes-nonemptyp ops) (consp octets))
           (fn-bs-writes-nonemptyp (append ops (list (list :write ino offset octets))))))
(defthm fn-bs-writes-nonemptyp-of-entry-op
  (implies (and (fn-bs-writes-nonemptyp ops) (not (equal (car op) :write)))
           (fn-bs-writes-nonemptyp (append ops (list op)))))

; -----------------------------------------------------------------------------
; Tearing a write yields writes to the same inode only, well-formed when the
; selectors are.

(local (in-theory (disable fn-bs-unit-count)))

(defthm fn-bs-tear-write-is-true-list
  (true-listp (fn-bs-tear-write op sels i unit)))
(defthm fn-bs-tear-write-has-no-writes-for-other
  (implies (not (equal other (nth 1 op)))
           (not (fn-bs-ops-for-ino (fn-bs-tear-write op sels i unit) other))))
(defthm fn-bs-tear-write-has-no-entries
  (not (fn-bs-ops-for-dir (fn-bs-tear-write op sels i unit) dir)))
(defthm fn-bs-apply-entries-of-tear-write
  (equal (fn-bs-apply-entries dirs (fn-bs-tear-write op sels i unit)) dirs))
(defthm fn-bs-tear-write-is-op-list
  (implies (and (fn-bs-opp op) (equal (car op) :write)
                (fn-bs-selector-listp sels))
           (fn-bs-op-listp (fn-bs-tear-write op sels i unit))))
(defthm fn-bs-tear-write-writes-known
  (implies (assoc-equal (nth 1 op) inodes)
           (fn-bs-writes-knownp (fn-bs-tear-write op sels i unit) inodes)))

; -----------------------------------------------------------------------------
; Crash selection keeps quiet objects quiet and well-formed sets well-formed.

(defthm fn-bs-crash-select-keeps-quiet-ino
  (implies (not (fn-bs-ops-for-ino ops ino))
           (not (fn-bs-ops-for-ino (fn-bs-crash-select ops choices unit) ino))))
(defthm fn-bs-crash-select-keeps-quiet-dir
  (implies (not (fn-bs-ops-for-dir ops dir))
           (not (fn-bs-ops-for-dir (fn-bs-crash-select ops choices unit) dir))))
(defthm fn-bs-crash-select-is-op-list
  (implies (and (fn-bs-op-listp ops) (fn-bs-crash-choicesp choices ops unit))
           (fn-bs-op-listp (fn-bs-crash-select ops choices unit))))
(defthm fn-bs-crash-select-writes-known
  (implies (fn-bs-writes-knownp ops inodes)
           (fn-bs-writes-knownp (fn-bs-crash-select ops choices unit) inodes)))
(defthm fn-bs-crash-select-with-no-choices-is-empty
  (equal (fn-bs-crash-select ops nil unit) nil))

; -----------------------------------------------------------------------------
; Applying a well-formed, known write set preserves the tables.

(defthm fn-bs-apply-writes-preserves-tables
  (implies (and (fn-bs-inode-tablep inodes) (fn-bs-keys-belowp inodes n) (natp n)
                (fn-bs-op-listp ops) (fn-bs-writes-knownp ops inodes))
           (and (fn-bs-inode-tablep (fn-bs-apply-writes inodes ops))
                (fn-bs-keys-belowp (fn-bs-apply-writes inodes ops) n)))
  :hints (("Goal" :induct (fn-bs-apply-writes inodes ops))))
(defthm fn-bs-apply-entries-preserves-dir-tablep
  (implies (and (fn-bs-dir-tablep dirs) (fn-bs-op-listp ops))
           (fn-bs-dir-tablep (fn-bs-apply-entries dirs ops)))
  :hints (("Goal" :induct (fn-bs-apply-entries dirs ops))))

; A path the lookup accepts is typed: the view's directories are a table.
(defthm fn-bs-dir-tablep-keys-are-dir-ids
  (implies (and (fn-bs-dir-tablep x) (assoc-equal k x)) (keywordp k)))
(defthm fn-bs-entriesp-keys-are-names
  (implies (and (fn-bs-entriesp x) (assoc-equal k x)) (stringp k)))
(defthm fn-bs-lookup-types-its-dir
  (implies (and (fn-bs-statep s) (fn-bs-lookup s dir name)) (keywordp dir))
  :hints (("Goal" :use ((:instance fn-bs-dir-tablep-keys-are-dir-ids
                                   (x (fn-bs-apply-entries (fn-bs-dirs s) (fn-bs-pending s)))
                                   (k dir))))))
(defthm fn-bs-lookup-types-its-name
  (implies (and (fn-bs-statep s) (fn-bs-lookup s dir name)) (stringp name))
  :hints (("Goal" :use ((:instance fn-bs-entriesp-keys-are-names
                                   (x (cdr (assoc-equal dir (fn-bs-apply-entries (fn-bs-dirs s) (fn-bs-pending s)))))
                                   (k name))
                        (:instance fn-bs-dir-tablep-entries-are-entries
                                   (x (fn-bs-apply-entries (fn-bs-dirs s) (fn-bs-pending s)))
                                   (k dir))))))

; -----------------------------------------------------------------------------
; K0: model well-formedness.

(defthm fn-bs-crash-preserves-statep
  (implies (and (fn-bs-statep s)
                (fn-bs-crash-choicesp choices (fn-bs-pending s) (fn-bs-unit s)))
           (fn-bs-statep (fn-bs-crash s choices))))
(defthm fn-bs-fence-file-preserves-statep
  (implies (fn-bs-statep s) (fn-bs-statep (fn-bs-fence-file s ino))))
(defthm fn-bs-fence-dir-preserves-statep
  (implies (fn-bs-statep s) (fn-bs-statep (fn-bs-fence-dir s dir))))
(defthm fn-bs-create-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp dir) (fn-bs-namep name))
           (fn-bs-statep (mv-nth 1 (fn-bs-create s dir name outcome)))))
(defthm fn-bs-write-preserves-statep
  (implies (and (fn-bs-statep s) (natp offset) (fn-cbor-octet-listp octets))
           (fn-bs-statep (mv-nth 1 (fn-bs-write s ino offset octets outcome)))))
(defthm fn-bs-fsync-file-preserves-statep
  (implies (and (fn-bs-statep s)
                (or (equal outcome :ok)
                    (fn-bs-crash-choicesp (cdr outcome)
                                          (fn-bs-ops-for-ino (fn-bs-pending s) ino)
                                          (fn-bs-unit s))))
           (fn-bs-statep (mv-nth 1 (fn-bs-fsync-file s ino outcome)))))
(defthm fn-bs-fsync-dir-preserves-statep
  (implies (and (fn-bs-statep s)
                (or (equal outcome :ok)
                    (fn-bs-crash-choicesp (cdr outcome)
                                          (fn-bs-ops-for-dir (fn-bs-pending s) dir)
                                          (fn-bs-unit s))))
           (fn-bs-statep (mv-nth 1 (fn-bs-fsync-dir s dir outcome)))))
(defthm fn-bs-link-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp ddir) (fn-bs-namep dname))
           (fn-bs-statep (mv-nth 1 (fn-bs-link s sdir sname ddir dname outcome)))))
(defthm fn-bs-rename-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp ddir) (fn-bs-namep dname))
           (fn-bs-statep (mv-nth 1 (fn-bs-rename s sdir sname ddir dname outcome))))
  :hints (("Goal" :in-theory (disable fn-bs-lookup)
           :use ((:instance fn-bs-lookup-types-its-dir (dir sdir) (name sname))
                 (:instance fn-bs-lookup-types-its-name (dir sdir) (name sname))))))
(defthm fn-bs-unlink-preserves-statep
  (implies (fn-bs-statep s)
           (fn-bs-statep (mv-nth 1 (fn-bs-unlink s dir name outcome))))
  :hints (("Goal" :in-theory (disable fn-bs-lookup)
           :use (fn-bs-lookup-types-its-dir fn-bs-lookup-types-its-name))))
(defthm fn-bs-mkdir-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp parent) (fn-bs-namep name)
                (fn-bs-dir-idp id))
           (fn-bs-statep (mv-nth 1 (fn-bs-mkdir s parent name id outcome)))))

; -----------------------------------------------------------------------------
; The fence lemmas.  A completed fence removes the pending set it names and
; nothing else.

(defthm fn-bs-fence-file-drains-exactly-its-inode
  (and (equal (fn-bs-ops-for-ino (fn-bs-pending (fn-bs-fence-file s ino)) ino) nil)
       (equal (fn-bs-ops-not-for-ino (fn-bs-pending (fn-bs-fence-file s ino)) ino)
              (fn-bs-ops-not-for-ino (fn-bs-pending s) ino))
       (equal (fn-bs-dirs (fn-bs-fence-file s ino)) (fn-bs-dirs s))))
(defthm fn-bs-fence-dir-drains-exactly-its-directory
  (and (equal (fn-bs-ops-for-dir (fn-bs-pending (fn-bs-fence-dir s dir)) dir) nil)
       (equal (fn-bs-ops-not-for-dir (fn-bs-pending (fn-bs-fence-dir s dir)) dir)
              (fn-bs-ops-not-for-dir (fn-bs-pending s) dir))
       (equal (fn-bs-inodes (fn-bs-fence-dir s dir)) (fn-bs-inodes s))))
(defthm fn-bs-fence-file-touches-only-its-inode
  (implies (not (equal other ino))
           (equal (fn-bs-durable-content (fn-bs-fence-file s ino) other)
                  (fn-bs-durable-content s other))))
(defthm fn-bs-fence-dir-touches-only-its-directory
  (implies (not (equal other dir))
           (equal (assoc-equal other (fn-bs-dirs (fn-bs-fence-dir s dir)))
                  (assoc-equal other (fn-bs-dirs s)))))

; fsyncgate: after a failed fence, a later successful fence of the same
; inode changes nothing durable.  Retrying fsync establishes no durability.
; No hypothesis: after :ok the first fence drained the set, after an error
; it discarded the set; either way the second fence finds nothing.
(defthm fn-bs-refence-after-error-fences-nothing
  (mv-let (r1 s1) (fn-bs-fsync-file s ino outcome)
    (declare (ignore r1))
    (mv-let (r2 s2) (fn-bs-fsync-file s1 ino :ok)
      (declare (ignore r2))
      (equal (fn-bs-inodes s2) (fn-bs-inodes s1)))))

; -----------------------------------------------------------------------------
; Crash images are bounded by the durable state and the pending set.

; Bottom: the lose-everything image is the durable state, and admissible.
(defthm fn-bs-crash-with-no-choices-is-the-durable-state
  (and (equal (fn-bs-inodes (fn-bs-crash s nil)) (fn-bs-inodes s))
       (equal (fn-bs-dirs (fn-bs-crash s nil)) (fn-bs-dirs s))
       (equal (fn-bs-pending (fn-bs-crash s nil)) nil)))
(defthm fn-bs-lose-everything-is-an-admissible-image
  (fn-bs-crash-imagep s (fn-bs-crash s nil))
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (choices nil) (image (fn-bs-crash s nil)))))))

; A-DURABILITY, positive half, and A-WRITE-ISOLATION, data half, in one
; statement: a fenced inode's durable content survives every admissible
; crash unchanged.  Torn selectors act only on PENDING writes, and a write
; to one inode never lands in another.
(defthm fn-bs-crash-with-choices-keeps-fenced-content
  (implies (fn-bs-fencedp s ino)
           (equal (fn-bs-durable-content (fn-bs-crash s choices) ino)
                  (fn-bs-durable-content s ino))))
(defthm fn-bs-crash-keeps-fenced-content
  (implies (and (fn-bs-fencedp s ino) (fn-bs-crash-imagep s image))
           (equal (fn-bs-durable-content image ino)
                  (fn-bs-durable-content s ino)))
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep))))

; The directory half: a quiet directory survives every admissible crash.
(defthm fn-bs-crash-with-choices-keeps-quiet-directory
  (implies (fn-bs-dir-quietp s dir)
           (equal (assoc-equal dir (fn-bs-dirs (fn-bs-crash s choices)))
                  (assoc-equal dir (fn-bs-dirs s)))))
(defthm fn-bs-crash-keeps-quiet-directory
  (implies (and (fn-bs-dir-quietp s dir) (fn-bs-crash-imagep s image))
           (equal (assoc-equal dir (fn-bs-dirs image))
                  (assoc-equal dir (fn-bs-dirs s))))
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep))))

; A-WRITE-ISOLATION, namespace half: an entry after a crash is its durable
; value or the target of one of its pending operations; never a third thing
; and never a partial name.
(defun fn-bs-entry-outcomes (ops old)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (append (fn-bs-entry-outcomes (cdr ops) old)
              (fn-bs-entry-outcomes (cdr ops)
                                    (if (equal (car (car ops)) :set-entry)
                                        (nth 3 (car ops))
                                      nil)))
    (list old)))

(defun fn-bs-ops-for-name (ops dir name)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (member-equal (car (car ops)) '(:set-entry :del-entry))
              (equal (nth 1 (car ops)) dir) (equal (nth 2 (car ops)) name))
         (cons (car ops) (fn-bs-ops-for-name (cdr ops) dir name)))
        (t (fn-bs-ops-for-name (cdr ops) dir name))))

; The value of one entry after a list of operations.
(defun fn-bs-entry-after (ops old dir name)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (let ((op (car ops)))
        (fn-bs-entry-after
         (cdr ops)
         (cond ((and (equal (car op) :set-entry)
                     (equal (nth 1 op) dir) (equal (nth 2 op) name))
                (nth 3 op))
               ((and (equal (car op) :del-entry)
                     (equal (nth 1 op) dir) (equal (nth 2 op) name))
                nil)
               (t old))
         dir name))
    old))

(defthm fn-bs-apply-entries-entry-is-entry-after
  (implies (and dir name)
           (equal (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bs-apply-entries dirs ops)))))
                  (fn-bs-entry-after ops (cdr (assoc-equal name (cdr (assoc-equal dir dirs))))
                                     dir name)))
  :hints (("Goal" :induct (fn-bs-apply-entries dirs ops))))
(defthm fn-bs-entry-after-of-append
  (equal (fn-bs-entry-after (append a b) old dir name)
         (fn-bs-entry-after b (fn-bs-entry-after a old dir name) dir name)))
(defthm fn-bs-entry-after-of-tear-write
  (equal (fn-bs-entry-after (fn-bs-tear-write op sels i unit) old dir name) old))
(defthm fn-bs-member-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b))))

(local (defun fn-bs-outcomes-induct (ops choices old dir name)
         (if (consp ops)
             (let ((op (car ops)))
               (list (fn-bs-outcomes-induct (cdr ops) (cdr choices) old dir name)
                     (fn-bs-outcomes-induct (cdr ops) (cdr choices)
                                            (if (equal (car op) :set-entry) (nth 3 op) nil)
                                            dir name)))
           (list old choices dir name))))

(defthm fn-bs-crash-select-entry-is-an-outcome
  (member-equal (fn-bs-entry-after (fn-bs-crash-select ops choices unit) old dir name)
                (fn-bs-entry-outcomes (fn-bs-ops-for-name ops dir name) old))
  :hints (("Goal" :induct (fn-bs-outcomes-induct ops choices old dir name))))

(defthm fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
  (implies (and (fn-bs-dir-idp dir) (fn-bs-namep name))
           (member-equal (fn-bs-durable-entry (fn-bs-crash s choices) dir name)
                         (fn-bs-entry-outcomes
                          (fn-bs-ops-for-name (fn-bs-pending s) dir name)
                          (fn-bs-durable-entry s dir name))))
  :hints (("Goal" :cases ((equal dir nil))
           :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs s))
                            (ops (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s))))))))
(defthm fn-bs-crash-entry-is-old-or-a-pending-target
  (implies (and (fn-bs-dir-idp dir) (fn-bs-namep name) (fn-bs-crash-imagep s image))
           (member-equal (fn-bs-durable-entry image dir name)
                         (fn-bs-entry-outcomes
                          (fn-bs-ops-for-name (fn-bs-pending s) dir name)
                          (fn-bs-durable-entry s dir name))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash-imagep)
                                  (fn-bs-durable-entry fn-bs-crash)))))

;                      -----------------------------------------------------
; The view is an admissible image.
;
; The obligation recorded against this statement was the splice-composition
; lemma over contiguous unit pieces.  It is fn-bs-splice-composition below:
; writing A at OFFSET and then B immediately after it is one write of
; (append A B) at OFFSET.  With it, the all-:new choice list reproduces each
; pending write from the pieces fn-bs-tear-write cuts, and :apply reproduces
; each entry operation, so the view -- what the running process saw -- is the
; top of the image lattice, as fn-bs-crash-with-no-choices-is-the-durable-
; state is its bottom.

(local (in-theory (enable fn-bs-splice)))

; List vocabulary for the composition lemma.  Local: these are generic
; append/take/nthcdr facts and no downstream book states anything in them.
(local (defthm fn-bs-append-associative
         (equal (append (append x y) z) (append x (append y z)))))
(local (defthm fn-bs-len-of-append
         (equal (len (append x y)) (+ (len x) (len y)))))
(local (defthm fn-bs-len-of-take
         (equal (len (fn-bs-take n xs)) (nfix n))))
(local (defthm fn-bs-take-of-len-is-identity
         (implies (true-listp xs) (equal (fn-bs-take (len xs) xs) xs))))
(local (defthm fn-bs-take-of-append-left
         (implies (and (natp n) (<= n (len a)) (true-listp a))
                  (equal (fn-bs-take n (append a b)) (fn-bs-take n a)))))
(local (defthm fn-bs-nthcdr-of-nthcdr
         (implies (and (natp n) (natp m))
                  (equal (nthcdr n (nthcdr m xs)) (nthcdr (+ n m) xs)))))
(local (defthm fn-bs-take-past-a-prefix
         (implies (and (natp n) (natp m) (true-listp x) (equal (len x) n))
                  (equal (fn-bs-take (+ n m) (append x y))
                         (append x (fn-bs-take m y))))))
(local (defthm fn-bs-nthcdr-past-a-prefix
         (implies (and (natp n) (natp m) (true-listp x) (equal (len x) n))
                  (equal (nthcdr (+ n m) (append x y)) (nthcdr m y)))))
(local (defthm fn-bs-take-split
         (implies (and (natp m) (natp n) (<= m n))
                  (equal (append (fn-bs-take m xs) (fn-bs-take (- n m) (nthcdr m xs)))
                         (fn-bs-take n xs)))))

; The splice-composition lemma (the obligation recorded with the open view
; theorem): the second write lands exactly where the first one ended, so the
; two are one write of the concatenation.  Both sides are three appends over
; the same OLD; the proof is the two prefix lemmas above, not an induction.
(defthm fn-bs-splice-composition
  (implies (and (natp offset) (true-listp a))
           (equal (fn-bs-splice (fn-bs-splice old offset a) (+ offset (len a)) b)
                  (fn-bs-splice old offset (append a b))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-splice) (fn-bs-take)))))

(local (in-theory (disable fn-bs-splice)))

; The nothing-lost choice: every unit of every write :new, every entry
; operation :apply.
(defun fn-bs-all-new (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp n) nil (cons :new (fn-bs-all-new (1- n)))))

(defun fn-bs-view-choices (ops unit)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (cons (if (equal (car (car ops)) :write)
                (fn-bs-all-new (fn-bs-unit-count (nth 2 (car ops))
                                                 (len (nth 3 (car ops))) unit))
              :apply)
            (fn-bs-view-choices (cdr ops) unit))
    nil))

; Floor facts for the unit arithmetic.  arithmetic-5 is included inside a
; local encapsulate so that its rules do not reach the rest of the book.
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-bs-floor-weakly-monotone
     (implies (and (integerp a) (integerp b) (<= a b) (posp unit))
              (<= (floor a unit) (floor b unit)))
     :rule-classes :linear)
   (defthm fn-bs-floor-times-unit-below
     (implies (and (integerp a) (posp unit))
              (<= (* (floor a unit) unit) a))
     :rule-classes :linear)
   (defthm fn-bs-floor-times-unit-above
     (implies (and (integerp a) (posp unit))
              (< a (* (+ 1 (floor a unit)) unit)))
     :rule-classes :linear)))

(local
 (defthm fn-bs-unit-count-nonnegative
   (<= 0 (fn-bs-unit-count offset len unit))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bs-unit-count) (floor))
            :use ((:instance fn-bs-floor-weakly-monotone
                             (a (nfix offset)) (b (+ (nfix offset) len -1))))))))

(defthm fn-bs-all-new-is-selector-list
  (fn-bs-selector-listp (fn-bs-all-new n)))
(defthm fn-bs-len-of-all-new
  (equal (len (fn-bs-all-new n)) (nfix n)))
(defthm fn-bs-view-choices-are-choices
  (fn-bs-crash-choicesp (fn-bs-view-choices ops unit) ops unit)
  :hints (("Goal" :in-theory (enable fn-bs-crash-choicep))))

; -----------------------------------------------------------------------------
; fn-bs-view-is-an-admissible-image: STILL OPEN, with a smaller obligation.
;
; What this lane closed:
;   * fn-bs-splice-composition, the lemma the obligation named.
;   * fn-bs-view-choices, the nothing-lost choice list, and
;     fn-bs-view-choices-are-choices: it is admissible for every pending list
;     and every unit, so the witness for fn-bs-crash-imagep-suff exists.
;   * A DEFECT in the model that made the statement FALSE as written, now
;     fixed: a pending (:write ino offset NIL) has fn-bs-unit-count 0, so a
;     crash tears it into no pieces, while fn-bs-apply-op splices it and
;     zero-extends the inode when offset exceeds the current length.  The
;     view of (:byte-store 4 ((0)) NIL ((:write 0 5 NIL)) 1) is five zero
;     octets and no crash image of that state has them.  fn-bs-statep now
;     carries fn-bs-writes-nonemptyp (byte-store.lisp), which fn-bs-write
;     establishes and every transition preserves (the eight lemmas above).
;
; What remains, exactly.  For a write of L>0 octets at OFFSET under unit U,
; let u0 = (floor OFFSET U), start_i = (max OFFSET (* (+ u0 i) U)) and
; k_i = (min L (- start_i OFFSET)).  Two arithmetic facts are needed, for
; 1 <= i <= count-1 where count = (fn-bs-unit-count OFFSET L U):
;   (A1)  (equal start_i (+ OFFSET k_i))      -- the i-th piece begins where
;         pieces 0..i-1 ended; from (<= (* (+ u0 i) U) (+ OFFSET L -1)),
;         which is fn-bs-floor-weakly-monotone with fn-bs-floor-times-unit-
;         below, both proved above.
;   (A2)  (equal (min (+ OFFSET L) (* (+ u0 i 1) U)) (+ OFFSET k_(i+1)))
; With them, the induction
;   (fn-bs-apply-writes
;     (fn-bs-put-assoc ino (fn-bs-splice c OFFSET (fn-bs-take k_i octets)) inodes)
;     (fn-bs-tear-write op (fn-bs-all-new (- count i)) i U))
;   = (fn-bs-put-assoc ino (fn-bs-splice c OFFSET octets) inodes)
; closes on i, its step being fn-bs-splice-composition (a = the first k_i
; octets, b = the i-th slice) followed by fn-bs-take-split; its base at
; i = count is fn-bs-take-of-len-is-identity.  Attempted here: the induction
; is right and the rewriting is right, but the waterfall re-derives A1 and A2
; inside every branch of fn-bs-tear-write's case split and exhausts a
; 2,000,000 step limit.  The next step is to state A1 and A2 as their own
; :linear lemmas over a named (fn-bs-piece-start offset i unit), with
; fn-bs-tear-write opened once by an :expand rather than by its definition
; rune, so the arithmetic is discharged once instead of per branch.
;
; Nothing below depends on the view theorem; the A-CRYPTO-TRAILER witness
; stays "no tears of an empty write" until it lands.

; -----------------------------------------------------------------------------
; The named assumptions (design §3.6) LIVE IN books/assumptions.lisp.
;
; A-CRASH-IMAGE (`fn-assume-physical-crash') and A-CRYPTO-TRAILER
; (`fn-assume-crash-tearp'), with `fn-bs-torn-variantp', moved there on
; 2026-09-20 (lane w9/storage-2), which is what the assurance rule "Assumptions
; are constrained functions" requires: a named assumption is an `encapsulate'
; with a local witness in `books/assumptions.lisp'.  The move puts this book
; into the include-closure of `books/assumptions' and therefore of
; `books/relay', `books/bp-release' and `books/scheduler-invariants'; there is
; no cycle, because nothing in the byte-store closure includes `assumptions'.
; The constraints did not change with the move.

; -----------------------------------------------------------------------------
; OPEN keystones, stated with their exact obligations.  None is weakened
; into a theorem here.
;
; (defthm fn-bs-view-is-an-admissible-image           ; OPEN
;   (implies (fn-bs-statep s)
;            (fn-bs-crash-imagep s (fn-bs-view s))))
; Obligation: a choice list fn-bs-all-new-choices (pending unit) with one
; :new selector per unit of every write and :apply for every entry, and the
; lemma that applying (fn-bs-tear-write op all-new 0 unit) equals applying
; op, by fn-bs-splice composition over contiguous unit pieces:
;   (fn-bs-splice (fn-bs-splice old o a) (+ o (len a)) b)
;   = (fn-bs-splice old o (append a b)).
;
; (defthm fn-bs-store-crash-image-scans                 ; K1, OPEN (P3)
;   (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
;            (fn-bs-scan-okp (fn-bs-scan-store image))))
; Obligation: fn-bs-scan-store and fn-bs-store-relation (design §3.1-3.2)
; over fn-frame-store-decode and the frontier codec encapsulate; then
; fn-bs-crash-keeps-fenced-content for every authority inode (the relation's
; fn-bs-authority-fencedp clause), fn-bs-crash-keeps-quiet-directory for the
; authority directories when quiet, and fn-bs-crash-entry-is-old-or-a-
; pending-target for the one pending :set-entry the phase allows.
;
; (defthm fn-bs-store-crash-image-is-kernel-admissible  ; K2, OPEN (P3)
;   (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
;            (fn-sf-crash-imagep ks
;                                (fn-bs-scan-frontier (fn-bs-scan-store image))
;                                (fn-bs-scan-records (fn-bs-scan-store image)))))
; Obligation: K1 plus, from fn-bs-pending-matches-phase, that the scanned
; frontier is fn-sf-frontier or (only while fn-sf-frontier-new-visiblep) the
; candidate, and the scanned records are fn-sf-records or (only while
; fn-sf-record-present-visiblep) that list plus the exact candidate.  This
; is the store deputy's seam: fn-sf-crash-imagep at store-files.lisp:499
; is the interface predicate it proves inhabited.
;
; (defthm fn-bs-store-recovery-is-a-kernel-crash         ; K3, OPEN (P3)
;   ...as design §3.3, from K2 and fn-sf-crash-realizes-every-admissible-image
;   (store-files-invariants.lisp), which the store deputy owns.)

; -----------------------------------------------------------------------------
; Export theory.  Enabled on include: the K0 keystones, the fence lemmas,
; the crash bounds, the two assumptions' constraints, the list vocabulary
; definitions.  Withdrawn: every alist, octet, apply, selector, tear and
; select lemma, which is proof vocabulary.

(deftheory fn-bs-invariants-vocabulary
  '(fn-bs-inode-tablep-implies-alistp fn-bs-entriesp-implies-alistp
    fn-bs-dir-tablep-implies-alistp fn-bs-op-listp-implies-true-listp
    fn-bs-alistp-of-put-assoc
    fn-bs-assoc-of-put-assoc-same fn-bs-assoc-of-put-assoc-other
    fn-bs-assoc-of-del-assoc-same fn-bs-assoc-of-del-assoc-other
    fn-bs-assoc-of-put-assoc-iff
    fn-bs-inode-tablep-content-is-octets fn-bs-inode-tablep-keys-are-inos
    fn-bs-put-assoc-preserves-inode-tablep fn-bs-dir-tablep-entries-are-entries
    fn-bs-put-assoc-preserves-entriesp fn-bs-del-assoc-preserves-entriesp
    fn-bs-put-assoc-preserves-dir-tablep
    fn-bs-keys-belowp-bounds-known-key fn-bs-keys-belowp-excludes-bound
    fn-bs-keys-belowp-monotone fn-bs-put-assoc-preserves-keys-belowp
    fn-bs-zeros-are-octets fn-bs-take-is-true-list
    fn-bs-take-of-octets-are-octets fn-bs-nthcdr-of-octets-are-octets
    fn-bs-splice-of-octets-are-octets
    fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-ops-dirs-are-apply-entries
    fn-bs-apply-writes-of-append fn-bs-apply-entries-of-append
    fn-bs-ops-for-ino-of-append fn-bs-ops-for-dir-of-append
    fn-bs-op-listp-of-append fn-bs-writes-knownp-of-append
    fn-bs-apply-writes-keeps-quiet-ino fn-bs-apply-entries-keeps-quiet-dir
    fn-bs-ops-for-ino-of-ops-not-for-ino fn-bs-ops-not-for-ino-idempotent
    fn-bs-ops-for-dir-of-ops-not-for-dir fn-bs-ops-not-for-dir-idempotent
    fn-bs-ops-for-ino-of-ops-for-ino-other fn-bs-ops-for-dir-of-ops-for-dir-other
    fn-bs-ops-for-dir-of-ops-for-ino fn-bs-ops-for-ino-of-ops-for-dir
    fn-bs-apply-entries-of-ops-for-ino fn-bs-apply-writes-of-ops-for-dir
    fn-bs-op-listp-of-ops-for-ino fn-bs-op-listp-of-ops-not-for-ino
    fn-bs-op-listp-of-ops-for-dir fn-bs-op-listp-of-ops-not-for-dir
    fn-bs-writes-knownp-of-ops-for-ino fn-bs-writes-knownp-of-ops-not-for-ino
    fn-bs-writes-knownp-of-ops-for-dir fn-bs-writes-knownp-of-ops-not-for-dir
    fn-bs-writes-knownp-of-put-assoc fn-bs-writes-knownp-of-cons
    fn-bs-writes-knownp-of-apply-writes
    fn-bs-tear-write-is-true-list fn-bs-tear-write-has-no-writes-for-other
    fn-bs-tear-write-has-no-entries fn-bs-apply-entries-of-tear-write
    fn-bs-tear-write-is-op-list fn-bs-tear-write-writes-known
    fn-bs-crash-select-keeps-quiet-ino fn-bs-crash-select-keeps-quiet-dir
    fn-bs-crash-select-is-op-list fn-bs-crash-select-writes-known
    fn-bs-crash-select-with-no-choices-is-empty
    fn-bs-apply-writes-preserves-tables fn-bs-apply-entries-preserves-dir-tablep
    fn-bs-dir-tablep-keys-are-dir-ids fn-bs-entriesp-keys-are-names
    fn-bs-lookup-types-its-dir fn-bs-lookup-types-its-name
    fn-bs-apply-entries-entry-is-entry-after fn-bs-entry-after-of-append
    fn-bs-entry-after-of-tear-write fn-bs-member-of-append
    fn-bs-crash-select-entry-is-an-outcome))
(in-theory (disable fn-bs-invariants-vocabulary fn-bs-entry-after))
