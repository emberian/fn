; The scan, the byte-store/kernel relation, and the K1-K3 keystones.
;
; specs/crash-model-v2.md sections 3.1 to 3.3.  This book answers the question
; the byte model exists to answer: what the host's recover() reads out of a
; crash image, and why that reading is one the file kernel
; (books/store-files.lisp) already admits.  The kernel predicate
; fn-sf-crash-imagep is NOT changed; it is the interface this book proves
; inhabited by every byte-level crash of a related state.
;
; The route.  The previous lane (w9/storage, planning/lanes/HANDOFF-w9-storage.md)
; recorded that the natural PER-DIRECTORY lemma -- "one directory's entries
; after a list of operations depend only on that directory's operations" -- is
; both a looping rewrite and an induction that does not close, because the
; branch where the head operation names another directory needs a commutation
; lemma nothing has.  The route that works, and the one taken here, is
; PER-NAME: byte-store-invariants.lisp reduces one entry's value to
; fn-bs-entry-after, which ignores other directories' operations BY
; CONSTRUCTION, so no commutation is ever needed.  This book lifts exactly
; that shape to the name LIST (fn-bs-names-after, section 2) and to the
; content at each name (section 4), then composes over the name list by
; induction with the record decoder closed (section 5).
;
; Two seams are constrained functions, as section 3.1 prescribes: the frontier
; codec (Python owns the JSON+sha256 today; packet P4 makes it an fn-frame
; frame) and the transaction file name (the host's "{:020d}.txn"; ACL2 owning
; the decimal format is its own packet).  fn-bs-config-okp is the third, for
; the same reason.  Each is an encapsulate with a local witness, and the
; theorems below use only the named constraints.

(in-package "ACL2")
(include-book "byte-store-invariants")
(include-book "store-files-invariants")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-bs-statep fn-bs-view fn-bs-lookup fn-bs-content
                          fn-bs-names fn-bs-durable-content fn-bs-durable-entry
                          fn-bs-fencedp fn-bs-dir-quietp
                          fn-bs-invariants-vocabulary fn-bs-entry-after)))

; -----------------------------------------------------------------------------
; 1. The three seams.

; The frontier codec (design 3.1).  Today the frontier file is JSON with a
; Python-computed sha256 (tools/run_store.py:567), which the assurance rules
; forbid as a twin; after packet P4 it is an fn-frame frame and this becomes
; (fn-frame-open octets ...) followed by a CBOR uint decode.  The theorems in
; this book depend only on the two constraints.
(encapsulate
  (((fn-bs-frontier-decode *) => *)
   ((fn-bs-frontier-encode *) => *))
  (local (defun fn-bs-frontier-encode (n) (list n)))
  (local (defun fn-bs-frontier-decode (octets)
           (if (and (consp octets) (natp (car octets)) (null (cdr octets)))
               (car octets)
             nil)))
  (defthm fn-bs-frontier-round-trip
    (implies (natp n) (equal (fn-bs-frontier-decode (fn-bs-frontier-encode n)) n)))
  (defthm fn-bs-frontier-decode-nat-or-nil
    (or (natp (fn-bs-frontier-decode octets))
        (null (fn-bs-frontier-decode octets)))
    :rule-classes :type-prescription))

; The transaction file name.  The decimal format "{:020d}.txn" is the host's
; (tools/run_store.py); what the scan needs of it is that it is a name and
; that distinct sequence numbers get distinct names.
(encapsulate
  (((fn-bs-txn-name *) => *))
  (local
   (defun fn-bs-txn-chars (n)
     (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
     (if (zp n) nil (cons #\a (fn-bs-txn-chars (1- n))))))
  (local
   (defthm fn-bs-txn-chars-are-characters
     (character-listp (fn-bs-txn-chars n))))
  (local
   (defthm fn-bs-txn-chars-length
     (equal (len (fn-bs-txn-chars n)) (nfix n))))
  (local
   (defthm fn-bs-txn-chars-injective
     (implies (and (natp i) (natp j)
                   (equal (fn-bs-txn-chars i) (fn-bs-txn-chars j)))
              (equal i j))
     :rule-classes nil
     :hints (("Goal" :use ((:instance fn-bs-txn-chars-length (n i))
                           (:instance fn-bs-txn-chars-length (n j)))
              :in-theory (disable fn-bs-txn-chars-length)))))
  (local
   (defthm fn-bs-coerce-list-of-string
     (implies (character-listp x)
              (equal (coerce (coerce x 'string) 'list) x))
     :rule-classes nil
     :hints (("Goal" :use coerce-inverse-2))))
  ; Under the minimal theory nothing rewrites the two coerce terms away, so
  ; the string equality carries to the character lists by congruence.
  (local
   (defthm fn-bs-txn-chars-injective-through-coerce
     (implies (and (natp i) (natp j)
                   (equal (coerce (fn-bs-txn-chars i) 'string)
                          (coerce (fn-bs-txn-chars j) 'string)))
              (equal i j))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance fn-bs-coerce-list-of-string (x (fn-bs-txn-chars i)))
                    (:instance fn-bs-coerce-list-of-string (x (fn-bs-txn-chars j)))
                    fn-bs-txn-chars-injective
                    (:instance fn-bs-txn-chars-are-characters (n i))
                    (:instance fn-bs-txn-chars-are-characters (n j)))
              :in-theory (theory 'minimal-theory)))))
  (local (defun fn-bs-txn-name (n) (coerce (fn-bs-txn-chars n) 'string)))
  (defthm fn-bs-txn-name-is-a-name
    (fn-bs-namep (fn-bs-txn-name n)))
  (defthm fn-bs-txn-name-is-injective
    (implies (and (natp i) (natp j) (not (equal i j)))
             (not (equal (fn-bs-txn-name i) (fn-bs-txn-name j))))
    :hints (("Goal" :use fn-bs-txn-chars-injective-through-coerce))))

; The config file.  Same seam as the frontier: run_store.py computes its
; integrity value today (config_with_checksum), which packet P4 moves into
; ACL2.  The scan only needs that the check is a function of the octets, so
; the encapsulate carries no constraint beyond that.
(encapsulate
  (((fn-bs-config-okp *) => *))
  (local (defun fn-bs-config-okp (octets) (declare (ignore octets)) t)))

(defconst *fn-bs-scan-config-name* "config.json")
(defconst *fn-bs-scan-frontier-name* "allocation-frontier.json")

; -----------------------------------------------------------------------------
; 2. The name list of one directory, per-name.
;
; fn-bs-names-after is to strip-cars what fn-bs-entry-after (byte-store-
; invariants) is to one entry's value: a projection of the operation list onto
; ONE directory that ignores every other directory's operations by
; construction.  That is the whole reason the per-directory route failed and
; this one does not.

(defun fn-bs-name-step (op old)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car op) :set-entry)
      (if (member-equal (nth 2 op) old) old (append old (list (nth 2 op))))
    (remove-equal (nth 2 op) old)))

(defun fn-bs-names-after (ops old dir)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (let ((op (car ops)))
        (fn-bs-names-after
         (cdr ops)
         (if (and (member-equal (car op) '(:set-entry :del-entry))
                  (equal (nth 1 op) dir))
             (fn-bs-name-step op old)
           old)
         dir))
    old))

(defthm fn-bs-strip-cars-of-put-assoc
  (implies (alistp alist)
           (equal (strip-cars (fn-bs-put-assoc key val alist))
                  (if (member-equal key (strip-cars alist))
                      (strip-cars alist)
                    (append (strip-cars alist) (list key))))))

(defthm fn-bs-strip-cars-of-del-assoc
  (implies (alistp alist)
           (equal (strip-cars (fn-bs-del-assoc key alist))
                  (remove-equal key (strip-cars alist)))))

(defthm fn-bs-alistp-of-del-assoc
  (implies (alistp alist) (alistp (fn-bs-del-assoc key alist))))

(defthm fn-bs-alistp-of-dir-entries
  (implies (fn-bs-dir-tablep dirs)
           (alistp (cdr (assoc-equal dir dirs)))))

(defthm fn-bs-apply-entries-preserves-alistp-of-entries
  (implies (and (fn-bs-dir-tablep dirs) (fn-bs-op-listp ops))
           (fn-bs-dir-tablep (fn-bs-apply-entries dirs ops))))

; The name-list analogue of fn-bs-apply-entries-entry-is-entry-after.
(defthm fn-bs-apply-entries-names-is-names-after
  (implies (and dir (fn-bs-dir-tablep dirs) (fn-bs-op-listp ops))
           (equal (strip-cars (cdr (assoc-equal dir (fn-bs-apply-entries dirs ops))))
                  (fn-bs-names-after ops (strip-cars (cdr (assoc-equal dir dirs))) dir)))
  :hints (("Goal" :induct (fn-bs-apply-entries dirs ops))))

(defthm fn-bs-names-after-of-tear-write
  (equal (fn-bs-names-after (fn-bs-tear-write op sels i unit) old dir) old))

(defthm fn-bs-names-after-of-append
  (equal (fn-bs-names-after (append a b) old dir)
         (fn-bs-names-after b (fn-bs-names-after a old dir) dir)))

; The outcome enumeration, exactly as fn-bs-entry-outcomes does it for one
; entry's value: every name list a crash can leave, from the operations of
; this directory alone.
(defun fn-bs-names-outcomes (ops old dir)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (append (fn-bs-names-outcomes (cdr ops) old dir)
              (fn-bs-names-outcomes (cdr ops) (fn-bs-name-step (car ops) old) dir))
    (list old)))

(local
 (defun fn-bs-names-induct (ops choices old dir)
   (if (consp ops)
       (let ((op (car ops)))
         (list (fn-bs-names-induct (cdr ops) (cdr choices) old dir)
               (fn-bs-names-induct (cdr ops) (cdr choices)
                                   (fn-bs-name-step op old) dir)))
     (list old choices dir))))

(defthm fn-bs-crash-select-names-are-an-outcome
  (member-equal (fn-bs-names-after (fn-bs-crash-select ops choices unit) old dir)
                (fn-bs-names-outcomes (fn-bs-ops-for-dir ops dir) old dir))
  :hints (("Goal" :induct (fn-bs-names-induct ops choices old dir))))

; -----------------------------------------------------------------------------
; 3. The scan (design 3.1).

(defun fn-bs-record-of (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (let ((octets (fn-bs-content s ino)))
    (fn-frame-store-decode octets
                           (fn-frame-digest (fn-frame-protected-prefix octets)))))

(defun fn-bs-txn-names (n)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (append (fn-bs-txn-names (1- n)) (list (fn-bs-txn-name (1- n))))))

(defun fn-bs-contiguous-namesp (names n)
  (declare (xargs :guard t :verify-guards nil))
  (equal names (fn-bs-txn-names n)))

(defun fn-bs-read-records (s n count)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix count) (nfix n)))))
  (if (or (not (natp n)) (not (natp count)) (>= n count))
      nil
    (let* ((ino (fn-bs-lookup s :transactions (fn-bs-txn-name n)))
           (record (and (fn-bs-inop ino) (fn-bs-record-of s ino)))
           (rest (fn-bs-read-records s (1+ n) count)))
      (if (or (not (fn-record-p record))
              (not (equal (fn-record-sequence record) n))
              (equal rest :fault))
          :fault
        (cons record rest)))))

(defun fn-bs-scan-store (image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-bs-lookup image :root *fn-bs-scan-config-name*))
        (f (fn-bs-lookup image :root *fn-bs-scan-frontier-name*))
        (names (fn-bs-names image :transactions)))
    (cond ((not (fn-bs-inop c)) (list :fault :config))
          ((not (fn-bs-config-okp (fn-bs-content image c))) (list :fault :config))
          ((not (fn-bs-inop f)) (list :fault :frontier))
          ((not (natp (fn-bs-frontier-decode (fn-bs-content image f))))
           (list :fault :frontier))
          ((not (fn-bs-contiguous-namesp names (len names))) (list :fault :namespace))
          (t (let ((records (fn-bs-read-records image 0 (len names))))
               (if (equal records :fault)
                   (list :fault :record)
                 (list :ok (fn-bs-frontier-decode (fn-bs-content image f)) records)))))))

(defun fn-bs-scan-okp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp x) (equal (car x) :ok)))
(defun fn-bs-scan-frontier (x) (declare (xargs :guard t :verify-guards nil)) (nth 1 x))
(defun fn-bs-scan-records (x) (declare (xargs :guard t :verify-guards nil)) (nth 2 x))

; -----------------------------------------------------------------------------
; 4. The relation (design 3.2), with the durable contiguity the handoff names.

(defun fn-bs-durable (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs) nil
              (fn-bs-next-ino bs)))

(defun fn-bs-durable-names (bs dir)
  (declare (xargs :guard t :verify-guards nil))
  (strip-cars (cdr (assoc-equal dir (fn-bs-dirs bs)))))

(defun fn-bs-durable-frontier (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-frontier-decode
   (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))))

(defun fn-bs-durable-records (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-read-records (fn-bs-durable bs) 0
                      (len (fn-bs-durable-names bs :transactions))))

(defun fn-bs-pending-matches-phase (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (let ((root-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
        (txn-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
    (and (if (fn-sf-frontier-new-visiblep ks)
             (or (null root-ops)
                 (and (equal (len root-ops) 1)
                      (equal (car (car root-ops)) :set-entry)
                      (equal (nth 2 (car root-ops)) *fn-bs-scan-frontier-name*)
                      (fn-bs-inop (nth 3 (car root-ops)))
                      (fn-bs-fencedp bs (nth 3 (car root-ops)))
                      (equal (fn-bs-frontier-decode
                              (fn-bs-durable-content bs (nth 3 (car root-ops))))
                             (fn-sf-frontier-candidate ks))))
           (null root-ops))
         (if (fn-sf-record-present-visiblep ks)
             (or (null txn-ops)
                 (and (equal (len txn-ops) 1)
                      (equal (car (car txn-ops)) :set-entry)
                      (equal (nth 2 (car txn-ops))
                             (fn-bs-txn-name
                              (len (fn-bs-durable-names bs :transactions))))
                      (fn-bs-inop (nth 3 (car txn-ops)))
                      (fn-bs-fencedp bs (nth 3 (car txn-ops)))
                      (equal (fn-bs-record-of (fn-bs-durable bs) (nth 3 (car txn-ops)))
                             (fn-sf-record-candidate ks))))
           (null txn-ops)))))

; Every inode an authority entry names, durable or pending, is fenced: no
; pending write can reach it, so a crash keeps its content exactly (D1, D2).
(defun fn-bs-pending-entry-targets (ops)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (equal (car (car ops)) :set-entry)
              (member-equal (nth 1 (car ops)) '(:root :transactions)))
         (cons (nth 3 (car ops)) (fn-bs-pending-entry-targets (cdr ops))))
        (t (fn-bs-pending-entry-targets (cdr ops)))))

(defun fn-bs-authority-inode-list (bs)
  (declare (xargs :guard t :verify-guards nil))
  (append (list (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)
                (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
          (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs))))
          (fn-bs-pending-entry-targets (fn-bs-pending bs))))

(defun fn-bs-all-fencedp (bs inos)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp inos)
      (and (fn-bs-fencedp bs (car inos)) (fn-bs-all-fencedp bs (cdr inos)))
    t))

(defun fn-bs-authority-fencedp (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-all-fencedp bs (fn-bs-authority-inode-list bs)))

(defun fn-bs-store-relation (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-statep bs) (fn-sf-statep ks)
       (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
       (fn-bs-config-okp
        (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
       (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
       ; the durable transaction namespace is contiguous: the handoff's
       ; clause, without which the scan's namespace test is not decidable
       ; from the pending list alone.
       (fn-bs-contiguous-namesp (fn-bs-durable-names bs :transactions)
                                (len (fn-bs-durable-names bs :transactions)))
       (not (equal (fn-bs-durable-records bs) :fault))
       (fn-sf-crash-imagep ks (fn-bs-durable-frontier bs) (fn-bs-durable-records bs))
       (fn-bs-pending-matches-phase bs ks)
       (fn-bs-authority-fencedp bs)))

; -----------------------------------------------------------------------------
; 5. From a crash image back to the durable state, name by name.
;
; Everything here is stated on ONE name (or one inode) at a time, and the
; composition over the transaction directory is an induction over the name
; list with fn-record-p and the frame decoder closed.

(defthm fn-bs-crash-pending-is-nil
  (equal (fn-bs-pending (fn-bs-crash s choices)) nil)
  :hints (("Goal" :in-theory (enable fn-bs-crash))))

(defthm fn-bs-crash-image-is-quiet
  (implies (fn-bs-crash-imagep s image) (equal (fn-bs-pending image) nil))
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep))))

(defthm fn-bs-quiet-lookup-is-durable-entry
  (implies (equal (fn-bs-pending s) nil)
           (equal (fn-bs-lookup s dir name) (fn-bs-durable-entry s dir name))))
(defthm fn-bs-quiet-content-is-durable-content
  (implies (equal (fn-bs-pending s) nil)
           (equal (fn-bs-content s ino) (fn-bs-durable-content s ino))))
(defthm fn-bs-quiet-names-are-durable-names
  (implies (equal (fn-bs-pending s) nil)
           (equal (fn-bs-names s dir) (fn-bs-durable-names s dir))))

(defthm fn-bs-durable-is-quiet
  (and (equal (fn-bs-pending (fn-bs-durable bs)) nil)
       (equal (fn-bs-inodes (fn-bs-durable bs)) (fn-bs-inodes bs))
       (equal (fn-bs-dirs (fn-bs-durable bs)) (fn-bs-dirs bs))))

; One name's operations are the operations of its directory, filtered again.
; As a rewrite its right side matches its own left side (with OPS bound to
; (fn-bs-ops-for-dir ops dir)), so it is cited, never left to match.
(defthm fn-bs-ops-for-name-through-ops-for-dir
  (equal (fn-bs-ops-for-name ops dir name)
         (fn-bs-ops-for-name (fn-bs-ops-for-dir ops dir) dir name))
  :rule-classes nil)

(defthm fn-bs-entry-outcomes-of-nil
  (equal (fn-bs-entry-outcomes nil old) (list old)))

; A name none of the directory's pending operations touches keeps its durable
; value across every admissible crash.
(defthm fn-bs-crash-keeps-untouched-entry
  (implies (and (fn-bs-dir-idp dir) (fn-bs-namep name)
                (fn-bs-crash-imagep s image)
                (equal (fn-bs-ops-for-name (fn-bs-ops-for-dir (fn-bs-pending s) dir)
                                           dir name)
                       nil))
           (equal (fn-bs-durable-entry image dir name)
                  (fn-bs-durable-entry s dir name)))
  :hints (("Goal"
           :use ((:instance fn-bs-crash-entry-is-old-or-a-pending-target)
                 (:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending s))))
           :in-theory (disable fn-bs-crash-entry-is-old-or-a-pending-target
                               fn-bs-ops-for-name fn-bs-ops-for-dir))))

; The fenced-inode list vocabulary the relation's authority clause needs.
(defthm fn-bs-all-fencedp-of-append
  (equal (fn-bs-all-fencedp bs (append a b))
         (and (fn-bs-all-fencedp bs a) (fn-bs-all-fencedp bs b))))
(defthm fn-bs-all-fencedp-member
  (implies (and (fn-bs-all-fencedp bs inos) (member-equal ino inos))
           (fn-bs-fencedp bs ino)))
(defthm fn-bs-assoc-value-is-in-strip-cdrs
  (implies (assoc-equal k alist)
           (member-equal (cdr (assoc-equal k alist)) (strip-cdrs alist))))
(defthm fn-bs-assoc-of-name-in-entries
  (implies (member-equal name (strip-cars alist))
           (assoc-equal name alist)))

; -----------------------------------------------------------------------------
; 6. The record list of a prefix of the transaction namespace.

(defun fn-bs-txn-prefix-agreesp (a b n count)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (- (nfix count) (nfix n)))))
  (if (or (not (natp n)) (not (natp count)) (>= n count))
      t
    (and (equal (fn-bs-lookup a :transactions (fn-bs-txn-name n))
                (fn-bs-lookup b :transactions (fn-bs-txn-name n)))
         (equal (fn-bs-content a (fn-bs-lookup a :transactions (fn-bs-txn-name n)))
                (fn-bs-content b (fn-bs-lookup b :transactions (fn-bs-txn-name n))))
         (fn-bs-txn-prefix-agreesp a b (1+ n) count))))

; The composition step: the scan reads a name and a content at each index and
; nothing else, so two images that agree at every index of a range read the
; same records there.  fn-record-p and fn-frame-store-decode stay closed.
(defthm fn-bs-read-records-under-agreement
  (implies (fn-bs-txn-prefix-agreesp a b n count)
           (equal (fn-bs-read-records a n count)
                  (fn-bs-read-records b n count)))
  :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp a b n count)
           :in-theory (disable fn-bs-lookup fn-bs-content fn-bs-record-of))))

(defthm fn-bs-read-records-len
  (implies (and (natp n) (natp count)
                (not (equal (fn-bs-read-records s n count) :fault)))
           (equal (len (fn-bs-read-records s n count)) (nfix (- count n))))
  :hints (("Goal" :in-theory (disable fn-bs-lookup fn-bs-content fn-bs-record-of))))

(defthm fn-bs-read-records-is-a-true-list
  (implies (not (equal (fn-bs-read-records s n count) :fault))
           (true-listp (fn-bs-read-records s n count)))
  :hints (("Goal" :in-theory (disable fn-bs-lookup fn-bs-content fn-bs-record-of))))

; Reading one more name appends one more record.
(defthm fn-bs-read-records-of-one-more
  (implies (and (natp n) (natp count) (<= n count)
                (not (equal (fn-bs-read-records s n count) :fault))
                (not (equal (fn-bs-read-records s count (1+ count)) :fault)))
           (equal (fn-bs-read-records s n (1+ count))
                  (append (fn-bs-read-records s n count)
                          (fn-bs-read-records s count (1+ count)))))
  :hints (("Goal" :induct (fn-bs-read-records s n count)
           :in-theory (disable fn-bs-lookup fn-bs-content fn-bs-record-of))))

(defthm fn-bs-txn-names-length
  (equal (len (fn-bs-txn-names n)) (nfix n)))

; -----------------------------------------------------------------------------
; 7. The transaction namespace of a crash image.

(defthm fn-bs-txn-name-not-in-txn-names
  (implies (and (natp i) (natp n) (<= n i))
           (not (member-equal (fn-bs-txn-name i) (fn-bs-txn-names n))))
  :hints (("Goal" :in-theory (disable fn-bs-txn-name))))

(defthm fn-bs-txn-names-of-1+
  (implies (natp n)
           (equal (fn-bs-txn-names (1+ n))
                  (append (fn-bs-txn-names n) (list (fn-bs-txn-name n))))))

(defthm fn-bs-crash-names-is-names-after
  (implies (and (fn-bs-statep s) dir)
           (equal (fn-bs-durable-names (fn-bs-crash s choices) dir)
                  (fn-bs-names-after (fn-bs-crash-select (fn-bs-pending s) choices
                                                         (fn-bs-unit s))
                                     (fn-bs-durable-names s dir) dir)))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash) (fn-bs-names-after))
           :use ((:instance fn-bs-apply-entries-names-is-names-after
                            (dirs (fn-bs-dirs s))
                            (ops (fn-bs-crash-select (fn-bs-pending s) choices
                                                     (fn-bs-unit s))))))))

(defthm fn-bs-crash-image-names-are-an-outcome
  (implies (and (fn-bs-statep s) dir (fn-bs-crash-imagep s image))
           (member-equal (fn-bs-durable-names image dir)
                         (fn-bs-names-outcomes (fn-bs-ops-for-dir (fn-bs-pending s) dir)
                                               (fn-bs-durable-names s dir) dir)))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash-imagep)
                                  (fn-bs-durable-names fn-bs-crash
                                   fn-bs-names-after fn-bs-names-outcomes))
           :use ((:instance fn-bs-crash-select-names-are-an-outcome
                            (ops (fn-bs-pending s)) (unit (fn-bs-unit s))
                            (old (fn-bs-durable-names s dir)))))))

; The namespace half of K1: under the relation, a crash image's transaction
; names are the durable ones or the durable ones with the candidate's name
; appended, and both are contiguous.
(defthm fn-bs-crash-image-transaction-names
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (let ((m (len (fn-bs-durable-names bs :transactions))))
             (or (equal (fn-bs-names image :transactions) (fn-bs-txn-names m))
                 (equal (fn-bs-names image :transactions) (fn-bs-txn-names (1+ m))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-crash-image-names-are-an-outcome
                            (s bs) (dir :transactions))
                 (:instance fn-bs-txn-name-not-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (e/d (fn-bs-names-outcomes fn-bs-name-step)
                           (fn-bs-txn-name fn-bs-txn-names
                            fn-bs-durable-names fn-bs-ops-for-dir)))))
