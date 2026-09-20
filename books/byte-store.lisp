; fn: the byte-level storage model under the file kernel (crash model v2, §1).
;
; A store is a table of inodes (octet lists), a table of directories (name
; maps), and an ordered list of PENDING operations the process has issued and
; no fence has drained: byte writes to inodes and entry updates to
; directories.  The process observes the VIEW (durable tables with every
; pending operation applied).  fsync(fd) drains exactly that inode's pending
; writes; fsync(dirfd) drains exactly that directory's pending entry
; operations.  A crash keeps the durable tables and lands an arbitrary
; subsequence of the pending operations, each write cut into write-unit
; pieces that land, land as zeros, or land as garbage; afterwards nothing is
; pending.  Every syscall takes an OUTCOME chosen by the environment so that
; EIO/ENOSPC with partial progress are explicit transitions, and a failed
; fsync lands a torn selection and discards the rest (fsyncgate).
;
; The definitions are specs/crash-model-v2.md §1.2-1.6 with three changes
; the well-formedness keystones of byte-store-invariants required, each
; recorded in that document's status section:
;   * fn-bs-statep carries three more conjuncts: every inode id in the table is
;     below next-ino, and every pending :write names a table inode.  Without
;     them fn-bs-create and fn-bs-crash do not preserve the inode table.
;   * fn-bs-write reports :ebadf for an inode the table does not hold (the
;     host only writes to a descriptor it opened); fn-bs-mkdir reports
;     :eexist for a directory id already in the table.
;   * fn-bs-tear-write takes its measure from fn-bs-unit-count, stated as an
;     integer first.
; Nothing here includes the file kernel: the relation to fn-sf- states is
; packet P3 (byte-store-scan), and the programs over this model are
; byte-store-programs.  This book exports its record lemmas and the list
; vocabulary; the recognizer, the view, the fences, the crash and every
; syscall are withdrawn at the end.

(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "cbor-invariants")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The state record: (:byte-store unit inodes dirs pending next-ino)
;   unit     : posp, the declared write unit in octets (512 or 4096 in the
;              development profile; every theorem holds for every posp)
;   inodes   : alist ino -> octets, the DURABLE content of every inode
;   dirs     : alist dir-id -> (alist name -> ino | dir-id), DURABLE entries
;   pending  : pending operations in issue order
;   next-ino : natp, the next unused inode id

(defun fn-bs-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6) (equal (car x) :byte-store)))

(defun fn-bs-unit (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr s)) :exec (fn-ag-car (fn-ag-cdr s))))
(verify-guards fn-bs-unit)
(defun fn-bs-inodes (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))
(verify-guards fn-bs-inodes)
(defun fn-bs-dirs (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr s))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))
(verify-guards fn-bs-dirs)
(defun fn-bs-pending (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr s)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))
(verify-guards fn-bs-pending)
(defun fn-bs-next-ino (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr s))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))))
(verify-guards fn-bs-next-ino)

(defun fn-bs-make (unit inodes dirs pending next-ino)
  (declare (xargs :guard t))
  (list :byte-store unit inodes dirs pending next-ino))

(defthm fn-bs-shapep-of-fn-bs-make
  (fn-bs-shapep (fn-bs-make unit inodes dirs pending next-ino)))
(defthm fn-bs-unit-of-fn-bs-make
  (equal (fn-bs-unit (fn-bs-make unit inodes dirs pending next-ino)) unit))
(defthm fn-bs-inodes-of-fn-bs-make
  (equal (fn-bs-inodes (fn-bs-make unit inodes dirs pending next-ino)) inodes))
(defthm fn-bs-dirs-of-fn-bs-make
  (equal (fn-bs-dirs (fn-bs-make unit inodes dirs pending next-ino)) dirs))
(defthm fn-bs-pending-of-fn-bs-make
  (equal (fn-bs-pending (fn-bs-make unit inodes dirs pending next-ino)) pending))
(defthm fn-bs-next-ino-of-fn-bs-make
  (equal (fn-bs-next-ino (fn-bs-make unit inodes dirs pending next-ino))
         next-ino))

(defthm fn-bs-shapep-forward-shape
  (implies (fn-bs-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-bs-accessors-forward-consp
  (and (implies (fn-bs-unit x) (consp x))
       (implies (fn-bs-inodes x) (consp x))
       (implies (fn-bs-dirs x) (consp x))
       (implies (fn-bs-pending x) (consp x))
       (implies (fn-bs-next-ino x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-bs-unit x) (consp x))
                                    :trigger-terms ((fn-bs-unit x)))
                 (:forward-chaining :corollary (implies (fn-bs-inodes x) (consp x))
                                    :trigger-terms ((fn-bs-inodes x)))
                 (:forward-chaining :corollary (implies (fn-bs-dirs x) (consp x))
                                    :trigger-terms ((fn-bs-dirs x)))
                 (:forward-chaining :corollary (implies (fn-bs-pending x) (consp x))
                                    :trigger-terms ((fn-bs-pending x)))
                 (:forward-chaining :corollary (implies (fn-bs-next-ino x) (consp x))
                                    :trigger-terms ((fn-bs-next-ino x)))))

(in-theory (disable (:d fn-bs-shapep) (:d fn-bs-unit) (:d fn-bs-inodes)
                    (:d fn-bs-dirs) (:d fn-bs-pending) (:d fn-bs-next-ino)
                    (:d fn-bs-make)))

; -----------------------------------------------------------------------------
; Domains and tables.

(defun fn-bs-inop (x) (declare (xargs :guard t)) (natp x))
(defun fn-bs-dir-idp (x) (declare (xargs :guard t)) (keywordp x))
(defun fn-bs-namep (x) (declare (xargs :guard t)) (stringp x))
(defun fn-bs-entry-valuep (x)
  (declare (xargs :guard t)) (or (fn-bs-inop x) (fn-bs-dir-idp x)))

(defun fn-bs-inode-tablep (x)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp x)
      (and (consp (car x)) (fn-bs-inop (car (car x)))
           (fn-cbor-octet-listp (cdr (car x)))
           (not (assoc-equal (car (car x)) (cdr x)))
           (fn-bs-inode-tablep (cdr x)))
    (null x)))

(defun fn-bs-entriesp (x)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp x)
      (and (consp (car x)) (fn-bs-namep (car (car x)))
           (fn-bs-entry-valuep (cdr (car x)))
           (not (assoc-equal (car (car x)) (cdr x)))
           (fn-bs-entriesp (cdr x)))
    (null x)))

(defun fn-bs-dir-tablep (x)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp x)
      (and (consp (car x)) (fn-bs-dir-idp (car (car x)))
           (fn-bs-entriesp (cdr (car x)))
           (not (assoc-equal (car (car x)) (cdr x)))
           (fn-bs-dir-tablep (cdr x)))
    (null x)))

; Every key of an inode table is below the allocator.
(defun fn-bs-keys-belowp (x n)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x)) (natp (car (car x)))
           (natp n) (< (car (car x)) n)
           (fn-bs-keys-belowp (cdr x) n))
    t))

; Pending operations.  There is deliberately no :truncate and no in-place
; :overwrite distinct from :write: overwriting a durable unit IS a :write to
; an inode that already has durable content there, and the crash rule below
; is what makes that dangerous (A-WRITE-ISOLATION is a theorem about
; programs that never do it, not a rule that forbids it).
;   (:write ino offset octets)
;   (:set-entry dir name value)      create, link, or rename destination
;   (:del-entry dir name)            unlink, or rename source
(defun fn-bs-opp (op)
  (declare (xargs :guard t))
  (and (true-listp op)
       (case (car op)
         (:write (and (equal (len op) 4) (fn-bs-inop (nth 1 op))
                      (natp (nth 2 op)) (fn-cbor-octet-listp (nth 3 op))))
         (:set-entry (and (equal (len op) 4) (fn-bs-dir-idp (nth 1 op))
                          (fn-bs-namep (nth 2 op))
                          (fn-bs-entry-valuep (nth 3 op))))
         (:del-entry (and (equal (len op) 3) (fn-bs-dir-idp (nth 1 op))
                          (fn-bs-namep (nth 2 op))))
         (otherwise nil))))

(defun fn-bs-op-listp (ops)
  (declare (xargs :guard t))
  (if (consp ops) (and (fn-bs-opp (car ops)) (fn-bs-op-listp (cdr ops)))
    (null ops)))

; Every pending :write names an inode the durable table holds.
(defun fn-bs-writes-knownp (ops inodes)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (or (not (equal (car (car ops)) :write))
               (assoc-equal (nth 1 (car ops)) inodes))
           (fn-bs-writes-knownp (cdr ops) inodes))
    t))

; Every pending :write carries at least one octet.  write(2) of zero octets
; changes nothing on POSIX, and fn-bs-write issues no operation for it
; ((zp n) returns the state unchanged), so this is a domain invariant of the
; model's own syscalls, in the same sense as fn-bs-writes-knownp above.  It
; is needed: fn-bs-unit-count of a zero-length write is 0, so a crash tears
; it into no pieces at all, while fn-bs-apply-op splices it and zero-extends
; the inode when the offset is past the end.  Without this conjunct the view
; of (:byte-store 4 ((0)) NIL ((:write 0 5 NIL)) 1) is five zero octets and
; no crash image of that state has them, which refutes
; fn-bs-view-is-an-admissible-image (byte-store-invariants).
(defun fn-bs-writes-nonemptyp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (or (not (equal (car (car ops)) :write)) (consp (nth 3 (car ops))))
           (fn-bs-writes-nonemptyp (cdr ops)))
    t))

(defun fn-bs-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-shapep s)
       (posp (fn-bs-unit s))
       (fn-bs-inode-tablep (fn-bs-inodes s))
       (fn-bs-dir-tablep (fn-bs-dirs s))
       (fn-bs-op-listp (fn-bs-pending s))
       (natp (fn-bs-next-ino s))
       (fn-bs-keys-belowp (fn-bs-inodes s) (fn-bs-next-ino s))
       (fn-bs-writes-knownp (fn-bs-pending s) (fn-bs-inodes s))
       (fn-bs-writes-nonemptyp (fn-bs-pending s))))

(defthm fn-bs-statep-forward-shape
  (implies (fn-bs-statep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

; -----------------------------------------------------------------------------
; Applying operations; the view.

(defun fn-bs-zeros (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp n) nil (cons 0 (fn-bs-zeros (1- n)))))

; Take n octets, zero-padding past the end: a write beyond the current end
; of a file reads back as zeros in the gap (POSIX lseek/write semantics).
(defun fn-bs-take (n xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp n) nil
    (cons (if (consp xs) (car xs) 0) (fn-bs-take (1- n) (cdr xs)))))

(defun fn-bs-splice (old offset octets)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bs-take (nfix offset) old)
          octets
          (nthcdr (+ (nfix offset) (len octets)) old)))

(defun fn-bs-put-assoc (key val alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (list (cons key val)))
        ((and (consp (car alist)) (equal (car (car alist)) key))
         (cons (cons key val) (cdr alist)))
        (t (cons (car alist) (fn-bs-put-assoc key val (cdr alist))))))

(defun fn-bs-del-assoc (key alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
        ((and (consp (car alist)) (equal (car (car alist)) key))
         (fn-bs-del-assoc key (cdr alist)))
        (t (cons (car alist) (fn-bs-del-assoc key (cdr alist))))))

(defun fn-bs-apply-op (inodes dirs op)
  (declare (xargs :guard t :verify-guards nil))
  (case (car op)
    (:write
     (mv (fn-bs-put-assoc (nth 1 op)
                          (fn-bs-splice (cdr (assoc-equal (nth 1 op) inodes))
                                        (nth 2 op) (nth 3 op))
                          inodes)
         dirs))
    (:set-entry
     (mv inodes
         (fn-bs-put-assoc (nth 1 op)
                          (fn-bs-put-assoc (nth 2 op) (nth 3 op)
                                           (cdr (assoc-equal (nth 1 op) dirs)))
                          dirs)))
    (:del-entry
     (mv inodes
         (fn-bs-put-assoc (nth 1 op)
                          (fn-bs-del-assoc (nth 2 op)
                                           (cdr (assoc-equal (nth 1 op) dirs)))
                          dirs)))
    (otherwise (mv inodes dirs))))

(defun fn-bs-apply-ops (inodes dirs ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (mv-let (inodes dirs) (fn-bs-apply-op inodes dirs (car ops))
        (fn-bs-apply-ops inodes dirs (cdr ops)))
    (mv inodes dirs)))

; What the running process observes: every pending operation applied.
(defun fn-bs-view (s)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s) (fn-bs-pending s))
    (fn-bs-make (fn-bs-unit s) inodes dirs nil (fn-bs-next-ino s))))

(defun fn-bs-lookup (s dir name)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bs-dirs (fn-bs-view s)))))))
(defun fn-bs-content (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal ino (fn-bs-inodes (fn-bs-view s)))))
(defun fn-bs-names (s dir)
  (declare (xargs :guard t :verify-guards nil))
  (strip-cars (cdr (assoc-equal dir (fn-bs-dirs (fn-bs-view s))))))

; The durable half, read without the view.  Recovery after a crash reads
; the view of a state whose pending list is empty, so the two agree there.
(defun fn-bs-durable-content (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal ino (fn-bs-inodes s))))
(defun fn-bs-durable-entry (s dir name)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bs-dirs s))))))

; -----------------------------------------------------------------------------
; Fences.

(defun fn-bs-ops-for-ino (ops ino)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino))
         (cons (car ops) (fn-bs-ops-for-ino (cdr ops) ino)))
        (t (fn-bs-ops-for-ino (cdr ops) ino))))

(defun fn-bs-ops-not-for-ino (ops ino)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino))
         (fn-bs-ops-not-for-ino (cdr ops) ino))
        (t (cons (car ops) (fn-bs-ops-not-for-ino (cdr ops) ino)))))

(defun fn-bs-ops-for-dir (ops dir)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (member-equal (car (car ops)) '(:set-entry :del-entry))
              (equal (nth 1 (car ops)) dir))
         (cons (car ops) (fn-bs-ops-for-dir (cdr ops) dir)))
        (t (fn-bs-ops-for-dir (cdr ops) dir))))

(defun fn-bs-ops-not-for-dir (ops dir)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (member-equal (car (car ops)) '(:set-entry :del-entry))
              (equal (nth 1 (car ops)) dir))
         (fn-bs-ops-not-for-dir (cdr ops) dir))
        (t (cons (car ops) (fn-bs-ops-not-for-dir (cdr ops) dir)))))

; fsync(fd) drains exactly the pending writes of that inode.  It does not
; drain the directory entry that names the inode (ALICE, Pillai et al. 2014;
; Ferrite, Bornholt et al. 2016: "fsync of a file does not persist its
; directory entry"), and it does not drain any other inode's writes.
(defun fn-bs-fence-file (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                     (fn-bs-ops-for-ino (fn-bs-pending s) ino))
    (fn-bs-make (fn-bs-unit s) inodes dirs
                (fn-bs-ops-not-for-ino (fn-bs-pending s) ino)
                (fn-bs-next-ino s))))

; fsync(dirfd) drains exactly the pending entry operations of that directory.
; It does not drain the data of the files those entries name.
(defun fn-bs-fence-dir (s dir)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                     (fn-bs-ops-for-dir (fn-bs-pending s) dir))
    (fn-bs-make (fn-bs-unit s) inodes dirs
                (fn-bs-ops-not-for-dir (fn-bs-pending s) dir)
                (fn-bs-next-ino s))))

(defun fn-bs-fencedp (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (null (fn-bs-ops-for-ino (fn-bs-pending s) ino)))
(defun fn-bs-dir-quietp (s dir)
  (declare (xargs :guard t :verify-guards nil))
  (null (fn-bs-ops-for-dir (fn-bs-pending s) dir)))

; -----------------------------------------------------------------------------
; Crash.  A crash choice is parallel to the pending list.  For a :write the
; choice is a list of one selector per write unit the write touches; for an
; entry operation it is :apply or :drop.  Missing choices are conservative
; loss.

; What one write unit of one pending write became:
;   :old              the unit is untouched
;   :new              the unit holds the written octets
;   :zero             the unit was allocated but its data did not land
;                     (ext4 delayed allocation, Ts'o 2009: zero-filled and
;                     zero-length files after a crash)
;   (:garble . octs)  the unit holds arbitrary octets (SSD shorn/torn
;                     writes, Zheng et al. FAST 2013)
(defun fn-bs-selectorp (x)
  (declare (xargs :guard t))
  (or (equal x :old) (equal x :new) (equal x :zero)
      (and (consp x) (equal (car x) :garble) (fn-cbor-octet-listp (cdr x)))))

(defun fn-bs-selector-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (fn-bs-selectorp (car xs)) (fn-bs-selector-listp (cdr xs)))
    (null xs)))

; Number of write units a write of LEN octets at OFFSET touches.
(defun fn-bs-unit-count (offset len unit)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (zp len) (zp unit)) 0
    (1+ (- (floor (+ (nfix offset) len -1) unit) (floor (nfix offset) unit)))))

(defthm fn-bs-unit-count-is-integer
  (integerp (fn-bs-unit-count offset len unit))
  :rule-classes :type-prescription)

; The write operations that landed for pieces i.. of OP under SELECTORS.
(defun fn-bs-tear-write (op selectors i unit)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (- (fn-bs-unit-count (nfix (nth 2 op)) (len (nth 3 op)) unit)
                                    (nfix i)))
                  :hints (("Goal" :in-theory (disable fn-bs-unit-count)))))
  (let* ((ino (nth 1 op)) (offset (nfix (nth 2 op))) (octets (nth 3 op))
         (count (fn-bs-unit-count offset (len octets) unit)))
    (if (or (not (consp selectors)) (zp unit) (>= (nfix i) count))
        nil
      (let* ((u (+ (floor offset unit) (nfix i)))
             (start (max offset (* u unit)))
             (end (min (+ offset (len octets)) (* (1+ u) unit)))
             (slice (fn-bs-take (- end start) (nthcdr (- start offset) octets)))
             (sel (car selectors))
             (rest (fn-bs-tear-write op (cdr selectors) (1+ (nfix i)) unit)))
        (cond ((equal sel :new) (cons (list :write ino start slice) rest))
              ((equal sel :zero)
               (cons (list :write ino start (fn-bs-zeros (- end start))) rest))
              ((and (consp sel) (equal (car sel) :garble))
               (cons (list :write ino start (fn-bs-take (- end start) (cdr sel)))
                     rest))
              (t rest))))))

(defun fn-bs-crash-choicep (op choice unit)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car op) :write)
      (and (fn-bs-selector-listp choice)
           (<= (len choice) (fn-bs-unit-count (nth 2 op) (len (nth 3 op)) unit)))
    (or (equal choice :apply) (equal choice :drop))))

(defun fn-bs-crash-choicesp (choices ops unit)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom choices) t)
        ((atom ops) nil)
        (t (and (fn-bs-crash-choicep (car ops) (car choices) unit)
                (fn-bs-crash-choicesp (cdr choices) (cdr ops) unit)))))

; The subsequence of pending operations that lands, in issue order, with each
; write cut into the pieces its selectors keep.  Issue order among the
; survivors is what the page cache guarantees for one file: a later write to
; the same unit is never undone by an earlier one landing after it.  Across
; files and directories there is no order at all, which subset selection
; already expresses.
(defun fn-bs-crash-select (ops choices unit)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (let ((op (car ops)) (choice (if (consp choices) (car choices) nil)))
        (append (if (equal (car op) :write)
                    (fn-bs-tear-write op choice 0 unit)
                  (if (equal choice :apply) (list op) nil))
                (fn-bs-crash-select (cdr ops) (cdr choices) unit)))
    nil))

(defun fn-bs-crash (s choices)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                     (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s)))
    (fn-bs-make (fn-bs-unit s) inodes dirs nil (fn-bs-next-ino s))))

; The admissible-image predicate.  fn-bs-crash is its constructor; every
; theorem about crash images quantifies over this predicate, never over a
; choice.
(defun-sk fn-bs-crash-imagep (s image)
  (exists (choices)
    (and (fn-bs-crash-choicesp choices (fn-bs-pending s) (fn-bs-unit s))
         (equal image (fn-bs-crash s choices)))))

; -----------------------------------------------------------------------------
; Syscalls with outcomes.  Every syscall returns (mv result state).  OUTCOME
; is chosen by the environment: :ok, or a failure with the progress the
; platform may have made before reporting it.  The result is :ok or an errno
; keyword: :eio, :enospc, :eexist, :enoent, :ebadf.

; open(O_CREAT|O_EXCL).  The inode exists durably and empty from creation;
; only its NAME is pending.  This is the "zero-length file after crash"
; outcome made first-class.  An error creates nothing.
(defun fn-bs-create (s dir name outcome)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-bs-lookup s dir name) (mv :eexist s))
        ((equal outcome :ok)
         (let ((ino (fn-bs-next-ino s)))
           (mv :ok (fn-bs-make (fn-bs-unit s)
                               (cons (cons ino nil) (fn-bs-inodes s))
                               (fn-bs-dirs s)
                               (append (fn-bs-pending s)
                                       (list (list :set-entry dir name ino)))
                               (1+ ino)))))
        (t (mv outcome s))))

; write(2) / write_all.  outcome :ok accepts every octet; (errno . n) accepts
; the first n octets and then reports errno (a short write followed by EIO or
; ENOSPC, or zero progress).  Accepted octets are pending, never durable.  An
; inode the table does not hold is a bad descriptor.
(defun fn-bs-write (s ino offset octets outcome)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (assoc-equal ino (fn-bs-inodes s)))
      (mv :ebadf s)
    (let* ((n (if (equal outcome :ok) (len octets) (nfix (cdr outcome))))
           (accepted (fn-bs-take n octets))
           (s1 (if (zp n) s
                 (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                             (append (fn-bs-pending s)
                                     (list (list :write ino offset accepted)))
                             (fn-bs-next-ino s)))))
      (mv (if (equal outcome :ok) :ok (car outcome)) s1))))

; fsync(fd) / F_FULLFSYNC.  :ok drains the inode's pending writes.
; (errno . choices) reports failure after landing the torn selection CHOICES
; of those writes and DISCARDING the rest: the platform has marked the dirty
; pages clean (Linux ext4/xfs, Rebello et al. 2020; PostgreSQL fsyncgate,
; 2018), so nothing remains for a retry to write and a later fsync that
; returns :ok fences nothing.  ENOSPC surfaces here under delayed
; allocation even though every write returned :ok.
(defun fn-bs-fsync-file (s ino outcome)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal outcome :ok)
      (mv :ok (fn-bs-fence-file s ino))
    (let ((mine (fn-bs-ops-for-ino (fn-bs-pending s) ino)))
      (mv-let (inodes dirs)
        (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                         (fn-bs-crash-select mine (cdr outcome) (fn-bs-unit s)))
        (mv (car outcome)
            (fn-bs-make (fn-bs-unit s) inodes dirs
                        (fn-bs-ops-not-for-ino (fn-bs-pending s) ino)
                        (fn-bs-next-ino s)))))))

; fsync(dirfd): the same, over the directory's entry operations.
(defun fn-bs-fsync-dir (s dir outcome)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal outcome :ok)
      (mv :ok (fn-bs-fence-dir s dir))
    (let ((mine (fn-bs-ops-for-dir (fn-bs-pending s) dir)))
      (mv-let (inodes dirs)
        (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                         (fn-bs-crash-select mine (cdr outcome) (fn-bs-unit s)))
        (mv (car outcome)
            (fn-bs-make (fn-bs-unit s) inodes dirs
                        (fn-bs-ops-not-for-dir (fn-bs-pending s) dir)
                        (fn-bs-next-ino s)))))))

; link(2): one pending entry operation on the destination directory.  An
; error outcome is (errno . :issued) or (errno . :not-issued): the host
; cannot tell which, and store-refinement.md item 11 says so ("an error does
; not become a known abort merely because the final name is absent").
(defun fn-bs-link (s sdir sname ddir dname outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bs-lookup s sdir sname)))
    (cond ((not (fn-bs-inop ino)) (mv :enoent s))
          ((fn-bs-lookup s ddir dname) (mv :eexist s))
          ((or (equal outcome :ok)
               (and (consp outcome) (equal (cdr outcome) :issued)))
           (mv (if (equal outcome :ok) :ok (car outcome))
               (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                           (append (fn-bs-pending s)
                                   (list (list :set-entry ddir dname ino)))
                           (fn-bs-next-ino s))))
          (t (mv (car outcome) s)))))

; rename(2) / os.replace: the destination entry is replaced by ONE
; :set-entry, so it is old or new and never half; the source entry's removal
; is a SEPARATE pending operation on the source directory.  The two are not
; assumed to land together (Pillai et al. 2014 Table 1: rename atomicity
; across a crash is per-filesystem).  Losing the removal leaves a staging
; orphan; losing the replacement leaves the old value; both are outcomes the
; host's recovery already accepts.
(defun fn-bs-rename (s sdir sname ddir dname outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bs-lookup s sdir sname)))
    (cond ((not (fn-bs-inop ino)) (mv :enoent s))
          ((or (equal outcome :ok)
               (and (consp outcome) (equal (cdr outcome) :issued)))
           (mv (if (equal outcome :ok) :ok (car outcome))
               (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                           (append (fn-bs-pending s)
                                   (list (list :set-entry ddir dname ino)
                                         (list :del-entry sdir sname)))
                           (fn-bs-next-ino s))))
          (t (mv (car outcome) s)))))

(defun fn-bs-unlink (s dir name outcome)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-bs-lookup s dir name)) (mv :enoent s))
        ((or (equal outcome :ok)
             (and (consp outcome) (equal (cdr outcome) :issued)))
         (mv (if (equal outcome :ok) :ok (car outcome))
             (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                         (append (fn-bs-pending s) (list (list :del-entry dir name)))
                         (fn-bs-next-ino s))))
        (t (mv (car outcome) s))))

; mkdir(2): the directory exists durably and empty; its name in the parent is
; pending until the parent is fenced.  A directory id already in the table is
; :eexist (the id stands for the inode the platform would allocate).
(defun fn-bs-mkdir (s parent name id outcome)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-bs-lookup s parent name) (mv :eexist s))
        ((assoc-equal id (fn-bs-dirs s)) (mv :eexist s))
        ((equal outcome :ok)
         (mv :ok (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s)
                             (cons (cons id nil) (fn-bs-dirs s))
                             (append (fn-bs-pending s)
                                     (list (list :set-entry parent name id)))
                             (fn-bs-next-ino s))))
        (t (mv outcome s))))

; read(2) and scandir(3) observe the view.  close(2) has no durability
; effect and is not a step; the host's close-EIO handling is an A-HOST
; classification, not a storage transition.
(defun fn-bs-read (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-content s ino))

; What the model leaves unspecified, on purpose: the view of an inode after a
; FAILED fsync (Linux keeps the never-written data in cache and reports it to
; read, so the view and the durable content diverge).  v2 adds no cache
; field; byte-store-programs requires instead that no program reads a file
; whose fence failed.

; -----------------------------------------------------------------------------
; Export theory.  Enabled on include: the record lemmas, the domain
; predicates, the tables and the list vocabulary (apply, fences' selectors,
; tear and select) that byte-store-invariants inducts on.  Withdrawn: the
; state recognizer, the view and its readers, the fences, the crash, the
; admissibility predicate and every syscall.

(in-theory (disable fn-bs-statep fn-bs-view fn-bs-lookup fn-bs-content
                    fn-bs-names fn-bs-durable-content fn-bs-durable-entry
                    fn-bs-fence-file fn-bs-fence-dir fn-bs-fencedp
                    fn-bs-dir-quietp fn-bs-crash fn-bs-crash-imagep
                    fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir
                    fn-bs-link fn-bs-rename fn-bs-unlink fn-bs-mkdir
                    fn-bs-read))
