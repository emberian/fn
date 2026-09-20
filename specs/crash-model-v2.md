# Crash model v2: a byte-level storage model under the file kernel

Status: design, 2026-09-19, lane `w4/crash-model-design`. Every ACL2 form in
this document is a proposed definition or a proposed theorem statement. None
has been admitted or proved; no certification ran in this lane. Book names,
the `fn-bs-` prefix and the theorem names are proposals for the packets in
§6; the prefix must be registered in `docs/prefixes.md` before the first book
is added.

Replaces, when the packets land: the crash constructor as the source of the
"old or new" and "absent or present" shapes in
[store-refinement.md](store-refinement.md) §"Observable events" item 15 and
§"Assumptions and claim boundary"; the prose form of A-DURABILITY and
A-WRITE-ISOLATION in [failures.md](failures.md); the two `gap` rows of
`tests/campaign/cuts.py`; and the six-cut table of
[store-fault-matrix.md](store-fault-matrix.md).

## 0. Why the present model is not acceptable

The present model (`books/store-files.lisp`, `fn-sf-crash-imagep`,
`fn-sf-crash`) is a model of *namespace observations*: a crash image is a
frontier value that is the stable one or the candidate, and a record list
that is the stable one or the stable one plus the exact candidate. That is
the right *conclusion*. It is stated as the *hypothesis*. Specifically:

1. **Old-or-new is assumed, not derived.** `fn-sf-crash-imagep` (store-files.lisp:499)
   asserts that a replacement is wholly old or wholly new and a link is
   absent or the exact inode. Nothing in the tree connects those shapes to
   `os.replace`, `os.link`, `fsync` or bytes; store-refinement.md
   §"Assumptions and claim boundary" says so in its own words. The 2026-09-19
   crash-fidelity revision made the constructor a corollary of the predicate,
   which is correct, but the predicate itself is where the platform is trusted.
2. **There are no torn writes.** The only torn write in the tree is the
   `:torn` slot tag of `books/journal.lisp`, which store-refinement.md
   already retires as "not the adapter model". FLR-001 says "unsynced writes
   may be absent, torn, or reordered"; no adapter theorem quantifies over any
   of those.
3. **`fsync` failure has no semantics.** The host treats a staging `fsync`
   error as a known abort and a recovery `fsync` error as a fence. Both are
   correct, but for a reason the model cannot state: on Linux, a failed
   `fsync` discards the dirty pages, a retry succeeds without writing them,
   and reading the file back shows the data that was never written (the
   PostgreSQL "fsyncgate" incident, 2018; Rebello et al. 2020). A model in
   which `fsync` is a boolean event cannot distinguish a host that aborts
   from one that retries.
4. **Directories are prose.** "A file flush alone is not automatically a
   directory commit" (failures.md) is a sentence. The model has no directory,
   no pending directory operation, and no way to state that `fsync_dir` of
   `transactions/` is what removes the absent choice while `staging/` is
   never fenced at all and need not be.
5. **Two campaign cuts are inexpressible** (`workflow:postlink`,
   `receipt:postlink`), and FNBI staging and the wave-3 checkpoint programs
   have no crash model of any kind.
6. **The named assumptions are strawmen.** `fn-assume-durability-image` and
   `fn-assume-write-isolation-observe` in `books/assumptions.lisp` constrain
   set-membership functions over abstract "records" and "units" that no
   theorem instantiates; the book's own header says so ("it does not yet
   discharge or apply them").
7. **The frontier and config files are validated in Python.**
   `_frontier_with_checksum` and `config_with_checksum` in `tools/run_store.py`
   compute an integrity value ACL2 never sees, which the assurance rules
   forbid ("integrity trailers" are ACL2-owned). A byte model cannot state
   what the frontier file means until ACL2 decodes it.
8. **"Every process-death cut is a model crash point" is checked by hand.**
   The cut table names the kernel phase per cut by prose; nothing checks
   that every syscall boundary of a write path is a cut, or that the cut's
   phase is the one the program is in.

v2 makes the platform facts a model with a small, literature-backed set of
freedoms; transcribes the host's syscall sequences as programs over it;
proves that every crash image of every cut of those programs scans to an
image the *present* kernel predicate admits; and moves the trust boundary to
one constrained function whose constraint is "the platform's crash is one the
model admits".

## 1. The byte-level storage model

Proposed book: `books/byte-store.lisp`, prefix `fn-bs-`. It includes
`books/frame.lisp` (for the trailer theorems) and `books/store-files.lisp`
(for the relation in §3). Everything below is written in the tree's style:
total functions, `:guard t :verify-guards nil` where guards are not the
point, `mv` for multiple values, recognizers before transitions.

### 1.1 What the model is, in one paragraph

A store is a table of inodes (octet sequences), a table of directories (maps
from names to inode ids or directory ids), and an ordered list of *pending*
operations that the process has issued and that no fence has drained: byte
writes to inodes and entry updates to directories. The process sees the
*view*, which is the durable tables with every pending operation applied in
issue order. `fsync(fd)` drains exactly the pending writes of that inode;
`fsync(dirfd)` drains exactly the pending entry operations of that
directory. A crash keeps the durable tables and applies an arbitrary
subsequence of the pending operations, each byte write cut into write-unit
pieces of which any subset lands, lands as zeros, or lands as garbage; then
the pending list is empty. `link` and `rename` are entry operations, atomic
per entry, durable only when their directory is fenced. Every syscall takes an
outcome chosen by the environment so that disk-full and I/O errors, with the
progress the platform may have made before reporting them, are explicit
transitions. A failed `fsync` lands an arbitrary torn subset and discards the
rest.

### 1.2 State

```lisp
(in-package "ACL2")
(include-book "frame")
(include-book "store-files")

; State layout: (:byte-store unit inodes dirs pending next-ino)
;   unit     : posp, the declared write unit in octets (512 or 4096 for the
;              development profile; the theorems hold for every posp)
;   inodes   : alist ino -> octets, the DURABLE content of every inode
;   dirs     : alist dir-id -> (alist name -> ino | dir-id), DURABLE entries
;   pending  : list of pending operations in issue order (below)
;   next-ino : natp, the next unused inode id
(defun fn-bs-unit (s) (declare (xargs :guard t)) (car (cdr s)))
(defun fn-bs-inodes (s) (declare (xargs :guard t)) (car (cdr (cdr s))))
(defun fn-bs-dirs (s) (declare (xargs :guard t)) (car (cdr (cdr (cdr s)))))
(defun fn-bs-pending (s) (declare (xargs :guard t)) (car (cdr (cdr (cdr (cdr s))))))
(defun fn-bs-next-ino (s)
  (declare (xargs :guard t)) (car (cdr (cdr (cdr (cdr (cdr s)))))))
(defun fn-bs-make (unit inodes dirs pending next-ino)
  (declare (xargs :guard t))
  (list :byte-store unit inodes dirs pending next-ino))

(defun fn-bs-inop (x) (declare (xargs :guard t)) (natp x))
(defun fn-bs-dir-idp (x) (declare (xargs :guard t)) (keywordp x))
(defun fn-bs-namep (x) (declare (xargs :guard t)) (stringp x))
(defun fn-bs-entry-valuep (x)
  (declare (xargs :guard t)) (or (fn-bs-inop x) (fn-bs-dir-idp x)))

(defun fn-bs-inode-tablep (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x)) (fn-bs-inop (car (car x)))
           (fn-cbor-octet-listp (cdr (car x)))
           (not (assoc-equal (car (car x)) (cdr x)))
           (fn-bs-inode-tablep (cdr x)))
    (null x)))

(defun fn-bs-entriesp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x)) (fn-bs-namep (car (car x)))
           (fn-bs-entry-valuep (cdr (car x)))
           (not (assoc-equal (car (car x)) (cdr x)))
           (fn-bs-entriesp (cdr x)))
    (null x)))

(defun fn-bs-dir-tablep (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x)) (fn-bs-dir-idp (car (car x)))
           (fn-bs-entriesp (cdr (car x)))
           (not (assoc-equal (car (car x)) (cdr x)))
           (fn-bs-dir-tablep (cdr x)))
    (null x)))

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

(defun fn-bs-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 6) (equal (car s) :byte-store)
       (posp (fn-bs-unit s))
       (fn-bs-inode-tablep (fn-bs-inodes s))
       (fn-bs-dir-tablep (fn-bs-dirs s))
       (fn-bs-op-listp (fn-bs-pending s))
       (natp (fn-bs-next-ino s))))
```

### 1.3 Applying operations; the view

```lisp
(defun fn-bs-zeros (n)
  (declare (xargs :guard t))
  (if (zp n) nil (cons 0 (fn-bs-zeros (1- n)))))

; Take n octets, zero-padding past the end: a write beyond the current end
; of a file reads back as zeros in the gap (POSIX lseek/write semantics).
(defun fn-bs-take (n xs)
  (declare (xargs :guard t))
  (if (zp n) nil
    (cons (if (consp xs) (car xs) 0) (fn-bs-take (1- n) (cdr xs)))))

(defun fn-bs-splice (old offset octets)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
  (if (consp ops)
      (mv-let (inodes dirs) (fn-bs-apply-op inodes dirs (car ops))
        (fn-bs-apply-ops inodes dirs (cdr ops)))
    (mv inodes dirs)))

; What the running process observes: every pending operation applied.
(defun fn-bs-view (s)
  (declare (xargs :guard t))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s) (fn-bs-pending s))
    (fn-bs-make (fn-bs-unit s) inodes dirs nil (fn-bs-next-ino s))))

(defun fn-bs-lookup (s dir name)
  (declare (xargs :guard t))
  (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bs-dirs (fn-bs-view s)))))))
(defun fn-bs-content (s ino)
  (declare (xargs :guard t))
  (cdr (assoc-equal ino (fn-bs-inodes (fn-bs-view s)))))
(defun fn-bs-names (s dir)
  (declare (xargs :guard t))
  (strip-cars (cdr (assoc-equal dir (fn-bs-dirs (fn-bs-view s))))))

; The durable half, read without the view.  Recovery after a crash reads
; the view of a state whose pending list is empty, so the two agree there.
(defun fn-bs-durable-content (s ino)
  (declare (xargs :guard t)) (cdr (assoc-equal ino (fn-bs-inodes s))))
(defun fn-bs-durable-entry (s dir name)
  (declare (xargs :guard t))
  (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bs-dirs s))))))
```

### 1.4 Fences

```lisp
(defun fn-bs-ops-for-ino (ops ino)
  (declare (xargs :guard t))
  (cond ((atom ops) nil)
        ((and (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino))
         (cons (car ops) (fn-bs-ops-for-ino (cdr ops) ino)))
        (t (fn-bs-ops-for-ino (cdr ops) ino))))

(defun fn-bs-ops-not-for-ino (ops ino)
  (declare (xargs :guard t))
  (cond ((atom ops) nil)
        ((and (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino))
         (fn-bs-ops-not-for-ino (cdr ops) ino))
        (t (cons (car ops) (fn-bs-ops-not-for-ino (cdr ops) ino)))))

(defun fn-bs-ops-for-dir (ops dir)
  (declare (xargs :guard t))
  (cond ((atom ops) nil)
        ((and (member-equal (car (car ops)) '(:set-entry :del-entry))
              (equal (nth 1 (car ops)) dir))
         (cons (car ops) (fn-bs-ops-for-dir (cdr ops) dir)))
        (t (fn-bs-ops-for-dir (cdr ops) dir))))

(defun fn-bs-ops-not-for-dir (ops dir)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                     (fn-bs-ops-for-ino (fn-bs-pending s) ino))
    (fn-bs-make (fn-bs-unit s) inodes dirs
                (fn-bs-ops-not-for-ino (fn-bs-pending s) ino)
                (fn-bs-next-ino s))))

; fsync(dirfd) drains exactly the pending entry operations of that directory.
; It does not drain the data of the files those entries name.
(defun fn-bs-fence-dir (s dir)
  (declare (xargs :guard t))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                     (fn-bs-ops-for-dir (fn-bs-pending s) dir))
    (fn-bs-make (fn-bs-unit s) inodes dirs
                (fn-bs-ops-not-for-dir (fn-bs-pending s) dir)
                (fn-bs-next-ino s))))

(defun fn-bs-fencedp (s ino)
  (declare (xargs :guard t)) (null (fn-bs-ops-for-ino (fn-bs-pending s) ino)))
(defun fn-bs-dir-quietp (s dir)
  (declare (xargs :guard t)) (null (fn-bs-ops-for-dir (fn-bs-pending s) dir)))
```

### 1.5 Crash

A crash choice is parallel to the pending list. For a `:write` the choice is
a list of one selector per write unit the write touches; for an entry
operation it is `:apply` or `:drop`. Missing choices are conservative loss.

```lisp
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
  (declare (xargs :guard t))
  (if (or (zp len) (zp unit)) 0
    (1+ (- (floor (+ (nfix offset) len -1) unit) (floor (nfix offset) unit)))))

; The write operations that landed for pieces i.. of OP under SELECTORS.
(defun fn-bs-tear-write (op selectors i unit)
  (declare (xargs :guard t :measure (nfix (- (fn-bs-unit-count (nth 2 op) (len (nth 3 op)) unit) (nfix i)))))
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
  (declare (xargs :guard t))
  (if (equal (car op) :write)
      (and (fn-bs-selector-listp choice)
           (<= (len choice) (fn-bs-unit-count (nth 2 op) (len (nth 3 op)) unit)))
    (or (equal choice :apply) (equal choice :drop))))

(defun fn-bs-crash-choicesp (choices ops unit)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
  (if (consp ops)
      (let ((op (car ops)) (choice (if (consp choices) (car choices) nil)))
        (append (if (equal (car op) :write)
                    (fn-bs-tear-write op choice 0 unit)
                  (if (equal choice :apply) (list op) nil))
                (fn-bs-crash-select (cdr ops) (cdr choices) unit)))
    nil))

(defun fn-bs-crash (s choices)
  (declare (xargs :guard t))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                     (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s)))
    (fn-bs-make (fn-bs-unit s) inodes dirs nil (fn-bs-next-ino s))))

; The admissible-image predicate.  fn-bs-crash is its constructor; every
; theorem in section 3 quantifies over this predicate, never over a choice.
(defun-sk fn-bs-crash-imagep (s image)
  (exists (choices)
    (and (fn-bs-crash-choicesp choices (fn-bs-pending s) (fn-bs-unit s))
         (equal image (fn-bs-crash s choices)))))
```

An executable decision procedure `fn-bs-image-admissiblep (s image)` is also
required (the campaign calls it, §5). Under `fn-bs-pending-disjointp`, which
says no two pending writes of one inode overlap and no name carries more than
two pending entry operations, admissibility is decidable per inode and per
name: a unit outside every pending write is unchanged, a unit inside one is
unconstrained, and a name's value is the durable one or the target of one of
its pending operations. The theorem `fn-bs-image-admissiblep-iff-crash-imagep`
under that hypothesis is a P1 obligation; every program in §2 satisfies the
hypothesis at every cut (`fn-bs-program-pending-disjoint`).

### 1.6 Syscalls with outcomes

Every syscall returns `(mv result state)`. `outcome` is chosen by the
environment: `:ok`, or a failure with the progress the platform may have made
before reporting it. The result is `:ok` or an errno keyword; errors are
`:eio`, `:enospc`, `:eexist`, `:enoent`.

```lisp
; open(O_CREAT|O_EXCL).  The inode exists durably and empty from creation;
; only its NAME is pending.  This is the "zero-length file after crash"
; outcome made first-class.  An error creates nothing.
(defun fn-bs-create (s dir name outcome)
  (declare (xargs :guard t))
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
; ENOSPC, or zero progress).  Accepted octets are pending, never durable.
(defun fn-bs-write (s ino offset octets outcome)
  (declare (xargs :guard t))
  (let* ((n (if (equal outcome :ok) (len octets) (nfix (cdr outcome))))
         (accepted (fn-bs-take n octets))
         (s1 (if (zp n) s
               (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                           (append (fn-bs-pending s)
                                   (list (list :write ino offset accepted)))
                           (fn-bs-next-ino s)))))
    (mv (if (equal outcome :ok) :ok (car outcome)) s1)))

; fsync(fd) / F_FULLFSYNC.  :ok drains the inode's pending writes.
; (errno . choices) reports failure after landing the torn selection CHOICES
; of those writes and DISCARDING the rest: the platform has marked the dirty
; pages clean (Linux ext4/xfs, Rebello et al. 2020; PostgreSQL fsyncgate,
; 2018), so nothing remains for a retry to write and a later fsync that
; returns :ok fences nothing.  ENOSPC surfaces here under delayed
; allocation even though every write returned :ok.
(defun fn-bs-fsync-file (s ino outcome)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
  (cond ((not (fn-bs-lookup s dir name)) (mv :enoent s))
        ((or (equal outcome :ok)
             (and (consp outcome) (equal (cdr outcome) :issued)))
         (mv (if (equal outcome :ok) :ok (car outcome))
             (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                         (append (fn-bs-pending s) (list (list :del-entry dir name)))
                         (fn-bs-next-ino s))))
        (t (mv (car outcome) s))))

; mkdir(2): the directory exists durably and empty; its name in the parent is
; pending until the parent is fenced.
(defun fn-bs-mkdir (s parent name id outcome)
  (declare (xargs :guard t))
  (cond ((fn-bs-lookup s parent name) (mv :eexist s))
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
(defun fn-bs-read (s ino) (declare (xargs :guard t)) (fn-bs-content s ino))
```

What the model leaves unspecified, on purpose: the view of an inode after a
*failed* `fsync` (Linux keeps the never-written data in cache and reports it
to `read`, so the view and the durable content diverge). v2 does not add a
cache field; instead §2.4 requires, and checks, that no program reads a file
whose fence failed. That is the fsyncgate discipline as a program property
rather than a modeling burden.

### 1.7 Contracts that are theorems about the model

These are the precise forms of the old prose assumptions. Each is provable
from the definitions above; none needs a platform fact. What the platform must
supply is §3.6.

```lisp
; A-DURABILITY, positive half: a fenced inode's durable content survives every
; admissible crash unchanged.  (Torn selectors act only on PENDING writes.)
(defthm fn-bs-crash-keeps-fenced-content
  (implies (and (fn-bs-statep s) (fn-bs-fencedp s ino)
                (fn-bs-crash-imagep s image))
           (equal (fn-bs-durable-content image ino)
                  (fn-bs-durable-content s ino))))

; A-DURABILITY, negative half: a crash invents nothing.  Every unit of every
; inode of the image is the durable unit or a piece of a pending write to it.
(defthm fn-bs-crash-invents-nothing
  (implies (and (fn-bs-statep s) (fn-bs-crash-imagep s image)
                (not (fn-bs-ops-for-ino (fn-bs-pending s) ino)))
           (equal (fn-bs-durable-content image ino)
                  (fn-bs-durable-content s ino))))

; A-WRITE-ISOLATION, data half: a torn write to one inode changes no other
; inode.  (This is where the model commits to block-granular allocation:
; see A-ISOLATION in section 3.6 for the platform side.)
(defthm fn-bs-tear-touches-only-its-inode
  (implies (and (fn-bs-statep s) (fn-bs-crash-imagep s image)
                (not (equal ino other))
                (not (fn-bs-ops-for-ino (fn-bs-pending s) other)))
           (equal (fn-bs-durable-content image other)
                  (fn-bs-durable-content s other))))

; A-WRITE-ISOLATION, namespace half: an entry after a crash is its durable
; value or the target of one of its pending operations; never a third thing
; and never a partial name.
(defun fn-bs-entry-outcomes (ops old)
  (declare (xargs :guard t))
  (if (consp ops)
      (append (fn-bs-entry-outcomes (cdr ops) old)
              (fn-bs-entry-outcomes (cdr ops)
                                    (if (equal (car (car ops)) :set-entry)
                                        (nth 3 (car ops))
                                      nil)))
    (list old)))

(defun fn-bs-ops-for-name (ops dir name)
  (declare (xargs :guard t))
  (cond ((atom ops) nil)
        ((and (member-equal (car (car ops)) '(:set-entry :del-entry))
              (equal (nth 1 (car ops)) dir) (equal (nth 2 (car ops)) name))
         (cons (car ops) (fn-bs-ops-for-name (cdr ops) dir name)))
        (t (fn-bs-ops-for-name (cdr ops) dir name))))

(defthm fn-bs-crash-entry-is-old-or-a-pending-target
  (implies (and (fn-bs-statep s) (fn-bs-crash-imagep s image))
           (member-equal (fn-bs-durable-entry image dir name)
                         (fn-bs-entry-outcomes
                          (fn-bs-ops-for-name (fn-bs-pending s) dir name)
                          (fn-bs-durable-entry s dir name)))))

; Fences drain exactly their named set.
(defthm fn-bs-fence-file-drains-exactly-its-inode
  (implies (fn-bs-statep s)
           (and (equal (fn-bs-ops-for-ino (fn-bs-pending (fn-bs-fence-file s ino)) ino) nil)
                (equal (fn-bs-ops-not-for-ino (fn-bs-pending (fn-bs-fence-file s ino)) ino)
                       (fn-bs-ops-not-for-ino (fn-bs-pending s) ino))
                (equal (fn-bs-dirs (fn-bs-fence-file s ino)) (fn-bs-dirs s)))))

(defthm fn-bs-fence-dir-drains-exactly-its-directory
  (implies (fn-bs-statep s)
           (and (equal (fn-bs-ops-for-dir (fn-bs-pending (fn-bs-fence-dir s dir)) dir) nil)
                (equal (fn-bs-ops-not-for-dir (fn-bs-pending (fn-bs-fence-dir s dir)) dir)
                       (fn-bs-ops-not-for-dir (fn-bs-pending s) dir))
                (equal (fn-bs-inodes (fn-bs-fence-dir s dir)) (fn-bs-inodes s)))))

; The view is a fixed point of fencing and crash-with-everything-applied:
; what the process saw is one admissible image (the "nothing lost" image).
(defthm fn-bs-view-is-an-admissible-image
  (implies (fn-bs-statep s)
           (fn-bs-crash-imagep s (fn-bs-view s))))

; fsyncgate: after a failed fence, a later successful fence of the same inode
; changes nothing durable.  Retrying fsync establishes no durability.
(defthm fn-bs-refence-after-error-fences-nothing
  (implies (and (fn-bs-statep s) (consp outcome))
           (mv-let (r1 s1) (fn-bs-fsync-file s ino outcome)
             (declare (ignore r1))
             (mv-let (r2 s2) (fn-bs-fsync-file s1 ino :ok)
               (declare (ignore r2))
               (equal (fn-bs-inodes s2) (fn-bs-inodes s1))))))
```

### 1.8 Literature grounding

| Model feature | Finding it encodes |
| --- | --- |
| `fsync(fd)` drains only that inode's writes; a directory entry needs `fsync(dirfd)` | Pillai et al., "All File Systems Are Not Created Equal: On the Complexity of Crafting Crash-Consistent Applications", OSDI 2014 (ALICE, 60 vulnerabilities in 11 applications; "directory operations are not persisted by fsync of the file"); Bornholt et al., "Specifying and Checking File System Crash-Consistency Models", ASPLOS 2016 (Ferrite litmus tests, including the atomic-rename-with-fsync pattern) |
| `rename` destination entry atomic per entry, durable only after the directory fence; source removal separate | Pillai et al. 2014 §3.2 and Table 1 (rename atomicity and ordering are per-filesystem; durability of a rename requires the directory `fsync`); Chidambaram et al., "Optimistic Crash Consistency", SOSP 2013 (ordering versus durability of directory operations) |
| Pending writes land as any subset of unit pieces; `:zero` units | Pillai et al. 2014 (appends not atomic beyond the sector; "size updated, content not"); Ts'o, ext4 delayed allocation and zero-length files after crash, 2009 (Ubuntu #317781, LWN "ext4 and data loss"); Mohan et al., "Finding Crash-Consistency Bugs with Bounded Black-Box Crash Testing", OSDI 2018 (CrashMonkey/ACE: reordering and loss of individual blocks) |
| `(:garble . octets)` units | Zheng et al., "Understanding the Robustness of SSDs under Power Fault", FAST 2013 (shorn writes, bit corruption, metadata corruption); Zheng et al., "Torturing Databases for Fun and Profit", OSDI 2014 |
| Failed `fsync` lands a torn subset and discards the rest; retry fences nothing | PostgreSQL "fsyncgate" (Craig Ringer, pgsql-hackers, 2018; LWN "PostgreSQL's fsync() surprise", 2018; PostgreSQL 11/12 now `PANIC` on fsync failure); Rebello et al., "Can Applications Recover from fsync Failures?", USENIX ATC 2020 (ext4 and XFS mark pages clean after EIO; reads return the unwritten data) |
| ENOSPC surfacing at `fsync` although every `write` succeeded | ext4/xfs delayed allocation; Rebello et al. 2020 |
| `durable_barrier` is `F_FULLFSYNC` on darwin | `fsync(2)` on macOS: "fsync does not flush the drive's cache; use F_FULLFSYNC" (review D12); SQLite `PRAGMA fullfsync`; the 2022 Apple-silicon measurements showing `fsync` alone leaves data in the drive cache |
| Data of one inode never shares a write unit with another inode's data (A-ISOLATION, §3.6) | SQLite "Powersafe Overwrite" (`SQLITE_IOCAP_POWERSAFE_OVERWRITE`, 2012): the precise contract "a write of a byte range does not damage bytes outside the range even on power loss", which is what our per-inode isolation assumes at unit granularity; failures.md's sector-sharing warning is the negation of this |
| Per-entry atomic namespace, no dangling entries (A-NAMESPACE, §3.6) | Journaled/COW metadata (ext4 `data=ordered`, XFS, APFS); ext2 and `data=writeback` are excluded by name |
| Directory contents are "old or a pending target" per name; nothing else | Yang, Sar, Engler, "EXPLODE", OSDI 2006 and "Using Model Checking to Find Serious File System Errors", OSDI 2004 (FiSC): crash images as subsets of pending block writes |

The model does **not** encode `auto_da_alloc` (ext4's rename-over-existing
heuristic that implicitly flushes) or any other filesystem's safety
heuristic, because a program that is correct only under a heuristic is not
correct (Pillai et al. 2014 §5 "masking"). It also does not encode
`fsync(fd)` incidentally committing the parent directory entry, which ext4 in
practice does for new files: a program that needs that would be wrong on
other filesystems.

## 2. The host's programs over the model

Proposed book: `books/byte-store-programs.lisp`. A program is a constant list
of steps; a step is one syscall on a path or one kernel observation. Paths are
`(dir . name)`; the step language resolves them through the view.

### 2.1 Step language and runner

```lisp
; Directory ids of the store layout (tools/run_store.py: root, transactions,
; staging; the parent of root is fenced by initialize and recover).
; Journals use :records / :staging / :inbound under their own :root.
(defconst *fn-bs-config-name* "config.json")
(defconst *fn-bs-frontier-name* "allocation-frontier.json")

; Steps:
;   (:create dir name)                    os.open(O_WRONLY|O_CREAT|O_EXCL)
;   (:write-all dir name octets)          write_all: one or more write(2)
;   (:fsync-file dir name)                fsync_file / durable_barrier(fd)
;   (:fsync-dir dir)                      fsync_dir
;   (:link sdir sname ddir dname)         os.link
;   (:rename sdir sname ddir dname)       os.replace
;   (:unlink dir name)                    os.unlink (best-effort cleanup)
;   (:mkdir parent name id)               os.mkdir
;   (:observe event)                      one fn-sf transition (kernel only)
;   (:cut name)                           a campaign fault point; no effect
(defun fn-bs-stepp (x) ...)               ; syntax recognizer, as fn-sf-eventp

; One step.  OUTCOME is that step's environment choice.  A kernel observation
; dispatches to the fn-sf transition named by the event, exactly as
; fn-sf-dispatch does; the syscall result is what the host would report.
(defun fn-bs-step (bs ks step outcome groups capacity)
  (declare (xargs :guard t))
  (case (car step)
    (:create (mv-let (r bs1) (fn-bs-create bs (nth 1 step) (nth 2 step) outcome)
               (mv r bs1 ks)))
    (:write-all (let ((ino (fn-bs-lookup bs (nth 1 step) (nth 2 step))))
                  (mv-let (r bs1) (fn-bs-write bs ino 0 (nth 3 step) outcome)
                    (mv r bs1 ks))))
    (:fsync-file (let ((ino (fn-bs-lookup bs (nth 1 step) (nth 2 step))))
                   (mv-let (r bs1) (fn-bs-fsync-file bs ino outcome)
                     (mv r bs1 ks))))
    (:fsync-dir (mv-let (r bs1) (fn-bs-fsync-dir bs (nth 1 step) outcome)
                  (mv r bs1 ks)))
    (:link (mv-let (r bs1) (fn-bs-link bs (nth 1 step) (nth 2 step)
                                       (nth 3 step) (nth 4 step) outcome)
             (mv r bs1 ks)))
    (:rename (mv-let (r bs1) (fn-bs-rename bs (nth 1 step) (nth 2 step)
                                           (nth 3 step) (nth 4 step) outcome)
               (mv r bs1 ks)))
    (:unlink (mv-let (r bs1) (fn-bs-unlink bs (nth 1 step) (nth 2 step) outcome)
               (mv r bs1 ks)))
    (:mkdir (mv-let (r bs1) (fn-bs-mkdir bs (nth 1 step) (nth 2 step)
                                         (nth 3 step) outcome)
              (mv r bs1 ks)))
    (:observe (mv :ok bs (fn-sf-dispatch ks (nth 1 step) groups capacity)))
    (otherwise (mv :ok bs ks))))

; Run to the first error, as the host does (every OSError raises).  Returns
; the list of (bs . ks) pairs after each step, most recent last; the last
; pair is where the process died or returned.  A crash at cut k is a crash
; of the k-th pair.
(defun fn-bs-run (bs ks steps outcomes groups capacity)
  (declare (xargs :guard t))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-bs-step bs ks (car steps) (if (consp outcomes) (car outcomes) :ok)
                    groups capacity)
        (cons (cons bs1 ks1)
              (if (equal r :ok)
                  (fn-bs-run bs1 ks1 (cdr steps) (cdr outcomes) groups capacity)
                nil)))
    nil))
```

The `:observe` events reuse `fn-sf-dispatch` from `store-files-traces.lisp`
unchanged. When a syscall errors, the host issues the observation the kernel
expects for that error (`:known-fail`, `:error`); the transcriptions below
carry both branches by listing the observation the host makes on `:ok` and,
in a comment, the one it makes on error, so `fn-bs-run`'s "stop at first
error" is followed by the error observation as a separate one-step program
(`*fn-bs-frontier-on-error*` etc.). This mirrors the `except OSError` arms of
`advance_frontier` and `publish`.

### 2.2 The transcriptions

Line numbers refer to `tools/run_store.py`, `tools/workflow_journal.py`,
`tools/receipt_journal.py` at `9321344`, and to the uncommitted
`tools/checkpoint.py` of `build/lanes/w3-checkpoint` as read on 2026-09-19.

**P-FRONTIER** (`Store.advance_frontier`, run_store.py:840-912). `F1` is the
new frontier's octets; `STAGE` is `.allocation-<pid>-<hex>`.

```lisp
(defun fn-bs-frontier-program (stage octets)
  (list (list :observe '(:start-frontier))                 ; 858
        (list :create :staging stage)                      ; 861  O_EXCL
        (list :write-all :staging stage octets)            ; 863
        (list :fsync-file :staging stage)                  ; 864  durable_barrier
        ; close(fd) 866: no step
        (list :observe '(:frontier-file :ok))              ; 870
        (list :cut "frontier-staged-durable")              ; 872
        (list :rename :staging stage :root *fn-bs-frontier-name*) ; 878 os.replace
        (list :cut "frontier-replaced")                    ; 882
        (list :observe '(:frontier-replace :ok))           ; 883
        (list :cut "frontier-attempted")                   ; 888
        (list :fsync-dir :root)                            ; 891
        (list :cut "frontier-durable")                     ; 895
        (list :observe '(:frontier-directory :ok))         ; 896
        (list :cut "frontier-reserved")))                  ; 903
; On error: before 878, (:observe (:frontier-file :known-fail)) [911]; at or
; after 878, the host raises StoreIndeterminate and observes
; (:frontier-replace :error) [880] or (:frontier-directory :error) [893].
; Note: the staging directory is never fenced; the source entry of the
; rename is a pending :del-entry on :staging for ever.  Recovery ignores it.
```

**P-RECORD** (`Store.publish`, run_store.py:914-989). `NAME` is
`{:020d}.txn` of the sequence; `STAGE` is `.stage-<pid>-<hex>`; `FRAME` is
the FNST frame octets from `fn-frame-store-encode`.

```lisp
(defun fn-bs-record-program (stage name frame)
  (list (list :create :staging stage)                      ; 924
        (list :write-all :staging stage frame)             ; 926
        (list :fsync-file :staging stage)                  ; 927
        (list :observe '(:record-file :ok))                ; 931
        (list :cut "record-staged-durable")                ; 937
        (list :link :staging stage :transactions name)     ; 941 os.link
        (list :cut "record-linked")                        ; 945
        (list :observe '(:record-link :ok))                ; 946
        (list :cut "record-attempted")                     ; 953
        (list :fsync-dir :transactions)                    ; 955
        (list :cut "record-durable")                       ; 959
        (list :observe '(:record-directory :ok))           ; 960
        (list :cut "record-completing")                    ; 966
        (list :unlink :staging stage)                      ; 970 best effort
        (list :fsync-dir :staging)                         ; 971 best effort
        (list :cut "record-staging-cleaned")))             ; 974
; On error before 941: the host raises StoreError and calls the composed
; fn-sn-known-abort (:record-file :known-fail then :abort-completion).  At or
; after 941: StoreIndeterminate with (:record-link :error) [943] or
; (:record-directory :error) [957].  Errors from 970-971 are swallowed.
```

**P-FINISH** (`Store.finish`, run_store.py:991-1010): no syscall; two cuts
(`finish-consumed`, `finish-durable`) around `(:observe (:core-completion seq txid))`
followed by `(:emit-success seq txid)` inside `fn-sn-finish`. Its byte state
is unchanged; its crash images are those of the `:ready` kernel state with the
pair in the ghost history (the `core-durable` cut).

**P-RECOVER** (`Store.recover`, run_store.py:786-838). Reads first, then five
fences on already-durable objects.

```lisp
(defun fn-bs-recover-program ()
  (list ; _load_frontier 795, durable_records 796 (scandir + read of each
        ; transactions/ name), staging_orphans 797: reads of the view; no step
        (list :observe '(:recover))                        ; 798 acl2.recover
        (list :cut "recover-replayed")                     ; 809
        (list :fsync-file :root *fn-bs-config-name*)       ; 815 fsync_regular
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-file :root *fn-bs-frontier-name*)     ; 816
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-dir :transactions)                    ; 817
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-dir :root)                            ; 818
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")
        (list :fsync-dir :parent)                          ; 819
        (list :observe '(:recovery-barrier :ok))
        (list :cut "recover-barrier")))
; On any fence error: (:observe (:recovery-barrier :uncertain)) [826] and
; StoreIndeterminate.  Recovery after an in-process uncertainty (no crash)
; runs with a NON-EMPTY pending list: the link or replacement whose reply
; was lost may still be pending, and 817/818 are what drain it.  That is
; the content of "recovery re-establishes barriers before use".
```

**P-INIT** (`Store.initialize` and `_publish_initial_file`,
run_store.py:612-667): `mkdir` root, transactions, staging; for each of
config and frontier: `:create` under `staging/.init-*`, `:write-all`,
`:fsync-file`, `:link` to `root/<name>` (EEXIST reported, never replaced),
`:fsync-dir :root`, `:unlink` the stage; then `:fsync-file` config,
`:fsync-file` frontier, `:fsync-dir :transactions`, `:fsync-dir :root`,
`:fsync-dir :parent`. Same shape as P-RECORD with `:root` as the authority
directory. No cuts exist in the host for P-INIT today; §6 P2 adds them.

**P-JOURNAL** (`WorkflowJournal.publish`, workflow_journal.py:197-266;
`ReceiptJournal.publish`, receipt_journal.py `publish`). `NAME` is
`{seq:016x}.wf` or `.rj`; `STAGE` is `{seq:016x}.<pid>.tmp`; `FRAME` is the
FNWF or FNRJ frame.

```lisp
(defun fn-bs-journal-program (stage name frame)
  (list (list :create :staging stage)                      ; wf 220 / rj
        (list :write-all :staging stage frame)             ; wf 223
        (list :cut "write")                                ; wf only
        (list :fsync-file :staging stage)                  ; wf 225 / rj durable_barrier
        (list :cut "file-fsync")                           ; wf; rj: "receipt-staged-durable"
        (list :cut "prepublish")                           ; wf only
        (list :link :staging stage :records name)          ; wf 235 / rj os.link
        (list :cut "postlink")                             ; wf and rj
        (list :fsync-dir :records)                         ; wf 237 / rj fsync_dir(records)
        (list :cut "directory-fsync")                      ; wf; rj: "receipt-durable"
        (list :unlink :staging stage)                      ; finally: best effort
        (list :cut "image-applied")))                      ; wf; rj: "receipt-applied"
; On error before the link: the stage is unlinked and the error raised; no
; journal record exists.  At or after the link: JournalUncertain and
; self.fenced = True.  Identical to P-RECORD without the kernel
; observations: the journals have no fn-sf twin, which is why the campaign's
; two postlink cuts had nothing to point at.
```

**P-INBOX** (`WorkflowJournal.stage_inbound`, workflow_journal.py:326-388).
`NAME` is `sha256(bid).hexdigest() + ".bp"`; `STAGE` is `NAME + ".<pid>.tmp"`;
`FRAME` is the FNBI frame.

```lisp
(defun fn-bs-inbox-program (stage name frame)
  (list (list :create :staging stage)                      ; 362
        (list :write-all :staging stage frame)             ; 365
        (list :fsync-file :staging stage)                  ; 365
        (list :cut "inbound-staged-durable")               ; 366
        (list :link :staging stage :inbound name)          ; 372
        (list :cut "inbound-linked")                       ; 373
        (list :fsync-dir :inbound)                         ; 374
        (list :cut "inbound-durable")                      ; 375
        (list :unlink :staging stage)                      ; finally
        ; delete(bid): BPA transport side effect, outside this model
        (list :cut "inbound-deleted")))                    ; 386
; The reconciliation branch (final exists: 349-360) issues only
; (:fsync-dir :inbound) and the cut "inbound-reconciled".
```

**P-CHECKPOINT** (wave-3 `tools/checkpoint.py`, uncommitted at
`build/lanes/w3-checkpoint`; re-transcribe when it lands). Two programs.

```lisp
; publish: a new generation file.  Shape of P-RECORD into :checkpoints.
(defun fn-bs-checkpoint-publish-program (stage generation frame)
  (list (list :create :staging stage)                      ; _stage_and_link 97
        (list :write-all :staging stage frame)
        (list :fsync-file :staging stage)                  ; 100
        (list :cut "checkpoint:candidate-durable")         ; 103 durable_point
        (list :link :staging stage :checkpoints generation) ; 105 generation-N.fncp
        (list :cut "checkpoint:candidate-linked")          ; 106
        (list :fsync-dir :checkpoints)                     ; 107
        (list :cut "checkpoint:candidate-published")       ; 108
        (list :unlink :staging stage)))                    ; 111
; select: the authority marker.  Shape of P-FRONTIER into :checkpoints.
(defun fn-bs-checkpoint-select-program (stage frame)
  (list (list :create :staging stage)                      ; 157
        (list :write-all :staging stage frame)
        (list :fsync-file :staging stage)                  ; 160
        (list :cut "checkpoint:selection-durable")         ; 163
        (list :rename :staging stage :checkpoints "selection") ; 165 os.replace
        (list :cut "checkpoint:selection-replaced")        ; 172
        (list :fsync-dir :checkpoints)                     ; 173
        (list :cut "checkpoint:selection-published")))     ; 174
```

### 2.3 Cuts are syscall boundaries, mechanically

A cut in `tests/campaign/cuts.py` is a `faults.at("<name>")` site. In v2 a
cut is additionally required to be a position in one of the step lists
above, and the table check gains two rules:

- every `:cut` in a program constant is a `faults.at` in the host function
  the program transcribes, and conversely (the existing AST discovery);
- every durable syscall in that host function (`os.open(O_CREAT)`,
  `os.write`/`write_all`, `durable_barrier`/`fsync_file`/`fsync_dir`,
  `os.link`, `os.replace`, `os.unlink`, `os.mkdir`) appears, in order, as a
  step of the program constant, with a `:cut` after it.

The second rule is what turns "every process-death cut is a model crash
point" from a hand-checked table into a generated one: a syscall without a
cut after it is a boundary the campaign never kills at, and it fails the
table test. `tools/transcribe_check.py` (P2) reads the ACL2 constants and the
Python AST and compares the two sequences; the same trick `cuts.py` already
uses for fault points.

Today's host has one such boundary with no cut: the `os.close` between
`fsync_file` and the kernel observation in P-FRONTIER and P-RECORD. `close`
has no durability effect, so the program lists no step for it; the rule
therefore exempts `os.close`.

### 2.4 Program discipline, as executable checks over the constants

Each of the following is an `assert-event` over the constant programs (they
are ground, so ACL2 evaluates them), and a theorem over the runner where the
statement is general.

```lisp
; D1: every :link and :rename names a source whose last :write-all was
; followed by a :fsync-file before the link ("safe link").
(defun fn-bs-links-only-fencedp (steps) ...)
; D2: no :write-all names a path that is a durable entry of an authority
; directory (:root, :transactions, :records, :inbound, :checkpoints):
; no in-place overwrite, ever.
(defun fn-bs-never-overwrites-authorityp (steps) ...)
; D3: every :link/:rename into an authority directory is followed by
; :fsync-dir of that directory before any further :link/:rename/:observe of
; a success ("fence after uncertainty").
(defun fn-bs-fences-authority-dirsp (steps) ...)
; D4: after a :fsync-file whose outcome is an error, no later step reads or
; links that path (the fsyncgate discipline, section 1.6).
(defun fn-bs-no-use-after-fence-errorp (steps) ...)
; D5: at every cut the pending list is disjoint (section 1.5), so the
; executable admissibility check is exact.
(defthm fn-bs-program-pending-disjoint ...)
```

D1 to D3 are the properties that make §3's theorems true. Their teeth are the
campaign's failure demonstration (§5.5): swap two steps and the theorem, and
the campaign, must fail.

## 3. Keystone theorems

Proposed book: `books/byte-store-scan.lisp` (scan, relation, keystones) and
`books/byte-store-frame.lisp` (the trailer theorems). Statements only.

### 3.1 The scan: what the host's `recover` reads

```lisp
; The frontier codec.  Today: JSON with a Python-computed sha256 field
; (run_store.py:567, a twin the assurance rules forbid).  After packet P4 the
; frontier and config files are fn-frame frames of a new store kind and this
; is (fn-frame-open octets *fn-frame-max-frontier-payload*) followed by a
; CBOR uint decode.  Until P4 the function is a constrained stand-in with
; the single round-trip constraint below; the theorems in this section do
; not depend on which.
(encapsulate
  (((fn-bs-frontier-decode *) => *)
   ((fn-bs-frontier-encode *) => *))
  (local (defun fn-bs-frontier-encode (n) (list n)))
  (local (defun fn-bs-frontier-decode (octets)
           (if (and (consp octets) (natp (car octets)) (null (cdr octets)))
               (car octets) nil)))
  (defthm fn-bs-frontier-round-trip
    (implies (natp n) (equal (fn-bs-frontier-decode (fn-bs-frontier-encode n)) n)))
  (defthm fn-bs-frontier-decode-nat-or-nil
    (or (natp (fn-bs-frontier-decode octets)) (null (fn-bs-frontier-decode octets)))
    :rule-classes nil))

; One record from one inode, through the specification decoder.
; fn-frame-store-decode is the function tools/run_store.py calls through
; host/store-host.lisp:153; supplying fn-frame-digest of the protected
; prefix is what fn-frame-open does (frame.lisp:697).
(defun fn-bs-record-of (s ino)
  (declare (xargs :guard t))
  (let ((octets (fn-bs-content s ino)))
    (fn-frame-store-decode octets (fn-frame-digest (fn-frame-protected-prefix octets)))))

(defun fn-bs-txn-name (n) ...)     ; "{:020d}.txn"
(defun fn-bs-contiguous-namesp (names n) ...)  ; exactly (fn-bs-txn-name 0) .. (fn-bs-txn-name (1- n)), sorted

; Read records 0..count-1 from :transactions; :fault if any is missing, is
; not a fenced regular inode, fails the frame, or carries the wrong sequence
; (run_store.py:782 "record sequence does not match immutable filename").
(defun fn-bs-read-records (s n count)
  (declare (xargs :guard t :measure (nfix (- count n))))
  (if (or (not (natp n)) (not (natp count)) (>= n count)) nil
    (let* ((ino (fn-bs-lookup s :transactions (fn-bs-txn-name n)))
           (record (and (fn-bs-inop ino) (fn-bs-record-of s ino)))
           (rest (fn-bs-read-records s (1+ n) count)))
      (if (or (not (fn-record-p record))
              (not (equal (fn-record-sequence record) n))
              (equal rest :fault))
          :fault
        (cons record rest)))))

; The whole scan, returning what fn-sn-open-observed is given
; (host/store-node-host.lisp:27 via run_store.py:798).
(defun fn-bs-scan-store (image)
  (declare (xargs :guard t))
  (let ((c (fn-bs-lookup image :root *fn-bs-config-name*))
        (f (fn-bs-lookup image :root *fn-bs-frontier-name*))
        (names (fn-bs-names image :transactions)))
    (cond ((not (fn-bs-inop c)) (list :fault :config))
          ((not (fn-bs-config-okp (fn-bs-content image c))) (list :fault :config))
          ((not (fn-bs-inop f)) (list :fault :frontier))
          ((not (natp (fn-bs-frontier-decode (fn-bs-content image f))))
           (list :fault :frontier))
          ((not (fn-bs-contiguous-namesp names (len names))) (list :fault :namespace))
          (t (let ((records (fn-bs-read-records image 0 (len names))))
               (if (equal records :fault) (list :fault :record)
                 (list :ok (fn-bs-frontier-decode (fn-bs-content image f)) records)))))))

(defun fn-bs-scan-okp (x) (declare (xargs :guard t)) (and (consp x) (equal (car x) :ok)))
(defun fn-bs-scan-frontier (x) (declare (xargs :guard t)) (nth 1 x))
(defun fn-bs-scan-records (x) (declare (xargs :guard t)) (nth 2 x))
```

### 3.2 The relation between a byte store and a kernel state

The relation says: the durable half of the byte store is already an
admissible kernel image, and the pending half adds at most the one namespace
operation the kernel's phase allows, pointing at a fenced inode that holds
the candidate.

**Except in the recovery window, where it says the opposite way round**
(decision D14-a, 2026-09-20). Process death is not power loss: a cut at
`record-linked` or `frontier-replaced` leaves the entry operation pending in
the kernel's cache, and the NEXT process scans the *view*, so the kernel it
builds already holds the value the durable half does not
(`tools/run_store.py:1100` reads the live directory; `:1164` replays what it
read; `host/store-node-host.lisp:39` builds the `:replaying` image from it).
Until the five recovery fences run — `fsync_dir(self.transactions)` at
`run_store.py:1187` is the one that drains `:transactions` — the kernel's
record list is the durable list plus one and its frontier may be the pending
one. So the relation is phase-indexed, and the pending entry's name is
written from the DURABLE namespace, which is right in both windows;
`(fn-bs-txn-name (len (fn-sf-records ks)))`, this section's earlier form, is
off by one at the three recovery cuts and is withdrawn.

```lisp
(defun fn-bs-durable-frontier (bs)
  (declare (xargs :guard t))
  (fn-bs-frontier-decode
   (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-frontier-name*))))

(defun fn-bs-durable-records (bs)   ; as fn-bs-read-records over the durable dirs
  (declare (xargs :guard t))
  (fn-bs-read-records (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs) nil (fn-bs-next-ino bs))
                      0 (len (cdr (assoc-equal :transactions (fn-bs-dirs bs))))))

; The recovery window: the phases a process is in between replaying what it
; scanned and completing the five recovery fences (run_store.py:1179-1201).
; A store reaches them with a NON-EMPTY pending list whenever the previous
; process died between its link or rename and that operation's directory
; fence.
(defun fn-bs-replay-visiblep (ks)
  (declare (xargs :guard t))
  (member-equal (fn-sf-phase ks)
                '(:replaying :recovering :fenced-recovery)))

; The single pending entry operation each phase allows, by SHAPE: at most one
; per authority directory, at the name the durable namespace fixes, pointing
; at a fenced inode.  Which VALUE that inode must hold is the window's
; question, below, not this one's.
(defun fn-bs-pending-shape-okp (bs)
  (declare (xargs :guard t))
  (let ((root-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
        (txn-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
    (and (or (null root-ops)
             ; "exactly one" by SPINE, not by (len ops): the enumeration
             ; fn-bs-names-outcomes walks the spine, and a bound on the
             ; length leaves it closed -- which is what kept the K1
             ; namespace clause from proving.
             (and (consp root-ops) (not (consp (cdr root-ops)))
                  (equal (car (car root-ops)) :set-entry)
                  (equal (nth 2 (car root-ops)) *fn-bs-frontier-name*)
                  (fn-bs-inop (nth 3 (car root-ops)))
                  (fn-bs-fencedp bs (nth 3 (car root-ops)))))
         (or (null txn-ops)
             (and (consp txn-ops) (not (consp (cdr txn-ops)))
                  (equal (car (car txn-ops)) :set-entry)
                  ; The DURABLE namespace names it.  In the publish window
                  ; this is (len (fn-sf-records ks)) as well; in the recovery
                  ; window it is that number minus one, and only this form is
                  ; right in both (D14-a).
                  (equal (nth 2 (car txn-ops))
                         (fn-bs-txn-name
                          (len (fn-bs-durable-names bs :transactions))))
                  (fn-bs-inop (nth 3 (car txn-ops)))
                  (fn-bs-fencedp bs (nth 3 (car txn-ops))))))))

; The publish window.  The kernel has not seen the directory barrier, so its
; record list is still the DURABLE list and the pending entry names the
; candidate.  The equality on the record list -- not on its length -- is what
; excludes the image that holds the candidate twice: it forces the durable
; namespace to be the pre-candidate one whenever a link is pending.
(defun fn-bs-pending-matches-phase (bs ks)
  (declare (xargs :guard t))
  (let ((root-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
        (txn-ops (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
    (and (fn-bs-pending-shape-okp bs)
         (if root-ops
             (and (fn-sf-frontier-new-visiblep ks)
                  (equal (fn-bs-frontier-decode
                          (fn-bs-durable-content bs (nth 3 (car root-ops))))
                         (fn-sf-frontier-candidate ks)))
           t)
         (if txn-ops
             (and (fn-sf-record-present-visiblep ks)
                  (equal (fn-bs-durable-records bs) (fn-sf-records ks))
                  (equal (fn-bs-record-of (fn-bs-durable bs) (nth 3 (car txn-ops)))
                         (fn-sf-record-candidate ks)))
           t))))

; The recovery window.  The kernel is exactly what this process's scan of the
; VIEW said, and it carries no success: fn-sn-initial starts with none and
; Store.recover runs once per process, at open (run_store.py:1674,
; run_owner.py:660, fn9p.py:428, run_reader.py:313, run_bp_ingress.py:132).
; That last conjunct is why a crash here cannot lose an acknowledged record
; even though fn-sf-crash-imagep does not admit its image (K2r).
(defun fn-bs-replay-matches-scan (bs ks)
  (declare (xargs :guard t))
  (let ((scan (fn-bs-scan-store bs)))
    (and (fn-bs-pending-shape-okp bs)
         (fn-bs-scan-okp scan)
         (equal (fn-sf-frontier ks) (fn-bs-scan-frontier scan))
         (equal (fn-sf-records ks) (fn-bs-scan-records scan))
         (equal (fn-sf-successes ks) nil))))

; Every inode an authority entry names, durable or pending, is fenced.
(defun fn-bs-authority-inodes (bs) ...)   ; config, frontier, every :transactions entry, every pending :set-entry target on :root/:transactions
(defun fn-bs-authority-fencedp (bs)
  (declare (xargs :guard t))
  (fn-bs-all-fencedp bs (fn-bs-authority-inodes bs)))

(defun fn-bs-store-relation (bs ks)
  (declare (xargs :guard t))
  (and (fn-bs-statep bs) (fn-sf-statep ks)
       (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-config-name*))
       (fn-bs-config-okp (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-config-name*)))
       (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-frontier-name*))
       (fn-bs-contiguous-namesp (fn-bs-durable-names bs :transactions)
                                (len (fn-bs-durable-names bs :transactions)))
       (not (equal (fn-bs-durable-records bs) :fault))
       (if (fn-bs-replay-visiblep ks)
           (fn-bs-replay-matches-scan bs ks)
         (and (fn-sf-crash-imagep ks (fn-bs-durable-frontier bs)
                                  (fn-bs-durable-records bs))
              (fn-bs-pending-matches-phase bs ks)))
       (fn-bs-authority-fencedp bs)))
```

The relation is established by `fn-sn-open-observed` at process start and
preserved by every step of every program in §2 (`K0` below). It is NOT
established with an empty pending list: a process that opens after a
process-death cut at `record-linked` or `frontier-replaced` inherits the
previous process's un-fenced entry operation, and the recovery arm is exactly
that state. The durable-namespace contiguity clause is what makes the scan's
namespace test decidable from the byte store alone.

### 3.3 The store keystones

```lisp
; K0. Every program step preserves the relation, for every outcome, with the
; kernel observation the host makes for that outcome.
(defthm fn-bs-program-step-preserves-relation
  (implies (and (fn-bs-store-relation bs ks)
                (member-equal steps (list (fn-bs-frontier-program stage octets)
                                          (fn-bs-record-program stage name frame)
                                          (fn-bs-recover-program)))
                (member-equal (cons bs1 ks1) (fn-bs-run bs ks steps outcomes groups capacity)))
           (fn-bs-store-relation bs1 ks1)))

; K1. The scan never faults on a crash image of a related state.  No torn
; unit is ever under an authority name, because links and renames are
; issued only after the inode's fence (D1) and the authority inodes are
; never overwritten (D2).  NO trailer assumption is needed here.
(defthm fn-bs-store-crash-image-scans
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image))
           (fn-bs-scan-okp (fn-bs-scan-store image))))

; K2. Old-or-new and absent-or-present as a THEOREM: every crash image of a
; related state scans to an image the present kernel predicate admits.
; The recovery-window hypothesis is NOT a convenience (D14-a): in
; :replaying/:recovering/:fenced-recovery the kernel's record list is this
; process's SCAN of the view, the durable half may be one authority entry
; behind it, and fn-sf-crash-imagep has no freedom for "replayed, not yet
; re-fenced".  That window is K2r.
(defthm fn-bs-store-crash-image-is-kernel-admissible
  (implies (and (fn-bs-store-relation bs ks)
                (not (fn-bs-replay-visiblep ks))
                (fn-bs-crash-imagep bs image))
           (fn-sf-crash-imagep ks
                               (fn-bs-scan-frontier (fn-bs-scan-store image))
                               (fn-bs-scan-records (fn-bs-scan-store image)))))

; K2r. The recovery window, where K2's conclusion is FALSE and does not need
; to be true.  A crash between the replay and the transaction fence loses the
; record the replay read, and the kernel of that process admits only the
; longer list -- but that process has acknowledged nothing, so no acknowledged
; record is at risk, and the next open reads whichever list survived, which
; K1 says scans.  What must be proved is the carried emptiness of the success
; history, not an admissibility the kernel cannot express.
(defthm fn-bs-replay-window-carries-no-success
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-replay-visiblep ks))
           (equal (fn-sf-successes ks) nil)))
; The alternative -- widening fn-sf-crash-imagep with a recovery freedom -- is
; a change to the premise books/store-observed.lisp and the store-node closure
; take from the kernel, and is recorded as an open proposal, not taken.

; K3. The present constructor as a corollary: fn-sf-crash with the choices
; read off the scanned image reproduces it exactly
; (fn-sf-crash-realizes-every-admissible-image does the work).
(defthm fn-bs-store-recovery-is-a-kernel-crash
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image))
           (let* ((scan (fn-bs-scan-store image))
                  (crashed (fn-sf-crash ks
                                        (fn-sf-image-frontier-choice ks (fn-bs-scan-frontier scan))
                                        (fn-sf-image-record-choice ks (fn-bs-scan-records scan)))))
             (and (equal (fn-sf-frontier crashed) (fn-bs-scan-frontier scan))
                  (equal (fn-sf-records crashed) (fn-bs-scan-records scan))
                  (equal (fn-sf-phase crashed) :replaying)))))

; K4. Acknowledged retention across a BYTE crash: the D5 keystone
; fn-sn-acknowledged-record-survives-observed-reopen with its premise
; discharged by K2.  This is the theorem the registry should cite for
; PRF-007 once P3 lands; the present one becomes its lemma.
(defthm fn-bs-acknowledged-record-survives-byte-crash
  (implies (and (fn-snt-relation s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image)
                (member-equal pair (fn-sf-successes (fn-sn-files s))))
           (let* ((scan (fn-bs-scan-store image))
                  (opened (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                               (fn-bs-scan-frontier scan)
                                               (fn-bs-scan-records scan))))
             (and (fn-sn-open-okp opened)
                  (fn-sf-record-has-pairp
                   pair (fn-sf-records (fn-sn-files (fn-sn-open-state opened))))))))

; K5. Stable-prefix retention at the byte level: every durable authority
; entry of the pre-crash state is a durable authority entry of the image
; with identical content, and the scanned record list extends the durable
; record list by at most the candidate.
(defthm fn-bs-stable-prefix-retained-by-byte-crash
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image))
           (and (fn-sf-prefixp (fn-bs-durable-records bs)
                               (fn-bs-scan-records (fn-bs-scan-store image)))
                (<= (len (fn-bs-scan-records (fn-bs-scan-store image)))
                    (1+ (len (fn-bs-durable-records bs)))))))

; K6. No partial transaction is visible: a scanned record is byte-identical
; to a frame the program wrote whole and fenced.  With K1 this is the exact
; form of "the trailer is never needed for crash recovery of these programs";
; the trailer's job is section 3.5.
(defthm fn-bs-scanned-record-is-an-exact-write
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image)
                (member-equal record (fn-bs-scan-records (fn-bs-scan-store image))))
           (or (member-equal record (fn-sf-records ks))
               (equal record (fn-sf-record-candidate ks)))))

; K7. Fence after uncertainty: after an error outcome of a :link, :rename or
; :fsync-dir step, the kernel is fenced and the byte store's pending list
; may be non-empty; P-RECOVER's :fsync-dir steps 817/818 leave it empty on
; :root and :transactions, and the kernel :ready only after all five.
(defthm fn-bs-uncertain-link-leaves-pending-until-recovery-fence
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-data-durable)
                (consp outcome) (equal (cdr outcome) :issued))
           (mv-let (r bs1) (fn-bs-link bs :staging stage :transactions name outcome)
             (declare (ignore r))
             (and (fn-sf-fencedp (fn-sf-record-link-result ks :error))
                  (not (fn-bs-dir-quietp bs1 :transactions))
                  (fn-bs-dir-quietp (fn-bs-fence-dir bs1 :transactions) :transactions)))))

; K8. The completed directory fence removes the choice, at the byte level:
; after (:fsync-dir :transactions) returns :ok, every crash image has the
; candidate under its final name.  The v1 theorem
; fn-sf-completed-record-barrier-removes-absent-choice is this one's kernel
; shadow.
(defthm fn-bs-completed-record-fence-removes-absent-choice
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-attempted)
                (fn-bs-crash-imagep (fn-bs-fence-dir bs :transactions) image))
           (equal (fn-bs-scan-records (fn-bs-scan-store image))
                  (append (fn-sf-records ks) (list (fn-sf-record-candidate ks))))))
```

The v1 "old-or-new" theorems and the constructor now sit *under* K2 and K3
as lemmas about the kernel, and the platform fact is no longer "the
namespace is old-or-new" but "the platform's crash image is one
`fn-bs-crash-imagep` admits" (§3.6), a statement about subsets of pending
byte and entry operations that ALICE, Ferrite and CrashMonkey test for on
real filesystems.

### 3.4 The journals: closing the two inexpressible cuts

The journals have no kernel; their logical image is a record list. The
predicate below is `fn-sf-crash-imagep` with the kernel state replaced by
the two values a journal program carries: the published prefix and the
candidate, plus the one bit "the link may have been issued".

```lisp
(defun fn-bs-journal-imagep (published candidate link-issued records)
  (declare (xargs :guard t))
  (or (equal records published)
      (and link-issued (equal records (append published (list candidate))))))

(defun fn-bs-scan-journal (image suffix) ...)  ; names {seq:016x}.<suffix> contiguous from 0, each a frame of the journal's magic; :fault otherwise

; K9 (FNWF and FNRJ).  At every cut of P-JOURNAL, every crash image scans
; to the published list, or, from the cut after the :link step on, that
; list plus the exact candidate.  The two campaign rows
; workflow:postlink and receipt:postlink point at this theorem with
; link-issued = t; every earlier cut has link-issued = nil.
(defthm fn-bs-journal-crash-image-is-published-or-plus-candidate
  (implies (and (fn-bs-journal-relation bs published)          ; durable records = published, fenced, quiet
                (member-equal (cons bs1 ks1)
                              (fn-bs-run bs nil (fn-bs-journal-program stage name frame) outcomes nil nil))
                (fn-bs-crash-imagep bs1 image)
                (fn-bs-scan-okp (fn-bs-scan-journal image suffix)))
           (fn-bs-journal-imagep published
                                 (fn-frame-journal-decode frame)
                                 (fn-bs-link-issuedp bs1 :records name)
                                 (fn-bs-scan-records (fn-bs-scan-journal image suffix)))))

; K9b.  The scan never faults on those images (the journal form of K1).
(defthm fn-bs-journal-crash-image-scans ...)

; K9c.  Both outcomes replay.  The workflow host preflights the extended
; history before staging (workflow_journal.py:203 history_preflight), so
; replay of published ++ [candidate] is as valid as replay of published; the
; replay theorems fn-bp-trace-preserves-state and the receiver's
; fn-bprv-* take the scanned list as their input.
(defthm fn-bs-journal-both-outcomes-replay
  (implies (and (fn-bs-journal-imagep published candidate t records)
                (equal (fn-bp-history-preflight (append published (list candidate))) t))
           (fn-bp-replay-okp (fn-bp-replay records))))

; K10 (FNBI).  The inbox is keyed by name, not sequence: at every cut of
; P-INBOX, every crash image has the BID's name absent or present with the
; exact frame; a present frame decodes to the BID that names it.
(defthm fn-bs-inbox-crash-image-is-absent-or-exact
  (implies (and (fn-bs-inbox-relation bs)
                (member-equal (cons bs1 ks1)
                              (fn-bs-run bs nil (fn-bs-inbox-program stage name frame) outcomes nil nil))
                (fn-bs-crash-imagep bs1 image))
           (or (not (fn-bs-lookup image :inbound name))
               (equal (fn-bs-content image (fn-bs-lookup image :inbound name)) frame))))
```

`fn-bp-history-preflight`, `fn-bp-replay`, `fn-frame-journal-decode` stand
for the workflow book's actual replay entry and the frame book's
kind-dispatching decoder; P5 names them exactly. The BPA delete stays outside
the model (`receive:bpa-deleted`); it is a transport effect, and the campaign
keeps checking it against `_in_inventory`.

### 3.5 The frame trailer as the detector

Two halves. The structural half needs no cryptography and is proved
outright. The content half is stated against A-CRYPTO and names the exact
event it cannot exclude.

```lisp
; A torn variant of a written frame: some unit-aligned pieces replaced by
; their old content, zeros or garbage, or the whole truncated to a unit
; boundary.  Defined through the crash machinery on a one-inode store so
; that "torn" means exactly what section 1.5 means.
(defun fn-bs-torn-variantp (unit observed written)
  (declare (xargs :guard t))
  (let ((s (fn-bs-make unit (list (cons 0 nil)) nil (list (list :write 0 0 written)) 1)))
    (fn-bs-crash-imagep s (fn-bs-make unit (list (cons 0 observed)) nil nil 1))))

; K11a. Truncation never validates.  A proper prefix of a frame that opens
; fails with :truncated, by the header's length field alone
; (fn-frame-decode, frame.lisp:631: declared + 32 > remaining).
(defthm fn-bs-truncated-frame-never-validates
  (implies (and (fn-frame-result-okp (fn-frame-open written max-payload))
                (natp k) (< k (len written)))
           (not (fn-frame-result-okp (fn-frame-open (fn-bs-take k written) max-payload)))))

; K11b. Any length change never validates: the header fixes the total.
(defthm fn-bs-resized-frame-never-validates
  (implies (and (fn-frame-result-okp (fn-frame-open written max-payload))
                (fn-frame-result-okp (fn-frame-open observed max-payload))
                (equal (fn-bs-take *fn-frame-header-octets* observed)
                       (fn-bs-take *fn-frame-header-octets* written)))
           (equal (len observed) (len written))))

; K11c. A validated torn variant that is not the exact write is a forgery:
; its protected prefix differs from the written one and its trailer is the
; digest of its own prefix.  This is as far as the logic goes: whether
; nature produces such a frame is the A-CRYPTO-TRAILER assumption below.
(defun fn-bs-frame-forgeryp (observed written max-payload)
  (declare (xargs :guard t))
  (and (fn-frame-result-okp (fn-frame-open observed max-payload))
       (not (equal (fn-frame-protected-prefix observed)
                   (fn-frame-protected-prefix written)))))

(defthm fn-bs-validated-torn-frame-is-a-forgery
  (implies (and (fn-bs-torn-variantp unit observed written)
                (not (equal observed written))
                (fn-frame-result-okp (fn-frame-open written max-payload))
                (fn-frame-result-okp (fn-frame-open observed max-payload)))
           (fn-bs-frame-forgeryp observed written max-payload)))

; K11d. Under A-CRYPTO-TRAILER, a validated record is an exact write.  This
; is the defence-in-depth theorem for images OUTSIDE the crash relation
; (media damage, a lying fence): the scan either returns exact bytes the
; host wrote or faults; it never returns a torn record.
(defthm fn-bs-validated-record-is-exact-or-assumption-broken
  (implies (and (fn-assume-crash-tearp unit observed written)
                (fn-frame-result-okp (fn-frame-open written max-payload))
                (fn-frame-result-okp (fn-frame-open observed max-payload)))
           (equal observed written)))
```

Lemmas from `frame-invariants.lisp` that carry these:
`fn-frame-decode-refuses-oversize-before-validation`,
`fn-frame-decode-bounds-its-payload`,
`fn-frame-decode-trailer-is-the-supplied-digest`, `fn-frame-open-of-seal`,
`fn-frame-protected-prefix-of-encode`.

### 3.6 Assumptions as constrained functions

Two encapsulates replace `fn-assume-durability-image` and
`fn-assume-write-isolation-observe`. Each has a local witness, a minimal
constraint, and a named qualification hook.

```lisp
; A-CRASH-IMAGE.  The platform's crash, whatever it does, leaves an image the
; byte model admits.  ORACLE is the platform's freedom (power timing, drive
; cache, scheduler); the constraint is over every oracle.
;
; This one constraint carries: fenced data survives (fn-bs-crash-keeps-fenced-
; content), nothing is invented (fn-bs-crash-invents-nothing), per-inode
; isolation of tears (fn-bs-tear-touches-only-its-inode), per-entry atomic
; namespace with no dangling entries (fn-bs-crash-entry-is-old-or-a-pending-
; target), and that fsync :ok means drained (the definition of
; fn-bs-fsync-file; the platform must not return :ok without the drive
; having committed, which on darwin is F_FULLFSYNC, review D12).
;
; Qualification: functional instantiation with the development profile's
; crash function, evidenced by the campaign of section 5 (process death
; only; no power-loss claim) and by the literature rows of section 1.8 for
; the filesystem class (journaled or COW metadata, block-granular data).
(encapsulate
  (((fn-assume-physical-crash * *) => *))
  (local (defun fn-assume-physical-crash (s oracle)
           (declare (ignore oracle))
           (fn-bs-crash s nil)))                ; the lose-everything image
  (defthm fn-assume-physical-crash-is-admissible
    (implies (fn-bs-statep s)
             (fn-bs-crash-imagep s (fn-assume-physical-crash s oracle)))))

; A-CRYPTO-TRAILER.  The tears the platform produces are a subset of the
; model's tears, and none of them validates unless it is the exact write.
; The witness is "no tears".  Its qualification is statistical: the
; campaign's garble and truncate variants (section 5) over SHA-256 never
; validate; a 2^-256 event is not modeled.  This replaces the sentence "the
; frame checksum supplies only the predicate that damaged bytes in the
; stated fault class are rejected" (store-refinement.md) with the class.
(encapsulate
  (((fn-assume-crash-tearp * * *) => *))
  (local (defun fn-assume-crash-tearp (unit observed written)
           (declare (ignore unit))
           (equal observed written)))
  (defthm fn-assume-crash-tear-is-a-model-tear
    (implies (fn-assume-crash-tearp unit observed written)
             (fn-bs-torn-variantp unit observed written)))
  (defthm fn-assume-crash-tear-never-validates-unless-exact
    (implies (and (fn-assume-crash-tearp unit observed written)
                  (not (equal observed written)))
             (not (fn-frame-result-okp (fn-frame-open observed max-payload))))))
```

What the model deliberately does not cover, each named with the contract a
future assumption would need, so that no theorem here is read as claiming it:

- **A-MEDIA** (media corruption, latent sector errors, bit rot): durable
  octets change with no pending write. Contract: `fn-assume-media (s) = s`
  restricted to the retention window; not stated in v2. FLR-003 keeps this
  as a separate fault-and-salvage model; K11d is what the salvage path can
  rely on.
- **A-FIRMWARE** (a fence that returns `:ok` without committing: drive
  caches ignoring FLUSH CACHE, `fsync` on darwin without `F_FULLFSYNC`, USB
  bridges): violates the definition of `fn-bs-fsync-file`. Not an
  assumption with a witness; it is the boundary of A-CRASH-IMAGE, and the
  development profile's `durable_barrier` fallback to plain `fsync` when
  `F_FULLFSYNC` is refused (run_store.py:200-207) is a profile note, not a
  modeled transition.
- **A-POSIX** (NFS close-to-open, FAT without directory fences, overlay and
  FUSE filesystems, `data=writeback`, ext2): namespace semantics outside
  §1.6. Excluded by name in the profile; no theorem holds there and none
  claims to.
- **Freshness** (whole-store rollback to an older valid image): unchanged
  from v1; `fn-bs-crash-imagep` cannot express it because it is not a crash.
  The anchor the retired journal model had (`fn-journal-anchorp`) is the
  right shape and remains future work.
- **The BPA delete and every transport side effect**: outside storage.

## 4. Refinement obligation map

| Existing | Becomes | Why |
| --- | --- | --- |
| `fn-sf-crash-imagep` (store-files.lisp:499) | **Interface predicate**, kept; its inhabitation by real images is K2 | It is the right conclusion; v2 proves it rather than assuming it |
| `fn-sf-crash` and `fn-sf-crash-realizes-every-admissible-image` | **Lemma** for K3 | The constructor is a corollary of K2 plus this |
| `fn-sf-unobserved-frontier-replacement-crash-is-old-or-new`, `fn-sf-unobserved-record-link-crash-is-absent-or-present` (store-files-invariants.lisp:191, 210) | **Corollaries** of K2 restricted to the `:frontier-data-durable` / `:record-data-durable` cuts | The choice comes from the pending `:set-entry` of the rename or link, applied or dropped |
| `fn-sf-completed-frontier-barrier-removes-old-choice`, `fn-sf-completed-record-barrier-removes-absent-choice` (:245, :258) | **Kernel shadows** of K8 and its frontier twin | The fence drains the entry operation; the kernel step records that it did |
| `fn-sf-crash-outside-namespace-window-keeps-image` (:230) | **Corollary** of K2 with `fn-bs-pending-matches-phase` forcing empty authority pending sets | |
| `fn-sf-stable-records-prefix-of-crash`, `fn-sf-surviving-candidate-is-exact-and-dominated` (:93, :107) | **Lemmas** for K5 and K6 | They remain the kernel-level statements; K5/K6 are their byte-level forms |
| `fn-sn-acknowledged-record-survives-observed-reopen`, `fn-snrt-acknowledged-record-retained-across-observed-reopen` (store-observed-traces.lisp) | **Lemmas** for K4 and its trace extension | Their `fn-sf-crash-imagep` premise is discharged by K2; PRF-007 cites K4 after P3 |
| `fn-snt-admissible-crash-image-is-recoverable`, `fn-sf-admissible-image-facts` | **Lemmas**, unchanged | |
| `fn-sn-open-observed-success-has-live-history-relation` (D6) | **Unchanged keystone**; the scan's output is its input | The process root stays `fn-sn-open-observed` |
| `fn-assume-durability-image`, `fn-assume-write-isolation-observe` (assumptions.lisp:753, 790) | **Retired** as strawmen | No theorem instantiates them (their own header says so); their content is §1.7 theorems plus A-CRASH-IMAGE |
| `books/journal.lisp` `fn-journal-crash`, `:torn` slots, reversal | **Retired** as the campaign's reference; kept as history | What it got right and v2 keeps: torn is first-class; no append-prefix assumption; durability is per fence not per write; the scanner sees physical content only, no durability bits; a torn acknowledged commit is a fault. What it lacked: bytes, directories, the fence/entry distinction, a connection to any host program |
| `fn-journal-recover-torn-anchored-commit-fault` and the anchor | **Kept as the freshness shape** for a later anchor packet | v2 has no anchor; the gap is unchanged |
| `fn-frame-decode-*`, `fn-frame-open-of-seal`, `fn-frame-protected-prefix-of-encode` | **Lemmas** for K11a-c | |
| `fn-frame-digest` encapsulate (A-CRYPTO) | **Unchanged**; A-CRYPTO-TRAILER is a second encapsulate beside it, not a twin | It says nothing about digests; it bounds nature's tears |
| The six-cut table (store-fault-matrix.md §"Process-death cuts") and `tests/store_crash_child.py` | **Retired**; regenerated from the `:cut` steps of §2.2 | Subsumed by the campaign since `3cb1bae`; v2 makes the table a program |
| `cuts.py` `model` strings | **Replaced** by `(program, step-index)` references; the two `gap` rows become K9 references | |
| `specs/store-exploration.md` "crash choices in the data-durable phases are asserted covered" | **Retired** as a coverage claim | Coverage is the campaign's differential check against `fn-bs-image-admissiblep` |
| `_frontier_with_checksum`, `config_with_checksum` (run_store.py:567, 174) | **Deleted** by P4; frontier and config become `fn-frame` frames | The assurance rule "integrity trailers are ACL2-owned" |
| `fn-checkpoint-*` (checkpoint.lisp) | **Unchanged**; P-CHECKPOINT programs get K12 (present-or-absent exact generation; old-or-new selection) after P8 | The logical checkpoint book never chose bytes; v2 supplies them |

## 5. Fault-campaign extension

`tests/campaign/` keeps its shape (table read from the host, one kill per
pair, reopen through the real recovery path). Four additions.

### 5.1 Image import and the differential check

After the kill, before reopening, `campaign/image.py` walks the case
directory and emits the ACL2 form of a byte-store image: every regular file
as `(ino . octets)` keyed by `st_ino`, every directory as `(id . entries)`,
pending `nil`. The campaign also imports the scenario template the same way
before the run. It then asks ACL2, in one call:

1. `(fn-bs-run template-bs template-ks (take k program) all-ok groups capacity)`
   for the cut's `(program, k)`, giving `bs_k`;
2. `(fn-bs-image-admissiblep bs_k image)`, which must be `t`: the killed
   process left an image the model admits;
3. `(fn-bs-scan-store image)` and `(fn-sn-open-observed ...)` of its output,
   whose result class, frontier, record count and record octets must equal
   what the host's reopen reports and what `--keep`'s case directory holds.

Step 3 subsumes the handoff's open item (recovered record bytes versus the
bytes the killed process staged). A disagreement is a minimal trace, as
today, plus the ACL2 image and the pending list of `bs_k`.

### 5.2 Torn-write injection

For each cut, the harness reads `(fn-bs-pending bs_k)` from ACL2 rather than
guessing what was unflushed, and for each pending `:write` produces:

- **truncate**: cut the file at each unit boundary within the write;
- **zero**: overwrite one unit of the write with zeros;
- **garble**: overwrite one unit with `os.urandom`;
- **lose**: restore the file to its pre-write content (empty for a new file);

and for each pending entry operation, **drop** (remove the linked name;
restore the old frontier entry; re-create the unlinked stage). Each variant
is applied to a copy of the case directory, checked admissible (5.1 step 2),
reopened, and checked differential (5.1 step 3). Run at `unit = 1` and at
`unit = 4096`; the former is a superset and both must pass.

Expected outcomes, from the theorems: every variant at every cut of P-FRONTIER
and P-RECORD recovers to the same class the unmutated image does (K1, K2),
because every pending write at every cut names a staging-only inode. A
variant that changes the recovered state is a differential failure and a
counterexample to K1.

### 5.3 Directory-loss injection

Two classes, distinguished by admissibility:

- **admissible** (inside the model): drop every pending entry operation of
  one directory (the "fsync(dir) never happened" image); remove or keep
  staging orphans. Must recover normally.
- **inadmissible** (outside the model, FLR-003): remove a durable
  `transactions/` entry, the config or frontier entry, or the whole
  `transactions/` directory. ACL2 must report `(not (fn-bs-image-admissiblep ...))`,
  and the host must exit `EXIT_FAULT` with the reason class
  `fn-bs-scan-store` returns for that image (`:namespace`, `:config`,
  `:frontier`, `:record`), never `EXIT_OK` and never silent recovery.

### 5.4 Journals and inbox

The same three additions over P-JOURNAL (FNWF, FNRJ) and P-INBOX (FNBI),
with `fn-bs-scan-journal` and K9/K10 as the reference. The two `gap` rows of
`cuts.py` gain `program="journal", step=<index of the :link step>` and lose
their `gap` string; `model_gaps()` must return empty after P5.

### 5.5 The campaign must be able to fail

A test-only environment flag (`FN_CAMPAIGN_UNSAFE=link-before-fsync`) makes
the host issue `os.link` before `fsync_file` in `publish`. With it set, the
torn-write variants at `record-linked` must produce a differential failure
(a validated-but-torn or a truncated record under a final name, faulting the
reopen the model predicts succeeds), and `transcribe_check.py` must fail the
table (D1 violated). A campaign that cannot fail on a known-bad host is not
evidence; this is the campaign-level tooth for K1.

## 6. Migration plan

Ordered packets. Each names an owner lane, its deliverables, and the
acceptance criterion the coordinator checks. No packet runs a bare `-p`
suite; each certifies its own roots and runs the filtered tests it names.

| # | Packet | Owner | Deliverables | Acceptance |
| --- | --- | --- | --- | --- |
| P0 | Register and adopt | this lane, then coordinator | This document; `DESIGN-crash-model-v2-summary.md`; `fn-bs-` row in `docs/prefixes.md` when P1 opens | `make check` green with the new spec present; decision recorded in `planning/decisions.md` |
| P1 | Byte-store kernel | lane `w5/bs-kernel` | `books/byte-store.lisp` (§1.2-1.6), `fn-bs-image-admissiblep` and `fn-bs-image-admissiblep-iff-crash-imagep`, §1.7 theorems, `tests/acl2/byte-store-tests.lisp` | Certifies; guard-verified; teeth: `must-fail` for "fenced content lost", "unissued write appears", "cross-inode damage", "entry neither old nor a target", "refence after error fences something"; a witness where a dropped rename leaves the old frontier and a dropped link leaves no name |
| P2 | Programs and the transcription check | lane `w5/bs-programs` (host + proof) | `books/byte-store-programs.lisp` (§2.1-2.2), D1-D5 as `assert-event`s, `tools/transcribe_check.py`, P-INIT cuts added to `run_store.py` | Table test green; every durable syscall in the six host functions has a step and a cut; `python3 tests/campaign/cuts.py` count equals the number of `:cut` steps; `transcribe_check.py` fails when one host line is moved |
| P3 | Scan, relation, store keystones | lane `w5/bs-scan` | `books/byte-store-scan.lisp` (§3.1-3.3, K0-K8), tests with witnesses at every cut | Certifies; K4 replaces the PRF-007 citation via `tools/ledger.py`; teeth: drop `:fsync-file` before `:link` in a test program and K1 `must-fail` with a torn record under a final name |
| P4 | ACL2-owned frontier and config frames; trailer theorems | lane `w5/bs-frame` (host + proof) | New store frame kinds for frontier and config; `fn-bs-frontier-decode` defined, encapsulate removed; `books/byte-store-frame.lisp` (K11a-d); `_frontier_with_checksum` and `config_with_checksum` deleted; store format bump with a migration note in `store-experiment.md` | Certifies; `grep -n checksum tools/run_store.py` returns nothing; `tests/test_store.py` corruption rows pass against the new frames; tooth: a truncated frame validating `must-fail` |
| P5 | Journals and inbox | lane `w5/bs-journals` | §3.4 relation and K9/K10 with the workflow and receiver replay entries named exactly; `cuts.py` gap rows resolved | Certifies; `python3 tests/campaign/cuts.py` prints `model-gaps=0`; campaign green |
| P6 | Campaign v2 | lane `w5/campaign-v2` | §5.1-5.5: `campaign/image.py`, torn/zero/garble/lose/drop variants, directory-loss classes, unit 1 and 4096, `FN_CAMPAIGN_UNSAFE` failure demonstration | Zero failures on the real host; at least one failure with the unsafe flag; runtime recorded; report JSON carries the ACL2 image for every failure |
| P7 | Assumptions | lane `w5/hygiene` | §3.6 encapsulates in `books/assumptions.lisp`; the two strawmen deleted; `specs/failures.md` table rows for A-DURABILITY and A-WRITE-ISOLATION rewritten to point at A-CRASH-IMAGE and the §1.7 theorems; ledger regenerated | `grep fn-assume-durability-image fn-assume-write-isolation-observe` empty; `make check`; `proofs.json` events generated, not typed |
| P8 | Checkpoint hookup | successor of `w3-checkpoint`, after it lands | P-CHECKPOINT re-transcribed from the committed `tools/checkpoint.py`; K12: selected generation present-or-absent exact, selection old-or-new; `corrupt` reachable only via a forgery | Certifies; checkpoint cuts in the campaign with the P6 variants |
| P9 | Retirements | lane `w5/hygiene` | `tests/store_crash_child.py` and the six hand cuts removed; store-fault-matrix.md cut table regenerated from §2.2; store-exploration.md coverage sentence replaced; store-refinement.md item 15 and the assumptions section rewritten to cite K2/K3 | `make check`; filtered `test_store_process_crash` removed from the test list; no spec sentence asserts old-or-new as a hypothesis |
| P10 | Platform qualification profile | lane `w6/qualify` | Functional instance of `fn-assume-physical-crash` and `fn-assume-crash-tearp` for the development profile (APFS, `F_FULLFSYNC`), `docs/proofs.md` "Qualifying a platform" filled in, `failures.md` "Required platform evidence" answered line by line for that profile only | The instance certifies against the P1-P6 books; the evidence file names the campaign run, unit sizes, filesystem, kernel, and states "process death only; no power-loss claim" in the same sentence as any number |

Dependencies: P1 before P2, P3, P4; P2 before P3, P6; P3 before P5, P7, P9;
P4 independent of P3 (the encapsulated codec keeps P3 honest until P4); P8
after w3 lands and P3; P10 last.

What lands on `dev` first: P0 and P1 together, because P1's teeth are the
first evidence that the model says something a strawman does not.

## 7. Status per keystone (2026-09-19, lane `w4/byte-store`, packets P0-P3)

The books are the source; where a book and §1-§3 differ, this section says
so. Certification evidence directories are named in
`planning/lanes/HANDOFF-w4-byte-store.md`.

### The model (`books/byte-store.lisp`, §1.2-1.6)

Admitted as written, with four changes the well-formedness proofs forced.
The fourth is lane `w9/storage`, 2026-09-20, and it is a defect the view
theorem's attempt found rather than a proof convenience: a pending
`(:write ino offset NIL)` has `fn-bs-unit-count` 0, so a crash tears it into
no pieces, while `fn-bs-apply-op` splices it and zero-extends the inode when
the offset is past the end.  The view of
`(:byte-store 4 ((0)) NIL ((:write 0 5 NIL)) 1)` is five zero octets and no
crash image of that state has them, so
`fn-bs-view-is-an-admissible-image` was FALSE as stated.  `write(2)` of zero
octets changes nothing on POSIX and `fn-bs-write` issues no operation for it,
so `fn-bs-statep` now carries `fn-bs-writes-nonemptyp`, a domain invariant of
the model's own syscalls in the same sense as `fn-bs-writes-knownp`.  The
three earlier changes:
`fn-bs-statep` carries two more conjuncts (every inode id in the table is
below `next-ino`; every pending `:write` names a table inode), without
which `fn-bs-create` and `fn-bs-crash` do not preserve the inode table;
`fn-bs-write` reports `:ebadf` for an inode the table does not hold and
`fn-bs-mkdir` reports `:eexist` for a directory id already present;
`fn-bs-tear-write` takes its measure from `fn-bs-unit-count` stated as an
integer. The state is an opaque record (`docs/proof-style.md` §1). Guards
are not verified on the model (`:guard t :verify-guards nil`, as §1 itself
prescribes); guard verification is open.

| Statement | Book | Status |
| --- | --- | --- |
| K0 (model well-formedness): `fn-bs-statep` preserved by `fn-bs-crash` (admissible choices), both fences, and every syscall for every outcome | `byte-store-invariants` | **proved**: `fn-bs-{crash,fence-file,fence-dir,create,write,fsync-file,fsync-dir,link,rename,unlink,mkdir}-preserves-statep`. `unlink` and the source path of `rename` need no `dir-idp`/`namep` hypotheses (the lookup types them). |
| `fn-bs-fence-file-drains-exactly-its-inode`, `fn-bs-fence-dir-drains-exactly-its-directory` | `byte-store-invariants` | **proved**, no `fn-bs-statep` hypothesis; plus `-touches-only-its-{inode,directory}` |
| `fn-bs-crash-keeps-fenced-content` (A-DURABILITY positive half) | `byte-store-invariants` | **proved**, no `fn-bs-statep` hypothesis. `fn-bs-crash-invents-nothing` and `fn-bs-tear-touches-only-its-inode` are the same statement (`fn-bs-fencedp` unfolds to their hypothesis; the latter's `ino` is unused) and are not separate events. |
| `fn-bs-crash-keeps-quiet-directory` | `byte-store-invariants` | **proved** (the directory half of the above; not in §1.7) |
| `fn-bs-crash-entry-is-old-or-a-pending-target` (A-WRITE-ISOLATION namespace half) | `byte-store-invariants` | **proved** with `(fn-bs-dir-idp dir) (fn-bs-namep name)` in place of `fn-bs-statep` |
| `fn-bs-refence-after-error-fences-nothing` (fsyncgate) | `byte-store-invariants` | **proved** with no hypothesis: after `:ok` the set was drained, after an error discarded; either way a second fence finds nothing |
| `fn-bs-lose-everything-is-an-admissible-image`, `fn-bs-crash-with-no-choices-is-the-durable-state` | `byte-store-invariants` | **proved** (the bottom of the image lattice; the top is the view, below) |
| `fn-bs-splice-composition`, `fn-bs-view-choices`, `fn-bs-view-choices-are-choices` | `byte-store-invariants` | **proved** (w9/storage): the composition lemma the view theorem's obligation named, and the nothing-lost choice list with its admissibility for every pending list and every unit |
| `fn-bs-view-is-an-admissible-image` | — | **open**, with a smaller obligation stated at its place in the book. The composition lemma is discharged and the witness choice list exists; what remains is two index facts for `1 <= i <= count-1`, `(equal start_i (+ offset k_i))` and `(equal (min (+ offset L) (* (+ u0 i 1) unit)) (+ offset k_(i+1)))`, where `start_i = (max offset (* (+ (floor offset unit) i) unit))` and `k_i = (min L (- start_i offset))`. With them the induction on `i` closes, its step being `fn-bs-splice-composition` then `fn-bs-take-split` and its base `fn-bs-take-of-len-is-identity`. The attempt exhausts a 2,000,000 step limit re-deriving the two facts inside every branch of `fn-bs-tear-write`; state them as `:linear` rules over a named `fn-bs-piece-start` and open the tear once by `:expand`. |
| `fn-bs-image-admissiblep` and `-iff-crash-imagep` (§1.5 decision procedure) | — | **open** (P1 residual; P6 needs it) |
| A-CRASH-IMAGE `fn-assume-physical-crash`, A-CRYPTO-TRAILER `fn-assume-crash-tearp` (§3.6) | `assumptions` | **admitted** as encapsulates with the stated constraints, **moved to `books/assumptions.lisp`** (P7) by lane `w9/storage-2` on 2026-09-20, with `fn-bs-torn-variantp`: that book now includes `byte-store-invariants`, and `books/relay`, `books/bp-release` and `books/scheduler-invariants` carry the byte-store closure. No cycle; the constraints did not change. The tearp witness is "no tears, of an empty write" until the view theorem lands. |

### The programs (`books/byte-store-programs.lisp`, §2)

P-FRONTIER, P-RECORD, P-FINISH, P-RECOVER and P-INIT are transcribed with a
`:cut` after every durable syscall (rule §2.3), which adds the cut names
`frontier-created`, `frontier-written`, `record-created`, `record-written`,
`record-stage-unlinked` and the `init-*` names: P2's host half must add
those `faults.at` sites. The directory observations are the kernel's real
events `:frontier-dir` / `:record-dir`, not §2.2's `:frontier-directory` /
`:record-directory`. D1-D3 are `assert-event`s over the constants with one
violating program each; D4 is `fn-bs-run-stops-at-first-error-by-definition`
(`:rule-classes nil`); D5 is asserted on the ground runs at every step
(`fn-bs-run-pending-disjointp`), not yet the theorem
`fn-bs-program-pending-disjoint`. P-JOURNAL (both halves), P-INBOX with its
reconciliation branch and both P-CHECKPOINT programs are transcribed by lane
`w9/storage` (2026-09-20) with the host's own cut names, and carry the same
ground assertions. `tools/transcribe_check.py` is §2.3's check, in both
directions, and reports `fidelity-defects=0`: every cut the campaign kills
at is a `:cut` of the program that transcribes its host function, or is one
of four paths named with its reason (the composite receiver and three
transport-delete boundaries). It also reports `missing-host-cuts=15`, which
is exactly P2's host half, and an advisory syscall-sequence comparison whose
five lines are each answered in the book. `fn-bs-checkpoint-select-program`
lost a step to it: the host's `os.unlink` after the replace is the `except`
arm, and a model program that took it stops at `:enoent`.

### The keystones of §3

| Keystone | Status |
| --- | --- |
| K0 `fn-bs-program-step-preserves-relation` | **open** (P3): needs `fn-bs-store-relation`. Ground form: `fn-bs-run-statep` holds on every ground run (`byte-store-programs`) and the composed runs reach `:reserved`, `:completing`, `:ready` and recover to `:ready` (`tests/acl2/byte-store-tests.lisp`). |
| K1 `fn-bs-store-crash-image-scans` | **open** (P3), and its NAMESPACE clause is closed as of 2026-09-20 (lane `w9/storage-3`, hbox `build/acl2/certify-20260920T204940Z-1181403`): `fn-bs-apply-entries-names-is-names-after` (the bridge the previous lane left open; `tools/proof_profile.py` named four opened recognizers as the cause and closing them took it from an induction-depth-limit blowout at 2,016,278 prover steps to 33,789), then `fn-bs-crash-names-is-names-after`, `fn-bs-crash-image-names-are-an-outcome` and `fn-bs-crash-image-transaction-names`, which is the "exactly the durable transaction namespace, or that namespace with the one pending link's name appended" clause. What is left of K1 is the other three scan clauses. |
| K2 `fn-bs-store-crash-image-is-kernel-admissible` | **open** (P3), and the MODEL question in front of it is now DECIDED: [decision D14-a](../planning/decisions.md) (2026-09-20, lane `w9/storage-3`) keeps `books/byte-store-scan.lisp`'s `(fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))` and withdraws §3.2's `(fn-bs-txn-name (len (fn-sf-records ks)))`. The evidence is the six cut states between the record write and the pending link's removal in `tools/run_store.py` at `ca8a2ef`. In the PUBLISH window (`record-linked` 1338, `record-attempted` 1346, and the `record-link :error` branch 1336) the two forms agree, because the only transition that appends to `fn-sf-records` is `fn-sf-record-dir-result :ok` (`store-files.lisp:507`), issued at `publish:1353` strictly after the `fsync_dir(self.transactions)` at 1348 that empties the directory's pending list. In the RECOVERY window they do not: process death is not power loss, so a cut at `record-linked` leaves the entry pending, the next process's `durable_records` (1100) scans the VIEW and `acl2.recover` (1164) replays `R+1` records, and at `recover-replayed` (1179) and the first two `recover-barrier` cuts (1200, before `fsync_dir(self.transactions)` at 1187) the durable namespace still holds `R` names. There §3.2's form names `(fn-bs-txn-name (1+ R))`, which names nothing. The rejected candidate `(equal (len (fn-bs-durable-records bs)) (len (fn-sf-records ks)))` is false at exactly those three cuts. The duplicate-record image is excluded instead by the publish window's `(equal (fn-bs-durable-records bs) (fn-sf-records ks))`, an equality of LISTS, and §3.2 now carries a third arm, `fn-bs-replay-matches-scan`, for the recovery window. K2 gains `(not (fn-bs-replay-visiblep ks))` as a hypothesis; the recovery window is the new open row K2r, and the finding it rests on is a GAP IN THE KERNEL, not in the byte model: `fn-sf-crash-imagep` (`store-files.lisp:593`) has no freedom for a record that was replayed and not yet re-fenced. |
| K2r `fn-bs-replay-window-carries-no-success` | **open** (P3, new 2026-09-20). The recovery window's obligation, stated so it does not need the kernel freedom K2 would need: such a state has `(fn-sf-successes ks)` empty -- `fn-sn-initial nil 0` starts with none and `Store.recover` runs exactly once per process, at open (`run_store.py:1674`, `run_owner.py:660`, `fn9p.py:428`, `run_reader.py:313`, `run_bp_ingress.py:132`) -- so a crash there risks no acknowledged record, and K1 says whichever list survives scans. Widening `fn-sf-crash-imagep` instead is recorded as a proposal and not taken: it changes the premise `books/store-observed.lisp` and the store-node closure take from the kernel. |
| K3 `fn-bs-store-recovery-is-a-kernel-crash` | **open** (P3): from K2 and `fn-sf-crash-realizes-every-admissible-image`. |
| K4-K8 | **open** (P3) |
| K9, K9b, K9c, K10 | **open** (P5) |
| K11a-d | **open** (P4) |
| K12 | **open** (P8) |

### Witnesses (`tests/acl2/byte-store-tests.lisp`)

Reached through the production syscalls from an initialized store at unit
4: a torn record (`:new :zero (:garble ...)` over a 10-octet frame), a
truncated and a zero-length record, a lost and a kept link, a failed
`fsync` (EIO after one unit; the retried `fsync` changes nothing), a
dropped rename and a staging orphan; the composed runs of the five
programs against the real `fn-sf` kernel; and one concrete violating value
per hypothesis of each keystone above, or the statement that none exists
and why.
