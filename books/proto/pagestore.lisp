; fn: a prototype page store (lane proto-pagestore, 2026-09-27).  Prefix pgs-.
;
; The owner's snapshot as a PAGE STORE with copy-on-write commits (the LMDB
; shape; Fare, "Houyhnhnm Computing" chapters 2-3: persistence by default,
; virtualization as branching).  Typed columns and a byte pool live in
; fixed-size pages.  A snapshot writes only the dirty pages, to FRESH space
; (never over a page any live commit references), then the page table, then
; one commit record into the root's other slot; the record names the page
; table and its digest and carries a self-check.  The previous commit stays
; valid until the new record is complete, and after it (the slot pair keeps
; both).  A FORK is a new root whose slot holds an existing record: the
; pages are shared, and a later commit on either root writes only fresh
; pages, so neither root sees the other's writes.
;
; Two layers, one owner of every decision.
;
;   The MODEL (section 2) is an abstract page store: `pages' maps a page
;   address to its content (logically an octet list; here any object), and
;   `roots' maps a root name to its two slots.  Every decision reads a
;   content only through `pgs-digest', the constrained digest seam of this
;   book (section 1).  The keystones (section 4) are about the model:
;   commit-then-open denotes the committed state
;   (`pgs-open-after-commit'), a crash anywhere in a commit opens on the
;   new or the previous state and never anything else, and on the previous
;   one whenever the record did not land whole (`pgs-open-after-crash'),
;   and fork isolation (`pgs-fork-isolation').
;
;   The EXECUTABLE (section 5) is the same decisions over a stobj of
;   little-endian (unsigned-byte 64) words that the host fills and drains
;   with exactly two primitives (host/native/proto-pagestore.lisp):
;   fill-typed-array-from-file-range and write-typed-array-to-file-range.
;   The digest is SHA-256 over the page's octets computed HERE, over the
;   words, with books/sha256-stobj.lisp's compression.  The shared
;   decisions (`pgs-alloc', `pgs-plan-ptab', `pgs-open-order',
;   `pgs-entry-verdict', the record fields) are the SAME functions in both
;   layers; what differs is only how a digest is observed.
;
; The boundary, named (prototype; not yet theorems):
;   A-PGS-OBSERVE: the words the fill primitive leaves in the stobj are the
;     page's content, and `pgs-x-words-digest' of them is `pgs-digest' of
;     that content (the SHA-256 correspondence books/sha256-buffer.lisp
;     proves for the octet buffer is not proved here for the word array);
;     `pgs-x-decode-ptab' of the encoded table is the table.
;   A-CRYPTO (books/crypto-seam.lisp, books/assumptions.lisp): the torn-write
;     keystone takes, as a HYPOTHESIS, that a stale page at a fresh address
;     whose digest equals the intended page's digest IS that page
;     (`pgs-writes-faithful'); the test book shows the conclusion fails for a
;     colliding digest.  SHA-256's pessimistic figure is the collision
;     bound, 2^-128, not the second-preimage one.
(in-package "ACL2")
(include-book "pagestore-words")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

; =============================================================================
; 1. The digest seam.

(encapsulate
  (((pgs-digest *) => * :formals (x) :guard t))
  (local (defun pgs-digest (x) (declare (ignore x)) 0))
  (defthm pgs-digest-natp
    (natp (pgs-digest x))
    :rule-classes :type-prescription))

; =============================================================================
; 2. The model.
;
; A page table (ptab) is a list of entries (PHYS TXID DIGEST), one per
; logical page, in logical order: the page's address, the commit that wrote
; it, and its content's digest.  A commit record is
;   (:pgs-commit TXID PTAB-ADDR PTAB-LEN PTAB-DIGEST CHECK)
; and it is VALID when CHECK is the digest of the rest.

(defun pgs-entry-p (e)
  (declare (xargs :guard t))
  (and (true-listp e) (= (len e) 3)
       (natp (first e)) (natp (second e)) (natp (third e))))

(defun pgs-ptab-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (pgs-entry-p (car x)) (pgs-ptab-p (cdr x)))
    (null x)))

(defun pgs-rec-shape-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (= (len x) 6)
       (eq (first x) :pgs-commit)
       (natp (second x)) (natp (third x)) (natp (fourth x))
       (natp (fifth x)) (natp (sixth x))))

(defun pgs-rec-body (x)
  (declare (xargs :guard t))
  (if (true-listp x) (take 5 x) nil))

(defun pgs-rec-ok (x check)
  ; Shared: the record is shaped and its CHECK field is the observed check.
  (declare (xargs :guard t))
  (and (pgs-rec-shape-p x) (equal (sixth x) check)))

(defun pgs-rec-valid (x)
  (declare (xargs :guard t))
  (pgs-rec-ok x (pgs-digest (pgs-rec-body x))))

(defun pgs-make-rec (txid ptab-addr ptab-len ptab-digest)
  (declare (xargs :guard t))
  (let ((body (list :pgs-commit txid ptab-addr ptab-len ptab-digest)))
    (append body (list (pgs-digest body)))))

(defun pgs-rec-txid (x) (declare (xargs :guard t)) (nfix (second (true-list-fix x))))
(defun pgs-rec-ptab-addr (x) (declare (xargs :guard t)) (nfix (third (true-list-fix x))))
(defun pgs-rec-ptab-len (x) (declare (xargs :guard t)) (nfix (fourth (true-list-fix x))))
(defun pgs-rec-ptab-digest (x) (declare (xargs :guard t)) (nfix (fifth (true-list-fix x))))

; Pages: an alist from address to content; a write is an acons.
(defun pgs-lookup (a pages)
  (declare (xargs :guard t))
  (cdr (hons-assoc-equal a pages)))

; The page verdict (shared).  In :eager mode every entry is checked; in
; :lazy mode only the entries the commit itself wrote (TXID equal to the
; record's), which are the only ones its own crash can have left unwritten;
; the rest are checked on first touch (`pgs-x-touch').
(defun pgs-entry-checked-p (e txid mode)
  (declare (xargs :guard (pgs-entry-p e)))
  (or (eq mode :eager) (equal (second e) txid)))

(defun pgs-entry-verdict (e txid mode observed)
  ; :ok, or :damaged when checked and the observed digest is not the entry's.
  (declare (xargs :guard (pgs-entry-p e)))
  (if (and (pgs-entry-checked-p e txid mode)
           (not (equal observed (third e))))
      :damaged
    :ok))

(defun pgs-check-pages (ptab txid mode pages i)
  ; nil when every checked page verifies; else (:page-damaged I PHYS).
  (declare (xargs :guard (and (pgs-ptab-p ptab) (natp i))))
  (if (atom ptab)
      nil
    (let ((e (car ptab)))
      (if (eq (pgs-entry-verdict e txid mode (pgs-digest (pgs-lookup (first e) pages)))
              :damaged)
          (list :page-damaged i (first e))
        (pgs-check-pages (cdr ptab) txid mode pages (+ 1 i))))))

(defun pgs-ptab-txids-ok (ptab txid)
  ; Shared: no entry claims a commit newer than the record naming the table.
  (declare (xargs :guard (pgs-ptab-p ptab)))
  (if (atom ptab)
      t
    (and (<= (second (car ptab)) (nfix txid))
         (pgs-ptab-txids-ok (cdr ptab) txid))))

(defun pgs-contents (ptab pages)
  (declare (xargs :guard (pgs-ptab-p ptab)))
  (if (atom ptab)
      nil
    (cons (pgs-lookup (first (car ptab)) pages)
          (pgs-contents (cdr ptab) pages))))

; The table verdict (shared): nil when the table read at the record's
; address has the record's digest, length and no entry newer than the
; record; else the refusal, by name.
(defun pgs-ptab-verdict (rec ptab observed)
  (declare (xargs :guard t))
  (let ((addr (pgs-rec-ptab-addr rec)))
    (cond ((not (equal observed (pgs-rec-ptab-digest rec)))
           (list :ptab-damaged addr))
          ((not (and (pgs-ptab-p ptab) (equal (len ptab) (pgs-rec-ptab-len rec))
                     (pgs-ptab-txids-ok ptab (pgs-rec-txid rec))))
           (list :ptab-malformed addr))
          (t nil))))

; Try one record: (:ok TXID CONTENTS) or (:refused REASON ...).
(defun pgs-try (rec pages mode)
  (declare (xargs :guard (pgs-rec-shape-p rec)))
  (let* ((ptab (pgs-lookup (pgs-rec-ptab-addr rec) pages))
         (tv (pgs-ptab-verdict rec ptab (pgs-digest ptab))))
    (if tv
        (cons :refused tv)
      (let ((bad (pgs-check-pages ptab (pgs-rec-txid rec) mode pages 0)))
        (if bad
            (cons :refused bad)
          (list :ok (pgs-rec-txid rec) (pgs-contents ptab pages)))))))

; The candidate order (shared): the valid slots, newest first; slot 0 wins a
; tie.  V0/V1 are the observed validities.
(defun pgs-open-order (s0 v0 s1 v1)
  (declare (xargs :guard t))
  (cond ((and v0 v1)
         (if (< (pgs-rec-txid s0) (pgs-rec-txid s1)) (list 1 0) (list 0 1)))
        (v0 (list 0))
        (v1 (list 1))
        (t nil)))

(defun pgs-slot (k slots)
  (declare (xargs :guard t))
  (if (equal k 1) (if (consp slots) (cdr slots) nil) (if (consp slots) (car slots) nil)))

(defun pgs-try-in-order (order slots pages mode refusals)
  ; (:ok SLOT TXID CONTENTS REFUSALS) or (:refused REFUSALS).
  (declare (xargs :guard (true-listp refusals)))
  (if (atom order)
      (list :refused refusals)
    (let* ((k (car order))
           (rec (pgs-slot k slots)))
      (if (not (pgs-rec-shape-p rec))
          (pgs-try-in-order (cdr order) slots pages mode refusals)
        (let ((r (pgs-try rec pages mode)))
          (if (eq (car r) :ok)
              (list :ok k (second r) (third r) refusals)
            (pgs-try-in-order (cdr order) slots pages mode
                              (append refusals (list (list* :slot k (cdr r)))))))))))

(defun pgs-slot-refusals (s0 v0 s1 v1)
  ; An invalid slot is refused by name: :commit-torn when it holds anything
  ; at all, nothing when it is empty.
  (declare (xargs :guard t))
  (append (if (and (not v0) s0) (list (list :slot 0 :commit-torn)) nil)
          (if (and (not v1) s1) (list (list :slot 1 :commit-torn)) nil)))

(defun pgs-open-slots (slots pages mode)
  (declare (xargs :guard t))
  (let* ((s0 (pgs-slot 0 slots)) (s1 (pgs-slot 1 slots))
         (v0 (pgs-rec-valid s0)) (v1 (pgs-rec-valid s1)))
    (pgs-try-in-order (pgs-open-order s0 v0 s1 v1) slots pages mode
                      (pgs-slot-refusals s0 v0 s1 v1))))

; The disk: (PAGES . ROOTS).  ROOTS maps a root name to (SLOT0 . SLOT1).
(defun pgs-pages (disk) (declare (xargs :guard t)) (if (consp disk) (car disk) nil))
(defun pgs-roots (disk) (declare (xargs :guard t)) (if (consp disk) (cdr disk) nil))
(defun pgs-root-slots (r disk)
  (declare (xargs :guard t))
  (cdr (hons-assoc-equal r (pgs-roots disk))))

(defun pgs-open (disk r mode)
  (declare (xargs :guard t))
  (pgs-open-slots (pgs-root-slots r disk) (pgs-pages disk) mode))

; What an open denotes, without the slot and the refusal trail: (TXID
; CONTENTS), or nil when it refused.  O is (:ok SLOT TXID CONTENTS REFUSALS).
(defun pgs-view (o)
  (declare (xargs :guard t))
  (if (and (consp o) (eq (car o) :ok) (true-listp o))
      (list (third o) (fourth o))
    nil))

; -----------------------------------------------------------------------------
; The live set and allocation (shared).
;
; A valid record keeps its page-table run (PTAB-ADDR and the pages after it
; the encoded table occupies) and every page its table names.  Fresh space
; is any address no valid record of any root keeps.

(defconst *pgs-page-words* 2048)        ; 16 KiB pages
(defconst *pgs-entry-words* 6)          ; phys, txid, four digest words

(defun pgs-ptab-run-pages (n)
  ; Pages the encoded table of N entries occupies (at least one).
  (declare (xargs :guard (natp n)))
  (max 1 (ceiling (* *pgs-entry-words* (nfix n)) *pgs-page-words*)))

(defun pgs-run (a m)
  (declare (xargs :guard (and (natp a) (natp m))))
  (if (zp m) nil (cons a (pgs-run (+ 1 (nfix a)) (1- m)))))

(defun pgs-ptab-physes (ptab)
  (declare (xargs :guard (pgs-ptab-p ptab)))
  (if (atom ptab) nil (cons (first (car ptab)) (pgs-ptab-physes (cdr ptab)))))

(defun pgs-rec-keeps (rec ptab)
  ; The addresses a record keeps, given the table read at its address.
  (declare (xargs :guard t))
  (append (pgs-run (pgs-rec-ptab-addr rec) (pgs-ptab-run-pages (pgs-rec-ptab-len rec)))
          (if (pgs-ptab-p ptab) (pgs-ptab-physes ptab) nil)))

(defun pgs-mark (xs fal)
  (declare (xargs :guard t))
  (if (atom xs) fal (pgs-mark (cdr xs) (hons-acons (car xs) t fal))))

(defun pgs-slots-keeps (slots pages)
  (declare (xargs :guard t))
  (let ((s0 (pgs-slot 0 slots)) (s1 (pgs-slot 1 slots)))
    (append (if (pgs-rec-valid s0)
                (pgs-rec-keeps s0 (pgs-lookup (pgs-rec-ptab-addr s0) pages)) nil)
            (if (pgs-rec-valid s1)
                (pgs-rec-keeps s1 (pgs-lookup (pgs-rec-ptab-addr s1) pages)) nil))))

(defun pgs-roots-keeps (roots pages)
  (declare (xargs :guard t))
  (if (atom roots)
      nil
    (append (and (consp (car roots)) (pgs-slots-keeps (cdar roots) pages))
            (pgs-roots-keeps (cdr roots) pages))))

(defun pgs-used (disk)
  ; The fast alist of kept addresses (model).  The host builds the same set
  ; from the tables it read (`pgs-x-used').
  (declare (xargs :guard t))
  (pgs-mark (pgs-roots-keeps (pgs-roots disk) (pgs-pages disk)) nil))

(defun pgs-free-run-p (a m used)
  (declare (xargs :guard (and (natp a) (natp m)) :measure (nfix m)))
  (if (zp m) t
    (and (not (hons-get a used)) (pgs-free-run-p (+ 1 a) (1- m) used))))

(defun pgs-find-run (a m bound used)
  ; The first A' >= A below BOUND with M free addresses from A'; nil if none.
  (declare (xargs :guard (and (natp a) (natp m) (natp bound))
                  :measure (nfix (- bound a))))
  (cond ((not (and (natp a) (natp bound) (< a bound))) nil)
        ((pgs-free-run-p a m used) a)
        (t (pgs-find-run (+ 1 a) m bound used))))

(defun pgs-find-singles (n a bound used)
  ; N free addresses from A, ascending, below BOUND (fewer if BOUND comes first).
  (declare (xargs :guard (and (natp n) (natp a) (natp bound))
                  :measure (nfix (- bound a))))
  (cond ((zp n) nil)
        ((not (and (natp a) (natp bound) (< a bound))) nil)
        ((hons-get a used) (pgs-find-singles n (+ 1 a) bound used))
        (t (cons a (pgs-find-singles (1- n) (+ 1 a) bound used)))))

(defun pgs-alloc (n m hwm used)
  ; Allocation for a commit of N dirty pages and an M-page table run, over
  ; the kept set USED whose addresses are all below HWM: the run first fit,
  ; then N singles.  Everything at or above HWM is free, so the search to
  ; HWM + M + N always succeeds; the result is (RUN-START . SINGLES), or
  ; :alloc-short (not reached when USED is below HWM; kept as a refusal
  ; rather than an assumption).
  (declare (xargs :guard (and (natp n) (natp m) (natp hwm))))
  (let* ((bound (+ hwm m n))
         (a (pgs-find-run 0 m bound used)))
    (if (not (natp a))
        :alloc-short
      (let* ((used2 (pgs-mark (pgs-run a m) used))
             (singles (pgs-find-singles n 0 bound used2)))
        (prog2$ (fast-alist-free used2)
                (if (equal (len singles) (nfix n))
                    (cons a singles)
                  :alloc-short))))))

; -----------------------------------------------------------------------------
; The commit.
;
; DIRTY is a list of (LPAGE . CONTENT); FRESH the singles, one per dirty
; page; the table after the commit replaces each dirty entry by
; (FRESH TXID DIGEST).  The planner is shared: the model hands it the
; content digests, the host the digests it computed over the stobj.

(defun pgs-update-entry (i e ptab)
  (declare (xargs :guard (and (natp i) (true-listp ptab))))
  (if (< (nfix i) (len ptab)) (update-nth (nfix i) e ptab) ptab))

(defun pgs-plan-ptab (ptab lpages fresh digests txid)
  ; Shared: LPAGES, FRESH and DIGESTS are parallel lists.
  (declare (xargs :guard (and (true-listp ptab) (nat-listp lpages)
                              (true-listp fresh) (true-listp digests))))
  (if (atom lpages)
      ptab
    (pgs-plan-ptab (pgs-update-entry (car lpages)
                                     (list (nfix (car fresh)) (nfix txid) (nfix (car digests)))
                                     ptab)
                   (cdr lpages) (cdr fresh) (cdr digests) txid)))

(defun pgs-dirty-lpages (dirty)
  (declare (xargs :guard (alistp dirty)))
  (if (atom dirty) nil (cons (nfix (caar dirty)) (pgs-dirty-lpages (cdr dirty)))))

(defun pgs-dirty-digests (dirty)
  (declare (xargs :guard (alistp dirty)))
  (if (atom dirty) nil (cons (pgs-digest (cdar dirty)) (pgs-dirty-digests (cdr dirty)))))

(defun pgs-page-writes (dirty fresh)
  ; The page writes: (ADDR . CONTENT), in dirty order.
  (declare (xargs :guard (and (alistp dirty) (true-listp fresh))))
  (if (atom dirty)
      nil
    (cons (cons (car fresh) (cdar dirty))
          (pgs-page-writes (cdr dirty) (cdr fresh)))))

(defun pgs-next-txid-of (s0 v0 s1 v1)
  ; Shared: one past the newest valid slot.
  (declare (xargs :guard t))
  (+ 1 (max (if v0 (pgs-rec-txid s0) 0) (if v1 (pgs-rec-txid s1) 0))))

(defun pgs-next-txid (slots)
  (declare (xargs :guard t))
  (pgs-next-txid-of (pgs-slot 0 slots) (pgs-rec-valid (pgs-slot 0 slots))
                    (pgs-slot 1 slots) (pgs-rec-valid (pgs-slot 1 slots))))

(defun pgs-hwm (xs)
  (declare (xargs :guard t))
  (if (atom xs) 0 (max (+ 1 (nfix (car xs))) (pgs-hwm (cdr xs)))))

(defun pgs-plan-commit (disk r mode dirty)
  ; The commit on root R of DIRTY over the state R opens on:
  ;   (:plan WRITES SLOT RECORD) where WRITES are the page writes then the
  ;   table write, and RECORD goes to SLOT (the slot the open did not use);
  ;   or (:refused REASON).  Model only (it digests contents through the
  ;   constrained seam): the host runs `pgs-x-plan', which calls the same
  ;   `pgs-alloc', `pgs-plan-ptab' and `pgs-make-rec-fields'.
  (declare (xargs :guard (alistp dirty) :verify-guards nil))
  (let* ((o (pgs-open disk r mode)))
    (if (not (and (consp o) (eq (car o) :ok) (true-listp o)))
        (list :refused :no-open-commit)
      (let* ((k (second o))
             (slots (pgs-root-slots r disk))
             (cur (pgs-slot k slots))
             (pages (pgs-pages disk))
             (ptab (pgs-lookup (pgs-rec-ptab-addr cur) pages))
             (keeps (pgs-roots-keeps (pgs-roots disk) pages))
             (used (pgs-mark keeps nil))
             (n (len dirty))
             (m (pgs-ptab-run-pages (len ptab)))
             (al (pgs-alloc n m (pgs-hwm keeps) used)))
        (prog2$
         (fast-alist-free used)
         (if (not (consp al))
             (list :refused :alloc-short)
           (let* ((txid (pgs-next-txid slots))
                  (ptab2 (pgs-plan-ptab (true-list-fix ptab) (pgs-dirty-lpages dirty)
                                        (cdr al) (pgs-dirty-digests dirty) txid))
                  (rec (pgs-make-rec txid (car al) (len ptab2) (pgs-digest ptab2)))
                  (writes (append (pgs-page-writes dirty (cdr al))
                                  (list (cons (car al) ptab2)))))
             (list :plan writes (if (equal k 1) 0 1) rec))))))))

; Applying writes.  KEEP says, per write, whether it reached the disk; the
; complete commit keeps all.  A slot write sets one slot of one root.
(defun pgs-apply-pages (writes keep pages)
  (declare (xargs :guard t))
  (if (atom writes)
      pages
    (pgs-apply-pages (cdr writes) (if (consp keep) (cdr keep) nil)
                     (if (and (or (atom keep) (car keep)) (consp (car writes)))
                         (cons (cons (car (car writes)) (cdr (car writes))) pages)
                       pages))))

(defun pgs-set-slot (k v slots)
  (declare (xargs :guard t))
  (if (equal k 1)
      (cons (pgs-slot 0 slots) v)
    (cons v (pgs-slot 1 slots))))

(defun pgs-set-root-slot (r k v disk)
  (declare (xargs :guard t))
  (cons (pgs-pages disk)
        (cons (cons r (pgs-set-slot k v (pgs-root-slots r disk)))
              (pgs-roots disk))))

(defun pgs-crash (disk r writes keep k slot-value)
  ; The image a crash leaves: the kept page writes, and SLOT-VALUE in slot K
  ; of root R (the old record, the new one, or a torn one).
  (declare (xargs :guard t))
  (pgs-set-root-slot r k slot-value
                     (cons (pgs-apply-pages writes keep (pgs-pages disk))
                           (pgs-roots disk))))

(defun pgs-commit (disk r mode dirty)
  ; The complete commit: every write, then the record.
  (declare (xargs :guard (alistp dirty) :verify-guards nil))
  (let ((p (pgs-plan-commit disk r mode dirty)))
    (if (eq (car p) :plan)
        (pgs-crash disk r (second p) nil (third p) (fourth p))
      disk)))

; The logical state after DIRTY: CONTENTS with each dirty page replaced.
(defun pgs-apply-dirty (contents dirty)
  (declare (xargs :guard (and (true-listp contents) (alistp dirty))))
  (if (atom dirty)
      contents
    (pgs-apply-dirty (if (< (nfix (caar dirty)) (len contents))
                         (update-nth (nfix (caar dirty)) (cdar dirty) contents)
                       contents)
                     (cdr dirty))))

; A fork: root R2 gets the record R opens on, in slot 0, and an empty slot 1.
(defun pgs-fork (disk r r2 mode)
  (declare (xargs :guard t))
  (let ((o (pgs-open disk r mode)))
    (if (and (consp o) (eq (car o) :ok) (true-listp o))
        (cons (pgs-pages disk)
              (cons (cons r2 (cons (pgs-slot (second o) (pgs-root-slots r disk)) nil))
                    (pgs-roots disk)))
      disk)))

; -----------------------------------------------------------------------------
; The snapshot program's process-death cuts, each a model crash point.
;
; The host (host/native/proto-pagestore.lisp, `fnps-at') names every point
; where the snapshot may die: before any write, after the K-th page write,
; after the table write, after the page file's barrier (two-barrier mode),
; with the record half-written, after the record write, after its barrier.
; A process death keeps every completed write (the page cache survives), so
; each cut is the model's `pgs-crash' with KEEP the completed prefix of the
; commit's writes and the slot old, torn or new: `pgs-cut-crash-point'.
; tools/proto/pagestore_bench.py `cut-map' checks that the host's cut names
; are exactly this list, and the campaign cuts at every one.

(defconst *pgs-snapshot-cuts*
  '(:begin :page-written :table-written :pages-synced
    :record-torn :record-written :record-synced))

(defun pgs-prefix-keep (k n)
  ; N flags, the first K true.
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp n) nil (cons (not (zp k)) (pgs-prefix-keep (if (zp k) 0 (1- k)) (1- n)))))

(defun pgs-cut-crash-point (cut k nwrites)
  ; (KEEP . SLOT) for host cut CUT (occurrence K for :page-written) in a
  ; commit of NWRITES writes (the pages, then the table): SLOT is :old,
  ; :torn or :new.
  (declare (xargs :guard (and (natp k) (natp nwrites))))
  (case cut
    (:begin (cons (pgs-prefix-keep 0 nwrites) :old))
    (:page-written (cons (pgs-prefix-keep k nwrites) :old))
    ((:table-written :pages-synced) (cons (pgs-prefix-keep nwrites nwrites) :old))
    (:record-torn (cons (pgs-prefix-keep nwrites nwrites) :torn))
    (otherwise (cons (pgs-prefix-keep nwrites nwrites) :new))))

; =============================================================================
; 5. The executable: the same decisions over words.
;
; The stobj `pgs-mem' and SHA-256 over its words are books/proto/pagestore-words.lisp.

(local (in-theory (disable floor mod truncate rem ash)))
(local (in-theory (disable nth update-nth)))
(local (in-theory (disable fn-shs-p)))

; -----------------------------------------------------------------------------
; Digests as four words (most significant first) and back.

(defun-inline pgs-u64-fix (x)
  (declare (xargs :guard t))
  (mod (nfix x) *pgs-u64-modulus*))

(local (defthm pgs-u64-of-u64-fix
  (unsigned-byte-p 64 (pgs-u64-fix x))
  :hints (("Goal" :in-theory (enable pgs-u64-fix$inline unsigned-byte-p mod)))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (pgs-u64-fix x)))
                 (:linear :corollary (< (pgs-u64-fix x) 18446744073709551616)))))

(local (in-theory (disable pgs-u64-fix$inline)))

(defun pgs-x-dig4 (base pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp base) (<= (+ base 4) (pgs-m-length pgs-mem)))))
  (+ (* (nfix (pgs-mi base pgs-mem)) 6277101735386680763835789423207666416102355444464034512896)
     (* (nfix (pgs-mi (+ 1 base) pgs-mem)) 340282366920938463463374607431768211456)
     (* (nfix (pgs-mi (+ 2 base) pgs-mem)) 18446744073709551616)
     (nfix (pgs-mi (+ 3 base) pgs-mem))))

(defun pgs-dig-word (d k)
  ; Word K (0 most significant) of the 256-bit digest D.
  (declare (xargs :guard (and (natp k) (< k 4))))
  (pgs-u64-fix (floor (nfix d) (expt 2 (* 64 (- 3 (nfix k)))))))

(defun pgs-x-put-m (i v pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (< i (pgs-m-length pgs-mem)))))
  (update-pgs-mi i (pgs-u64-fix v) pgs-mem))

(defthm pgs-m-length-of-put-m
  (implies (and (natp i) (< i (pgs-m-length pgs-mem)))
           (equal (pgs-m-length (pgs-x-put-m i v pgs-mem)) (pgs-m-length pgs-mem))))

(defthm pgs-w-length-of-put-m
  (implies (natp i)
           (equal (pgs-w-length (pgs-x-put-m i v pgs-mem)) (pgs-w-length pgs-mem))))

(defthm pgs-memp-of-put-m
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-m-length pgs-mem)))
           (pgs-memp (pgs-x-put-m i v pgs-mem))))

(in-theory (disable pgs-x-put-m))

(defun pgs-x-put-dig4 (base d pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp base) (<= (+ base 4) (pgs-m-length pgs-mem)))))
  (let* ((pgs-mem (pgs-x-put-m base (pgs-dig-word d 0) pgs-mem))
         (pgs-mem (pgs-x-put-m (+ 1 base) (pgs-dig-word d 1) pgs-mem))
         (pgs-mem (pgs-x-put-m (+ 2 base) (pgs-dig-word d 2) pgs-mem)))
    (pgs-x-put-m (+ 3 base) (pgs-dig-word d 3) pgs-mem)))

(defthm pgs-lengths-of-put-dig4
  (implies (and (natp base) (<= (+ base 4) (pgs-m-length pgs-mem)))
           (and (equal (pgs-m-length (pgs-x-put-dig4 base d pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-w-length (pgs-x-put-dig4 base d pgs-mem)) (pgs-w-length pgs-mem)))))

(defthm pgs-memp-of-put-dig4
  (implies (and (pgs-memp pgs-mem) (natp base) (<= (+ base 4) (pgs-m-length pgs-mem)))
           (pgs-memp (pgs-x-put-dig4 base d pgs-mem))))

(in-theory (disable pgs-x-put-dig4))

; -----------------------------------------------------------------------------
; The commit record, 20 words in the metadata array at BASE:
;   0 magic  1 txid  2 ptab-addr  3 ptab-len  4 page words  5-7 zero
;   8-11 ptab digest  12-15 zero  16-19 check = SHA-256 of words 0-15.
; A slot of zeros is EMPTY (nil); anything else that is not this shape is
; :torn, which `pgs-slot-refusals' names.

(defun pgs-x-zero-words-p (i n pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp n) (<= (+ i n) (pgs-m-length pgs-mem)))
                  :measure (nfix n)))
  (if (zp n)
      t
    (and (equal (pgs-mi i pgs-mem) 0)
         (pgs-x-zero-words-p (+ 1 i) (1- n) pgs-mem))))

(defun pgs-x-read-rec (base pgs-mem fn-shs)
  ; (mv RECORD CHECK fn-shs): the record the words hold (nil when empty,
  ; :torn when malformed) and the check observed over them.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp base) (<= (+ base *pgs-rec-words*) (pgs-m-length pgs-mem)))))
  (mv-let (check fn-shs)
    (pgs-x-words-digest 1 base 2 pgs-mem fn-shs)
    (mv (cond ((pgs-x-zero-words-p base *pgs-rec-words* pgs-mem) nil)
              ((and (equal (pgs-mi base pgs-mem) *pgs-magic*)
                    (equal (pgs-mi (+ 4 base) pgs-mem) *pgs-page-words*)
                    (pgs-x-zero-words-p (+ 5 base) 3 pgs-mem)
                    (pgs-x-zero-words-p (+ 12 base) 4 pgs-mem))
               (list :pgs-commit
                     (pgs-mi (+ 1 base) pgs-mem) (pgs-mi (+ 2 base) pgs-mem)
                     (pgs-mi (+ 3 base) pgs-mem) (pgs-x-dig4 (+ 8 base) pgs-mem)
                     (pgs-x-dig4 (+ 16 base) pgs-mem)))
              (t :torn))
        check
        fn-shs)))

(defun pgs-x-zero-m (i n pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp n) (<= (+ i n) (pgs-m-length pgs-mem)))
                  :measure (nfix n)))
  (if (zp n)
      pgs-mem
    (let ((pgs-mem (pgs-x-put-m i 0 pgs-mem)))
      (pgs-x-zero-m (+ 1 i) (1- n) pgs-mem))))

(defthm pgs-lengths-of-zero-m
  (implies (and (natp i) (natp n) (<= (+ i n) (pgs-m-length pgs-mem)))
           (and (equal (pgs-m-length (pgs-x-zero-m i n pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-w-length (pgs-x-zero-m i n pgs-mem)) (pgs-w-length pgs-mem)))))

(defthm pgs-memp-of-zero-m
  (implies (and (pgs-memp pgs-mem) (natp i) (natp n) (<= (+ i n) (pgs-m-length pgs-mem)))
           (pgs-memp (pgs-x-zero-m i n pgs-mem))))

(in-theory (disable pgs-x-zero-m))

(defun pgs-x-write-rec (base txid addr len pdig pgs-mem fn-shs)
  ; Encode the record at BASE and compute its check: (mv RECORD pgs-mem fn-shs).
  ; RECORD is `pgs-x-read-rec' of the words (the check over the words that
  ; were written).
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp base) (<= (+ base *pgs-rec-words*) (pgs-m-length pgs-mem)))))
  (let* ((pgs-mem (pgs-x-zero-m base *pgs-rec-words* pgs-mem))
         (pgs-mem (pgs-x-put-m base *pgs-magic* pgs-mem))
         (pgs-mem (pgs-x-put-m (+ 1 base) txid pgs-mem))
         (pgs-mem (pgs-x-put-m (+ 2 base) addr pgs-mem))
         (pgs-mem (pgs-x-put-m (+ 3 base) len pgs-mem))
         (pgs-mem (pgs-x-put-m (+ 4 base) *pgs-page-words* pgs-mem))
         (pgs-mem (pgs-x-put-dig4 (+ 8 base) pdig pgs-mem)))
    (mv-let (check fn-shs)
      (pgs-x-words-digest 1 base 2 pgs-mem fn-shs)
      (let ((pgs-mem (pgs-x-put-dig4 (+ 16 base) check pgs-mem)))
        (mv (list :pgs-commit (pgs-u64-fix txid) (pgs-u64-fix addr) (pgs-u64-fix len)
                  (pgs-x-dig4 (+ 8 base) pgs-mem) check)
            pgs-mem fn-shs)))))

; -----------------------------------------------------------------------------
; The page table, 6 words per entry (phys, txid, digest) from BASE; the run
; is zero-padded to whole pages and digested whole.

(defun pgs-x-decode-ptab (j n base acc pgs-mem)
  ; Entries J..N-1, consed onto ACC in reverse; the caller reverses.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp j) (natp n) (natp base) (<= j n)
                              (<= (+ base (* 6 n)) (pgs-m-length pgs-mem)))
                  :measure (nfix (- (nfix n) (nfix j)))))
  (if (mbe :logic (zp (- (nfix n) (nfix j))) :exec (= j n))
      acc
    (let ((b (+ base (* 6 j))))
      (pgs-x-decode-ptab (+ 1 (nfix j)) n base
                         (cons (list (pgs-mi b pgs-mem) (pgs-mi (+ 1 b) pgs-mem)
                                     (pgs-x-dig4 (+ 2 b) pgs-mem))
                               acc)
                         pgs-mem))))

(defun pgs-x-encode-ptab (ptab j base pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (pgs-ptab-p ptab) (natp j) (natp base)
                              (<= (+ base (* 6 (+ j (len ptab)))) (pgs-m-length pgs-mem)))
                  :measure (len ptab)))
  (if (atom ptab)
      pgs-mem
    (let* ((e (car ptab))
           (b (+ base (* 6 j)))
           (pgs-mem (pgs-x-put-m b (first e) pgs-mem))
           (pgs-mem (pgs-x-put-m (+ 1 b) (second e) pgs-mem))
           (pgs-mem (pgs-x-put-dig4 (+ 2 b) (third e) pgs-mem)))
      (pgs-x-encode-ptab (cdr ptab) (+ 1 j) base pgs-mem))))

; -----------------------------------------------------------------------------
; Verification of the resident image (the open), and at first touch.

(defun pgs-x-verify (ptab i txid mode pgs-mem fn-shs)
  ; (mv BAD pgs-mem fn-shs): BAD is nil when every page the mode checks
  ; verifies (each is flagged verified), else (:page-damaged I PHYS) for the
  ; first that does not: `pgs-check-pages' over the observed digests.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (pgs-ptab-p ptab) (natp i)
                              (<= (* (+ i (len ptab)) *pgs-page-words*) (pgs-w-length pgs-mem))
                              (<= (+ i (len ptab)) (pgs-v-length pgs-mem)))
                  :measure (len ptab)))
  (if (atom ptab)
      (mv nil pgs-mem fn-shs)
    (let ((e (car ptab)))
      (if (pgs-entry-checked-p e txid mode)
          (mv-let (d fn-shs)
            (pgs-x-page-digest i pgs-mem fn-shs)
            (if (eq (pgs-entry-verdict e txid mode d) :damaged)
                (mv (list :page-damaged i (first e)) pgs-mem fn-shs)
              (let ((pgs-mem (update-pgs-vi i 1 pgs-mem)))
                (pgs-x-verify (cdr ptab) (+ 1 i) txid mode pgs-mem fn-shs))))
        (pgs-x-verify (cdr ptab) (+ 1 i) txid mode pgs-mem fn-shs)))))

(defun pgs-x-touch (i tbase pgs-mem fn-shs)
  ; Lazy mode, first touch of resident page I: :ok (now flagged verified)
  ; or :damaged, against the table entry encoded at TBASE.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp i) (natp tbase)
                              (< i (pgs-v-length pgs-mem))
                              (<= (* (+ 1 i) *pgs-page-words*) (pgs-w-length pgs-mem))
                              (<= (+ tbase (* 6 (+ 1 i))) (pgs-m-length pgs-mem)))))
  (if (equal (pgs-vi i pgs-mem) 1)
      (mv :ok pgs-mem fn-shs)
    (mv-let (d fn-shs)
      (pgs-x-page-digest i pgs-mem fn-shs)
      (let ((b (+ tbase (* 6 i))))
        (if (eq (pgs-entry-verdict (list (pgs-mi b pgs-mem) (pgs-mi (+ 1 b) pgs-mem)
                                         (pgs-x-dig4 (+ 2 b) pgs-mem))
                                   0 :eager d)
                :damaged)
            (mv :damaged pgs-mem fn-shs)
          (let ((pgs-mem (update-pgs-vi i 1 pgs-mem)))
            (mv :ok pgs-mem fn-shs)))))))

(defthm pgs-stobjs-of-x-touch
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs) (natp i) (< i (pgs-v-length pgs-mem)))
           (and (pgs-memp (mv-nth 1 (pgs-x-touch i tbase pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 2 (pgs-x-touch i tbase pgs-mem fn-shs)))
                (equal (pgs-w-length (mv-nth 1 (pgs-x-touch i tbase pgs-mem fn-shs))) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (mv-nth 1 (pgs-x-touch i tbase pgs-mem fn-shs))) (pgs-m-length pgs-mem))
                (equal (pgs-v-length (mv-nth 1 (pgs-x-touch i tbase pgs-mem fn-shs))) (pgs-v-length pgs-mem))
                (equal (pgs-d-length (mv-nth 1 (pgs-x-touch i tbase pgs-mem fn-shs))) (pgs-d-length pgs-mem)))))

(in-theory (disable pgs-x-touch))

; -----------------------------------------------------------------------------
; Writers and the dirty bitmap (one flag word per page).

(defun pgs-x-put (lp off v pgs-mem)
  ; Word OFF of resident page LP := V, and LP is dirty.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp lp) (natp off) (< off *pgs-page-words*)
                              (< lp (pgs-d-length pgs-mem))
                              (<= (* (+ 1 lp) *pgs-page-words*) (pgs-w-length pgs-mem)))))
  (let ((pgs-mem (update-pgs-wi (+ (* lp *pgs-page-words*) off) (pgs-u64-fix v) pgs-mem)))
    (update-pgs-di lp 1 pgs-mem)))

(defun pgs-x-dirty-list (j acc pgs-mem)
  ; The dirty pages below J, ascending, onto ACC.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp j) (<= j (pgs-d-length pgs-mem)))
                  :measure (nfix j)))
  (if (zp j)
      acc
    (pgs-x-dirty-list (1- j)
                      (if (equal (pgs-di (1- j) pgs-mem) 1) (cons (1- j) acc) acc)
                      pgs-mem)))

(defun pgs-x-lpages-fit (lpages n)
  (declare (xargs :guard t))
  (if (atom lpages)
      (null lpages)
    (and (natp (car lpages)) (< (car lpages) (nfix n))
         (pgs-x-lpages-fit (cdr lpages) n))))

(defun pgs-x-clear-dirty (lpages pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (pgs-x-lpages-fit lpages (pgs-d-length pgs-mem))))
  (if (atom lpages)
      pgs-mem
    (let ((pgs-mem (update-pgs-di (car lpages) 0 pgs-mem)))
      (pgs-x-clear-dirty (cdr lpages) pgs-mem))))

(defun pgs-x-dirty-digests (lpages pgs-mem fn-shs)
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (pgs-x-lpages-fit lpages (pgs-d-length pgs-mem))
                              (<= (* (pgs-d-length pgs-mem) *pgs-page-words*)
                                  (pgs-w-length pgs-mem)))))
  (if (atom lpages)
      (mv nil fn-shs)
    (mv-let (d fn-shs)
      (pgs-x-page-digest (car lpages) pgs-mem fn-shs)
      (mv-let (ds fn-shs)
        (pgs-x-dirty-digests (cdr lpages) pgs-mem fn-shs)
        (mv (cons d ds) fn-shs)))))

(defthm pgs-nat-listp-of-lpages-fit
  (implies (pgs-x-lpages-fit lpages n) (nat-listp lpages)))

(defthm pgs-true-listp-of-dirty-digests
  (and (true-listp (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-shs)))
       (true-listp (car (pgs-x-dirty-digests lpages pgs-mem fn-shs)))))

(defthm pgs-true-listp-of-find-singles
  (true-listp (pgs-find-singles n a bound used)))

(defthm pgs-alloc-shape
  (implies (consp (pgs-alloc n m hwm used))
           (true-listp (cdr (pgs-alloc n m hwm used)))))

(defthm pgs-ptab-run-pages-posp
  (and (integerp (pgs-ptab-run-pages n)) (< 0 (pgs-ptab-run-pages n)))
  :rule-classes ((:type-prescription :corollary (integerp (pgs-ptab-run-pages n)))
                 (:linear :corollary (< 0 (pgs-ptab-run-pages n)))))

(in-theory (disable pgs-alloc pgs-x-dirty-digests pgs-ptab-run-pages))

(defun pgs-x-keeps (pairs)
  ; The kept addresses of every valid record the host read: PAIRS is a list
  ; of (RECORD . TABLE).
  (declare (xargs :guard t))
  (if (atom pairs)
      nil
    (append (and (consp (car pairs)) (pgs-rec-keeps (caar pairs) (cdar pairs)))
            (pgs-x-keeps (cdr pairs)))))

(defun pgs-x-plan (ptab lpages pairs txid pgs-mem fn-shs)
  ; The host's commit decision: (mv (RUN-START SINGLES PTAB2) fn-shs), or
  ; (mv :alloc-short fn-shs).  The same `pgs-alloc' and `pgs-plan-ptab' as
  ; `pgs-plan-commit', over the digests observed in the stobj.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (true-listp ptab)
                              (pgs-x-lpages-fit lpages (pgs-d-length pgs-mem))
                              (<= (* (pgs-d-length pgs-mem) *pgs-page-words*)
                                  (pgs-w-length pgs-mem)))))
  (let* ((keeps (pgs-x-keeps pairs))
         (used (pgs-mark keeps nil))
         (al (pgs-alloc (len lpages) (pgs-ptab-run-pages (len ptab)) (pgs-hwm keeps) used)))
    (prog2$
     (fast-alist-free used)
     (if (not (consp al))
         (mv :alloc-short fn-shs)
       (mv-let (digests fn-shs)
         (pgs-x-dirty-digests lpages pgs-mem fn-shs)
         (mv (list (car al) (cdr al)
                   (pgs-plan-ptab ptab lpages (cdr al) digests txid))
             fn-shs))))))

; -----------------------------------------------------------------------------
; Reads through the store, and the two first requests (a lookup by sequence,
; a lookup by Message-ID) over the fn-hist-shaped columns.
;
; Every read is bounds-checked at run time (the words came from a file) and,
; in lazy mode, verifies its page at first touch; a failed check is a
; refusal by name, never a value.  Layout (logical page 0, the header):
;   0 magic "FNPSCOLS"  1 N records  2 HBITS (table of 2^HBITS slots)
;   3 OFF: word index of the offsets column (N words: pool byte offsets)
;   4 TAB: word index of the Message-ID table (slot = sequence + 1, 0 empty)
;   5 POOL: word index of the byte pool   6 pool words   7 salt
; A pool entry at byte offset O (8-aligned): its first word holds the
; Message-ID length L (bits 0-15) and the row length R (bits 16-31); the
; Message-ID's octets follow from O + 8, then the row's.

(defconst *pgs-cols-magic* #x534C4F4353504E46)   ; "FNPSCOLS", little-endian

(defun pgs-x-rd (i lazy tbase pgs-mem fn-shs)
  ; (mv VERDICT WORD pgs-mem fn-shs): VERDICT :ok, :out-of-range, or
  ; (:page-damaged LP).
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (natp i) (natp tbase))))
  (let ((lp (nfix (floor (nfix i) *pgs-page-words*))))
    (if (not (and (natp i) (natp tbase)
                  (< i (pgs-w-length pgs-mem)) (< lp (pgs-v-length pgs-mem))
                  (<= (* (+ 1 lp) *pgs-page-words*) (pgs-w-length pgs-mem))
                  (<= (+ tbase (* 6 (+ 1 lp))) (pgs-m-length pgs-mem))))
        (mv :out-of-range 0 pgs-mem fn-shs)
      (if lazy
          (mv-let (v pgs-mem fn-shs)
            (pgs-x-touch lp tbase pgs-mem fn-shs)
            (if (eq v :ok)
                (mv :ok (pgs-wi i pgs-mem) pgs-mem fn-shs)
              (mv (list :page-damaged lp) 0 pgs-mem fn-shs)))
        (mv :ok (pgs-wi i pgs-mem) pgs-mem fn-shs)))))

(defthm pgs-stobjs-of-x-rd
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-rd i lazy tbase pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-rd i lazy tbase pgs-mem fn-shs)))
                (equal (pgs-w-length (mv-nth 2 (pgs-x-rd i lazy tbase pgs-mem fn-shs))) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (mv-nth 2 (pgs-x-rd i lazy tbase pgs-mem fn-shs))) (pgs-m-length pgs-mem))
                (equal (pgs-v-length (mv-nth 2 (pgs-x-rd i lazy tbase pgs-mem fn-shs))) (pgs-v-length pgs-mem))
                (equal (pgs-d-length (mv-nth 2 (pgs-x-rd i lazy tbase pgs-mem fn-shs))) (pgs-d-length pgs-mem)))))

(defun pgs-byte-of-word (w k)
  (declare (xargs :guard (and (natp w) (natp k))))
  (mod (floor (nfix w) (expt 2 (* 8 (mod (nfix k) 8)))) 256))

(defun pgs-x-pool-byte (o pool lazy tbase pgs-mem fn-shs)
  ; Octet O of the pool that starts at word POOL.
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp o) (natp pool) (natp tbase))))
  (mv-let (v w pgs-mem fn-shs)
    (pgs-x-rd (+ pool (floor o 8)) lazy tbase pgs-mem fn-shs)
    (mv v (pgs-byte-of-word w o) pgs-mem fn-shs)))

(defthm pgs-stobjs-of-x-pool-byte
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-pool-byte o pool lazy tbase pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-pool-byte o pool lazy tbase pgs-mem fn-shs)))
                (equal (pgs-w-length (mv-nth 2 (pgs-x-pool-byte o pool lazy tbase pgs-mem fn-shs))) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (mv-nth 2 (pgs-x-pool-byte o pool lazy tbase pgs-mem fn-shs))) (pgs-m-length pgs-mem))
                (equal (pgs-v-length (mv-nth 2 (pgs-x-pool-byte o pool lazy tbase pgs-mem fn-shs))) (pgs-v-length pgs-mem))
                (equal (pgs-d-length (mv-nth 2 (pgs-x-pool-byte o pool lazy tbase pgs-mem fn-shs))) (pgs-d-length pgs-mem)))))

(in-theory (disable pgs-x-rd pgs-x-pool-byte))

(defun pgs-x-pool-bytes (o n pool lazy tbase acc pgs-mem fn-shs)
  ; N octets from O, reversed onto ACC (the caller reverses).
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (natp o) (natp n) (natp pool) (natp tbase) (true-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      (mv :ok acc pgs-mem fn-shs)
    (mv-let (v b pgs-mem fn-shs)
      (pgs-x-pool-byte o pool lazy tbase pgs-mem fn-shs)
      (if (not (eq v :ok))
          (mv v acc pgs-mem fn-shs)
        (pgs-x-pool-bytes (+ 1 o) (1- n) pool lazy tbase (cons b acc) pgs-mem fn-shs)))))

(defthm pgs-true-listp-of-pool-bytes
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (pgs-x-pool-bytes o n pool lazy tbase acc pgs-mem fn-shs)))))

(defthm pgs-stobjs-of-x-pool-bytes
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-pool-bytes o n pool lazy tbase acc pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-pool-bytes o n pool lazy tbase acc pgs-mem fn-shs)))
                (equal (pgs-w-length (mv-nth 2 (pgs-x-pool-bytes o n pool lazy tbase acc pgs-mem fn-shs))) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (mv-nth 2 (pgs-x-pool-bytes o n pool lazy tbase acc pgs-mem fn-shs))) (pgs-m-length pgs-mem))
                (equal (pgs-v-length (mv-nth 2 (pgs-x-pool-bytes o n pool lazy tbase acc pgs-mem fn-shs))) (pgs-v-length pgs-mem))
                (equal (pgs-d-length (mv-nth 2 (pgs-x-pool-bytes o n pool lazy tbase acc pgs-mem fn-shs))) (pgs-d-length pgs-mem)))))

(in-theory (disable pgs-x-pool-bytes))

(defun pgs-x-header (k lazy tbase pgs-mem fn-shs)
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (natp k) (natp tbase))))
  (pgs-x-rd k lazy tbase pgs-mem fn-shs))

(defthm pgs-stobjs-of-x-header
  (implies (and (pgs-memp pgs-mem) (fn-shs-p fn-shs))
           (and (pgs-memp (mv-nth 2 (pgs-x-header k lazy tbase pgs-mem fn-shs)))
                (fn-shs-p (mv-nth 3 (pgs-x-header k lazy tbase pgs-mem fn-shs)))
                (equal (pgs-w-length (mv-nth 2 (pgs-x-header k lazy tbase pgs-mem fn-shs))) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (mv-nth 2 (pgs-x-header k lazy tbase pgs-mem fn-shs))) (pgs-m-length pgs-mem))
                (equal (pgs-v-length (mv-nth 2 (pgs-x-header k lazy tbase pgs-mem fn-shs))) (pgs-v-length pgs-mem))
                (equal (pgs-d-length (mv-nth 2 (pgs-x-header k lazy tbase pgs-mem fn-shs))) (pgs-d-length pgs-mem)))))

(in-theory (disable pgs-x-header))

(defun pgs-x-entry (seq lazy tbase pgs-mem fn-shs)
  ; (mv VERDICT (O L R) pgs-mem fn-shs) for record SEQ.
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (natp seq) (natp tbase))))
  (mv-let (v0 magic pgs-mem fn-shs) (pgs-x-header 0 lazy tbase pgs-mem fn-shs)
    (mv-let (v1 n pgs-mem fn-shs) (pgs-x-header 1 lazy tbase pgs-mem fn-shs)
      (mv-let (v3 off pgs-mem fn-shs) (pgs-x-header 3 lazy tbase pgs-mem fn-shs)
        (mv-let (v5 pool pgs-mem fn-shs) (pgs-x-header 5 lazy tbase pgs-mem fn-shs)
          (cond ((not (and (eq v0 :ok) (eq v1 :ok) (eq v3 :ok) (eq v5 :ok)))
                 (mv :header-unreadable nil pgs-mem fn-shs))
                ((not (equal magic *pgs-cols-magic*))
                 (mv :header-malformed nil pgs-mem fn-shs))
                ((not (< seq (nfix n)))
                 (mv :no-such-sequence nil pgs-mem fn-shs))
                (t
                 (mv-let (v o pgs-mem fn-shs)
                   (pgs-x-rd (+ (nfix off) seq) lazy tbase pgs-mem fn-shs)
                   (if (not (eq v :ok))
                       (mv v nil pgs-mem fn-shs)
                     (mv-let (v h pgs-mem fn-shs)
                       (pgs-x-rd (+ (nfix pool) (floor (nfix o) 8)) lazy tbase pgs-mem fn-shs)
                       (if (not (eq v :ok))
                           (mv v nil pgs-mem fn-shs)
                         (mv :ok (list (nfix o) (mod (nfix h) 65536)
                                       (mod (floor (nfix h) 65536) 65536)
                                       (nfix pool))
                             pgs-mem fn-shs))))))))))))

(in-theory (disable pgs-x-entry))

(defun pgs-x-lookup-seq (seq lazy tbase pgs-mem fn-shs)
  ; The first request by sequence: (mv VERDICT MSGID-OCTETS pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (natp seq) (natp tbase))))
  (mv-let (v e pgs-mem fn-shs)
    (pgs-x-entry seq lazy tbase pgs-mem fn-shs)
    (if (not (and (eq v :ok) (true-listp e) (= (len e) 4)))
        (mv v nil pgs-mem fn-shs)
      (mv-let (v bytes pgs-mem fn-shs)
        (pgs-x-pool-bytes (+ 8 (nfix (first e))) (nfix (second e)) (nfix (fourth e))
                          lazy tbase nil pgs-mem fn-shs)
        (mv v (revappend bytes nil) pgs-mem fn-shs)))))

(defthm pgs-true-listp-of-revappend
  (implies (true-listp y) (true-listp (revappend x y))))

(defthm pgs-true-listp-of-lookup-seq
  (true-listp (mv-nth 1 (pgs-x-lookup-seq seq lazy tbase pgs-mem fn-shs))))

(in-theory (disable pgs-x-lookup-seq))

(defun pgs-fnv (s i h)
  ; FNV-1a, 32 bits, over the octets of S from I.
  (declare (xargs :guard (and (stringp s) (natp i) (natp h))
                  :measure (nfix (- (length s) (nfix i)))))
  (if (and (stringp s) (natp i) (< i (length s)))
      (pgs-fnv s (1+ i) (mod (* (logxor (nfix h) (char-code (char s i))) 16777619)
                            4294967296))
    (nfix h)))

(defun pgs-x-octets-match (s i bytes)
  (declare (xargs :guard (and (stringp s) (natp i) (true-listp bytes))
                  :measure (len bytes)))
  (if (atom bytes)
      (and (natp i) (= i (length s)))
    (and (natp i) (< i (length s))
         (equal (char-code (char s i)) (car bytes))
         (pgs-x-octets-match s (+ 1 i) (cdr bytes)))))

(defun pgs-x-probe (s slot k size tab lazy tbase pgs-mem fn-shs)
  ; Walk the table from SLOT for at most K slots; every candidate is
  ; compared exactly.  (mv VERDICT SEQ-OR-NIL pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs)
                  :guard (and (stringp s) (natp slot) (natp k) (natp size)
                              (natp tab) (natp tbase))
                  :measure (nfix k)))
  (if (zp k)
      (mv :ok nil pgs-mem fn-shs)
    (mv-let (v x pgs-mem fn-shs)
      (pgs-x-rd (+ tab slot) lazy tbase pgs-mem fn-shs)
      (cond ((not (eq v :ok)) (mv v nil pgs-mem fn-shs))
            ((equal x 0) (mv :ok nil pgs-mem fn-shs))
            ((not (posp x)) (mv :table-malformed nil pgs-mem fn-shs))
            (t (mv-let (v bytes pgs-mem fn-shs)
                 (pgs-x-lookup-seq (1- (nfix x)) lazy tbase pgs-mem fn-shs)
                 (cond ((not (eq v :ok)) (mv v nil pgs-mem fn-shs))
                       ((pgs-x-octets-match s 0 bytes) (mv :ok (1- (nfix x)) pgs-mem fn-shs))
                       (t (pgs-x-probe s (if (< (+ 1 slot) size) (+ 1 slot) 0) (1- k)
                                       size tab lazy tbase pgs-mem fn-shs)))))))))

(defun pgs-msgid-start (s salt size)
  (declare (xargs :guard (and (stringp s) (posp size))))
  (mod (pgs-fnv s 0 (mod (logxor 2166136261 (nfix salt)) 4294967296)) size))

(defthm pgs-natp-of-msgid-start
  (implies (posp size) (natp (pgs-msgid-start s salt size)))
  :rule-classes :type-prescription)

(in-theory (disable pgs-msgid-start))

(defun pgs-x-lookup-msgid (s lazy tbase pgs-mem fn-shs)
  ; The first request by Message-ID: (mv VERDICT SEQ-OR-NIL pgs-mem fn-shs).
  (declare (xargs :stobjs (pgs-mem fn-shs) :guard (and (stringp s) (natp tbase))))
  (mv-let (v2 hbits pgs-mem fn-shs) (pgs-x-header 2 lazy tbase pgs-mem fn-shs)
    (mv-let (v4 tab pgs-mem fn-shs) (pgs-x-header 4 lazy tbase pgs-mem fn-shs)
      (mv-let (v7 salt pgs-mem fn-shs) (pgs-x-header 7 lazy tbase pgs-mem fn-shs)
        (let ((size (expt 2 (nfix hbits))))
          (if (not (and (eq v2 :ok) (eq v4 :ok) (eq v7 :ok) (< (nfix hbits) 40) (posp size)))
              (mv :header-unreadable nil pgs-mem fn-shs)
            (pgs-x-probe s (pgs-msgid-start s salt size) size size (nfix tab)
                         lazy tbase pgs-mem fn-shs)))))))
