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
;   The digest is BLAKE3 over the page's octets computed HERE: the words
;   are copied into the page store's octet buffer and hashed in place by
;   books/blake3-stobj.lisp (books/pagestore-words.lisp).  The shared
;   decisions (`pgs-alloc', `pgs-plan-ptab', `pgs-open-order',
;   `pgs-entry-verdict', the record fields) are the SAME functions in both
;   layers; what differs is only how a digest is observed.
;
; The boundary, named (prototype; not yet theorems):
;   A-PGS-OBSERVE: the words the fill primitive leaves in the stobj are the
;     page's content, and `pgs-x-words-digest' of them is `pgs-digest' of
;     that content (the BLAKE3 part is proved: `pgs-x-words-digest' is
;     `fn-blake3' of the words' little-endian octets,
;     `pgs-x-words-digest-is-blake3' in books/pagestore-words-blake3.lisp;
;     `fn-blake3' is what `fn-digest' is attached to);
;     `pgs-x-decode-ptab' of the encoded table is the table.
;   A-CRYPTO (books/crypto-seam.lisp, books/assumptions.lisp): the torn-write
;     keystone takes, as a HYPOTHESIS, that a stale page at a fresh address
;     whose digest equals the intended page's digest IS that page
;     (`pgs-writes-faithful'); the test book shows the conclusion fails for a
;     colliding digest.  BLAKE3-256's pessimistic figure is the collision
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
; A table is a list of entries (PHYS TXID DIGEST): the page's address, the
; commit that wrote it, and its content's digest.  The page table of a
; commit has TWO LEVELS: the flat table (one entry per logical page) is cut
; into TABLE PAGES of *pgs-tab-entries* entries (`pgs-chunk'; the last one
; partial), each stored in a page of its own, and the DIRECTORY (one entry
; per table page, the same entry shape) is stored in a run of pages the
; record names.  A commit rewrites only the table pages holding a dirty
; entry, and the directory.  A commit record is
;   (:pgs-commit TXID DIR-ADDR NPAGES DIR-DIGEST CHECK)
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

(defun pgs-make-rec (txid dir-addr npages dir-digest)
  (declare (xargs :guard t))
  (let ((body (list :pgs-commit txid dir-addr npages dir-digest)))
    (append body (list (pgs-digest body)))))

(defun pgs-rec-txid (x) (declare (xargs :guard t)) (nfix (second (true-list-fix x))))
(defun pgs-rec-dir-addr (x) (declare (xargs :guard t)) (nfix (third (true-list-fix x))))
(defun pgs-rec-npages (x) (declare (xargs :guard t)) (nfix (fourth (true-list-fix x))))
(defun pgs-rec-dir-digest (x) (declare (xargs :guard t)) (nfix (fifth (true-list-fix x))))

; Pages: an alist from address to content; a write is an acons.
(defun pgs-lookup (a pages)
  (declare (xargs :guard t))
  (cdr (hons-assoc-equal a pages)))

; The page verdict (shared).  In :eager mode every entry is checked; in
; :lazy mode only the entries the commit itself wrote (TXID equal to the
; record's), which are the only ones its own crash can have left unwritten;
; the rest are checked on first touch.
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

(defun pgs-check-pages (ptab txid mode pages i tag)
  ; nil when every checked page of PTAB verifies; else (TAG I PHYS), TAG
  ; :table-damaged for the directory's pages, :page-damaged for the table's.
  (declare (xargs :guard (and (pgs-ptab-p ptab) (natp i))))
  (if (atom ptab)
      nil
    (let ((e (car ptab)))
      (if (eq (pgs-entry-verdict e txid mode (pgs-digest (pgs-lookup (first e) pages)))
              :damaged)
          (list tag i (first e))
        (pgs-check-pages (cdr ptab) txid mode pages (+ 1 i) tag)))))

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

; -----------------------------------------------------------------------------
; Table pages.

(defconst *pgs-entry-words* 6)          ; phys, txid, four digest words
(defconst *pgs-tab-entries* 341)        ; entries per table page: floor(2048 / 6)

(defun pgs-ntables (n)
  ; The table pages of a table of N entries.
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) 0 (+ 1 (pgs-ntables (- n *pgs-tab-entries*))))))

(defthm pgs-len-of-nthcdr
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n x))))

(defun pgs-chunk (x)
  ; The flat table X as its table pages.
  (declare (xargs :guard (true-listp x) :measure (len x)))
  (if (atom x)
      nil
    (cons (take (min *pgs-tab-entries* (len x)) x)
          (pgs-chunk (nthcdr *pgs-tab-entries* x)))))

(defun pgs-flatten (cs)
  (declare (xargs :guard t))
  (if (atom cs) nil (append (true-list-fix (car cs)) (pgs-flatten (cdr cs)))))

; The directory's verdict (shared): nil when the directory read at the
; record's address has the record's digest, one entry per table page of
; NPAGES entries, and no entry newer than the record; else the refusal.
(defun pgs-dir-verdict (rec dir observed)
  (declare (xargs :guard t))
  (let ((addr (pgs-rec-dir-addr rec)))
    (cond ((not (equal observed (pgs-rec-dir-digest rec)))
           (list :dir-damaged addr))
          ((not (and (pgs-ptab-p dir)
                     (equal (len dir) (pgs-ntables (pgs-rec-npages rec)))
                     (pgs-ptab-txids-ok dir (pgs-rec-txid rec))))
           (list :dir-malformed addr))
          (t nil))))

; The table pages' verdict (shared; the host checks each table page as it
; decodes it): table page I is a table of min(E, REM) entries, REM the
; entries from it on, none newer than the record.
(defun pgs-table-ok (c rem txid)
  (declare (xargs :guard t))
  (and (pgs-ptab-p c)
       (equal (len c) (min *pgs-tab-entries* (nfix rem)))
       (pgs-ptab-txids-ok c txid)))

(defun pgs-tables-verdict (cs rem txid i)
  (declare (xargs :guard (natp i)))
  (if (atom cs)
      nil
    (if (pgs-table-ok (car cs) rem txid)
        (pgs-tables-verdict (cdr cs) (- (nfix rem) *pgs-tab-entries*) txid (+ 1 i))
      (list :table-malformed i))))

(defthm pgs-ptab-p-of-append
  (implies (and (pgs-ptab-p a) (pgs-ptab-p b))
           (pgs-ptab-p (append a b))))

(defthm pgs-ptab-p-true-listp
  (implies (pgs-ptab-p x) (true-listp x))
  :rule-classes (:forward-chaining :rewrite))

(defthm pgs-true-list-fix-when-true-listp
  (implies (true-listp x) (equal (true-list-fix x) x)))

(defthm pgs-ptab-p-of-flatten-when-tables-ok
  (implies (not (pgs-tables-verdict cs rem txid i))
           (pgs-ptab-p (pgs-flatten cs))))

; Try one record: (:ok TXID CONTENTS) or (:refused REASON ...).
(defun pgs-try (rec pages mode)
  (declare (xargs :guard (pgs-rec-shape-p rec)))
  (let* ((txid (pgs-rec-txid rec))
         (dir (pgs-lookup (pgs-rec-dir-addr rec) pages))
         (dv (pgs-dir-verdict rec dir (pgs-digest dir))))
    (if dv
        (cons :refused dv)
      (let ((tbad (pgs-check-pages dir txid mode pages 0 :table-damaged)))
        (if tbad
            (cons :refused tbad)
          (let* ((cs (pgs-contents dir pages))
                 (tv (pgs-tables-verdict cs (pgs-rec-npages rec) txid 0)))
            (if tv
                (cons :refused tv)
              (let* ((ptab (pgs-flatten cs))
                     (bad (pgs-check-pages ptab txid mode pages 0 :page-damaged)))
                (if bad
                    (cons :refused bad)
                  (list :ok txid (pgs-contents ptab pages)))))))))))

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
; The live set (shared).
;
; A valid record keeps its directory run (DIR-ADDR and the pages after it
; the encoded directory occupies), every table page its directory names and
; every page its table names.  Fresh space is any address no valid record of
; any root keeps.

(defun pgs-ptab-run-pages (n)
  ; Pages the encoded table of N entries occupies (at least one).
  (declare (xargs :guard (natp n)))
  (max 1 (ceiling (* *pgs-entry-words* (nfix n)) *pgs-page-words*)))

(defun pgs-dir-run-pages (npages)
  ; Pages a directory for NPAGES logical pages occupies.
  (declare (xargs :guard t))
  (pgs-ptab-run-pages (pgs-ntables npages)))

(defun pgs-run (a m)
  (declare (xargs :guard (and (natp a) (natp m))))
  (if (zp m) nil (cons a (pgs-run (+ 1 (nfix a)) (1- m)))))

(defun pgs-ptab-physes (ptab)
  (declare (xargs :guard (pgs-ptab-p ptab)))
  (if (atom ptab) nil (cons (first (car ptab)) (pgs-ptab-physes (cdr ptab)))))

(defun pgs-rec-keeps (rec dir tables)
  ; The addresses a record keeps, given its directory DIR (read at its
  ; address) and TABLES, the contents of the pages DIR names.
  (declare (xargs :guard t))
  (append (pgs-run (pgs-rec-dir-addr rec) (pgs-dir-run-pages (pgs-rec-npages rec)))
          (if (pgs-ptab-p dir)
              (append (pgs-ptab-physes dir)
                      (let ((ptab (pgs-flatten tables)))
                        (if (pgs-ptab-p ptab) (pgs-ptab-physes ptab) nil)))
            nil)))

(defun pgs-rec-keeps-in (rec pages)
  (declare (xargs :guard t))
  (let ((dir (pgs-lookup (pgs-rec-dir-addr rec) pages)))
    (pgs-rec-keeps rec dir (if (pgs-ptab-p dir) (pgs-contents dir pages) nil))))

(defun pgs-slots-keeps (slots pages)
  (declare (xargs :guard t))
  (let ((s0 (pgs-slot 0 slots)) (s1 (pgs-slot 1 slots)))
    (append (if (pgs-rec-valid s0) (pgs-rec-keeps-in s0 pages) nil)
            (if (pgs-rec-valid s1) (pgs-rec-keeps-in s1 pages) nil))))

(defun pgs-roots-keeps (roots pages seen)
  ; The live bindings only: a root's first binding in ROOTS is the one
  ; `pgs-root-slots' reads; SEEN holds the names already visited.
  (declare (xargs :guard (true-listp seen)))
  (if (atom roots)
      nil
    (append (and (consp (car roots)) (not (member-equal (caar roots) seen))
                 (pgs-slots-keeps (cdar roots) pages))
            (pgs-roots-keeps (cdr roots) pages
                             (if (consp (car roots)) (cons (caar roots) seen) seen)))))

(defconst *pgs-reserved-page* 0)   ; the page holding the owner's root slots

(defun pgs-disk-keeps (disk)
  ; Every address a valid record of any root keeps, and the reserved page
  ; (page 0: the owner's root's two record slots live there in the one-barrier
  ; layout, so no allocation or reclamation may ever hand it out).
  (declare (xargs :guard t))
  (cons *pgs-reserved-page* (pgs-roots-keeps (pgs-roots disk) (pgs-pages disk) nil)))

; -----------------------------------------------------------------------------
; Allocation (shared).
;
; The allocator's state is (FREE HWM): FREE a list of reusable addresses
; (reclamation adds to it, section 3), HWM the high-water mark (everything
; at or above it is unwritten).  A commit takes the directory run first --
; the first address of FREE that starts M free addresses (M = 1 below
; 116,281 logical pages), else M pages at HWM -- then N singles: FREE in
; order, then HWM upward.  It never refuses.

(defun pgs-all-in (xs free)
  (declare (xargs :guard (true-listp free)))
  (if (atom xs) t (and (member-equal (car xs) free) (pgs-all-in (cdr xs) free))))

(defun pgs-find-free-run (cands m free)
  ; The first A in CANDS with A..A+M-1 all in FREE, or nil.
  (declare (xargs :guard (and (natp m) (true-listp free))))
  (cond ((atom cands) nil)
        ((and (natp (car cands)) (pgs-all-in (pgs-run (car cands) m) free)) (car cands))
        (t (pgs-find-free-run (cdr cands) m free))))

(defun pgs-remove-all (xs free)
  (declare (xargs :guard (and (true-listp xs) (true-listp free))))
  (if (atom free)
      nil
    (if (member-equal (car free) xs)
        (pgs-remove-all xs (cdr free))
      (cons (car free) (pgs-remove-all xs (cdr free))))))

(defun pgs-take-singles (n free hwm)
  ; (mv SINGLES FREE2 HWM2): N addresses, FREE first.
  (declare (xargs :guard (and (natp n) (true-listp free) (natp hwm))))
  (cond ((zp n) (mv nil free (nfix hwm)))
        ((consp free)
         (mv-let (s f h) (pgs-take-singles (1- n) (cdr free) hwm)
           (mv (cons (car free) s) f h)))
        (t (mv-let (s f h) (pgs-take-singles (1- n) nil (+ 1 (nfix hwm)))
             (mv (cons (nfix hwm) s) f h)))))

(defun pgs-alloc (n m alloc)
  ; (RUN-START SINGLES FREE2 HWM2) for a commit of N singles and an M-page
  ; directory run over the allocator state ALLOC = (FREE HWM).  A one-page
  ; run (below 116,281 logical pages) is the first of N+1 singles, so the
  ; common commit costs O(N); a longer run is searched in FREE.
  (declare (xargs :guard (and (natp n) (natp m))))
  (let* ((free (true-list-fix (car (true-list-fix alloc))))
         (hwm (nfix (cadr (true-list-fix alloc)))))
    (if (<= (nfix m) 1)
        (mv-let (s f h) (pgs-take-singles (+ 1 (nfix n)) free hwm)
          (list (car s) (cdr s) f h))
      (let ((a (pgs-find-free-run free m free)))
        (if (natp a)
            (mv-let (s f h) (pgs-take-singles n (pgs-remove-all (pgs-run a m) free) hwm)
              (list a s f h))
          (mv-let (s f h) (pgs-take-singles n free (+ hwm (nfix m)))
            (list hwm s f h)))))))

; -----------------------------------------------------------------------------
; The commit.
;
; DIRTY is a list of (LPAGE . CONTENT), LPAGES strictly ascending; an LPAGE
; equal to the table's length at that point APPENDS a page (growth), so the
; new pages are exactly N, N+1, ... (`pgs-lpages-ok').  The planner is shared:
; the model hands it the content digests, the host the digests it computed
; over the stobj.

(defun pgs-lpages-ok (ls n lo)
  ; LS strictly ascending from LO, each at most the length N reached so far.
  (declare (xargs :guard t))
  (if (atom ls)
      (null ls)
    (let ((l (car ls)))
      (and (natp l) (<= (nfix lo) l) (<= l (nfix n))
           (pgs-lpages-ok (cdr ls) (if (equal l (nfix n)) (+ 1 (nfix n)) n) (+ 1 l))))))

(defun pgs-grown-len (ls n)
  ; Shared: the table's length after the commit of LS over N entries.
  (declare (xargs :guard t))
  (if (atom ls)
      (nfix n)
    (pgs-grown-len (cdr ls) (if (equal (nfix (car ls)) (nfix n)) (+ 1 (nfix n)) n))))

(defun pgs-update-entry (i e ptab)
  ; Replace entry I, or append it when I is the length.
  (declare (xargs :guard (and (natp i) (true-listp ptab))))
  (cond ((< (nfix i) (len ptab)) (update-nth (nfix i) e ptab))
        ((equal (nfix i) (len ptab)) (append ptab (list e)))
        (t ptab)))

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

(defun pgs-touched (lpages prev)
  ; Shared: the table pages LPAGES (ascending) fall in, ascending, each once;
  ; PREV the last one emitted (nil at the start).
  (declare (xargs :guard (nat-listp lpages)))
  (if (atom lpages)
      nil
    (let ((tp (floor (nfix (car lpages)) *pgs-tab-entries*)))
      (if (equal tp prev)
          (pgs-touched (cdr lpages) prev)
        (cons tp (pgs-touched (cdr lpages) tp))))))

(defun pgs-dirty-lpages (dirty)
  (declare (xargs :guard (alistp dirty)))
  (if (atom dirty) nil (cons (nfix (caar dirty)) (pgs-dirty-lpages (cdr dirty)))))

(defun pgs-dirty-digests (dirty)
  (declare (xargs :guard (alistp dirty)))
  (if (atom dirty) nil (cons (pgs-digest (cdar dirty)) (pgs-dirty-digests (cdr dirty)))))

(defun pgs-table-dirty (tl cs)
  ; The table pages a commit rewrites: (T . table page T of CS) for T in TL.
  (declare (xargs :guard (and (nat-listp tl) (true-listp cs))))
  (if (atom tl) nil (cons (cons (car tl) (nth (car tl) cs)) (pgs-table-dirty (cdr tl) cs))))

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

(defun pgs-plan-commit (disk r mode dirty alloc)
  ; The commit on root R of DIRTY over the state R opens on, allocating from
  ; ALLOC = (FREE HWM):
  ;   (:plan WRITES SLOT RECORD ALLOC2) where WRITES are the page writes,
  ;   the table-page writes and the directory write, and RECORD goes to SLOT
  ;   (the slot the open did not use); or (:refused REASON).  Model only (it
  ;   digests contents through the constrained seam): the host runs the same
  ;   `pgs-alloc', `pgs-plan-ptab', `pgs-touched' over the stobj.
  (declare (xargs :guard (alistp dirty) :verify-guards nil))
  (let* ((o (pgs-open disk r mode)))
    (if (not (and (consp o) (eq (car o) :ok) (true-listp o)))
        (list :refused :no-open-commit)
      (let* ((k (second o))
             (slots (pgs-root-slots r disk))
             (cur (pgs-slot k slots))
             (pages (pgs-pages disk))
             (dir (pgs-lookup (pgs-rec-dir-addr cur) pages))
             (ptab (pgs-flatten (pgs-contents dir pages)))
             (lpages (pgs-dirty-lpages dirty)))
        (if (not (pgs-lpages-ok lpages (len ptab) 0))
            (list :refused :dirty-out-of-order)
          (let* ((txid (pgs-next-txid slots))
                 (tl (pgs-touched lpages nil))
                 (n (len dirty))
                 (al (pgs-alloc (+ n (len tl)) (pgs-dir-run-pages (pgs-grown-len lpages (len ptab)))
                                alloc))
                 (rs (first al))
                 (fresh (take n (second al)))
                 (tfresh (nthcdr n (second al)))
                 (ptab2 (pgs-plan-ptab ptab lpages fresh (pgs-dirty-digests dirty) txid))
                 (tdirty (pgs-table-dirty tl (pgs-chunk ptab2)))
                 (dir2 (pgs-plan-ptab (true-list-fix dir) tl tfresh (pgs-dirty-digests tdirty) txid))
                 (rec (pgs-make-rec txid rs (len ptab2) (pgs-digest dir2)))
                 (writes (append (pgs-page-writes dirty fresh)
                                 (pgs-page-writes tdirty tfresh)
                                 (list (cons rs dir2)))))
            (list :plan writes (if (equal k 1) 0 1) rec (list (third al) (fourth al)))))))))

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

(defun pgs-commit (disk r mode dirty alloc)
  ; The complete commit: every write, then the record.
  (declare (xargs :guard (alistp dirty) :verify-guards nil))
  (let ((p (pgs-plan-commit disk r mode dirty alloc)))
    (if (eq (car p) :plan)
        (pgs-crash disk r (second p) nil (third p) (fourth p))
      disk)))

; The logical state after DIRTY: CONTENTS with each dirty page replaced,
; or appended when its LPAGE is the length.
(defun pgs-apply-dirty (contents dirty)
  (declare (xargs :guard (and (true-listp contents) (alistp dirty))))
  (if (atom dirty)
      contents
    (pgs-apply-dirty (let ((i (nfix (caar dirty))))
                       (cond ((< i (len contents)) (update-nth i (cdar dirty) contents))
                             ((equal i (len contents)) (append contents (list (cdar dirty))))
                             (t contents)))
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
; where the snapshot may die: before any write, after the K-th data-page
; write, after the K-th table-page write, after the directory write, with
; the record half-written, after the record write, after its barrier.  A
; process death keeps every completed write (the page cache survives), so
; each cut is the model's `pgs-crash' with KEEP the completed prefix of the
; commit's writes (NDATA data pages, then the table pages, then the
; directory) and the slot old, torn or new: `pgs-cut-crash-point'.

(defconst *pgs-snapshot-cuts*
  '(:begin :page-written :table-written :dir-written
    :record-torn :record-written :record-synced))

(defun pgs-prefix-keep (k n)
  ; N flags, the first K true.
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp n) nil (cons (not (zp k)) (pgs-prefix-keep (if (zp k) 0 (1- k)) (1- n)))))

(defun pgs-cut-crash-point (cut k ndata nwrites)
  ; (KEEP . SLOT) for host cut CUT (occurrence K for the per-write cuts) in
  ; a commit of NWRITES writes whose first NDATA are data pages: SLOT is
  ; :old, :torn or :new.
  (declare (xargs :guard (and (natp k) (natp ndata) (natp nwrites))))
  (case cut
    (:begin (cons (pgs-prefix-keep 0 nwrites) :old))
    (:page-written (cons (pgs-prefix-keep k nwrites) :old))
    (:table-written (cons (pgs-prefix-keep (+ ndata k) nwrites) :old))
    (:dir-written (cons (pgs-prefix-keep nwrites nwrites) :old))
    (:record-torn (cons (pgs-prefix-keep nwrites nwrites) :torn))
    (otherwise (cons (pgs-prefix-keep nwrites nwrites) :new))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition pgs-entry-p)
                    (:definition pgs-ptab-p)
                    (:rewrite pgs-ptab-p-true-listp)))
