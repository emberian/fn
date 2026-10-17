; fn: the store's history (fn-hist) as FNADTSN2 pages in the page store
; (lane arena-store-2, 2026-09-27).  Prefix fn-hp-.
;
; The history's snapshot IS the canonical byte form of a sequence ADT
; (books/proto/adt-bytes.lisp, FNADTSN2) over the schema
;   field 0  (:u64)     MKEY: 1 + the salted FNV hash of the event's key
;                       Message-ID (`fn-hist-key-msgid', books/history-columns),
;                       0 when the event has none
;   field 1  (:u64)     the length of the event's tree octets
;   field 2  (:octets)  the event's tree octets (`fn-scc-encode',
;                       books/store-checkpoint-codec: a proved codec,
;                       `fn-scc-decode-tree-of-encode'), zero-padded to a
;                       multiple of 8; decoded on access
; one row per retained event, oldest first.  So the image has five regions:
; the MKEY and length columns, the offset and length columns of field 2,
; and the pool.  Every cell is 8 octets and every pool entry starts on a
; word, so an append writes whole words and a column read is one word.
;
; Image pages are the page store's logical pages 1:1 (image page K = page
; store logical page K; the store's physical page 0, its root slots, is
; another thing).  The page store's per-page digest (the table entry a
; commit writes, `pgs-x-page-digest' over the page's words) IS the FNADTSN2
; page-digest leaf of the same page (`fn-hp-page-digest-is-leaf'): there is
; no second per-page digest table.
;
; KEYSTONES
;   fn-hp-decode-image               the decoder inverts the image
;   fn-hp-page-digest-is-leaf        the store's page digest = the leaf
;   fn-hp-append-changes-only-dirty  an append changes only the dirty list
;   fn-hp-append-dirty-bound         the dirty list is O(K + columns) pages
;                                    while no region doubles
; Named limit L-HP-DOUBLING: the canonical image places regions contiguously;
; a region that doubles is the writer's verdict (:grow R) and FNADTSN2's free
; placement lets it move alone (the growth path, lane arena-store-3, open).
;
; Sections: A. rows and schema; B. image and decoder; C. the digest
; theorem; D. the region plan.
(in-package "ACL2")
(include-book "proto/adt-bytes")
(include-book "store-checkpoint-buffer")
(include-book "history-columns-logic")
(include-book "pagestore-words-blake3")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; A. The rows and the schema.

(defconst *fn-hp-schema* '((:u64) (:u64) (:octets)))

(defthm fn-hp-schema-bschemap
  (adt-bschemap *fn-hp-schema*))

(local
 (defthm fn-hp-mod-u32-below
   (implies (integerp x) (< (mod x 4294967296) 4294967296))
   :rule-classes :linear))

(local
 (defthm fn-hp-fnv-below
   (implies (< (nfix h) 4294967296)
            (< (fn-hist-fnv s i h) 4294967296))
   :hints (("Goal" :in-theory (disable logxor mod)))
   :rule-classes :linear))

; MKEY: the Message-ID bucket the history stobj keys an event under
; (`fn-hist$c-append'), plus one; 0 for an event with no key Message-ID.
(defun fn-hp-mkey (ev salt)
  (declare (xargs :guard t))
  (let ((m (fn-hist-key-msgid ev)))
    (if (stringp m) (+ 1 (fn-hist-hash m salt)) 0)))

(defthm fn-hp-mkey-u64
  (unsigned-byte-p 64 (fn-hp-mkey ev salt))
  :hints (("Goal" :in-theory (disable logxor mod fn-hist-fnv))))

; The tree's octets padded with zeros to a multiple of 8, so every pool
; entry starts on a word and an append writes whole words.
(defun fn-hp-pad8-count (n)
  (declare (xargs :guard (natp n)))
  (mod (- 8 (mod (nfix n) 8)) 8))

(defun fn-hp-pad8 (x)
  (declare (xargs :guard (true-listp x)))
  (append x (adt-zeros (fn-hp-pad8-count (len x)))))

; An event the image can hold: its tree encodes to octets
; (`fn-sccb-treep-encodes-octets') of a u64 length; the writer refuses any
; other by name.
(defun fn-hp-evp (ev)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sccb-treep ev) (unsigned-byte-p 64 (len (fn-scc-encode ev)))))

(defun fn-hp-events-okp (h)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom h) (null h) (and (fn-hp-evp (car h)) (fn-hp-events-okp (cdr h)))))

; A row: MKEY, the tree's length, its padded octets.
(defun fn-hp-row (ev salt)
  (declare (xargs :guard (fn-sccb-treep ev) :verify-guards nil))
  (let ((enc (fn-scc-encode ev)))
    (list (fn-hp-mkey ev salt) (len enc) (fn-hp-pad8 enc))))

(defun fn-hp-rows (h salt)
  (declare (xargs :verify-guards nil))
  (if (atom h) nil (cons (fn-hp-row (car h) salt) (fn-hp-rows (cdr h) salt))))

(local
 (defthm fn-hp-octetsp-of-scc-octets
   (implies (fn-scc-octet-listp x) (adt-octetsp x))))

(defthm fn-hp-octetsp-pad8
  (implies (adt-octetsp x) (adt-octetsp (fn-hp-pad8 x))))

(in-theory (disable fn-hp-pad8))

(defthm fn-hp-rec-p-of-row
  (implies (fn-hp-evp ev)
           (adt-rec-p *fn-hp-schema* (fn-hp-row ev salt)))
  :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-mkey))))

(defthm fn-hp-rows-seq-p
  (implies (fn-hp-events-okp h)
           (adt-seq-p *fn-hp-schema* (fn-hp-rows h salt)))
  :hints (("Goal" :in-theory (disable fn-hp-row fn-hp-evp adt-rec-p))))

(defthm fn-hp-len-rows (equal (len (fn-hp-rows h salt)) (len h))
  :hints (("Goal" :in-theory (disable fn-hp-row))))

; -----------------------------------------------------------------------------
; B. The image and its decoder.

; THE snapshot bytes of the history H.
(defun fn-hp-image (h salt)
  (declare (xargs :verify-guards nil))
  (adt-ser *fn-hp-schema* (fn-hp-rows h salt)))

; Each row's tree decoded from its padded octets; the padding must be the
; canonical one and MKEY the decoded event's.  Every check refuses by name;
; none repairs.
(defun fn-hp-dec-row (row salt)
  (declare (xargs :verify-guards nil))
  (let* ((n (nfix (cadr row))) (bytes (caddr row)))
    (if (not (and (<= n (len bytes)) (equal bytes (fn-hp-pad8 (take n bytes)))))
        (list :refused :padding)
      (let ((d (fn-scc-decode-tree (take n bytes))))
        (cond ((not (eq (car d) :ok)) (list :refused :tree))
              ((not (equal (car row) (fn-hp-mkey (cadr d) salt))) (list :refused :mkey))
              (t d))))))

(defun fn-hp-dec-events (rows salt)
  (declare (xargs :verify-guards nil))
  (if (atom rows)
      (list :ok nil)
    (let ((d (fn-hp-dec-row (car rows) salt)))
      (if (not (eq (car d) :ok))
          d
        (let ((rest (fn-hp-dec-events (cdr rows) salt)))
          (if (eq (car rest) :ok)
              (list :ok (cons (cadr d) (cadr rest)))
            rest))))))

(defun fn-hp-decode (b salt)
  (declare (xargs :verify-guards nil))
  (let ((d (adt-decode *fn-hp-schema* b)))
    (if (eq (car d) :ok) (fn-hp-dec-events (cadr d) salt) d)))

(local
 (defthm fn-hp-decode-tree-of-program
   (implies (fn-sccb-treep x)
            (equal (fn-scc-decode-tree (fn-scc-program x)) (list :ok x)))
   :hints (("Goal" :use ((:instance fn-scc-decode-tree-of-encode))
            :in-theory (disable fn-scc-decode-tree-of-encode fn-scc-decode-tree fn-scc-program)))))

(local
 (defthm fn-hp-take-of-pad8
   (implies (true-listp x)
            (equal (take (len x) (fn-hp-pad8 x)) x))
   :hints (("Goal" :in-theory (enable fn-hp-pad8)))))

(local
 (defthm fn-hp-len-pad8-bound
   (<= (len x) (len (fn-hp-pad8 x)))
   :hints (("Goal" :in-theory (enable fn-hp-pad8)))
   :rule-classes :linear))

(defthm fn-hp-dec-row-of-row
  (implies (fn-hp-evp ev)
           (equal (fn-hp-dec-row (fn-hp-row ev salt) salt) (list :ok ev)))
  :hints (("Goal" :in-theory (disable fn-scc-program fn-hp-mkey fn-scc-decode-tree))))

(defthm fn-hp-dec-events-of-rows
  (implies (fn-hp-events-okp h)
           (equal (fn-hp-dec-events (fn-hp-rows h salt) salt) (list :ok h)))
  :hints (("Goal" :in-theory (disable fn-hp-dec-row fn-hp-row fn-hp-evp))))

; KEYSTONE (the round trip): the decoder inverts the image on every history
; whose events encode and whose image is addressable by u64 offsets.
(defthm fn-hp-decode-image
  (implies (and (fn-hp-events-okp h)
                (< (len h) *adt-u64-limit*)
                (< (len (fn-hp-image h salt)) *adt-u64-limit*))
           (equal (fn-hp-decode (fn-hp-image h salt) salt) (list :ok h)))
  :hints (("Goal" :in-theory (disable adt-decode adt-ser fn-hp-dec-events fn-hp-rows)
           :use ((:instance adt-decode-ser (s *fn-hp-schema*) (a (fn-hp-rows h salt)))))))

; -----------------------------------------------------------------------------
; C. The one digest theorem: the page store's page digest IS the FNADTSN2
; leaf.
;
; `pgs-x-page-digest' is what the commit writes into the table entry of a
; dirty page (`pgs-x-dirty-digests' in `pgs-x-commit-prepare') and what the
; open and every first touch check a page against (`pgs-x-open-page',
; `pgs-x-read').  When page K's words are page K of an image (little-endian,
; as the host's fill leaves them), that digest is leaf K of the image's
; `adt-page-digests', as the big-endian natural of its 32 octets.  So the
; image's per-page digest table IS the page store's table: nothing else is
; stored or checked.

(defun fn-hp-page (b k)
  ; page K of the octets B
  (declare (xargs :guard (and (true-listp b) (natp k))))
  (take *adt-page* (nthcdr (* *adt-page* k) b)))

(local
 (defthm fn-hp-page-digest-is-leaf-any
  (implies (and (natp k)
                (< k (len (adt-page-digests s a)))
                (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 k) (pgs-x-arr 0 pgs-mem))))
                       (fn-hp-page (adt-ser s a) k)))
           (equal (mv-nth 0 (pgs-x-page-digest k pgs-mem fn-octets-pg))
                  (pgs-octets-be-nat (nth k (adt-page-digests s a)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pgs-x-words-digest-is-blake3 (sel 0) (base (* k 2048)) (nb 256))
                 (:instance adt-page-digest-nth))
           :in-theory (e/d (pgs-x-page-digest fn-hp-page)
                           (adt-ser pgs-x-words-digest pgs-x-words-digest-is-blake3 adt-page-digest-nth
                            adt-page-digests fn-blake3 pgs-words-le-octets pgs-octets-be-nat))))))

(local
 (defthm fn-hp-car-le-octets-natp
   (implies (consp ws) (natp (car (pgs-words-le-octets ws))))
   :hints (("Goal" :in-theory (enable pgs-words-le-octets pgs-word-le-octets)))))

(local
 (defthm fn-hp-nthcdr-beyond
   (implies (and (true-listp b) (natp m) (<= (len b) m))
            (equal (nthcdr m b) nil))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-hp-page-past-digests
   (implies (and (adt-bschemap s) (natp k) (<= (len (adt-page-digests s a)) k))
            (equal (fn-hp-page (adt-ser s a) k) (take *adt-page* nil)))
   :hints (("Goal" :in-theory (e/d (fn-hp-page) (adt-ser take))
            :use ((:instance adt-len-page-digests) (:instance adt-len-ser))))))

(local
 (defthm fn-hp-take-nil-not-octets
   (implies (and (consp ws) (posp n))
            (not (equal (pgs-words-le-octets ws) (take n nil))))
   :hints (("Goal" :use ((:instance fn-hp-car-le-octets-natp)) :in-theory (disable fn-hp-car-le-octets-natp)
            :expand ((take n nil))))))

; KEYSTONE (the digest): the store's page digest is the leaf.  (A page
; past the image's end cannot satisfy the hypothesis: its octets would be
; NILs, the words' are naturals.)
(defthm fn-hp-page-digest-is-leaf
  (implies (and (natp k)
                (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 k) (pgs-x-arr 0 pgs-mem))))
                       (fn-hp-page (fn-hp-image h salt) k)))
           (equal (mv-nth 0 (pgs-x-page-digest k pgs-mem fn-octets-pg))
                  (pgs-octets-be-nat (nth k (adt-page-digests *fn-hp-schema* (fn-hp-rows h salt))))))
  :hints (("Goal" :do-not-induct t
           :cases ((< k (len (adt-page-digests *fn-hp-schema* (fn-hp-rows h salt)))))
           :use ((:instance fn-hp-page-digest-is-leaf-any (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-page-past-digests (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-take-nil-not-octets (n *adt-page*)
                  (ws (take 2048 (nthcdr (* 2048 k) (pgs-x-arr 0 pgs-mem))))))
           :in-theory (disable fn-hp-page-digest-is-leaf-any fn-hp-page-past-digests fn-hp-take-nil-not-octets
                               adt-ser fn-hp-page pgs-x-page-digest adt-page-digests pgs-words-le-octets take
                               fn-hp-rows))))

(local (in-theory (disable fn-hp-nthcdr-beyond)))

; -----------------------------------------------------------------------------
; D. The region plan: what an append changes.
;
; A region takes a power-of-two number of pages (`adt-cap'), so while no
; region's cap changes, an append changes only the header page (N and the
; regions' lengths) and, per region, the pages its new octets overlap.  When
; a region's cap changes (it doubles), it and every region after it move:
; those pages are all dirty (amortized O(1) per row; the named limit
; L-HP-DOUBLING in the record).  Stated first for any body whose regions
; grow in place (`fn-hp-prefixes'), then for the history.

(local
 (defthm fn-hp-take-nthcdr-append-below
   (implies (and (natp m) (natp n) (<= (+ m n) (len x)))
            (equal (take n (nthcdr m (append x y))) (take n (nthcdr m x))))
   :hints (("Goal" :in-theory (enable take nthcdr) :induct (nthcdr m x)))))

(local
 (defthm fn-hp-nthcdr-append-above
   (implies (and (natp m) (<= (len x) m))
            (equal (nthcdr m (append x y)) (nthcdr (- m (len x)) y)))
   :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr m x)))))

(local
 (defun fn-hp-zeros-ind (m z)
   (if (or (zp m) (zp z)) (list m z) (fn-hp-zeros-ind (1- m) (1- z)))))

(local
 (defthm fn-hp-nthcdr-zeros
   (implies (and (natp m) (<= m (nfix z)))
            (equal (nthcdr m (adt-zeros z)) (adt-zeros (- (nfix z) m))))
   :hints (("Goal" :in-theory (enable nthcdr) :induct (fn-hp-zeros-ind m z)))))

(local
 (defthm fn-hp-take-zeros
   (implies (and (natp n) (<= n (nfix z)))
            (equal (take n (adt-zeros z)) (adt-zeros n)))
   :hints (("Goal" :in-theory (enable take) :induct (fn-hp-zeros-ind n z)))))

(local
 (defun fn-hp-tt-ind (n l y)
   (if (or (zp n) (zp l)) (list n l y) (fn-hp-tt-ind (1- n) (1- l) (cdr y)))))

(local
 (defthm fn-hp-take-take-below
   (implies (and (natp n) (natp l) (<= n l))
            (equal (take n (take l y)) (take n y)))
   :hints (("Goal" :in-theory (enable take) :induct (fn-hp-tt-ind n l y)))))

(local
 (defthm fn-hp-nthcdr-take
   (implies (and (natp m) (natp l) (<= m l))
            (equal (nthcdr m (take l y)) (take (- l m) (nthcdr m y))))
   :hints (("Goal" :in-theory (enable take nthcdr) :induct (fn-hp-tt-ind m l y)))))

(local
 (defthm fn-hp-take-nthcdr-prefix
   (implies (and (natp m) (natp n) (<= (+ m n) (len x))
                 (equal (take (len x) x2) x))
            (equal (take n (nthcdr m x2)) (take n (nthcdr m x))))
   :hints (("Goal" :use ((:instance fn-hp-nthcdr-take (l (len x)) (y x2))
                         (:instance fn-hp-take-take-below (l (- (len x) m)) (y (nthcdr m x2))))
            :in-theory (disable fn-hp-nthcdr-take fn-hp-take-take-below)))))

(defun fn-hp-prefixp (x y)
  ; X is a prefix of Y
  (declare (xargs :verify-guards nil))
  (and (true-listp x) (<= (len x) (len y)) (equal (take (len x) y) x)))

(defun fn-hp-reg-page-dirty (k reg reg2)
  ; page K of a region that grows from REG to REG2 in place: it overlaps
  ; the octets [len REG, len REG2)
  (declare (xargs :guard (natp k)))
  (not (or (<= (* *adt-page* (+ 1 (nfix k))) (len reg))
           (<= (len reg2) (* *adt-page* (nfix k))))))

(local
 (defthm fn-hp-pad-page-inside
   (implies (and (natp k) (<= (* *adt-page* (+ 1 k)) (len reg)))
            (equal (fn-hp-page (adt-pad reg) k) (take *adt-page* (nthcdr (* *adt-page* k) reg))))
   :hints (("Goal" :do-not-induct t :in-theory (e/d (adt-pad) (adt-cap))))))

(local
 (defthm fn-hp-pad-page-beyond
   (implies (and (natp k) (< k (adt-cap (len reg))) (<= (len reg) (* *adt-page* k)))
            (equal (fn-hp-page (adt-pad reg) k) (adt-zeros *adt-page*)))
   :hints (("Goal" :do-not-induct t :in-theory (e/d (adt-pad) (adt-cap adt-zeros))))))

(local
 (defthm fn-hp-pad-page-same
   (implies (and (natp k) (< k (adt-cap (len reg)))
                 (equal (adt-cap (len reg)) (adt-cap (len reg2)))
                 (fn-hp-prefixp reg reg2)
                 (not (fn-hp-reg-page-dirty k reg reg2)))
            (equal (fn-hp-page (adt-pad reg2) k) (fn-hp-page (adt-pad reg) k)))
   :hints (("Goal" :do-not-induct t :in-theory (disable adt-cap fn-hp-page adt-pad fn-hp-take-nthcdr-prefix)
            :use ((:instance fn-hp-take-nthcdr-prefix (x reg) (x2 reg2) (m (* *adt-page* k)) (n *adt-page*)))
            :cases ((<= (* *adt-page* (+ 1 k)) (len reg)))))))

(defun fn-hp-prefixes (regs regs2)
  ; each region of REGS is a prefix of REGS2's
  (declare (xargs :verify-guards nil))
  (if (atom regs)
      (atom regs2)
    (and (consp regs2) (fn-hp-prefixp (car regs) (car regs2))
         (fn-hp-prefixes (cdr regs) (cdr regs2)))))

(defun fn-hp-body-dirty (k regs regs2)
  ; body page K when the regions grow from REGS to REGS2: a page of a region
  ; whose cap changed, or of any region after it (they move), is dirty
  (declare (xargs :verify-guards nil :measure (len regs)))
  (cond ((or (atom regs) (atom regs2)) (not (and (atom regs) (atom regs2))))
        ((not (equal (adt-cap (len (car regs))) (adt-cap (len (car regs2))))) t)
        ((< (nfix k) (adt-cap (len (car regs)))) (fn-hp-reg-page-dirty k (car regs) (car regs2)))
        (t (fn-hp-body-dirty (- (nfix k) (adt-cap (len (car regs)))) (cdr regs) (cdr regs2)))))

(local
 (defthm fn-hp-page-of-append-pad
   (implies (natp k)
            (equal (fn-hp-page (append (adt-pad r) rest) k)
                   (if (< k (adt-cap (len r)))
                       (fn-hp-page (adt-pad r) k)
                     (fn-hp-page rest (- k (adt-cap (len r)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable adt-cap adt-pad adt-nthcdr-of-append-less fn-hp-take-nthcdr-append-below)
            :use ((:instance fn-hp-take-nthcdr-append-below (x (adt-pad r)) (y rest)
                   (m (* *adt-page* k)) (n *adt-page*)))
            :cases ((< k (adt-cap (len r))))))))

(defthm fn-hp-body-page-same
  (implies (and (natp k) (fn-hp-prefixes regs regs2)
                (not (fn-hp-body-dirty k regs regs2)))
           (equal (fn-hp-page (adt-body regs2) k) (fn-hp-page (adt-body regs) k)))
  :hints (("Goal" :induct (fn-hp-body-dirty k regs regs2)
           :in-theory (disable adt-cap adt-pad fn-hp-page fn-hp-prefixp fn-hp-reg-page-dirty))))

(defun fn-hp-image-dirty (k regs regs2)
  ; image page K: the header (page 0) always, else the body's page K-1
  (declare (xargs :verify-guards nil))
  (or (zp k) (fn-hp-body-dirty (1- k) regs regs2)))

(local
 (defthm fn-hp-page-of-append-header
   (implies (and (posp k) (equal (len h) *adt-page*))
            (equal (fn-hp-page (append h rest) k) (fn-hp-page rest (1- k))))
   :hints (("Goal" :do-not-induct t :in-theory (disable adt-nthcdr-of-append-less)))))

(local
 (defthm fn-hp-bschemap-header-room
   (implies (adt-bschemap s)
            (<= (+ 72 (* 16 (+ 1 (adt-ncols s)))) *adt-page*))
   :rule-classes :linear))

(defthm fn-hp-ser-page-same
  (implies (and (adt-bschemap s) (natp k)
                (fn-hp-prefixes (adt-regs s a) (adt-regs s a2))
                (not (fn-hp-image-dirty k (adt-regs s a) (adt-regs s a2))))
           (equal (fn-hp-page (adt-ser s a2) k) (fn-hp-page (adt-ser s a) k)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-page-of-append-header (h (adt-header s (len a) (adt-regs s a)))
                  (rest (adt-body (adt-regs s a))))
                 (:instance fn-hp-page-of-append-header (h (adt-header s (len a2) (adt-regs s a2)))
                  (rest (adt-body (adt-regs s a2))))
                 (:instance fn-hp-body-page-same (k (1- k)) (regs (adt-regs s a)) (regs2 (adt-regs s a2)))
                 (:instance adt-len-header (n (len a)) (regs (adt-regs s a)))
                 (:instance adt-len-header (n (len a2)) (regs (adt-regs s a2))))
           :in-theory (e/d (adt-ser) (adt-header fn-hp-page adt-body fn-hp-body-dirty fn-hp-prefixes
                                      adt-bschemap adt-regs adt-ser-is-header-body
                                      fn-hp-page-of-append-header fn-hp-body-page-same adt-len-header)))))

; An append grows every region in place.
(defun fn-hp-zapp (xs ys)
  ; pointwise append
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil (cons (append (car xs) (car ys)) (fn-hp-zapp (cdr xs) (cdr ys)))))

(local
 (defthm fn-hp-rows-cells-of-append
   (implies (natp pos)
            (equal (adt-rows-cells s (append a b) pos)
                   (append (adt-rows-cells s a pos)
                           (adt-rows-cells s b (+ pos (len (adt-rows-pool s a)))))))
   :hints (("Goal" :induct (adt-rows-cells s a pos) :in-theory (disable adt-row-cells adt-row-pool)))))

(local
 (defthm fn-hp-rows-pool-of-append
   (equal (adt-rows-pool s (append a b)) (append (adt-rows-pool s a) (adt-rows-pool s b)))
   :hints (("Goal" :in-theory (disable adt-row-pool)))))

(local
 (defthm fn-hp-cars-of-append
   (equal (adt-cars (append x y)) (append (adt-cars x) (adt-cars y)))))

(local
 (defthm fn-hp-cdrs-of-append
   (equal (adt-cdrs (append x y)) (append (adt-cdrs x) (adt-cdrs y)))))

(local
 (defthm fn-hp-transpose-of-append
   (equal (adt-transpose m (append x y))
          (fn-hp-zapp (adt-transpose m x) (adt-transpose m y)))))

(local
 (defthm fn-hp-le-list-of-append
   (equal (adt-le-list w (append x y)) (append (adt-le-list w x) (adt-le-list w y)))))

(local
 (defthm fn-hp-col-regs-of-zapp
   (implies (equal (len c1) (len ws))
            (equal (adt-col-regs ws (fn-hp-zapp c1 c2))
                   (fn-hp-zapp (adt-col-regs ws c1) (adt-col-regs ws c2))))))

(local
 (defthm fn-hp-zapp-snoc
   (implies (equal (len x) (len y))
            (equal (fn-hp-zapp (append x (list p)) (append y (list q)))
                   (append (fn-hp-zapp x y) (list (append p q)))))))

(local
 (defthm fn-hp-prefixes-of-zapp
   (implies (true-list-listp x)
            (fn-hp-prefixes x (fn-hp-zapp x d)))))

(defthm fn-hp-regs-of-append
  (fn-hp-prefixes (adt-regs s a) (adt-regs s (append a b)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-prefixes-of-zapp (x (adt-regs s a))
                  (d (append (adt-col-regs (adt-col-widths s)
                                           (adt-transpose (adt-ncols s)
                                                          (adt-rows-cells s b (len (adt-rows-pool s a)))))
                             (list (adt-rows-pool s b))))))
           :in-theory (e/d (adt-regs) (fn-hp-prefixes-of-zapp fn-hp-prefixes)))))

; The dirty pages as a list, and its size.
(defun fn-hp-range (lo hi)
  (declare (xargs :guard (and (natp lo) (natp hi)) :measure (nfix (- (nfix hi) (nfix lo)))))
  (if (< (nfix lo) (nfix hi)) (cons (nfix lo) (fn-hp-range (+ 1 (nfix lo)) hi)) nil))

(defthm fn-hp-member-range
  (implies (and (natp k) (natp lo))
           (iff (member-equal k (fn-hp-range lo hi))
                (and (<= lo k) (< k (nfix hi))))))

(defthm fn-hp-len-range
  (equal (len (fn-hp-range lo hi)) (nfix (- (nfix hi) (nfix lo)))))

(defun fn-hp-body-dirty-pages (regs regs2 base)
  ; the pages from BASE that an in-place growth REGS -> REGS2 changes: per
  ; region the pages its new octets overlap; from a region whose cap
  ; changed, every page to the new end
  (declare (xargs :verify-guards nil :measure (len regs)))
  (cond ((or (atom regs) (atom regs2)) nil)
        ((not (equal (adt-cap (len (car regs))) (adt-cap (len (car regs2)))))
         (fn-hp-range base (adt-end regs2 base)))
        (t (append (fn-hp-range (+ (nfix base) (floor (len (car regs)) *adt-page*))
                                (+ (nfix base) (ceiling (len (car regs2)) *adt-page*)))
                   (fn-hp-body-dirty-pages (cdr regs) (cdr regs2)
                                           (+ (nfix base) (adt-cap (len (car regs)))))))))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-hp-floor-below
     (implies (and (natp l) (natp j) (< l (* 16384 (+ 1 j))))
              (<= (floor l 16384) j))
     :rule-classes :linear)
   (defthm fn-hp-ceiling-above
     (implies (and (natp l) (natp j) (< (* 16384 j) l))
              (< j (ceiling l 16384)))
     :rule-classes :linear)
   (defthm fn-hp-ceiling-upper
     (implies (natp l) (< (* 16384 (ceiling l 16384)) (+ l 16384)))
     :rule-classes :linear)
   (defthm fn-hp-floor-lower
     (implies (natp l) (< l (+ 16384 (* 16384 (floor l 16384)))))
     :rule-classes :linear)
   (defthm fn-hp-floor-le-ceiling
     (implies (and (natp l1) (natp l2) (<= l1 l2))
              (<= (floor l1 16384) (ceiling l2 16384)))
     :rule-classes :linear)))

(local
 (defthm fn-hp-member-append
   (iff (member-equal k (append x y)) (or (member-equal k x) (member-equal k y)))))

(defthm fn-hp-body-dirty-in-pages
  (implies (and (natp k) (natp base) (<= base k) (< k (adt-end regs2 base))
                (equal (len regs) (len regs2))
                (fn-hp-body-dirty (- k base) regs regs2))
           (member-equal k (fn-hp-body-dirty-pages regs regs2 base)))
  :hints (("Goal" :induct (fn-hp-body-dirty-pages regs regs2 base)
           :expand ((fn-hp-body-dirty (+ (- base) k) regs regs2))
           :in-theory (disable adt-cap floor ceiling adt-end-is-end-l))
          ("Subgoal *1/3" :use ((:instance fn-hp-floor-below (l (len (car regs))) (j (- k base)))
                                (:instance fn-hp-ceiling-above (l (len (car regs2))) (j (- k base)))))))

(defun fn-hp-caps-same (regs regs2)
  (declare (xargs :verify-guards nil))
  (if (atom regs) (atom regs2)
    (and (consp regs2) (equal (adt-cap (len (car regs))) (adt-cap (len (car regs2))))
         (fn-hp-caps-same (cdr regs) (cdr regs2)))))

(defun fn-hp-regs-octets (regs)
  (declare (xargs :guard t))
  (if (atom regs) 0 (+ (len (car regs)) (fn-hp-regs-octets (cdr regs)))))

(defthm fn-hp-dirty-pages-bound
  (implies (and (fn-hp-caps-same regs regs2) (fn-hp-prefixes regs regs2) (natp base))
           (<= (* *adt-page* (len (fn-hp-body-dirty-pages regs regs2 base)))
               (+ (- (fn-hp-regs-octets regs2) (fn-hp-regs-octets regs))
                  (* 2 *adt-page* (len regs)))))
  :hints (("Goal" :induct (fn-hp-body-dirty-pages regs regs2 base)
           :in-theory (disable adt-cap floor ceiling))))

; The history's instance.
(defthm fn-hp-rows-of-append
  (equal (fn-hp-rows (append h new) salt) (append (fn-hp-rows h salt) (fn-hp-rows new salt)))
  :hints (("Goal" :in-theory (disable fn-hp-row))))

(defun fn-hp-regs (h salt)
  (declare (xargs :verify-guards nil))
  (adt-regs *fn-hp-schema* (fn-hp-rows h salt)))

(defun fn-hp-npages (h salt)
  ; the image's page count
  (declare (xargs :verify-guards nil))
  (adt-end (fn-hp-regs h salt) 1))

(defun fn-hp-append-dirty (h new salt)
  ; the image pages an append of NEW to H changes: the header and the
  ; body's (image page = body page + 1)
  (declare (xargs :verify-guards nil))
  (cons 0 (fn-hp-body-dirty-pages (fn-hp-regs h salt) (fn-hp-regs (append h new) salt) 1)))

(local
 (defthm fn-hp-append-changes-only-dirty-in-range
  (implies (and (natp k) (< k (fn-hp-npages (append h new) salt))
                (not (member-equal k (fn-hp-append-dirty h new salt))))
           (equal (fn-hp-page (fn-hp-image (append h new) salt) k)
                  (fn-hp-page (fn-hp-image h salt) k)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-ser-page-same (s *fn-hp-schema*) (a (fn-hp-rows h salt))
                  (a2 (append (fn-hp-rows h salt) (fn-hp-rows new salt))))
                 (:instance fn-hp-regs-of-append (s *fn-hp-schema*) (a (fn-hp-rows h salt))
                  (b (fn-hp-rows new salt)))
                 (:instance fn-hp-body-dirty-in-pages (base 1)
                  (regs (adt-regs *fn-hp-schema* (fn-hp-rows h salt)))
                  (regs2 (adt-regs *fn-hp-schema* (append (fn-hp-rows h salt) (fn-hp-rows new salt))))))
           :in-theory (e/d (fn-hp-image-dirty)
                           (fn-hp-ser-page-same fn-hp-body-dirty-in-pages adt-ser fn-hp-page fn-hp-regs-of-append
                            fn-hp-body-dirty fn-hp-body-dirty-pages fn-hp-prefixes adt-regs fn-hp-rows
                            adt-end adt-end-is-end-l))))))

; Pages past the new image's end are past the old one's too (caps only grow).
(local
 (defthm fn-hp-pow2-monotone
   (implies (and (natp k1) (natp k2) (<= k1 k2) (posp acc))
            (<= (adt-pow2-at-least k1 acc) (adt-pow2-at-least k2 acc)))
   :hints (("Goal" :induct (adt-pow2-at-least k2 acc)))
   :rule-classes :linear))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-hp-ceiling-lower-2
     (implies (natp l) (<= l (* 16384 (ceiling l 16384))))
     :rule-classes :linear)
   (defthm fn-hp-ceiling-upper-2
     (implies (natp l) (< (* 16384 (ceiling l 16384)) (+ l 16384)))
     :rule-classes :linear)))

(local
 (defthm fn-hp-ceiling-monotone
   (implies (and (natp l1) (natp l2) (<= l1 l2))
            (<= (ceiling l1 16384) (ceiling l2 16384)))
   :hints (("Goal" :in-theory (disable ceiling)))
   :rule-classes :linear))

(local
 (defthm fn-hp-cap-monotone
   (implies (and (natp l1) (natp l2) (<= l1 l2))
            (<= (adt-cap l1) (adt-cap l2)))
   :hints (("Goal" :in-theory (disable adt-pow2-at-least ceiling fn-hp-pow2-monotone)
            :use ((:instance fn-hp-pow2-monotone (k1 (ceiling l1 16384)) (k2 (ceiling l2 16384)) (acc 1)))))
   :rule-classes :linear))

(local
 (defthm fn-hp-end-monotone
   (implies (and (fn-hp-prefixes regs regs2) (natp b1) (natp b2) (<= b1 b2))
            (<= (adt-end regs b1) (adt-end regs2 b2)))
   :hints (("Goal" :in-theory (disable adt-cap adt-end-is-end-l)))
   :rule-classes :linear))

(local
 (defthm fn-hp-page-beyond
   (implies (and (natp k) (true-listp b1) (true-listp b2)
                 (<= (len b1) (* *adt-page* k)) (<= (len b2) (* *adt-page* k)))
            (equal (fn-hp-page b1 k) (fn-hp-page b2 k)))
   :hints (("Goal" :in-theory (e/d (fn-hp-nthcdr-beyond) (take))))
   :rule-classes nil))

; KEYSTONE (the region plan, 1): every page outside the dirty list is the
; old image's page, so a snapshot writes only the dirty list (the store is
; region-agnostic: it writes the pages marked dirty).
(defthm fn-hp-append-changes-only-dirty
  (implies (and (natp k)
                (not (member-equal k (fn-hp-append-dirty h new salt))))
           (equal (fn-hp-page (fn-hp-image (append h new) salt) k)
                  (fn-hp-page (fn-hp-image h salt) k)))
  :hints (("Goal" :do-not-induct t :cases ((< k (fn-hp-npages (append h new) salt)))
           :use ((:instance fn-hp-append-changes-only-dirty-in-range)
                 (:instance fn-hp-regs-of-append (s *fn-hp-schema*) (a (fn-hp-rows h salt))
                  (b (fn-hp-rows new salt)))
                 (:instance fn-hp-end-monotone (regs (fn-hp-regs h salt)) (regs2 (fn-hp-regs (append h new) salt))
                  (b1 1) (b2 1))
                 (:instance adt-len-ser (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance adt-len-ser (s *fn-hp-schema*) (a (fn-hp-rows (append h new) salt)))
                 (:instance fn-hp-page-beyond (b1 (fn-hp-image (append h new) salt)) (b2 (fn-hp-image h salt))))
           :in-theory (disable fn-hp-append-changes-only-dirty-in-range fn-hp-regs-of-append fn-hp-end-monotone
                               adt-len-ser adt-ser fn-hp-page fn-hp-rows fn-hp-append-dirty adt-end-is-end-l
                               adt-end adt-regs))))

(defthm fn-hp-regs-octets-of-regs
  (equal (fn-hp-regs-octets (adt-regs *fn-hp-schema* rows))
         (+ (* 32 (len rows)) (len (adt-rows-pool *fn-hp-schema* rows))))
  :hints (("Goal" :do-not-induct t :in-theory (enable adt-regs)
           :expand ((adt-transpose 4 (adt-rows-cells *fn-hp-schema* rows 0))
                    (adt-transpose 3 (adt-cdrs (adt-rows-cells *fn-hp-schema* rows 0)))
                    (adt-transpose 2 (adt-cdrs (adt-cdrs (adt-rows-cells *fn-hp-schema* rows 0))))
                    (adt-transpose 1 (adt-cdrs (adt-cdrs (adt-cdrs (adt-rows-cells *fn-hp-schema* rows 0)))))))))

(defun fn-hp-enc-len (new)
  ; the pool octets of NEW's rows: each tree padded to a word
  (declare (xargs :verify-guards nil))
  (if (atom new) 0 (+ (len (fn-hp-pad8 (fn-scc-encode (car new)))) (fn-hp-enc-len (cdr new)))))

(local
 (defthm fn-hp-row-pool-of-row
   (equal (adt-row-pool *fn-hp-schema* (fn-hp-row ev salt)) (fn-hp-pad8 (fn-scc-encode ev)))
   :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-mkey)))))

(defthm fn-hp-len-rows-pool
  (equal (len (adt-rows-pool *fn-hp-schema* (fn-hp-rows new salt))) (fn-hp-enc-len new))
  :hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-mkey fn-hp-row adt-row-pool))))

; KEYSTONE (the region plan, 2): while no region doubles, an append of K
; events dirties at most 11 + (32 K + their padded tree octets) / 16384
; pages: the header, and per region (five) at most two partial pages plus
; the pages its new octets fill.  O(K + columns).
(defthm fn-hp-append-dirty-bound
  (implies (fn-hp-caps-same (fn-hp-regs h salt) (fn-hp-regs (append h new) salt))
           (<= (* *adt-page* (len (fn-hp-append-dirty h new salt)))
               (+ (* 11 *adt-page*) (* 32 (len new)) (fn-hp-enc-len new))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-dirty-pages-bound (base 1)
                  (regs (adt-regs *fn-hp-schema* (fn-hp-rows h salt)))
                  (regs2 (adt-regs *fn-hp-schema* (append (fn-hp-rows h salt) (fn-hp-rows new salt)))))
                 (:instance fn-hp-regs-of-append (s *fn-hp-schema*) (a (fn-hp-rows h salt))
                  (b (fn-hp-rows new salt))))
           :in-theory (disable fn-hp-dirty-pages-bound fn-hp-regs-of-append fn-hp-body-dirty-pages
                               fn-hp-prefixes adt-regs fn-hp-rows fn-hp-caps-same fn-hp-enc-len))))
