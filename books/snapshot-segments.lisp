; fn: the snapshot container (lane snapshot-open, 2026-09-27; ember's
; decision of 2026-09-27 ~16:30Z: the on-disk snapshot IS the in-memory
; structure).
;
; A snapshot file is an append-only run of SEGMENTS.  A segment is
;
;   PREFIX (32 octets)  "FNSS" | version 1 | column | 0 0 | first u64 |
;                       count u64 | length u64          (little-endian)
;   BODY   (length octets)
;   DIGEST (32 octets)  fn-frame-digest of (previous segment's DIGEST ++
;                       PREFIX ++ BODY); the first segment's previous is
;                       32 zero octets
;
; so every segment is chained to the one before it (a splice, a reorder or
; a stale tail does not verify).  Column 0 is the COMMIT: count 1, first 0,
; its body the K column lengths (u64 each) the commit covers and 48 octets
; of META (the caller's: the log position and frontier the snapshot is
; taken at).  Columns 1..K are fixed-width columns, WIDTHS giving each
; one's element width in octets (1 to 8; a width-1 column is a byte pool);
; a data segment of column c holds elements [first, first+count) of c,
; little-endian, and its first must be the column's length so far: the
; columns only grow, and each write appends only what is new since the
; previous commit (the incremental property: O(what changed)).
;
; The load is ONE linear pass over the file in the octet buffer
; (`fn-snap-scan'): each segment's prefix is read by index, its shape and
; digest checked, and a data segment is kept as a DESCRIPTOR (column,
; first, count, body offset) -- no element is parsed.  A commit is
; accepted when the lengths it states are the lengths the segments before
; it built; the scan answers the LAST accepted commit and why it stopped:
; :end (the file ends at a segment boundary), :torn (a segment runs past
; the end: the torn tail of a write that did not finish), :shape, :digest
; or :commit (damage, a recovery event).  Segments after the last commit
; are never used: an interrupted write leaves the previous snapshot intact,
; and the open falls back to it (`fn-snap-open-choice').
;
; What a commit DENOTES: for column c, the concatenation of the elements
; its descriptors hold (`fn-snap-column').  KEYSTONE
; `fn-snap-scan-of-writes': a file made of the writes of successive states
; S1 .. Sm (each extending the last, `fn-snap-extendsp') scans to :end and
; its last commit denotes Sm exactly -- whatever the chunking of each
; write and however the states were split into writes.  KEYSTONE
; `fn-snap-scan-of-torn-write': the same file followed by any proper prefix
; of the next write scans to the same last commit.  What the digest proves
; is only what the constrained `fn-frame-digest' gives (A-CRYPTO: the
; trailer function yields 32 octets); that a damaged segment is detected is
; the digest's collision resistance, outside the logic, and is witnessed by
; evaluation in the test book (the attached SHA-256).

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "frame-octets")
(local (include-book "arithmetic/top" :dir :system))

(defconst *fn-snap-magic* '(70 78 83 83))
(defconst *fn-snap-version* 1)
(defconst *fn-snap-prefix-octets* 32)
(defconst *fn-snap-digest-octets* 32)
(defconst *fn-snap-meta-octets* 48)
(defconst *fn-snap-genesis*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
(defconst *fn-snap-max-columns* 255)
(defconst *fn-snap-u64-limit* 18446744073709551616)

; -----------------------------------------------------------------------------
; The column table and the states.

(defun fn-snap-widthp (w)
  (declare (xargs :guard t))
  (and (natp w) (<= 1 w) (<= w 8)))

(defun fn-snap-widthsp (widths)
  (declare (xargs :guard t))
  (if (consp widths)
      (and (fn-snap-widthp (car widths)) (fn-snap-widthsp (cdr widths)))
    (null widths)))

(defun fn-snap-tablep (widths)
  (declare (xargs :guard t))
  (and (fn-snap-widthsp widths)
       (<= (len widths) *fn-snap-max-columns*)))

; Every value fits its width.
(defun fn-snap-fitp (vals w)
  (declare (xargs :guard (natp w)))
  (if (consp vals)
      (and (natp (car vals))
           (< (car vals) (expt 256 w))
           (fn-snap-fitp (cdr vals) w))
    (null vals)))

; A state: K columns, column c (1-based) the list of its elements.
(defun fn-snap-statep (cols widths)
  (declare (xargs :guard (fn-snap-widthsp widths)))
  (if (consp widths)
      (and (consp cols)
           (fn-snap-fitp (car cols) (car widths))
           (< (len (car cols)) *fn-snap-u64-limit*)
           (fn-snap-statep (cdr cols) (cdr widths)))
    (null cols)))

(defun fn-snap-lens (cols)
  (declare (xargs :guard t))
  (if (consp cols) (cons (len (car cols)) (fn-snap-lens (cdr cols))) nil))

; NEW extends OLD column by column.
(defun fn-snap-extendsp (old new)
  (declare (xargs :guard t))
  (if (consp old)
      (and (consp new)
           (true-listp (car old))
           (true-listp (car new))
           (<= (len (car old)) (len (car new)))
           (equal (take (len (car old)) (car new)) (car old))
           (fn-snap-extendsp (cdr old) (cdr new)))
    (atom new)))

; -----------------------------------------------------------------------------
; The encoding.

(defun fn-snap-words-octets (vals w)
  (declare (xargs :guard (natp w)))
  (if (consp vals)
      (append (fn-oct-word-octets (car vals) w)
              (fn-snap-words-octets (cdr vals) w))
    nil))

(defun fn-snap-prefix (col first count len)
  (declare (xargs :guard t))
  (append *fn-snap-magic*
          (list *fn-snap-version* (nfix col) 0 0)
          (fn-oct-word-octets first 8)
          (fn-oct-word-octets count 8)
          (fn-oct-word-octets len 8)))

; One segment after PREV: (mv octets digest).
(defun fn-snap-seg (prev col first count body)
  (declare (xargs :guard (true-listp body)))
  (let* ((pre (fn-snap-prefix col first count (len body)))
         (d (fn-frame-digest (append (true-list-fix prev) pre body))))
    (mv (append pre body d) d)))

; The chunks of VALS, at most MAX each (MAX positive; one chunk per call of
; the writer's work bound, D27: the bound is on a step, never on a column).
(defun fn-snap-chunks (vals max)
  (declare (xargs :guard (and (true-listp vals) (posp max))
                  :measure (len vals)))
  (if (and (consp vals) (posp max))
      (cons (take (min max (len vals)) vals)
            (fn-snap-chunks (nthcdr (min max (len vals)) vals) max))
    nil))

; The data segments of column COL for the elements VALS starting at FIRST.
(defun fn-snap-col-segs (prev col first chunks w)
  (declare (xargs :guard (and (natp first) (true-list-listp chunks) (natp w))
                  :verify-guards nil))
  (if (consp chunks)
      (mv-let (octets d)
        (fn-snap-seg prev col first (len (car chunks))
                     (fn-snap-words-octets (car chunks) w))
        (mv-let (rest d2)
          (fn-snap-col-segs d col (+ (nfix first) (len (car chunks)))
                            (cdr chunks) w)
          (mv (append octets rest) d2)))
    (mv nil prev)))

; Every column's elements past the previous commit's LENS, column 1 first.
(defun fn-snap-data (prev col lens cols widths max)
  (declare (xargs :guard (and (natp col) (nat-listp lens) (true-list-listp cols)
                              (fn-snap-widthsp widths) (posp max))
                  :verify-guards nil))
  (if (consp widths)
      (let* ((l (nfix (car lens)))
             (new (nthcdr l (true-list-fix (car cols)))))
        (mv-let (octets d)
          (fn-snap-col-segs prev col l (fn-snap-chunks new max) (car widths))
          (mv-let (rest d2)
            (fn-snap-data d (1+ (nfix col)) (cdr lens) (cdr cols) (cdr widths) max)
            (mv (append octets rest) d2))))
    (mv nil prev)))

(defun fn-snap-commit-body (lens meta)
  (declare (xargs :guard (true-listp meta)))
  (append (fn-snap-words-octets lens 8) meta))

; One write: the new elements of every column, then the commit of COLS'
; lengths with META.  (mv octets digest).
(defun fn-snap-write (prev lens cols meta widths max)
  (declare (xargs :guard (and (nat-listp lens) (true-list-listp cols)
                              (fn-snap-widthsp widths) (posp max)
                              (true-listp meta))
                  :verify-guards nil))
  (mv-let (data d)
    (fn-snap-data prev 1 lens cols widths max)
    (mv-let (commit d2)
      (fn-snap-seg d 0 0 1 (fn-snap-commit-body (fn-snap-lens cols) meta))
      (mv (append data commit) d2))))

; The file of successive writes of STATES (each with its META), from the
; empty snapshot.
(defun fn-snap-writes (prev lens states metas widths max)
  (declare (xargs :guard (and (nat-listp lens) (true-list-listp metas)
                              (fn-snap-widthsp widths) (posp max))
                  :verify-guards nil))
  (if (consp states)
      (mv-let (octets d)
        (fn-snap-write prev lens (car states) (car metas) widths max)
        (mv-let (rest d2)
          (fn-snap-writes d (fn-snap-lens (car states)) (cdr states) (cdr metas)
                          widths max)
          (mv (append octets rest) d2)))
    (mv nil prev)))

; -----------------------------------------------------------------------------
; The load: one pass over the buffer.

(defun fn-snap-shapep (col first count len lens widths)
  ; The prefix's fields against the lengths built so far.
  (declare (xargs :guard (and (nat-listp lens) (fn-snap-widthsp widths))))
  (if (equal col 0)
      (and (equal first 0) (equal count 1)
           (equal len (+ (* 8 (len widths)) *fn-snap-meta-octets*)))
    (and (natp col)
         (<= col (len widths))
         (posp count)
         (equal first (nfix (nth (1- col) lens)))
         (equal len (* count (nfix (nth (1- col) widths)))))))

(defun fn-snap-read-u64s (i k fn-octets)
  ; K little-endian u64 words from I.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp k)
                              (<= (+ i (* 8 k)) (fn-octets-len fn-octets)))
                  :measure (nfix k)))
  (if (zp k)
      nil
    (cons (fn-octets-get-word i 8 fn-octets)
          (fn-snap-read-u64s (+ (nfix i) 8) (1- k) fn-octets))))

; The scan.  LAST is NIL or the last accepted commit (END DIGEST LENS META
; DESCS), DESCS newest first, each (COL FIRST COUNT BODY-OFFSET).
; (mv REASON LAST).
(defun fn-snap-scan (i end prev lens descs last widths fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end)
                              (<= end (fn-octets-len fn-octets))
                              (nat-listp lens) (fn-snap-widthsp widths))
                  :measure (nfix (- (nfix end) (nfix i)))
                  :verify-guards nil))
  (let ((i (nfix i)) (end (nfix end)))
    (cond
     ((<= end i) (mv :end last))
     ((< end (+ i *fn-snap-prefix-octets*)) (mv :torn last))
     ((not (and (equal (fn-octets-get i fn-octets) 70)
                (equal (fn-octets-get (+ i 1) fn-octets) 78)
                (equal (fn-octets-get (+ i 2) fn-octets) 83)
                (equal (fn-octets-get (+ i 3) fn-octets) 83)
                (equal (fn-octets-get (+ i 4) fn-octets) *fn-snap-version*)
                (equal (fn-octets-get (+ i 6) fn-octets) 0)
                (equal (fn-octets-get (+ i 7) fn-octets) 0)))
      (mv :shape last))
     (t
      (let* ((col (fn-octets-get (+ i 5) fn-octets))
             (first (fn-octets-get-word (+ i 8) 8 fn-octets))
             (count (fn-octets-get-word (+ i 16) 8 fn-octets))
             (len (fn-octets-get-word (+ i 24) 8 fn-octets))
             (b (+ i *fn-snap-prefix-octets* len))
             (e (+ b *fn-snap-digest-octets*)))
        (cond
         ((< end e) (mv :torn last))
         ((not (fn-snap-shapep col first count len lens widths)) (mv :shape last))
         (t
          (let ((d (fn-oct-slice-list b e fn-octets)))
            (if (not (equal d (fn-frame-digest
                               (append prev (fn-oct-slice-list i b fn-octets)))))
                (mv :digest last)
              (if (equal col 0)
                  (let ((stated (fn-snap-read-u64s (+ i *fn-snap-prefix-octets*)
                                                   (len widths) fn-octets)))
                    (if (not (equal stated lens))
                        (mv :commit last)
                      (fn-snap-scan e end d lens descs
                                    (list e d lens
                                          (fn-oct-slice-list
                                           (+ i *fn-snap-prefix-octets* (* 8 (len widths)))
                                           b fn-octets)
                                          descs)
                                    widths fn-octets)))
                (fn-snap-scan e end d
                              (update-nth (1- col) (+ first count) lens)
                              (cons (list col first count (+ i *fn-snap-prefix-octets*))
                                    descs)
                              last widths fn-octets)))))))))))

; -----------------------------------------------------------------------------
; What a commit denotes.

(defun fn-snap-seg-values (a count w x)
  ; COUNT words of W octets from offset A of the octet list X.
  (declare (xargs :guard (and (natp a) (natp count) (natp w))
                  :measure (nfix count)))
  (if (zp count)
      nil
    (cons (fn-oct-word-at a w x)
          (fn-snap-seg-values (+ (nfix a) (nfix w)) (1- count) w x))))

; Column COL's elements, from the descriptors (newest first).
(defun fn-snap-column (col descs widths x)
  (declare (xargs :guard (and (true-list-listp descs) (fn-snap-widthsp widths))
                  :verify-guards nil))
  (if (consp descs)
      (let ((d (car descs)))
        (append (fn-snap-column col (cdr descs) widths x)
                (if (equal (nth 0 d) col)
                    (fn-snap-seg-values (nth 3 d) (nth 2 d)
                                        (nth (1- col) widths) x)
                  nil)))
    nil))

(defun fn-snap-columns-from (col k descs widths x)
  (declare (xargs :guard (and (natp col) (natp k))
                  :measure (nfix k) :verify-guards nil))
  (if (zp k)
      nil
    (cons (fn-snap-column col descs widths x)
          (fn-snap-columns-from (1+ (nfix col)) (1- k) descs widths x))))

; The state the last commit of a scan denotes.
(defun fn-snap-denotes (last widths x)
  (declare (xargs :verify-guards nil))
  (fn-snap-columns-from 1 (len widths) (nth 4 last) widths x))

; -----------------------------------------------------------------------------
; The scan over what the writer wrote, one segment at a time.  A data segment
; (`fn-snap-scan-of-seg', over the writer's own `fn-snap-seg') advances the scan
; past itself with its column's length grown by its count and its descriptor
; kept; a commit (`fn-snap-scan-of-commit-seg') whose stated lengths are the
; lengths built becomes the last commit.  The file-level keystones
; (`fn-snap-scan-of-writes', `fn-snap-scan-of-torn-write') compose these over
; `fn-snap-col-segs', `fn-snap-data' and `fn-snap-writes': OPEN (lane
; snapshot-open LANEDUMP, the exact next step).

(defthm fn-snap-nth-of-nthcdr
  (implies (and (natp i) (natp j))
           (equal (nth j (nthcdr i x)) (nth (+ i j) x)))
  :hints (("Goal" :in-theory (enable nth nthcdr) :induct (nthcdr i x))))

(local
 (defun fn-snap-wa-ind (j k)
   (declare (xargs :measure (nfix k)))
   (if (posp k) (fn-snap-wa-ind (1+ (nfix j)) (1- k)) (list j k))))

(defthm fn-snap-word-at-of-nthcdr
  (implies (and (natp i) (natp j))
           (equal (fn-oct-word-at j k (nthcdr i x))
                  (fn-oct-word-at (+ i j) k x)))
  :hints (("Goal" :induct (fn-snap-wa-ind j k)
           :in-theory (enable fn-oct-word-at))))

(defthm fn-snap-word-at-of-word-octets
  (implies (and (natp v) (< v (expt 256 (nfix k))))
           (equal (fn-oct-word-at 0 k (fn-oct-word-octets v k)) v))
  :hints (("Goal" :induct (fn-oct-word-octets v k)
           :in-theory (enable fn-oct-word-octets)
           :expand ((fn-oct-word-at 0 k (fn-oct-word-octets v k))))
          ("Subgoal *1/1" :use ((:instance fn-snap-word-at-of-nthcdr (i 1) (j 0) (k (1- k))
                                           (x (cons (mod v 256) (fn-oct-word-octets (floor v 256) (1- k)))))))))

(defthm fn-snap-nth-of-append
  (implies (and (natp j) (< j (len a)))
           (equal (nth j (append a b)) (nth j a)))
  :hints (("Goal" :in-theory (enable nth) :induct (nth j a))))

(defthm fn-snap-word-at-of-append
  (implies (and (natp j) (<= (+ j (nfix k)) (len a)))
           (equal (fn-oct-word-at j k (append a b))
                  (fn-oct-word-at j k a)))
  :hints (("Goal" :induct (fn-snap-wa-ind j k)
           :in-theory (enable fn-oct-word-at))))

(defthm fn-snap-nth-of-append-past
  (implies (natp j)
           (equal (nth (+ j (len a)) (append a b)) (nth j b)))
  :hints (("Goal" :in-theory (enable nth) :induct (len a))))

(defthm fn-snap-nth-of-append-len
  (equal (nth (len a) (append a b)) (car b))
  :hints (("Goal" :use ((:instance fn-snap-nth-of-append-past (j 0))))))

(defthm fn-snap-word-at-of-append-past
  (implies (natp j)
           (equal (fn-oct-word-at (+ j (len a)) k (append a b))
                  (fn-oct-word-at j k b)))
  :hints (("Goal" :use ((:instance fn-snap-word-at-of-nthcdr (i (len a)) (x (append a b))))
           :in-theory (disable fn-snap-word-at-of-nthcdr))))

(defthm fn-snap-nthcdr-of-append-past
  (implies (natp j)
           (equal (nthcdr (+ j (len a)) (append a b)) (nthcdr j b)))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (len a))))

(defthm fn-snap-nthcdr-of-append-len
  (equal (nthcdr (len a) (append a b)) b)
  :hints (("Goal" :use ((:instance fn-snap-nthcdr-of-append-past (j 0))))))

(defthm fn-snap-take-of-append-within
  (implies (and (natp n) (<= n (len a)))
           (equal (take n (append a b)) (take n a)))
  :hints (("Goal" :in-theory (enable take) :induct (take n a))))

(defthm fn-snap-take-of-append-exact
  (implies (true-listp a)
           (equal (take (len a) (append a b)) a))
  :hints (("Goal" :in-theory (enable take) :induct (len a))))

(defthm fn-snap-len-words-octets
  (equal (len (fn-snap-words-octets vals w)) (* (len vals) (nfix w))))

(defthm fn-snap-true-listp-words-octets
  (true-listp (fn-snap-words-octets vals w))
  :rule-classes :type-prescription)

(defthm fn-snap-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-snap-len-prefix
  (equal (len (fn-snap-prefix col first count len)) 32))

(defthm fn-snap-octet-listp-word-octets-words
  (fn-cbor-octet-listp (fn-snap-words-octets vals w)))

(defthm fn-snap-width-of-nth
  (implies (and (fn-snap-widthsp widths) (natp j) (< j (len widths)))
           (and (integerp (nth j widths))
                (<= 1 (nth j widths))
                (<= (nth j widths) 8)))
  :hints (("Goal" :in-theory (enable nth) :induct (nth j widths))))

(defthm fn-snap-width-of-nth-linear
  (implies (and (fn-snap-widthsp widths) (natp j) (< j (len widths)))
           (and (<= 1 (nth j widths))
                (<= (nth j widths) 8)))
  :rule-classes :linear)

(defthm fn-snap-natp-nth-lens
  (implies (and (nat-listp lens) (natp j) (< j (len lens)))
           (natp (nth j lens)))
  :hints (("Goal" :in-theory (enable nth) :induct (nth j lens)))
  :rule-classes ((:rewrite) (:type-prescription)))

(defthm fn-snap-prefix-bytes
  (and (equal (car (append (fn-snap-prefix col f c l) b)) 70)
       (equal (nth 1 (append (fn-snap-prefix col f c l) b)) 78)
       (equal (nth 2 (append (fn-snap-prefix col f c l) b)) 83)
       (equal (nth 3 (append (fn-snap-prefix col f c l) b)) 83)
       (equal (nth 4 (append (fn-snap-prefix col f c l) b)) 1)
       (equal (nth 5 (append (fn-snap-prefix col f c l) b)) (nfix col))
       (equal (nth 6 (append (fn-snap-prefix col f c l) b)) 0)
       (equal (nth 7 (append (fn-snap-prefix col f c l) b)) 0))
  :hints (("Goal" :in-theory (enable fn-snap-prefix))))

(defthm fn-snap-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-snap-word-at-of-cons
  (implies (posp j)
           (equal (fn-oct-word-at j k (cons e x))
                  (fn-oct-word-at (1- j) k x)))
  :hints (("Goal" :use ((:instance fn-snap-word-at-of-nthcdr (i 1) (j (1- j)) (x (cons e x))))
           :in-theory (disable fn-snap-word-at-of-nthcdr))))

(defthm fn-snap-word-at-of-append-beyond
  (implies (and (natp j) (<= (len a) j))
           (equal (fn-oct-word-at j k (append a b))
                  (fn-oct-word-at (- j (len a)) k b)))
  :hints (("Goal" :use ((:instance fn-snap-word-at-of-append-past (j (- j (len a)))))
           :in-theory (disable fn-snap-word-at-of-append-past))))

(defthm fn-snap-prefix-words
  (implies (and (natp f) (< f 18446744073709551616)
                (natp c) (< c 18446744073709551616)
                (natp l) (< l 18446744073709551616))
           (and (equal (fn-oct-word-at 8 8 (append (fn-snap-prefix col f c l) b)) f)
                (equal (fn-oct-word-at 16 8 (append (fn-snap-prefix col f c l) b)) c)
                (equal (fn-oct-word-at 24 8 (append (fn-snap-prefix col f c l) b)) l)))
  :hints (("Goal" :in-theory (enable fn-snap-prefix))))

(defthm fn-snap-nthcdr-of-append-beyond
  (implies (and (natp j) (<= (len a) j))
           (equal (nthcdr j (append a b)) (nthcdr (- j (len a)) b)))
  :hints (("Goal" :use ((:instance fn-snap-nthcdr-of-append-past (j (- j (len a)))))
           :in-theory (disable fn-snap-nthcdr-of-append-past))))

(defthm fn-snap-take-of-append-exact2
  (implies (and (true-listp a) (equal (len a) n))
           (equal (take n (append a b)) a)))

(local (defun fn-snap-tal-ind (a n) (if (consp a) (fn-snap-tal-ind (cdr a) (1- n)) (list a n))))

(defthm fn-snap-nonneg-product
  (implies (and (natp a) (natp b)) (and (integerp (* a b)) (<= 0 (* a b)))))

(defthm fn-snap-take-of-append-longer
  (implies (and (true-listp a) (natp n) (<= (len a) n))
           (equal (take n (append a b)) (append a (take (- n (len a)) b))))
  :hints (("Goal" :in-theory (enable take) :induct (fn-snap-tal-ind a n))))

(defthm fn-snap-true-listp-digest
  (true-listp (fn-frame-digest x))
  :hints (("Goal" :use ((:instance fn-frame-digest-octet-listp (octets x)))
           :in-theory (enable fn-cbor-octet-listp)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-snap-true-listp-prefix
  (true-listp (fn-snap-prefix col first count len))
  :rule-classes :type-prescription)

(in-theory (disable fn-snap-prefix))

(defthm fn-snap-prefix-words-alone
  (implies (and (natp f) (< f 18446744073709551616)
                (natp c) (< c 18446744073709551616)
                (natp l) (< l 18446744073709551616))
           (and (equal (fn-oct-word-at 8 8 (fn-snap-prefix col f c l)) f)
                (equal (fn-oct-word-at 16 8 (fn-snap-prefix col f c l)) c)
                (equal (fn-oct-word-at 24 8 (fn-snap-prefix col f c l)) l)))
  :hints (("Goal" :use ((:instance fn-snap-prefix-words (b nil)))
           :in-theory (disable fn-snap-prefix-words))))

(defthm fn-snap-prefix-bytes-alone
  (and (equal (car (fn-snap-prefix col f c l)) 70)
       (equal (nth 1 (fn-snap-prefix col f c l)) 78)
       (equal (nth 2 (fn-snap-prefix col f c l)) 83)
       (equal (nth 3 (fn-snap-prefix col f c l)) 83)
       (equal (nth 4 (fn-snap-prefix col f c l)) 1)
       (equal (nth 5 (fn-snap-prefix col f c l)) (nfix col))
       (equal (nth 6 (fn-snap-prefix col f c l)) 0)
       (equal (nth 7 (fn-snap-prefix col f c l)) 0))
  :hints (("Goal" :in-theory (enable fn-snap-prefix))))

(defthm fn-snap-len-pos (implies (consp x) (< 0 (len x))) :rule-classes :linear)

(defthm fn-snap-scan-of-data-seg
  (let* ((w (nth (1- col) widths))
         (first (nth (1- col) lens))
         (body (fn-snap-words-octets vals w))
         (pre (fn-snap-prefix col first (len vals) (len body)))
         (d (fn-frame-digest (append prev pre body)))
         (x (append a (append pre (append body (append d rest))))))
    (implies (and (true-listp a) (true-listp rest) (true-listp prev)
                  (posp col) (<= col (len widths)) (< col 256)
                  (fn-snap-widthsp widths) (nat-listp lens)
                  (equal (len lens) (len widths))
                  (consp vals)
                  (< first *fn-snap-u64-limit*)
                  (< (len vals) *fn-snap-u64-limit*)
                  (< (len body) *fn-snap-u64-limit*)
                  (natp end) (<= (+ (len a) 64 (len body)) end)
                  (<= end (len x)))
             (equal (fn-snap-scan (len a) end prev lens descs last widths x)
                    (fn-snap-scan (+ (len a) 64 (len body)) end d
                                  (update-nth (1- col) (+ first (len vals)) lens)
                                  (cons (list col first (len vals) (+ 32 (len a))) descs)
                                  last widths x))))
  :hints (("Goal" :expand ((:free (x) (fn-snap-scan (len a) end prev lens descs last widths x)))
           :use ((:instance fn-snap-nonneg-product (a (len vals)) (b (nth (1- col) widths))))
           :in-theory (disable fn-snap-scan))))

(local
 (defun fn-snap-ru-ind (j k)
   (declare (xargs :measure (nfix k)))
   (if (zp k) (list j k) (fn-snap-ru-ind (+ (nfix j) 8) (1- k)))))

(defthm fn-snap-read-u64s-of-nthcdr
  (implies (and (natp i) (natp j))
           (equal (fn-snap-read-u64s j k (nthcdr i x))
                  (fn-snap-read-u64s (+ i j) k x)))
  :hints (("Goal" :induct (fn-snap-ru-ind j k)
           :in-theory (enable fn-snap-read-u64s))))

(defun fn-snap-u64-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (< (car xs) 18446744073709551616)
           (fn-snap-u64-listp (cdr xs)))
    (null xs)))

(defthm fn-snap-word-at-of-append-len
  (equal (fn-oct-word-at (len a) k (append a b))
         (fn-oct-word-at 0 k b))
  :hints (("Goal" :use ((:instance fn-snap-word-at-of-append-past (j 0))))))

(local
 (defun fn-snap-rw-ind (lens pre)
   (if (consp lens)
       (fn-snap-rw-ind (cdr lens) (append pre (fn-oct-word-octets (car lens) 8)))
     (list lens pre))))

(defthm fn-snap-read-u64s-of-words
  (implies (fn-snap-u64-listp lens)
           (equal (fn-snap-read-u64s (len pre) (len lens)
                                     (append pre (append (fn-snap-words-octets lens 8) r)))
                  lens))
  :hints (("Goal" :induct (fn-snap-rw-ind lens pre)
           :in-theory (enable fn-snap-read-u64s))))

(defthm fn-snap-u64-listp-when-nat-listp-bounded
  (implies (fn-snap-u64-listp xs) (nat-listp xs)))

(defthm fn-snap-scan-of-commit-seg
  (let* ((body (fn-snap-commit-body lens meta))
         (pre (fn-snap-prefix 0 0 1 (len body)))
         (d (fn-frame-digest (append prev pre body)))
         (x (append a (append pre (append body (append d rest))))))
    (implies (and (true-listp a) (true-listp rest) (true-listp prev)
                  (true-listp meta) (equal (len meta) 48)
                  (fn-snap-widthsp widths)
                  (fn-snap-u64-listp lens)
                  (equal (len lens) (len widths))
                  (< (len body) *fn-snap-u64-limit*)
                  (natp end)
                  (<= (+ (len a) 64 (len body)) end)
                  (<= end (len x)))
             (equal (fn-snap-scan (len a) end prev lens descs last widths x)
                    (fn-snap-scan (+ (len a) 64 (len body)) end d lens descs
                                  (list (+ (len a) 64 (len body)) d lens meta descs)
                                  widths x))))
  :hints (("Goal" :expand ((:free (x) (fn-snap-scan (len a) end prev lens descs last widths x)))
           :use ((:instance fn-snap-read-u64s-of-words
                            (pre (append a (fn-snap-prefix 0 0 1 (len (fn-snap-commit-body lens meta)))))
                            (r (append meta (append (fn-frame-digest (append prev (fn-snap-prefix 0 0 1 (len (fn-snap-commit-body lens meta))) (fn-snap-commit-body lens meta))) rest)))))
           :in-theory (disable fn-snap-scan fn-snap-read-u64s-of-words))))

(defun fn-snap-col-descs (col first chunks at w descs)
  ; The descriptors the scan conses for COL's segments of CHUNKS written at AT.
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chunks)
      (fn-snap-col-descs col (+ (nfix first) (len (car chunks))) (cdr chunks)
                         (+ (nfix at) 64 (* (len (car chunks)) (nfix w))) w
                         (cons (list col (nfix first) (len (car chunks)) (+ (nfix at) 32)) descs))
    descs))

(defun fn-snap-chunks-okp (chunks first w)
  (declare (xargs :guard t))
  (if (consp chunks)
      (and (consp (car chunks))
           (< (nfix first) *fn-snap-u64-limit*)
           (< (len (car chunks)) *fn-snap-u64-limit*)
           (< (* (len (car chunks)) (nfix w)) *fn-snap-u64-limit*)
           (fn-snap-chunks-okp (cdr chunks) (+ (nfix first) (len (car chunks))) w))
    t))

(defun fn-snap-chunks-len (chunks)
  (declare (xargs :guard t))
  (if (consp chunks) (+ (len (car chunks)) (fn-snap-chunks-len (cdr chunks))) 0))

(defthm fn-snap-true-listp-col-segs
  (true-listp (mv-nth 0 (fn-snap-col-segs prev col first chunks w))))

(defthm fn-snap-true-listp-col-segs-digest
  (implies (true-listp prev)
           (true-listp (mv-nth 1 (fn-snap-col-segs prev col first chunks w)))))

(defthm fn-snap-len-col-segs
  (equal (len (mv-nth 0 (fn-snap-col-segs prev col first chunks w)))
         (+ (* 64 (len chunks)) (* (fn-snap-chunks-len chunks) (nfix w)))))

(defthm fn-snap-update-nth-nth-same
  (implies (< (nfix n) (len l))
           (equal (update-nth n (nth n l) l) l)))

(defthm fn-snap-len-seg
  (equal (len (mv-nth 0 (fn-snap-seg prev col first count body)))
         (+ 64 (len body))))

(defthm fn-snap-true-listp-seg
  (and (true-listp (mv-nth 0 (fn-snap-seg prev col first count body)))
       (true-listp (mv-nth 1 (fn-snap-seg prev col first count body)))))

(local
 (defun fn-snap-cs-ind (prev col first chunks w a lens descs)
   (if (consp chunks)
       (mv-let (octets d)
         (fn-snap-seg prev col first (len (car chunks)) (fn-snap-words-octets (car chunks) w))
         (fn-snap-cs-ind d col (+ (nfix first) (len (car chunks))) (cdr chunks) w
                         (append a octets)
                         (update-nth (1- col) (+ (nfix first) (len (car chunks))) lens)
                         (cons (list col (nfix first) (len (car chunks)) (+ (len a) 32)) descs)))
     (list prev col first chunks w a lens descs))))

(defthm fn-snap-len-update-nth
  (implies (< (nfix n) (len l))
           (equal (len (update-nth n v l)) (len l))))

(defthm fn-snap-nat-listp-update-nth
  (implies (and (nat-listp l) (natp v) (< (nfix n) (len l)))
           (nat-listp (update-nth n v l))))

(defthm fn-snap-true-list-fix-id (implies (true-listp x) (equal (true-list-fix x) x)))

(defthm fn-snap-scan-of-seg
  (let* ((w (nth (1- col) widths))
         (first (nth (1- col) lens))
         (s (fn-snap-seg prev col first (len vals) (fn-snap-words-octets vals w)))
         (x (append a (append (mv-nth 0 s) rest))))
    (implies (and (true-listp a) (true-listp rest) (true-listp prev)
                  (posp col) (<= col (len widths)) (< col 256)
                  (fn-snap-widthsp widths) (nat-listp lens)
                  (equal (len lens) (len widths))
                  (consp vals)
                  (< first *fn-snap-u64-limit*)
                  (< (len vals) *fn-snap-u64-limit*)
                  (< (* (len vals) w) *fn-snap-u64-limit*)
                  (natp end) (<= (+ (len a) 64 (* (len vals) w)) end)
                  (<= end (len x)))
             (equal (fn-snap-scan (len a) end prev lens descs last widths x)
                    (fn-snap-scan (+ (len a) 64 (* (len vals) w)) end (mv-nth 1 s)
                                  (update-nth (1- col) (+ first (len vals)) lens)
                                  (cons (list col first (len vals) (+ 32 (len a))) descs)
                                  last widths x))))
  :hints (("Goal" :use ((:instance fn-snap-scan-of-data-seg))
           :in-theory (e/d (fn-snap-seg) (fn-snap-scan fn-snap-scan-of-data-seg)))))

(defthm fn-snap-update-nth-twice (equal (update-nth n v2 (update-nth n v1 l)) (update-nth n v2 l)))

(defthm fn-snap-true-listp-append (equal (true-listp (append a b)) (true-listp b)))
