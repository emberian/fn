; fn: the record log's crash theorem (design 2026-09-27-storage-log section 5.1, T2).
;
; P-BATCH appends a batch's entries with ONE pending write at the frontier F
; of the segment inode and fences it once.  This book proves what a crash
; image of that inode scans to, over the byte model's own crash
; (books/byte-store.lisp fn-bs-crash, fn-bs-tear-write):
;
;   fn-bs-crash-of-aligned-append   the SHIFT LEMMA: a crash of an inode
;                                   holding D ++ Z (len D = F, a multiple of
;                                   the unit) with one pending write of W at
;                                   F holds D followed by the offset-0 tear
;                                   of W over Z;
;   fn-lg-batch-tear-is-a-prefix    the scan of a tear of a batch's log over
;                                   a zero region is a PREFIX of the batch
;                                   (with the prefix's aligned length as its
;                                   consumed count), or the first damaged
;                                   entry validates as a chained frame that is
;                                   not the written one (fn-lg-forgery-in);
;   fn-lg-batch-crash-is-a-prefix   T2 over the store: every crash image of a
;                                   segment whose durable content scans
;                                   completely to COMMITTED, with the batch's
;                                   one pending write at the frontier, scans to
;                                   COMMITTED ++ a prefix of the batch, or a
;                                   forgery;
;   fn-lg-batch-crash-is-a-prefix-under-a-crypto-trailer
;                                   the corollary: when every entry's observed
;                                   slice is a platform tear of its frame
;                                   (A-CRYPTO-TRAILER, books/assumptions.lisp),
;                                   the forgery disjunct goes.
;
; The segment is PREALLOCATED (the coordinator's addition of 2026-09-27,
; standard in WAL engines): the durable content past the frontier is a zero
; region at least as long as the batch, so the append overwrites zeros inside
; the file's size.  A zero region is "no entry" (its first octets are not the
; log's magic), distinct from a torn entry; fdatasync then fences exactly what
; the model's fn-bs-fsync-file fences, since no size or block allocation
; changes.  The host refuses an append that does not fit the extent
; (fn-lg-fits-extentp): rotation or extension is lane w6-log-recovery's step.

(in-package "ACL2")
(include-book "store-log")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-bs-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; List vocabulary (local copies: the prototype's are local to it).

(defthm fn-lgc-len-nthcdr
   (equal (len (nthcdr k x)) (nfix (- (len x) (nfix k))))
   :hints (("Goal" :induct (nthcdr k x))))

(defthm fn-lgc-nthcdr-shorter
   (implies (and (posp k) (consp x))
            (< (len (nthcdr k x)) (len x)))
   :rule-classes :linear)

(defthm fn-lgc-take-len
   (equal (len (fn-bs-take n x)) (nfix n)))

(defthm fn-lgc-len-append
   (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-lgc-append-assoc
   (equal (append (append a b) c) (append a (append b c))))

(defthm fn-lgc-take-of-append-exact
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-bs-take n (append a b)) a)))

(defthm fn-lgc-take-of-append-shorter
   (implies (and (natp n) (<= n (len a)))
            (equal (fn-bs-take n (append a b)) (fn-bs-take n a))))

(defthm fn-lgc-take-of-append-longer
   (implies (and (true-listp a) (natp n) (<= (len a) n))
            (equal (fn-bs-take n (append a b))
                   (append a (fn-bs-take (- n (len a)) b))))
   :hints (("Goal" :induct (fn-bs-take n a))))

(defthm fn-lgc-nthcdr-of-append-exact
   (implies (equal n (len a))
            (equal (nthcdr n (append a b)) b)))

(defthm fn-lgc-nthcdr-of-append-shorter
   (implies (and (natp n) (<= n (len a)))
            (equal (nthcdr n (append a b)) (append (nthcdr n a) b)))
   :hints (("Goal" :induct (nthcdr n a))))

(defthm fn-lgc-nthcdr-of-append-longer
   (implies (and (true-listp a) (natp n) (<= (len a) n))
            (equal (nthcdr n (append a b)) (nthcdr (- n (len a)) b)))
   :hints (("Goal" :induct (nthcdr n a))))

(defthm fn-lgc-nthcdr-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x))))

(defthm fn-lgc-true-listp-append
   (implies (true-listp b) (true-listp (append a b))))

(defthm fn-lgc-append-nil
   (implies (true-listp x) (equal (append x nil) x)))

(defthm fn-lgc-take-then-nthcdr
   (implies (and (true-listp x) (natp n) (<= n (len x)))
            (equal (append (fn-bs-take n x) (nthcdr n x)) x))
   :hints (("Goal" :induct (nthcdr n x))))

(defthm fn-lgc-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x))))

(defthm fn-lgc-take-of-take
   (implies (and (natp m) (natp n) (<= m n))
            (equal (fn-bs-take m (fn-bs-take n x)) (fn-bs-take m x)))
   :hints (("Goal" :induct (list (fn-bs-take m x) (fn-bs-take n x)))))

(defthm fn-lgc-take-of-nthcdr-of-take
   (implies (and (natp k) (natp m) (natp n) (<= (+ k m) n))
            (equal (fn-bs-take m (nthcdr k (fn-bs-take n x)))
                   (fn-bs-take m (nthcdr k x)))))


(defthm fn-lgc-take-all
  (implies (and (true-listp a) (equal n (len a)))
           (equal (fn-bs-take n a) a)))

(defthm fn-lgc-len-nthcdr-of-atom
  (implies (atom x) (equal (len (nthcdr k x)) 0)))

(defthm fn-lgc-octets-true-listp
  (implies (fn-cbor-octet-listp x) (true-listp x)))

(defthm fn-lgc-nthcdr-past-end-is-atom
  (implies (<= (len x) (nfix k)) (atom (nthcdr k x))))

(defthm fn-lgc-scan-of-atom
  (implies (atom x) (equal (fn-lg-scan x prev unit max) (cons nil 0))))

; -----------------------------------------------------------------------------
; Zero regions.

(defun fn-lg-zerosp (x)
  (declare (xargs :guard t))
  (if (consp x) (and (equal (car x) 0) (fn-lg-zerosp (cdr x))) (null x)))

(defthm fn-lg-zerosp-true-listp
  (implies (fn-lg-zerosp x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm fn-lg-zerosp-of-nthcdr
  (implies (fn-lg-zerosp x) (fn-lg-zerosp (nthcdr n x))))

(defthm fn-lg-zerosp-of-zeros
  (fn-lg-zerosp (fn-bs-zeros n)))

(defthm fn-lgc-take-of-zerosp
   (implies (and (fn-lg-zerosp x) (posp n))
            (equal (car (fn-bs-take n x)) 0)))

; A zero region is no entry: its front is not the log's magic, so the scan
; stops there and reads nothing.
(defthm fn-lg-scan-of-zeros
  (implies (fn-lg-zerosp z)
           (equal (fn-lg-scan z prev unit max) (cons nil 0)))
  :hints (("Goal" :expand ((fn-lg-scan z prev unit max)
                           (fn-lg-slice z)
                           (fn-lg-declared-len z)
                           (fn-bs-take 4 z))
           :in-theory (disable fn-lg-entry-okp))))

; -----------------------------------------------------------------------------
; The pieces of an aligned write: the byte model's tear, one unit at a time.

(defun fn-lg-pieces (ino start w sels unit)
  (declare (xargs :guard t :verify-guards nil :measure (len w)))
  (if (or (atom sels) (zp unit) (atom w))
      nil
    (let* ((n (min unit (len w)))
           (sel (car sels))
           (rest (fn-lg-pieces ino (+ (nfix start) unit) (nthcdr unit w) (cdr sels) unit)))
      (cond ((equal sel :new) (cons (list :write ino (nfix start) (fn-bs-take n w)) rest))
            ((equal sel :zero) (cons (list :write ino (nfix start) (fn-bs-zeros n)) rest))
            ((and (consp sel) (equal (car sel) :garble))
             (cons (list :write ino (nfix start) (fn-bs-take n (cdr sel))) rest))
            (t rest)))))

; The floor arithmetic of fn-bs-tear-write at an aligned offset, once.
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgc-floor-shift
     (implies (and (integerp k) (posp unit) (integerp x))
              (equal (floor (+ (* k unit) x) unit) (+ k (floor x unit)))))
   (defthm fn-lgc-le-floor
     (implies (and (integerp i) (posp unit) (integerp y))
              (iff (<= i (floor y unit)) (<= (* i unit) y)))
     :hints (("Goal" :cases ((<= i (floor y unit))))))
   (defthm fn-lgc-times-plus-one
     (equal (* (+ 1 a) unit) (+ unit (* a unit))))))

(defthm fn-lgc-floor-aligned
   (implies (and (natp k) (posp unit))
            (equal (floor (* k unit) unit) k))
   :hints (("Goal" :in-theory (disable floor fn-lgc-floor-shift)
            :use ((:instance fn-lgc-floor-shift (x 0))))))

(defthm fn-lgc-unit-count-aligned
   (implies (and (natp k) (posp unit) (natp len) (natp i))
            (equal (< i (fn-bs-unit-count (* k unit) len unit))
                   (< (* i unit) len)))
   :hints (("Goal" :in-theory (e/d (fn-bs-unit-count) (floor fn-lgc-floor-shift fn-lgc-le-floor))
            :use ((:instance fn-lgc-floor-shift (x (+ -1 len)))
                  (:instance fn-lgc-floor-shift (x 0))
                  (:instance fn-lgc-le-floor (y (+ -1 len)))))))

(local (in-theory (disable fn-bs-unit-count)))

(defthm fn-lgc-consp-nthcdr
   (iff (consp (nthcdr n x)) (< (nfix n) (len x)))
   :hints (("Goal" :induct (nthcdr n x))))

(defthm fn-lg-tear-write-is-pieces
  (implies (and (natp k) (posp unit) (natp i) (true-listp w))
           (equal (fn-bs-tear-write (list :write ino (* k unit) w) sels i unit)
                  (fn-lg-pieces ino (+ (* k unit) (* i unit)) (nthcdr (* i unit) w)
                                sels unit)))
  :hints (("Goal" :induct (fn-bs-tear-write (list :write ino (* k unit) w) sels i unit)
           :in-theory (disable floor)
           :expand ((fn-bs-tear-write (list :write ino (* k unit) w) sels i unit)
                    (fn-lg-pieces ino (+ (* k unit) (* i unit)) (nthcdr (* i unit) w)
                                  sels unit)))))

; -----------------------------------------------------------------------------
; One inode's content under a list of writes to it.

(defun fn-lg-apply-to (c ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (fn-lg-apply-to (fn-bs-splice c (nth 2 (car ops)) (nth 3 (car ops))) (cdr ops))
    c))

(defun fn-lg-writes-to (ops ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (consp (car ops)) (equal (car (car ops)) :write)
           (equal (nth 1 (car ops)) ino)
           (fn-lg-writes-to (cdr ops) ino))
    t))

(defthm fn-lg-pieces-write-to
  (fn-lg-writes-to (fn-lg-pieces ino start w sels unit) ino))

(defthm fn-lg-apply-writes-of-writes-to
  (implies (and (fn-lg-writes-to ops ino) ino)
           (equal (cdr (assoc-equal ino (fn-bs-apply-writes inodes ops)))
                  (fn-lg-apply-to (cdr (assoc-equal ino inodes)) ops)))
  :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
           :in-theory (disable fn-bs-splice))))

; The splice arithmetic.
(defthm fn-lgc-splice-len
   (equal (len (fn-bs-splice old offset octets))
          (max (len old) (+ (nfix offset) (len octets)))))

(defthm fn-lgc-splice-true-listp
   (implies (true-listp old) (true-listp (fn-bs-splice old offset octets))))

; A write at F + s over D ++ Z with len D = F is D followed by the write at
; s over Z: fn-bs-splice past a prefix is a splice of the rest.
(defthm fn-lg-splice-past-prefix
  (implies (and (true-listp d) (natp s))
           (equal (fn-bs-splice (append d z) (+ (len d) s) octets)
                  (append d (fn-bs-splice z s octets)))))

; Every write in OPS ends at or before BOUND and starts at or after LOW.
(defun fn-lg-writes-between (ops low bound)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (natp (nth 2 (car ops)))
           (true-listp (nth 3 (car ops)))
           (<= low (nth 2 (car ops)))
           (<= (+ (nth 2 (car ops)) (len (nth 3 (car ops)))) bound)
           (fn-lg-writes-between (cdr ops) low bound))
    t))

(defthm fn-lgc-zeros-len
   (equal (len (fn-bs-zeros n)) (nfix n)))

(defthm fn-lgc-zeros-true-listp
   (true-listp (fn-bs-zeros n)))

(defthm fn-lgc-writes-between-weaken
   (implies (and (fn-lg-writes-between ops low bound)
                 (<= low2 low) (<= bound bound2))
            (fn-lg-writes-between ops low2 bound2)))

(defthm fn-lgc-pieces-of-short
   (implies (<= (len w) 0) (equal (fn-lg-pieces ino start w sels unit) nil)))

(defthm fn-lg-pieces-between
  (implies (and (natp start) (posp unit))
           (fn-lg-writes-between (fn-lg-pieces ino start w sels unit)
                                 start (+ start (len w)))))

(defthm fn-lg-apply-to-len
  (implies (fn-lg-writes-between ops low bound)
           (<= (len c) (len (fn-lg-apply-to c ops))))
  :rule-classes :linear)

(defthm fn-lg-apply-to-len-within
  (implies (and (fn-lg-writes-between ops low bound) (<= bound (len c)))
           (equal (len (fn-lg-apply-to c ops)) (len c))))

(defthm fn-lg-apply-to-true-listp
  (implies (true-listp c) (true-listp (fn-lg-apply-to c ops))))

; The shift: writes at or past len D over D ++ Z.
(defun fn-lg-shift-ops (ops d)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (cons (list :write (nth 1 (car ops)) (+ (nfix d) (nfix (nth 2 (car ops)))) (nth 3 (car ops)))
            (fn-lg-shift-ops (cdr ops) d))
    nil))

(defun fn-lg-offsets-natp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (natp (nth 2 (car ops))) (fn-lg-offsets-natp (cdr ops)))
    t))

(defthm fn-lg-apply-to-of-shift
  (implies (and (true-listp d) (fn-lg-offsets-natp ops))
           (equal (fn-lg-apply-to (append d z) (fn-lg-shift-ops ops (len d)))
                  (append d (fn-lg-apply-to z ops))))
  :hints (("Goal" :induct (fn-lg-apply-to z ops)
           :in-theory (disable fn-bs-splice))))

(defthm fn-lg-pieces-offsets-natp
  (fn-lg-offsets-natp (fn-lg-pieces ino start w sels unit)))

(defthm fn-lg-pieces-shift
  (implies (and (natp d) (natp s))
           (equal (fn-lg-pieces ino (+ d s) w sels unit)
                  (fn-lg-shift-ops (fn-lg-pieces ino s w sels unit) d))))

(defthm fn-lg-apply-to-past-prefix
  (implies (and (true-listp d) (natp s))
           (equal (fn-lg-apply-to (append d z)
                                  (fn-lg-pieces ino (+ (len d) s) w sels unit))
                  (append d (fn-lg-apply-to z (fn-lg-pieces ino s w sels unit)))))
  :hints (("Goal" :in-theory (disable fn-lg-pieces fn-lg-apply-to fn-lg-pieces-shift)
           :use ((:instance fn-lg-pieces-shift (d (len d)))))))

; Writes that end at or before B leave the octets from B on unchanged.
(defthm fn-lgc-nthcdr-of-splice-below
   (implies (and (natp off) (natp b) (true-listp o) (<= (+ off (len o)) b) (<= b (len c)))
            (equal (nthcdr b (fn-bs-splice c off o)) (nthcdr b c)))
   :hints (("Goal" :in-theory (enable fn-bs-splice) :do-not-induct t)))

(defthm fn-lg-nthcdr-of-apply-to-below
  (implies (and (fn-lg-writes-between ops low b) (natp b) (<= b (len c)))
           (equal (nthcdr b (fn-lg-apply-to c ops)) (nthcdr b c)))
  :hints (("Goal" :induct (fn-lg-apply-to c ops)
           :in-theory (disable fn-bs-splice))))

; -----------------------------------------------------------------------------
; A write of A ++ B with A a whole number of units splits at A's end.

(defun fn-lgc-split-ind (a m sels unit start)
  (declare (xargs :measure (nfix m)))
  (if (or (zp m) (atom sels) (zp unit)) (list a sels start)
    (fn-lgc-split-ind (nthcdr unit a) (1- m) (cdr sels) unit (+ start unit))))

(defthm fn-lgc-consp-append
   (equal (consp (append a b)) (or (consp a) (consp b))))

(defthm fn-lgc-unit-le-multiple
   (implies (and (posp m) (posp unit)) (<= unit (* m unit)))
   :rule-classes :linear)

(defthm fn-lgc-multiple-minus-unit
   (equal (+ (- unit) (* m unit)) (* (+ -1 m) unit)))

(defthm fn-lg-pieces-of-append
  (implies (and (natp m) (posp unit) (natp start)
                (true-listp a) (equal (len a) (* m unit)))
           (equal (fn-lg-pieces ino start (append a b) sels unit)
                  (append (fn-lg-pieces ino start a sels unit)
                          (fn-lg-pieces ino (+ start (len a)) b (nthcdr m sels) unit))))
  :hints (("Goal" :induct (fn-lgc-split-ind a m sels unit start)
           :in-theory (disable fn-lg-pieces-shift)
           :expand ((fn-lg-pieces ino start (append a b) sels unit)
                    (fn-lg-pieces ino start a sels unit)))))

; -----------------------------------------------------------------------------
; The entry is a whole number of units.

(defun fn-lg-entry-units (prev chunk unit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((n (len (fn-lg-frame prev chunk))) (unit (nfix unit)))
    (if (zp unit) n
      (if (equal (mod n unit) 0) (floor n unit) (1+ (floor n unit))))))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgc-pad-aligned
     (implies (and (natp n) (posp unit))
              (equal (+ n (fn-lg-pad-len n unit))
                     (* unit (if (equal (mod n unit) 0) (floor n unit)
                               (1+ (floor n unit))))))
     :hints (("Goal" :in-theory (enable fn-lg-pad-len))))))

(local
 (defthm fn-lgc-len-of-entry
   (equal (len (fn-lg-entry prev chunk unit))
          (+ (len (fn-lg-frame prev chunk))
             (fn-lg-pad-len (len (fn-lg-frame prev chunk)) unit)))
   :hints (("Goal" :in-theory (disable fn-lg-frame fn-lg-pad-len)))))

(local
 (defthm fn-lgc-pad-aligned-commuted
   (implies (and (natp n) (posp unit))
            (equal (+ n (fn-lg-pad-len n unit))
                   (* (if (equal (mod n unit) 0) (floor n unit) (1+ (floor n unit))) unit)))
   :hints (("Goal" :in-theory (disable fn-lg-pad-len) :use fn-lgc-pad-aligned))))

; A closed theory: the arithmetic library is not needed once the length is
; the frame and its padding.
(defthm fn-lg-entry-len-is-units
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp (fn-lg-frame-body chunk)) (posp unit))
           (equal (len (fn-lg-entry prev chunk unit))
                  (* (fn-lg-entry-units prev chunk unit) unit)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgc-len-of-entry fn-lg-entry-units
                                        (:type-prescription len) natp posp nfix zp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgc-pad-aligned-commuted (n (len (fn-lg-frame prev chunk))))))))

(local (in-theory (disable fn-lgc-len-of-entry fn-lgc-pad-aligned-commuted)))

(defthm fn-lg-entry-units-natp
  (natp (fn-lg-entry-units prev chunk unit))
  :rule-classes :type-prescription)

; -----------------------------------------------------------------------------
; The scan: a complete prefix, then the rest; the trailer the scan ends on.

(defun fn-lg-scan-last (octets prev unit max)
  (declare (xargs :guard t :verify-guards nil
                  :measure (len octets)
                  :hints (("Goal"
                           :use ((:instance fn-lg-slice-len)
                                 (:instance fn-lg-entry-okp-consp
                                            (slice (fn-lg-slice octets))))
                           :in-theory (disable fn-lg-declared-len fn-lg-entry-okp
                                               fn-lg-slice fn-lg-pad-len
                                               fn-lg-slice-len fn-lg-entry-okp-consp)))))
  (let ((slice (fn-lg-slice octets)))
    (if (not (fn-lg-entry-okp slice prev max))
        prev
      (let ((step (+ (len slice) (fn-lg-pad-len (len slice) unit))))
        (fn-lg-scan-last (nthcdr step octets) (fn-lg-trailer slice) unit max)))))

(defthm fn-lgc-declared-len-of-append
   (implies (<= *fn-frame-header-octets* (len d))
            (equal (fn-lg-declared-len (append d x)) (fn-lg-declared-len d)))
   :hints (("Goal" :in-theory (e/d (fn-lg-declared-len) (fn-cbor-u32-from)))))

(defthm fn-lgc-slice-of-append
   (implies (consp (fn-lg-slice d))
            (equal (fn-lg-slice (append d x)) (fn-lg-slice d)))
   :hints (("Goal" :in-theory (e/d (fn-lg-slice) (fn-lg-declared-len))
            :use ((:instance fn-lg-slice-len (octets d))))))

(defthm fn-lgc-scan-consumed-bound
   (<= (cdr (fn-lg-scan octets prev unit max))
       (+ (len octets) (cdr (fn-lg-scan octets prev unit max))))
   :rule-classes nil)

(defthm fn-lgc-true-list-len-0
   (implies (and (true-listp d) (not (consp d))) (equal d nil))
   :rule-classes :forward-chaining)

; The scan of D ++ X, when the scan of D consumes all of D.
(defthm fn-lg-scan-of-complete-append
  (implies (and (true-listp d)
                (equal (cdr (fn-lg-scan d prev unit max)) (len d)))
           (equal (fn-lg-scan (append d x) prev unit max)
                  (let ((rest (fn-lg-scan x (fn-lg-scan-last d prev unit max) unit max)))
                    (cons (append (car (fn-lg-scan d prev unit max)) (car rest))
                          (+ (len d) (cdr rest))))))
  :hints (("Goal" :induct (fn-lg-scan d prev unit max)
           :expand ((fn-lg-scan (append d x) prev unit max)
                    (fn-lg-scan d prev unit max)
                    (fn-lg-scan-last d prev unit max))
           :in-theory (disable fn-lg-declared-len fn-lg-entry-okp fn-lg-slice-records
                               fn-lg-trailer fn-lg-pad-len fn-lg-slice)
           :do-not '(generalize))
          ("Subgoal *1/2" :use ((:instance fn-lg-slice-len (octets d))
                                (:instance fn-lg-entry-okp-consp
                                           (slice (fn-lg-slice d)) (prev prev))))))

; -----------------------------------------------------------------------------
; A prefix of the batch, and the forgery at the first damaged entry.

(defun fn-lg-prefixp (a b)
  (declare (xargs :guard t))
  (if (consp a)
      (and (consp b) (equal (car a) (car b)) (fn-lg-prefixp (cdr a) (cdr b)))
    t))

(defun fn-lg-forgery-in (x batch prev unit max)
  (declare (xargs :guard t :verify-guards nil :measure (len batch)))
  (if (atom batch)
      nil
    (let ((fr (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))))
      (if (equal (fn-lg-slice x) fr)
          (fn-lg-forgery-in (nthcdr (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)) x)
                            (nthcdr (fn-lg-chunk-len batch) batch) (fn-lg-trailer fr) unit max)
        (fn-lg-forgeryp x prev max fr)))))

; The verdict the crash theorems state: the scan read a prefix P of the
; batch and consumed exactly the log of P.
(defun fn-lg-prefix-verdictp (scan batch prev unit)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lg-prefixp (car scan) batch)
       (equal (cdr scan) (len (fn-lg-log (car scan) prev unit)))))

; -----------------------------------------------------------------------------
; The batch over a zero region.

(defthm fn-lgc-scan-when-slice-is-frame
   (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max)
                 (equal (fn-lg-slice x) (fn-lg-frame prev chunk)))
            (equal (fn-lg-scan x prev unit max)
                   (let ((rest (fn-lg-scan (nthcdr (len (fn-lg-entry prev chunk unit)) x)
                                           (fn-lg-trailer (fn-lg-frame prev chunk))
                                           unit max)))
                     (cons (append chunk (car rest))
                           (+ (len (fn-lg-entry prev chunk unit)) (cdr rest))))))
   :hints (("Goal" :expand ((fn-lg-scan x prev unit max))
            :in-theory (disable fn-lg-entry fn-lg-frame fn-lg-slice fn-lg-entry-okp
                                fn-lg-slice-records fn-lg-trailer fn-lg-pad-len
                                fn-lg-chunkp)
            :use (fn-lg-entry-len fn-lg-entry-okp-of-frame fn-lg-slice-records-of-frame))))

(defthm fn-lgc-scan-when-slice-is-not-frame
   (implies (and (not (equal (fn-lg-slice x) fr))
                 (not (fn-lg-forgeryp x prev max fr)))
            (equal (fn-lg-scan x prev unit max) (cons nil 0)))
   :hints (("Goal" :expand ((fn-lg-scan x prev unit max))
            :in-theory (disable fn-lg-slice fn-lg-entry-okp))))

(defun fn-lgc-batch-ind (z batch prev sels unit)
  (declare (xargs :guard t :verify-guards nil :measure (len batch)))
  (if (atom batch) (list z prev sels unit)
    (fn-lgc-batch-ind
     (nthcdr (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)) z)
     (nthcdr (fn-lg-chunk-len batch) batch)
     (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch)))
     (nthcdr (fn-lg-entry-units prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit) sels)
     unit)))

(defthm fn-lgc-log-len-of-consp
   (implies (consp batch)
            (equal (len (fn-lg-log batch prev unit))
                   (+ (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit))
                      (len (fn-lg-log (nthcdr (fn-lg-chunk-len batch) batch) (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit)))))
   :hints (("Goal" :in-theory (e/d (fn-lg-log-unfolds)
                                   (fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-log)))))

(defthm fn-lg-log-true-listp
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (true-listp (fn-lg-log records prev unit)))
  :hints (("Goal" :induct (fn-lg-log records prev unit)
           :in-theory (e/d (fn-lg-log-unfolds)
                           (fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-recordsp
                            fn-lg-chunkp (:definition fn-lg-log)
                            fn-lg-trailer-of-frame-digestp)))
          ("Subgoal *1/2" :expand ((fn-lg-log records prev unit) (fn-lg-log nil prev unit)))
          ("Subgoal *1/1"
           :use ((:instance fn-lg-chunkp-of-first-chunk)
                 (:instance fn-lg-recordsp-of-nthcdr (k (fn-lg-chunk-len records)))
                 (:instance fn-lg-trailer-of-frame-digestp
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))
                 (:instance fn-lg-entry-true-listp
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))
                 (:instance fn-lg-chunk-body-octets
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))))))

; A prefix of a batch that ends on a chunk boundary chunks as the batch
; does: its first chunk is the batch's first chunk.
(defthm fn-lgc-fit-count-of-prefix
   (implies (fn-lg-prefixp p (nthcdr (fn-lg-fit-count x used) x))
            (equal (fn-lg-fit-count (append (fn-bs-take (fn-lg-fit-count x used) x) p) used)
                   (fn-lg-fit-count x used)))
   :hints (("Goal" :induct (fn-lg-fit-count x used)
            :expand ((fn-lg-fit-count p used)
                     (:free (a b) (fn-lg-fit-count (cons a b) used))))))

(defthm fn-lgc-take-true-listp
   (true-listp (fn-bs-take n x)))

(defthm fn-lgc-chunk-len-of-prefix
   (implies (and (consp batch)
                 (fn-lg-prefixp p (nthcdr (fn-lg-chunk-len batch) batch)))
            (equal (fn-lg-chunk-len (append (fn-bs-take (fn-lg-chunk-len batch) batch) p))
                   (fn-lg-chunk-len batch)))
   :hints (("Goal" :in-theory (enable fn-lg-chunk-len)
            :cases ((equal (fn-lg-fit-count batch *fn-frame-trailer-octets*) 0))
            :use ((:instance fn-lgc-fit-count-of-prefix (x batch) (used *fn-frame-trailer-octets*))))
           ("Subgoal 1" :expand ((fn-lg-fit-count batch 32)
                                 (:free (a b) (fn-lg-fit-count (cons a b) 32))
                                 (fn-bs-take 1 batch) (fn-bs-take 0 (cdr batch))))))

(defthm fn-lgc-log-of-prefix
   (implies (and (consp batch) (true-listp batch)
                 (fn-lg-prefixp p (nthcdr (fn-lg-chunk-len batch) batch)))
            (equal (fn-lg-log (append (fn-bs-take (fn-lg-chunk-len batch) batch) p) prev unit)
                   (append (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)
                           (fn-lg-log p (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lg-log-unfolds)
                            (fn-lg-entry fn-lg-frame fn-lg-trailer (:definition fn-lg-log)
                             fn-lgc-chunk-len-of-prefix))
            :use (fn-lgc-chunk-len-of-prefix
                  (:instance fn-lg-chunk-len-bounds (records batch))))))

(defthm fn-lg-take-then-nthcdr-append-2
   (implies (and (true-listp x) (<= (nfix k) (len x)))
            (equal (append (fn-bs-take k x) (nthcdr k x)) x)))

(defthm fn-lgc-prefixp-of-append-chunk
   (implies (and (true-listp c) (true-listp batch)
                 (equal (append c r) batch))
            (equal (fn-lg-prefixp (append c p) batch) (fn-lg-prefixp p r)))
   :hints (("Goal" :induct (fn-lg-prefixp c batch))))

(defthm fn-lgc-apply-to-of-append
   (equal (fn-lg-apply-to c (append p q))
          (fn-lg-apply-to (fn-lg-apply-to c p) q)))

; The tear of A ++ B over Z, read from A's end, is the tear of B over Z's
; octets from A's end: the batch's entries split per unit.
(defthm fn-lg-nthcdr-of-tear-of-append
  (implies (and (natp m) (posp unit) (true-listp a) (equal (len a) (* m unit))
                (true-listp z) (<= (len a) (len z)))
           (equal (nthcdr (len a) (fn-lg-apply-to z (fn-lg-pieces ino 0 (append a b) sels unit)))
                  (fn-lg-apply-to (nthcdr (len a) z)
                                  (fn-lg-pieces ino 0 b (nthcdr m sels) unit))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-pieces fn-lg-apply-to fn-lg-apply-to-past-prefix
                               fn-lg-pieces-shift fn-lgc-take-then-nthcdr fn-lg-pieces-between
                               fn-lg-apply-to-true-listp
                               fn-lg-nthcdr-of-apply-to-below fn-lg-apply-to-len-within)
           :use ((:instance fn-lg-pieces-of-append (start 0))
                 (:instance fn-lg-pieces-between (start 0) (w a))
                 (:instance fn-lg-apply-to-true-listp (c z) (ops (fn-lg-pieces ino 0 a sels unit)))
                 (:instance fn-lg-apply-to-len-within
                            (c z) (ops (fn-lg-pieces ino 0 a sels unit)) (low 0) (bound (len a)))
                 (:instance fn-lgc-take-then-nthcdr
                            (n (len a)) (x (fn-lg-apply-to z (fn-lg-pieces ino 0 a sels unit))))
                 (:instance fn-lg-apply-to-past-prefix
                            (d (fn-bs-take (len a) (fn-lg-apply-to z (fn-lg-pieces ino 0 a sels unit))))
                            (z (nthcdr (len a) (fn-lg-apply-to z (fn-lg-pieces ino 0 a sels unit))))
                            (s 0) (w b) (sels (nthcdr m sels)))
                 (:instance fn-lg-nthcdr-of-apply-to-below
                            (c z) (ops (fn-lg-pieces ino 0 a sels unit)) (low 0) (b (len a)))))))

(defthm fn-lgc-apply-to-of-nil
   (equal (fn-lg-apply-to c nil) c))

; The tear of the batch's log W over a zero region Z at least as long.
; One chunk of the batch, read exactly: the verdict for the rest extends to
; the batch.
(defthm fn-lgc-verdict-step-frame
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp batch max) (consp batch)
                (equal (fn-lg-slice x) (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch)))
                (or (fn-lg-prefix-verdictp
                     (fn-lg-scan (nthcdr (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)) x)
                                 (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit max)
                     (nthcdr (fn-lg-chunk-len batch) batch) (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit)
                    (fn-lg-forgery-in (nthcdr (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)) x)
                                      (nthcdr (fn-lg-chunk-len batch) batch) (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit max)))
           (or (fn-lg-prefix-verdictp (fn-lg-scan x prev unit max) batch prev unit)
               (fn-lg-forgery-in x batch prev unit max)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (unit) (fn-lg-forgery-in x batch prev unit max)))
           :in-theory (e/d (fn-lg-prefix-verdictp)
                           (fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-slice fn-lg-scan
                            fn-lg-forgery-in fn-lg-chunkp fn-lg-recordsp fn-lgc-log-of-prefix
                            fn-lgc-scan-when-slice-is-frame fn-lg-take-then-nthcdr-append-2
                            fn-lgc-prefixp-of-append-chunk (:definition fn-lg-log)))
           :use ((:instance fn-lg-chunkp-of-first-chunk (records batch))
                 (:instance fn-lgc-scan-when-slice-is-frame (chunk (fn-bs-take (fn-lg-chunk-len batch) batch)))
                 (:instance fn-lg-take-then-nthcdr-append-2 (k (fn-lg-chunk-len batch)) (x batch))
                 (:instance fn-lgc-prefixp-of-append-chunk
                            (c (fn-bs-take (fn-lg-chunk-len batch) batch)) (r (nthcdr (fn-lg-chunk-len batch) batch))
                            (p (car (fn-lg-scan (nthcdr (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)) x)
                                                (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit max))))
                 (:instance fn-lgc-log-of-prefix
                            (p (car (fn-lg-scan (nthcdr (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)) x)
                                                (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit max))))))))

; The first chunk not read exactly: nothing read, or a forgery there.
(defthm fn-lgc-verdict-step-not-frame
  (implies (and (consp batch)
                (not (equal (fn-lg-slice x) (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch)))))
           (or (fn-lg-prefix-verdictp (fn-lg-scan x prev unit max) batch prev unit)
               (fn-lg-forgery-in x batch prev unit max)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-lg-forgery-in x batch prev unit max) (fn-lg-log nil prev unit))
           :in-theory (e/d (fn-lg-prefix-verdictp)
                           (fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-slice fn-lg-scan
                            fn-lg-forgeryp))
           :use ((:instance fn-lgc-scan-when-slice-is-not-frame (fr (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))))))))

; The tear of the batch's log W over a zero region Z at least as long.
(defthm fn-lg-batch-tear-is-a-prefix
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp batch max) (posp unit)
                (fn-lg-zerosp z)
                (<= (len (fn-lg-log batch prev unit)) (len z)))
           (let ((x (fn-lg-apply-to z (fn-lg-pieces ino 0 (fn-lg-log batch prev unit)
                                                    sels unit))))
             (or (fn-lg-prefix-verdictp (fn-lg-scan x prev unit max) batch prev unit)
                 (fn-lg-forgery-in x batch prev unit max))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-lgc-batch-ind z batch prev sels unit)
           :in-theory (e/d (fn-lg-log-unfolds)
                           (fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-slice
                            fn-lg-forgeryp fn-lg-recordp fn-lg-entry-units
                            fn-lg-scan fn-lg-apply-to fn-lg-pieces (:definition fn-lg-log)
                            fn-lg-entry-len-is-units fn-lg-entry-len fn-lg-recordsp
                            fn-lg-chunkp fn-lgc-log-of-prefix fn-lg-forgery-in
                            fn-lg-prefix-verdictp fn-lg-nthcdr-of-tear-of-append)))
          ("Subgoal *1/2"
           :use ((:instance fn-lg-nthcdr-of-tear-of-append
                            (a (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit))
                            (b (fn-lg-log (nthcdr (fn-lg-chunk-len batch) batch) (fn-lg-trailer (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))) unit))
                            (m (fn-lg-entry-units prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)))
                 (:instance fn-lg-entry-len-is-units (chunk (fn-bs-take (fn-lg-chunk-len batch) batch)))
                 (:instance fn-lg-entry-true-listp (chunk (fn-bs-take (fn-lg-chunk-len batch) batch)))
                 (:instance fn-lg-chunk-body-octets (chunk (fn-bs-take (fn-lg-chunk-len batch) batch)))
                 (:instance fn-lg-chunkp-of-first-chunk (records batch))
                 (:instance fn-lg-recordsp-of-nthcdr (records batch) (k (fn-lg-chunk-len batch)))
                 (:instance fn-lg-trailer-of-frame-digestp (chunk (fn-bs-take (fn-lg-chunk-len batch) batch)))
                 (:instance fn-lgc-verdict-step-frame
                            (x (fn-lg-apply-to z (fn-lg-pieces ino 0 (fn-lg-log batch prev unit)
                                                               sels unit))))
                 (:instance fn-lgc-verdict-step-not-frame
                            (x (fn-lg-apply-to z (fn-lg-pieces ino 0 (fn-lg-log batch prev unit)
                                                               sels unit))))))
          ("Subgoal *1/1" :expand ((fn-lg-log nil prev unit)
                                   (fn-lg-log batch prev unit)
                                   (fn-lg-pieces ino 0 nil sels unit)
                                   (fn-lg-apply-to z nil))
           :in-theory (e/d (fn-lg-prefix-verdictp)
                           (fn-lg-scan fn-lg-recordsp)))))

; -----------------------------------------------------------------------------
; The shift lemma over the byte model's crash.

(defun fn-lg-crash-sels (s image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((choices (fn-bs-crash-imagep-witness s image)))
    (if (consp choices) (car choices) nil)))

(defthm fn-bs-crash-of-aligned-append
  (implies (and (posp (fn-bs-unit s)) (natp k) ino (true-listp d) (true-listp w)
                (equal (len d) (* k (fn-bs-unit s)))
                (equal (fn-bs-durable-content s ino) (append d z))
                (equal (fn-bs-pending s) (list (list :write ino (len d) w)))
                (fn-bs-crash-imagep s image))
           (equal (fn-bs-durable-content image ino)
                  (append d (fn-lg-apply-to z (fn-lg-pieces ino 0 w (fn-lg-crash-sels s image)
                                                            (fn-bs-unit s))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-crash-imagep fn-bs-crash fn-bs-durable-content)
                           (fn-lg-tear-write-is-pieces fn-lg-apply-to-past-prefix
                            fn-lg-pieces fn-lg-apply-to fn-bs-tear-write))
           :expand ((fn-bs-crash-select (list (list :write ino (len d) w))
                                        (fn-bs-crash-imagep-witness s image)
                                        (fn-bs-unit s)))
           :use ((:instance fn-lg-tear-write-is-pieces
                            (unit (fn-bs-unit s)) (i 0)
                            (sels (fn-lg-crash-sels s image)))
                 (:instance fn-lg-apply-to-past-prefix
                            (s 0) (unit (fn-bs-unit s))
                            (sels (fn-lg-crash-sels s image)))))))

; -----------------------------------------------------------------------------
; T2 over the store.

(defthm fn-lgc-scan-records-true-listp
   (true-listp (car (fn-lg-scan octets prev unit max)))
   :hints (("Goal" :induct (fn-lg-scan octets prev unit max)
            :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-records
                                fn-lg-declared-len fn-lg-trailer fn-lg-pad-len))))

; The verdict of a crash image's scan: the committed records followed by a
; prefix P of the batch, with the frontier past exactly P's log.
(defun fn-lg-crash-verdictp (scan committed frontier batch last unit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((p (nthcdr (len committed) (car scan))))
    (and (fn-lg-prefixp p batch)
         (equal (car scan) (append committed p))
         (equal (cdr scan) (+ frontier (len (fn-lg-log p last unit)))))))

(defthm fn-lgc-nthcdr-len-append
   (implies (true-listp a)
            (equal (nthcdr (len a) (append a b)) b)))

(defthm fn-lgc-tail-verdict
   (implies (and (posp unit) (true-listp d)
                 (equal (fn-lg-scan d genesis unit max) (cons committed (len d)))
                 (fn-frame-digestp last) (fn-lg-recordsp batch max)
                 (fn-lg-zerosp z)
                 (<= (len (fn-lg-log batch last unit)) (len z))
                 (equal c (append d (fn-lg-apply-to z (fn-lg-pieces ino 0 (fn-lg-log batch last unit)
                                                                    sels unit))))
                 (equal (fn-lg-scan-last d genesis unit max) last))
            (or (fn-lg-crash-verdictp (fn-lg-scan c genesis unit max) committed (len d) batch last unit)
                (fn-lg-forgery-in (nthcdr (len d) c) batch last unit max)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-lg-scan fn-lg-log fn-lg-apply-to fn-lg-pieces fn-lg-forgery-in
                                fn-lg-scan-of-complete-append fn-lg-scan-last)
            :use ((:instance fn-lg-batch-tear-is-a-prefix (prev last))
                  (:instance fn-lg-scan-of-complete-append
                             (prev genesis)
                             (x (fn-lg-apply-to z (fn-lg-pieces ino 0 (fn-lg-log batch last unit)
                                                                sels unit))))
                  (:instance fn-lgc-scan-records-true-listp (octets d) (prev genesis))))))

(defthm fn-lg-batch-crash-is-a-prefix
  (implies (and (posp (fn-bs-unit s)) (natp k) ino (true-listp d)
                (equal (len d) (* k (fn-bs-unit s)))
                (equal (fn-lg-scan d genesis (fn-bs-unit s) max) (cons committed (len d)))
                (equal (fn-lg-scan-last d genesis (fn-bs-unit s) max) last)
                (fn-frame-digestp last) (fn-lg-recordsp batch max)
                (fn-lg-zerosp z)
                (<= (len (fn-lg-log batch last (fn-bs-unit s))) (len z))
                (equal (fn-bs-durable-content s ino) (append d z))
                (equal (fn-bs-pending s)
                       (list (list :write ino (len d) (fn-lg-log batch last (fn-bs-unit s)))))
                (fn-bs-crash-imagep s image))
           (let ((content (fn-bs-durable-content image ino)))
             (or (fn-lg-crash-verdictp (fn-lg-scan content genesis (fn-bs-unit s) max)
                                       committed (len d) batch last (fn-bs-unit s))
                 (fn-lg-forgery-in (nthcdr (len d) content) batch last (fn-bs-unit s) max))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bs-crash-of-aligned-append fn-lg-scan fn-lg-log
                               fn-lg-apply-to fn-lg-pieces fn-lg-forgery-in fn-lg-crash-verdictp
                               fn-lg-scan-last fn-bs-durable-content)
           :use ((:instance fn-bs-crash-of-aligned-append
                            (w (fn-lg-log batch last (fn-bs-unit s))))
                 (:instance fn-lg-log-true-listp (prev last) (records batch))
                 (:instance fn-lgc-tail-verdict
                            (unit (fn-bs-unit s))
                            (sels (fn-lg-crash-sels s image))
                            (c (fn-bs-durable-content image ino)))))))

; -----------------------------------------------------------------------------
; The corollary under A-CRYPTO-TRAILER.  The platform's image of each
; entry, read as far as the scan reads it, is a platform tear of that
; entry's frame (fn-assume-crash-tearp, a model tear by its first
; constraint), up to the first entry that is not exact.  Then no entry
; forges: fn-assume-crash-tear-never-validates-unless-exact.  The figure,
; pessimistically: SHA-256's collision figure, about 2^-128 per chosen pair,
; not the second-preimage figure (the record quotes it).
(defun fn-lg-platform-tears-p (x batch prev unit)
  (declare (xargs :guard t :verify-guards nil :measure (len batch)))
  (if (atom batch)
      t
    (let ((fr (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len batch) batch))))
      (if (equal (fn-lg-slice x) fr)
          (fn-lg-platform-tears-p (nthcdr (len (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len batch) batch) unit)) x)
                                  (nthcdr (fn-lg-chunk-len batch) batch) (fn-lg-trailer fr) unit)
        (fn-assume-crash-tearp unit (fn-lg-slice x) fr)))))

(defthm fn-lgc-no-forgeryp-of-a-platform-tear
  (implies (and (fn-assume-crash-tearp unit (fn-lg-slice x) fr)
                (not (equal (fn-lg-slice x) fr)))
           (not (fn-lg-forgeryp x prev max fr)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-forgeryp fn-lg-entry-okp)
                           (fn-lg-slice fn-frame-open fn-lg-open-bound
                            fn-assume-crash-tear-never-validates-unless-exact))
           :use ((:instance fn-assume-crash-tear-never-validates-unless-exact
                            (observed (fn-lg-slice x)) (written fr)
                            (max-payload (fn-lg-open-bound (fn-lg-slice x) max)))))))

(defthm fn-lg-no-forgery-under-a-crypto-trailer
  (implies (fn-lg-platform-tears-p x batch prev unit)
           (not (fn-lg-forgery-in x batch prev unit max)))
  :hints (("Goal" :induct (fn-lg-forgery-in x batch prev unit max)
           :in-theory (disable fn-lg-frame fn-lg-entry fn-lg-slice fn-lg-trailer
                               fn-lg-forgeryp fn-lg-entry-okp))))

(defthm fn-lg-batch-crash-is-a-prefix-under-a-crypto-trailer
  (implies (and (posp (fn-bs-unit s)) (natp k) ino (true-listp d)
                (equal (len d) (* k (fn-bs-unit s)))
                (equal (fn-lg-scan d genesis (fn-bs-unit s) max) (cons committed (len d)))
                (equal (fn-lg-scan-last d genesis (fn-bs-unit s) max) last)
                (fn-frame-digestp last) (fn-lg-recordsp batch max)
                (fn-lg-zerosp z)
                (<= (len (fn-lg-log batch last (fn-bs-unit s))) (len z))
                (equal (fn-bs-durable-content s ino) (append d z))
                (equal (fn-bs-pending s)
                       (list (list :write ino (len d) (fn-lg-log batch last (fn-bs-unit s)))))
                (fn-bs-crash-imagep s image)
                (fn-lg-platform-tears-p (nthcdr (len d) (fn-bs-durable-content image ino))
                                        batch last (fn-bs-unit s)))
           (fn-lg-crash-verdictp (fn-lg-scan (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit s) max)
                                 committed (len d) batch last (fn-bs-unit s)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-crash-verdictp fn-lg-platform-tears-p fn-lg-forgery-in
                               fn-lg-no-forgery-under-a-crypto-trailer)
           :use (fn-lg-batch-crash-is-a-prefix
                 (:instance fn-lg-no-forgery-under-a-crypto-trailer
                            (x (nthcdr (len d) (fn-bs-durable-content image ino)))
                            (prev last) (unit (fn-bs-unit s)))))))
