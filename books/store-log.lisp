; fn: the record log, prototype of the storage-log design's core
; (planning/design-2026-09-27-storage-log.md, section 3).
;
; A LOG is one append-only inode holding a run of ENTRIES.  An entry is an
; FNLG frame (books/frame-fields.lisp: MAGIC VERSION KIND LENGTH, payload,
; the 32-octet trailer `fn-frame-digest' over the protected prefix) padded
; with zeros to the write unit, and its payload is the previous entry's
; trailer (the CHAIN, 32 octets) followed by the committed record's bytes
; (the FNST record frame of books/frame.lisp, unchanged).  The SCAN reads
; entries from the front while each one is complete (its declared length
; lies within the octets), validates (`fn-frame-open'), carries this log's
; magic and kind, and names the previous trailer; it stops at the first
; entry that does not, and answers the records read and the aligned offset
; where the next append goes.  That offset is the FRONTIER: the durable
; history is what the scan reads, and nothing else names it (no allocation
; frontier file, no committed-history marker: design section 3.4).
;
; Two keystones, stated over any octets so that the crash argument of the
; design's section 5 can instantiate them at any batch:
;
;   fn-lg-scan-of-log-append   the scan of a well-formed log followed by any
;                              octets X reads every record of the log and then
;                              scans X from the log's last trailer (so the
;                              scan of a well-formed log alone is exactly its
;                              records and its length: the frontier is the
;                              last complete entry's end);
;   fn-lg-scan-of-torn-entry   the scan of a TORN entry (a crash image of the
;                              one pending write that appends it, the byte
;                              model's fn-bs-torn-variantp) is the empty
;                              history, or exactly the one record, or the
;                              first slice validates as a chained frame that
;                              is not the written one (fn-lg-forgeryp: the
;                              event A-CRYPTO-TRAILER excludes; the design
;                              quotes its figure).
;
; Composed (fn-lg-scan-of-log-then-torn-entry): a log followed by a torn
; append scans to the log's records, or to the log's records and the new
; one, or the tail is a forgery.  The append at a NON-EMPTY log is the
; design's shift lemma (a crash of a pending write at an aligned offset of
; an inode holding L is L followed by a torn variant of the write): stated
; in the design's proof plan, not here.
;
; The scan is the logical decoder (fn-frame-open, the specification decoder
; under A-CRYPTO: not executable except under the attachment); the host's
; executable scan takes the digest from fn-frame-trailer as fn-frame-decode
; does.  Nothing here is guard-verified: this is the prototype book the
; design lane admits, and the log-core lane owns the executable twin.

(in-package "ACL2")
(include-book "assumptions")
(include-book "frame-invariants")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-bs-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The entry.

(defconst *fn-lg-magic* '(70 78 76 71))      ; "FNLG"
(defconst *fn-lg-version* 1)
(defconst *fn-lg-record-kind* 1)
(defconst *fn-lg-genesis* (make-list 32 :initial-element 0))

; The zeros that take N octets to the next multiple of UNIT (none when UNIT
; is not positive: an unpadded log is a log whose unit is one).  The nfix
; is the identity for a natural N and a positive UNIT (mod is below the
; modulus); that the padded length is a multiple of the unit is the
; alignment lemma of the log-core lane, under an arithmetic library this
; closure does not carry.  The theorems below need only that the padding is
; a natural.
(defun fn-lg-pad-len (n unit)
  (declare (xargs :guard t))
  (let ((n (nfix n)) (unit (nfix unit)))
    (if (or (zp unit) (equal (mod n unit) 0)) 0 (nfix (- unit (mod n unit))))))

(defthm fn-lg-pad-len-natp
  (natp (fn-lg-pad-len n unit))
  :rule-classes :type-prescription)

; A CHUNK is a non-empty list of records written as ONE entry (PKT-749: the
; batch is padded once, not per record).  One record is a KIND 1 frame whose
; payload is the chain and the record, as before; two or more are a KIND 2
; frame whose payload is the chain and the records PACKED, each after its
; length in four octets.  A batch's log is its greedy chunks
; (fn-lg-chunk-len): as many records as fit one frame's payload bound,
; *fn-frame-max-payload*; a batch below four GiB is one entry.

(defconst *fn-lg-batch-kind* 2)

(defun fn-lg-pack (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (append (fn-cbor-u32-bytes (len (car records)))
              (append (true-list-fix (car records)) (fn-lg-pack (cdr records))))
    nil))

(defun fn-lg-pack-len (records)
  (declare (xargs :guard t))
  (if (consp records)
      (+ 4 (len (car records)) (fn-lg-pack-len (cdr records)))
    0))

(local
 (defthm fn-lg-len-nthcdr-early
   (equal (len (nthcdr k x)) (nfix (- (len x) (nfix k))))
   :hints (("Goal" :induct (nthcdr k x)))))

(local
 (defthm fn-lg-nthcdr-shorter-early
   (implies (and (posp k) (consp x))
            (< (len (nthcdr k x)) (len x)))
   :rule-classes :linear))

; The records of a packed body, read while each length lies within it.
(defun fn-lg-unpack (x)
  (declare (xargs :guard t :verify-guards nil :measure (len x)))
  (if (and (consp x) (<= 4 (len x)))
      (let ((n (nfix (fn-cbor-u32-from (fn-bs-take 4 x)))))
        (if (<= (+ 4 n) (len x))
            (cons (fn-bs-take n (nthcdr 4 x)) (fn-lg-unpack (nthcdr (+ 4 n) x)))
          nil))
    nil))

; The body is exactly its packed records: every length lies within it and
; the last record ends it.
(defun fn-lg-unpack-exactp (x)
  (declare (xargs :guard t :verify-guards nil :measure (len x)))
  (if (consp x)
      (and (<= 4 (len x))
           (let ((n (nfix (fn-cbor-u32-from (fn-bs-take 4 x)))))
             (and (<= (+ 4 n) (len x))
                  (fn-lg-unpack-exactp (nthcdr (+ 4 n) x)))))
    t))

; How many records from the front fit one frame after USED payload octets.
(defun fn-lg-fit-count (records used)
  (declare (xargs :guard (natp used)))
  (if (and (consp records)
           (<= (+ (nfix used) 4 (len (car records))) *fn-frame-max-payload*))
      (1+ (fn-lg-fit-count (cdr records) (+ (nfix used) 4 (len (car records)))))
    0))

; The first chunk's length: at least one record.
(defun fn-lg-chunk-len (records)
  (declare (xargs :guard t))
  (max 1 (fn-lg-fit-count records *fn-frame-trailer-octets*)))

(defun fn-lg-frame-kind (chunk)
  (declare (xargs :guard t))
  (if (and (consp chunk) (consp (cdr chunk))) *fn-lg-batch-kind* *fn-lg-record-kind*))

(defun fn-lg-frame-body (chunk)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp chunk) (consp (cdr chunk))) (fn-lg-pack chunk) (car chunk)))

(defun fn-lg-frame (prev chunk)
  (declare (xargs :guard t :verify-guards nil))
  (fn-frame-seal *fn-lg-magic* *fn-lg-version* (fn-lg-frame-kind chunk)
                 (append prev (fn-lg-frame-body chunk))))

(defun fn-lg-entry (prev chunk unit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-lg-frame prev chunk)))
    (append frame (fn-bs-zeros (fn-lg-pad-len (len frame) unit)))))

; The last 32 octets of a frame.
(defun fn-lg-trailer (frame)
  (declare (xargs :guard t :verify-guards nil))
  (nthcdr (nfix (- (len frame) *fn-frame-trailer-octets*)) frame))

; A record the log admits under the payload bound MAX.
(defun fn-lg-recordp (record max)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp record)
       (natp max)
       (<= max *fn-frame-max-payload*)
       (<= (+ *fn-frame-trailer-octets* (len record)) max)))

(defthm fn-lg-recordp-forward
  (implies (fn-lg-recordp record max)
           (and (fn-cbor-octet-listp record) (natp max)
                (<= (+ *fn-frame-trailer-octets* (len record)) max)))
  :rule-classes :forward-chaining)

(defun fn-lg-recordsp (records max)
  (declare (xargs :guard t))
  (if (consp records)
      (and (fn-lg-recordp (car records) max) (fn-lg-recordsp (cdr records) max))
    (null records)))

; A chunk the log writes as one entry: records the log admits, and two or
; more only when their packed payload fits one frame.
(defun fn-lg-chunkp (chunk max)
  (declare (xargs :guard t))
  (and (consp chunk)
       (fn-lg-recordsp chunk max)
       (or (atom (cdr chunk))
           (<= (+ *fn-frame-trailer-octets* (fn-lg-pack-len chunk))
               *fn-frame-max-payload*))))

; -----------------------------------------------------------------------------
; The scan.

; The total length the header at the front declares, or nil when there is no
; header of this log's magic there.
(defun fn-lg-declared-len (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (<= *fn-frame-header-octets* (len octets))
           (fn-cbor-octet-listp (fn-bs-take *fn-frame-header-octets* octets))
           (equal (fn-bs-take *fn-frame-magic-octets* octets) *fn-lg-magic*))
      (+ *fn-frame-overhead-octets*
         (nfix (fn-cbor-u32-from (fn-bs-take 4 (nthcdr 6 octets)))))
    nil))

(defthm fn-lg-declared-len-bound
  (implies (fn-lg-declared-len octets)
           (<= *fn-frame-overhead-octets* (fn-lg-declared-len octets)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from fn-bs-take))))

; The slice the scan opens: the frame the header at the front declares,
; when the octets hold all of it.
(defun fn-lg-slice (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((n (fn-lg-declared-len octets)))
    (if (and n (<= n (len octets))) (fn-bs-take n octets) nil)))

; The payload bound the slice is opened under: a KIND 2 header (its sixth
; octet) names a packed chunk, bounded by the frame's own limit; any other
; is one record under the log's record bound MAX, as before.
(defun fn-lg-open-bound (slice max)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp slice) (equal (nth 5 slice) *fn-lg-batch-kind*))
      *fn-frame-max-payload*
    max))

; A packed body the scan accepts: exactly its records, at least two, each
; one the log admits.
(defun fn-lg-unpack-okp (x max)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lg-unpack-exactp x)
       (consp (cdr (fn-lg-unpack x)))
       (fn-lg-recordsp (fn-lg-unpack x) max)))

; The slice validates as a chained frame of this log: one record (kind 1)
; or a packed chunk (kind 2).
(defun fn-lg-entry-okp (slice prev max)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp slice)
       (let ((r (fn-frame-open slice (fn-lg-open-bound slice max))))
         (and (fn-frame-result-okp r)
              (equal (fn-frame-result-magic r) *fn-lg-magic*)
              (equal (fn-frame-result-version r) *fn-lg-version*)
              (or (equal (fn-frame-result-kind r) *fn-lg-record-kind*)
                  (and (equal (fn-frame-result-kind r) *fn-lg-batch-kind*)
                       (fn-lg-unpack-okp (nthcdr *fn-frame-trailer-octets*
                                                 (fn-frame-result-payload r))
                                         max)))
              (equal (fn-bs-take *fn-frame-trailer-octets*
                                 (fn-frame-result-payload r))
                     prev)))))

; The records of a validated slice.
(defun fn-lg-slice-records (slice max)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((r (fn-frame-open slice (fn-lg-open-bound slice max)))
         (body (nthcdr *fn-frame-trailer-octets* (fn-frame-result-payload r))))
    (if (equal (fn-frame-result-kind r) *fn-lg-batch-kind*)
        (fn-lg-unpack body)
      (list body))))

(local
 (defthm fn-lg-len-nthcdr-of-atom
   (implies (atom x) (equal (len (nthcdr k x)) 0))))
(local
 (defthm fn-lg-len-nthcdr
   (equal (len (nthcdr k x)) (nfix (- (len x) (nfix k))))
   :hints (("Goal" :induct (nthcdr k x)))))
(local
 (defthm fn-lg-nthcdr-shorter
   (implies (and (posp k) (consp x))
            (< (len (nthcdr k x)) (len x)))
   :rule-classes :linear))

(local
 (defthm fn-lg-take-len
   (equal (len (fn-bs-take n x)) (nfix n))))

(defthm fn-lg-entry-okp-consp
  (implies (fn-lg-entry-okp slice prev max) (consp slice))
  :rule-classes :forward-chaining)

; A slice that exists is the declared length, at least the frame overhead
; and within the octets.
(defthm fn-lg-slice-len
  (implies (consp (fn-lg-slice octets))
           (and (equal (len (fn-lg-slice octets)) (fn-lg-declared-len octets))
                (<= *fn-frame-overhead-octets* (fn-lg-declared-len octets))
                (<= (fn-lg-declared-len octets) (len octets))))
  :hints (("Goal" :in-theory (disable fn-lg-declared-len))))

; (RECORDS . CONSUMED): the records of the complete chained entries at the
; front, and the aligned offset after the last of them.
(defun fn-lg-scan (octets prev unit max)
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
        (cons nil 0)
      (let* ((n (len slice))
             (step (+ n (fn-lg-pad-len n unit)))
             (rest (fn-lg-scan (nthcdr step octets) (fn-lg-trailer slice) unit max)))
        (cons (append (fn-lg-slice-records slice max) (car rest))
              (+ step (cdr rest)))))))

(defthm fn-lg-scan-of-empty
  (equal (fn-lg-scan nil prev unit max) (cons nil 0)))

; -----------------------------------------------------------------------------
; A well-formed log: the chained entries of RECORDS from PREV.

(defun fn-lg-log (records prev unit)
  (declare (xargs :guard t :verify-guards nil :measure (len records)))
  (if (consp records)
      (let ((k (fn-lg-chunk-len records)))
        (append (fn-lg-entry prev (fn-bs-take k records) unit)
                (fn-lg-log (nthcdr k records)
                           (fn-lg-trailer (fn-lg-frame prev (fn-bs-take k records)))
                           unit)))
    nil))

(defun fn-lg-last-trailer (records prev)
  (declare (xargs :guard t :verify-guards nil :measure (len records)))
  (if (consp records)
      (let ((k (fn-lg-chunk-len records)))
        (fn-lg-last-trailer (nthcdr k records)
                            (fn-lg-trailer (fn-lg-frame prev (fn-bs-take k records)))))
    prev))

; -----------------------------------------------------------------------------
; The frame's shape: its length, its header's length field, its trailer.

(local (in-theory (enable fn-frame-seal fn-frame-encode fn-frame-protected
                          fn-frame-header fn-frame-inputp fn-frame-magicp
                          fn-frame-digestp fn-frame-item)))

(local
 (defthm fn-lg-take-of-append-exact
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-bs-take n (append a b)) a))))

(local
 (defthm fn-lg-take-of-append-shorter
   (implies (and (natp n) (<= n (len a)))
            (equal (fn-bs-take n (append a b)) (fn-bs-take n a)))))

(local
 (defthm fn-lg-take-all
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-bs-take n a) a))))

(local
 (defthm fn-lg-nthcdr-of-append-exact
   (implies (equal n (len a))
            (equal (nthcdr n (append a b)) b))))

(local
 (defthm fn-lg-len-of-u32-bytes
   (equal (len (fn-cbor-u32-bytes n)) 4)
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

(local
 (defthm fn-lg-digest-len
   (equal (len (fn-frame-digest x)) 32)
   :hints (("Goal" :use fn-frame-digest-length))))

(local
 (defthm fn-lg-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-lg-octets-append
   (implies (true-listp a)
            (equal (fn-cbor-octet-listp (append a b))
                   (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))))))
(local
 (defthm fn-lg-octets-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))))
(local
 (defthm fn-lg-true-listp-append
   (implies (true-listp b) (true-listp (append a b)))))

; The kind is an octet, and the payload bound a chunk's frame is opened under.
(defthm fn-lg-frame-kind-octetp
  (fn-cbor-octetp (fn-lg-frame-kind chunk))
  :hints (("Goal" :in-theory (enable fn-cbor-octetp))))

(defun fn-lg-kind-bound (chunk max)
  (declare (xargs :guard t))
  (if (equal (fn-lg-frame-kind chunk) *fn-lg-batch-kind*) *fn-frame-max-payload* max))

; The packed body: its length, its octets, and its records read back.
(local
 (defthm fn-lg-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(defthm fn-lg-pack-len-is-len
  (equal (len (fn-lg-pack records)) (fn-lg-pack-len records))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-bytes))))

(defthm fn-lg-pack-len-natp
  (natp (fn-lg-pack-len records))
  :rule-classes :type-prescription)

(defthm fn-lg-recordp-len-bound
  (implies (fn-lg-recordp record max)
           (<= (len record) *fn-cbor-max-uint*))
  :rule-classes :linear)

(defthm fn-lg-pack-octets
  (implies (fn-lg-recordsp records max)
           (fn-cbor-octet-listp (fn-lg-pack records)))
  :hints (("Goal" :induct (fn-lg-pack records)
           :in-theory (disable fn-cbor-u32-bytes fn-lg-recordp))
          ("Subgoal *1/1" :in-theory (disable fn-cbor-u32-bytes)
           :use ((:instance fn-cbor-u32-bytes-are-octets (n (len (car records))))))))

(defthm fn-lg-pack-true-listp
  (true-listp (fn-lg-pack records))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-bytes))))

(local
 (defthm fn-lg-take-of-append-true-list-exact
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-bs-take n (append a b)) a))))

(local
 (defthm fn-lg-nthcdr-of-append-exact-2
   (implies (and (true-listp a) (equal n (len a)))
            (equal (nthcdr n (append a b)) b))))

(local
 (defthm fn-lg-true-list-fix-id
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-lg-nthcdr-of-append-two
   (implies (and (true-listp a) (true-listp b))
            (equal (nthcdr (+ (len a) (len b)) (append a (append b c))) c))
   :hints (("Goal" :induct (len a)))))

(local
 (defthm fn-lg-len-u32-bytes-4
   (equal (len (fn-cbor-u32-bytes n)) 4)))

(local
 (defthm fn-lg-consp-u32-bytes
   (consp (fn-cbor-u32-bytes n))
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

(local
 (defthm fn-lg-consp-append
   (equal (consp (append a b)) (or (consp a) (consp b)))))

(local
 (defthm fn-lg-unpack-of-one
   (implies (and (true-listp r) (<= (len r) *fn-cbor-max-uint*))
            (and (equal (fn-lg-unpack (append (fn-cbor-u32-bytes (len r)) (append r rest)))
                        (cons r (fn-lg-unpack rest)))
                 (equal (fn-lg-unpack-exactp (append (fn-cbor-u32-bytes (len r)) (append r rest)))
                        (fn-lg-unpack-exactp rest))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-lg-unpack (append (fn-cbor-u32-bytes (len r)) (append r rest)))
                     (fn-lg-unpack-exactp (append (fn-cbor-u32-bytes (len r)) (append r rest))))
            :in-theory (disable fn-cbor-u32-bytes fn-cbor-u32-from fn-lg-unpack fn-lg-unpack-exactp)
            :use ((:instance fn-cbor-u32-from-u32-bytes (n (len r)))
                  (:instance fn-lg-take-of-append-true-list-exact
                             (n 4) (a (fn-cbor-u32-bytes (len r))) (b (append r rest)))
                  (:instance fn-lg-nthcdr-of-append-exact-2
                             (n 4) (a (fn-cbor-u32-bytes (len r))) (b (append r rest)))
                  (:instance fn-lg-take-of-append-true-list-exact
                             (n (len r)) (a r) (b rest))
                  (:instance fn-lg-nthcdr-of-append-two
                             (a (fn-cbor-u32-bytes (len r))) (b r) (c rest)))))))

(defthm fn-lg-unpack-of-pack
  (implies (fn-lg-recordsp records max)
           (and (equal (fn-lg-unpack (fn-lg-pack records)) records)
                (fn-lg-unpack-exactp (fn-lg-pack records))))
  :hints (("Goal" :induct (fn-lg-pack records)
           :in-theory (disable fn-cbor-u32-bytes fn-cbor-u32-from fn-lg-recordp
                               fn-lg-unpack fn-lg-unpack-exactp))
          ("Subgoal *1/2" :expand ((fn-lg-unpack nil) (fn-lg-unpack-exactp nil)))))

; A chunk's body: octets, within the bound its kind is opened under.
(defthm fn-lg-chunk-body-octets
  (implies (fn-lg-chunkp chunk max)
           (fn-cbor-octet-listp (fn-lg-frame-body chunk)))
  :hints (("Goal" :in-theory (e/d (fn-lg-frame-body) (fn-lg-pack fn-lg-pack-octets))
           :expand ((fn-lg-recordsp chunk max))
           :use ((:instance fn-lg-pack-octets (records chunk))))))

(defthm fn-lg-chunk-body-bound
  (implies (fn-lg-chunkp chunk max)
           (and (<= (+ *fn-frame-trailer-octets* (len (fn-lg-frame-body chunk)))
                    (fn-lg-kind-bound chunk max))
                (natp (fn-lg-kind-bound chunk max))
                (<= (fn-lg-kind-bound chunk max) *fn-frame-max-payload*)))
  :hints (("Goal" :in-theory (e/d (fn-lg-frame-body fn-lg-frame-kind) (fn-lg-pack)))))

(in-theory (disable fn-lg-kind-bound))

(defthm fn-lg-frame-len
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp (fn-lg-frame-body chunk)))
           (equal (len (fn-lg-frame prev chunk))
                  (+ *fn-frame-overhead-octets* *fn-frame-trailer-octets*
                     (len (fn-lg-frame-body chunk)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-frame-body fn-lg-frame-kind))))

(defthm fn-lg-frame-octets
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (fn-cbor-octet-listp (fn-lg-frame prev chunk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-frame-body fn-lg-frame-kind fn-lg-chunkp
                               fn-lg-chunk-body-bound)
           :use (fn-lg-chunk-body-bound
                 (:instance fn-cbor-u32-bytes-are-octets
                            (n (+ *fn-frame-trailer-octets* (len (fn-lg-frame-body chunk)))))))))

(defthm fn-lg-frame-true-listp
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp (fn-lg-frame-body chunk)))
           (true-listp (fn-lg-frame prev chunk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-frame-body fn-lg-frame-kind))))

(defthm fn-lg-frame-consp
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp (fn-lg-frame-body chunk)))
           (consp (fn-lg-frame prev chunk)))
  :hints (("Goal" :do-not-induct t
           :use fn-lg-frame-len
           :expand ((len (fn-lg-frame prev chunk)))
           :in-theory (disable fn-lg-frame fn-lg-frame-len fn-lg-frame-body))))

(local
 (defthm fn-lg-u32-bytes-true-listp
   (true-listp (fn-cbor-u32-bytes n))
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

; The header of a frame of this log declares the frame's own length, so the
; scan's slice of the frame followed by anything is the frame.
(defthm fn-lg-declared-len-of-frame-append
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (equal (fn-lg-declared-len (append (fn-lg-frame prev chunk) x))
                  (len (fn-lg-frame prev chunk))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-declared-len fn-lg-frame)
                           (fn-cbor-u32-bytes fn-cbor-u32-from fn-lg-frame-body
                            fn-lg-frame-kind fn-lg-chunkp fn-lg-chunk-body-bound
                            fn-lg-frame-len fn-lg-frame-octets))
           :use ((:instance fn-cbor-u32-from-u32-bytes
                            (n (+ *fn-frame-trailer-octets* (len (fn-lg-frame-body chunk)))))
                 (:instance fn-lg-frame-len)
                 (:instance fn-lg-frame-octets)
                 fn-lg-chunk-body-bound
                 (:instance fn-cbor-u32-bytes-are-octets
                            (n (+ *fn-frame-trailer-octets* (len (fn-lg-frame-body chunk)))))))))

(defthm fn-lg-slice-of-frame-append
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (equal (fn-lg-slice (append (fn-lg-frame prev chunk) x))
                  (fn-lg-frame prev chunk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-slice) (fn-lg-frame fn-lg-declared-len fn-lg-chunkp))
           :use (fn-lg-declared-len-of-frame-append fn-lg-frame-true-listp
                 fn-lg-frame-len))))

; The sixth octet of a frame is its kind: the open bound is the kind's.
(defthm fn-lg-open-bound-of-frame
  (implies (fn-frame-digestp prev)
           (equal (fn-lg-open-bound (fn-lg-frame prev chunk) max)
                  (fn-lg-kind-bound chunk max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-frame fn-lg-open-bound fn-lg-kind-bound)
                           (fn-cbor-u32-bytes fn-lg-frame-body)))))

(local
 (defthm fn-lg-take-32-of-append-prev
   (implies (fn-frame-digestp prev)
            (equal (fn-bs-take 32 (append prev body)) prev))))

(local
 (defthm fn-lg-nthcdr-32-of-append-prev
   (implies (fn-frame-digestp prev)
            (equal (nthcdr 32 (append prev body)) body))))

(local
 (defthm fn-lg-seal-open
   (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
            (equal (fn-frame-open (fn-lg-frame prev chunk) (fn-lg-kind-bound chunk max))
                   (fn-frame-ok *fn-lg-magic* *fn-lg-version* (fn-lg-frame-kind chunk)
                                (append prev (fn-lg-frame-body chunk)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lg-frame)
                            (fn-frame-seal fn-frame-open fn-frame-encode
                             fn-frame-protected fn-lg-frame-body fn-lg-frame-kind
                             fn-lg-chunkp fn-lg-chunk-body-bound))
            :use (fn-lg-chunk-body-bound
                  (:instance fn-frame-open-of-seal
                             (magic *fn-lg-magic*) (version *fn-lg-version*)
                             (kind (fn-lg-frame-kind chunk))
                             (payload (append prev (fn-lg-frame-body chunk)))
                             (max-payload (fn-lg-kind-bound chunk max))))))))

(local
 (defthm fn-lg-chunk-kind-2-facts
   (implies (and (fn-lg-chunkp chunk max)
                 (equal (fn-lg-frame-kind chunk) *fn-lg-batch-kind*))
            (fn-lg-unpack-okp (fn-lg-frame-body chunk) max))
   :hints (("Goal" :in-theory (e/d (fn-lg-frame-body fn-lg-frame-kind)
                                   (fn-lg-pack fn-lg-unpack-of-pack fn-lg-recordsp
                                    fn-lg-unpack fn-lg-unpack-exactp))
            :use ((:instance fn-lg-unpack-of-pack (records chunk)))))))

(local
 (defthm fn-lg-chunk-kind-1-records
   (implies (and (fn-lg-chunkp chunk max)
                 (not (equal (fn-lg-frame-kind chunk) *fn-lg-batch-kind*)))
            (equal (list (fn-lg-frame-body chunk)) chunk))
   :hints (("Goal" :in-theory (enable fn-lg-frame-body fn-lg-frame-kind)))))

(local
 (defthm fn-lg-chunk-kind-2-records
   (implies (and (fn-lg-chunkp chunk max)
                 (equal (fn-lg-frame-kind chunk) *fn-lg-batch-kind*))
            (equal (fn-lg-unpack (fn-lg-frame-body chunk)) chunk))
   :hints (("Goal" :in-theory (e/d (fn-lg-frame-body fn-lg-frame-kind)
                                   (fn-lg-pack fn-lg-unpack-of-pack fn-lg-recordsp
                                    fn-lg-unpack fn-lg-unpack-exactp))
            :use ((:instance fn-lg-unpack-of-pack (records chunk)))))))

(local
 (defthm fn-lg-frame-kind-values
   (or (equal (fn-lg-frame-kind chunk) 1) (equal (fn-lg-frame-kind chunk) 2))
   :rule-classes nil))

; The frame validates against its predecessor and yields its records.
(defthm fn-lg-entry-okp-of-frame
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (fn-lg-entry-okp (fn-lg-frame prev chunk) prev max))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-frame fn-frame-open fn-lg-frame-body fn-lg-frame-kind
                               fn-lg-chunkp fn-lg-unpack-okp)
           :use (fn-lg-frame-consp fn-lg-chunk-body-octets fn-lg-seal-open
                 fn-lg-frame-kind-values))))

(defthm fn-lg-slice-records-of-frame
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (equal (fn-lg-slice-records (fn-lg-frame prev chunk) max) chunk))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-frame fn-frame-open fn-lg-frame-body fn-lg-frame-kind
                               fn-lg-chunkp fn-lg-unpack)
           :use (fn-lg-seal-open fn-lg-frame-kind-values))))

(local
 (defthm fn-lg-zeros-len
   (equal (len (fn-bs-zeros n)) (nfix n))))
(local
 (defthm fn-lg-zeros-true-listp
   (true-listp (fn-bs-zeros n))))

; An entry is its frame and its padding; its length is the aligned step.
(defthm fn-lg-entry-len
  (equal (len (fn-lg-entry prev chunk unit))
         (+ (len (fn-lg-frame prev chunk))
            (fn-lg-pad-len (len (fn-lg-frame prev chunk)) unit)))
  :hints (("Goal" :in-theory (disable fn-lg-frame fn-lg-frame-len fn-lg-pad-len))))

(defthm fn-lg-entry-true-listp
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp (fn-lg-frame-body chunk)))
           (true-listp (fn-lg-entry prev chunk unit)))
  :hints (("Goal" :in-theory (disable fn-lg-frame fn-lg-frame-body))))

(local
 (defthm fn-lg-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; An entry followed by anything: the scan's slice is the entry's frame, and
; the aligned step past the frame lands on the rest.
(defthm fn-lg-slice-of-entry-append
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (equal (fn-lg-slice (append (fn-lg-entry prev chunk unit) x))
                  (fn-lg-frame prev chunk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-entry)
                           (fn-lg-frame fn-lg-slice fn-lg-declared-len fn-lg-pad-len
                            fn-lg-slice-of-frame-append fn-lg-chunkp))
           :use ((:instance fn-lg-slice-of-frame-append
                            (x (append (fn-bs-zeros
                                        (fn-lg-pad-len (len (fn-lg-frame prev chunk))
                                                       unit))
                                       x)))))))

(defthm fn-lg-nthcdr-of-entry-append
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp (fn-lg-frame-body chunk)))
           (equal (nthcdr (+ (len (fn-lg-frame prev chunk))
                             (fn-lg-pad-len (len (fn-lg-frame prev chunk)) unit))
                          (append (fn-lg-entry prev chunk unit) x))
                  x))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-frame fn-lg-entry fn-lg-pad-len fn-lg-frame-len
                               fn-lg-entry-len fn-lg-frame-body)
           :use (fn-lg-entry-len
                 (:instance fn-lg-nthcdr-of-append-exact
                            (n (len (fn-lg-entry prev chunk unit)))
                            (a (fn-lg-entry prev chunk unit)) (b x))))))

(local (in-theory (disable fn-frame-seal fn-frame-encode fn-frame-protected
                           fn-frame-header fn-frame-inputp fn-frame-magicp
                           fn-frame-digestp fn-frame-item fn-lg-frame
                           fn-lg-frame-body fn-lg-frame-kind)))

; -----------------------------------------------------------------------------
; The chunks of a batch.

(local
 (defthm fn-lg-fit-count-bound
   (<= (fn-lg-fit-count records used) (len records))
   :rule-classes :linear))

(defthm fn-lg-chunk-len-bounds
  (implies (consp records)
           (and (<= 1 (fn-lg-chunk-len records))
                (<= (fn-lg-chunk-len records) (len records))))
  :rule-classes :linear)

(local
 (defthm fn-lg-fit-count-fits
   (implies (and (natp used) (<= used *fn-frame-max-payload*))
            (<= (+ used (fn-lg-pack-len (fn-bs-take (fn-lg-fit-count records used) records)))
                *fn-frame-max-payload*))
   :hints (("Goal" :induct (fn-lg-fit-count records used)))))

(local
 (defthm fn-lg-recordsp-of-take
   (implies (and (fn-lg-recordsp records max) (<= (nfix k) (len records)))
            (fn-lg-recordsp (fn-bs-take k records) max))
   :hints (("Goal" :in-theory (disable fn-lg-recordp)))))

(defthm fn-lg-recordsp-of-nthcdr
  (implies (fn-lg-recordsp records max)
           (fn-lg-recordsp (nthcdr k records) max))
  :hints (("Goal" :in-theory (disable fn-lg-recordp))))

(local
 (defthm fn-lg-consp-take
   (implies (posp k) (consp (fn-bs-take k x)))))

(local
 (defthm fn-lg-take-1-cdr
   (not (consp (cdr (fn-bs-take 1 x))))
   :hints (("Goal" :expand ((fn-bs-take 1 x) (fn-bs-take 0 (cdr x)))))))

; Every chunk the log writes is a chunk the scan reads back.
(defthm fn-lg-chunkp-of-first-chunk
  (implies (and (fn-lg-recordsp records max) (consp records))
           (fn-lg-chunkp (fn-bs-take (fn-lg-chunk-len records) records) max))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-recordsp fn-lg-fit-count-fits)
           :cases ((<= (fn-lg-fit-count records *fn-frame-trailer-octets*) 1))
           :use ((:instance fn-lg-fit-count-fits (used *fn-frame-trailer-octets*))))))

(local
 (defthm fn-lg-take-then-nthcdr-append
   (implies (and (true-listp x) (<= (nfix k) (len x)))
            (equal (append (fn-bs-take k x) (nthcdr k x)) x))))

(local
 (defthm fn-lg-take-nthcdr-append-assoc
   (implies (and (true-listp x) (<= (nfix k) (len x)))
            (equal (append (fn-bs-take k x) (append (nthcdr k x) y)) (append x y)))
   :hints (("Goal" :use fn-lg-take-then-nthcdr-append
            :in-theory (disable fn-lg-take-then-nthcdr-append)))))

(in-theory (disable fn-lg-chunk-len))

; -----------------------------------------------------------------------------
; Keystone 1: the scan of a log followed by X.

(local
 (defthm fn-lg-scan-step
   (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
            (equal (fn-lg-scan (append (fn-lg-entry prev chunk unit) x) prev unit max)
                   (let ((rest (fn-lg-scan x (fn-lg-trailer (fn-lg-frame prev chunk))
                                           unit max)))
                     (cons (append chunk (car rest))
                           (+ (len (fn-lg-entry prev chunk unit)) (cdr rest))))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-lg-scan (append (fn-lg-entry prev chunk unit) x)
                                 prev unit max))
            :use (fn-lg-chunk-body-octets)
            :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-records
                                fn-lg-declared-len fn-lg-frame-len fn-lg-trailer
                                fn-lg-entry fn-lg-pad-len fn-lg-frame fn-lg-chunkp)))))

; The consumed count is a natural, and a frame's trailer is a digest (so the
; chain's next predecessor satisfies the keystone's hypothesis).
(defthm fn-lg-scan-consumed-natp
  (natp (cdr (fn-lg-scan octets prev unit max)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-lg-scan octets prev unit max)
           :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-records
                               fn-lg-declared-len fn-lg-trailer fn-lg-pad-len))))

(defthm fn-lg-trailer-of-frame-digestp
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (fn-frame-digestp (fn-lg-trailer (fn-lg-frame prev chunk))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-trailer fn-lg-frame fn-frame-seal fn-frame-encode
                            fn-frame-digestp)
                           (fn-lg-frame-len fn-frame-protected fn-lg-chunkp
                            fn-lg-frame-body fn-lg-frame-kind))
           :use (fn-lg-chunk-body-octets fn-lg-chunk-body-bound
                 (:instance fn-lg-nthcdr-of-append-exact
                            (n (len (fn-frame-protected *fn-lg-magic* *fn-lg-version*
                                                        (fn-lg-frame-kind chunk)
                                                        (append prev (fn-lg-frame-body chunk)))))
                            (a (fn-frame-protected *fn-lg-magic* *fn-lg-version*
                                                   (fn-lg-frame-kind chunk)
                                                   (append prev (fn-lg-frame-body chunk))))
                            (b (fn-frame-digest
                                (fn-frame-protected *fn-lg-magic* *fn-lg-version*
                                                    (fn-lg-frame-kind chunk)
                                                    (append prev (fn-lg-frame-body chunk))))))))))

(defthm fn-lg-recordsp-true-listp
  (implies (fn-lg-recordsp records max) (true-listp records))
  :rule-classes :forward-chaining)

(defthm fn-lg-log-unfolds
   (implies (consp records)
            (equal (fn-lg-log records prev unit)
                   (append (fn-lg-entry prev (fn-bs-take (fn-lg-chunk-len records) records) unit)
                           (fn-lg-log (nthcdr (fn-lg-chunk-len records) records)
                                      (fn-lg-trailer
                                       (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len records)
                                                                     records)))
                                      unit))))
   :hints (("Goal" :expand ((fn-lg-log records prev unit)))))

(defthm fn-lg-last-trailer-unfolds
   (implies (consp records)
            (equal (fn-lg-last-trailer records prev)
                   (fn-lg-last-trailer (nthcdr (fn-lg-chunk-len records) records)
                                       (fn-lg-trailer
                                        (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len records)
                                                                      records))))))
   :hints (("Goal" :expand ((fn-lg-last-trailer records prev)))))

(local
 (defthm fn-lg-scan-step-then
   (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max)
                 (equal (fn-lg-scan y (fn-lg-trailer (fn-lg-frame prev chunk)) unit max)
                        (cons ra b)))
            (equal (fn-lg-scan (append (fn-lg-entry prev chunk unit) y) prev unit max)
                   (cons (append chunk ra) (+ (len (fn-lg-entry prev chunk unit)) b))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lg-scan-step (x y)))
            :in-theory (disable fn-lg-scan-step fn-lg-scan fn-lg-entry fn-lg-frame
                                fn-lg-trailer fn-lg-chunkp fn-lg-entry-len)))))

(defthm fn-lg-scan-of-log-append
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (equal (fn-lg-scan (append (fn-lg-log records prev unit) x) prev unit max)
                  (let ((rest (fn-lg-scan x (fn-lg-last-trailer records prev) unit max)))
                    (cons (append records (car rest))
                          (+ (len (fn-lg-log records prev unit)) (cdr rest))))))
  :hints (("Goal" :induct (fn-lg-log records prev unit)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (disable fn-lg-scan fn-lg-entry fn-lg-trailer fn-lg-entry-len
                               fn-lg-recordp fn-lg-frame fn-lg-pad-len fn-lg-chunkp
                               fn-lg-recordsp (:definition fn-lg-log)
                               (:definition fn-lg-last-trailer)
                               fn-lg-take-then-nthcdr-append fn-lg-recordsp-of-nthcdr
                               fn-lg-chunkp-of-first-chunk fn-lg-trailer-of-frame-digestp
                               fn-lg-scan-step fn-lg-scan-step-then))
          ("Subgoal *1/2" :expand ((fn-lg-log records prev unit)
                                   (fn-lg-last-trailer records prev)
                                   (fn-lg-log nil prev unit)
                                   (fn-lg-last-trailer nil prev)))
          ("Subgoal *1/1"
           :use ((:instance fn-lg-chunkp-of-first-chunk)
                 (:instance fn-lg-recordsp-of-nthcdr (k (fn-lg-chunk-len records)))
                 (:instance fn-lg-trailer-of-frame-digestp
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))
                 (:instance fn-lg-scan-step-then
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records))
                            (y (append (fn-lg-log (nthcdr (fn-lg-chunk-len records) records)
                                                  (fn-lg-trailer
                                                   (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len records)
                                                                                 records)))
                                                  unit)
                                       x))
                            (ra (append (nthcdr (fn-lg-chunk-len records) records)
                                        (car (fn-lg-scan x (fn-lg-last-trailer
                                                            (nthcdr (fn-lg-chunk-len records) records)
                                                            (fn-lg-trailer
                                                             (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len records)
                                                                                           records))))
                                                         unit max))))
                            (b (+ (len (fn-lg-log (nthcdr (fn-lg-chunk-len records) records)
                                                  (fn-lg-trailer
                                                   (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len records)
                                                                                 records)))
                                                  unit))
                                  (cdr (fn-lg-scan x (fn-lg-last-trailer
                                                      (nthcdr (fn-lg-chunk-len records) records)
                                                      (fn-lg-trailer
                                                       (fn-lg-frame prev (fn-bs-take (fn-lg-chunk-len records)
                                                                                     records))))
                                                   unit max)))))))))

(local
 (defthm fn-lg-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

; The frontier of a well-formed log is its length: every record is read back
; and the next append goes at the end.
(defthm fn-lg-scan-of-log
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (equal (fn-lg-scan (fn-lg-log records prev unit) prev unit max)
                  (cons records (len (fn-lg-log records prev unit)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lg-scan-of-log-append (x nil)))
           :in-theory (disable fn-lg-scan fn-lg-log fn-lg-scan-of-log-append
                               fn-lg-recordsp))))

; -----------------------------------------------------------------------------
; Keystone 2: the scan of a torn entry.

; The first slice validates as a chained record frame and is not FRAME: the
; event the structural argument cannot exclude.  A-CRYPTO-TRAILER
; (books/assumptions.lisp) is what excludes it for the platform's tears; the
; design quotes the figure.
(defun fn-lg-forgeryp (octets prev max frame)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lg-entry-okp (fn-lg-slice octets) prev max)
       (not (equal (fn-lg-slice octets) frame))))

; A torn variant of a write is no longer than the write: every piece the
; crash lands lies within the write's range.
(local
 (defthm fn-lg-splice-len
   (equal (len (fn-bs-splice old offset octets))
          (max (len old) (+ (nfix offset) (len octets))))
   :hints (("Goal" :in-theory (enable fn-bs-splice)))))

; Every write among OPS ends at or before BOUND.
(defun fn-lg-writes-within (ops bound)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (or (not (equal (car (car ops)) :write))
               (<= (+ (nfix (nth 2 (car ops))) (len (nth 3 (car ops)))) bound))
           (fn-lg-writes-within (cdr ops) bound))
    t))

(local
 (defthm fn-lg-writes-within-of-append
   (equal (fn-lg-writes-within (append a b) bound)
          (and (fn-lg-writes-within a bound) (fn-lg-writes-within b bound)))))

; Applying writes that end within BOUND to a table whose inode 0 is within
; BOUND keeps inode 0 within BOUND.
(local
 (defthm fn-lg-apply-writes-len-bound
   (implies (and (fn-lg-writes-within ops bound)
                 (<= (len (cdr (assoc-equal 0 inodes))) bound))
            (<= (len (cdr (assoc-equal 0 (fn-bs-apply-writes inodes ops)))) bound))
   :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
            :in-theory (enable fn-bs-apply-writes))
           ("Subgoal *1/1" :cases ((equal (nth 1 (car ops)) 0))))))

(local
 (defthm fn-lg-apply-ops-len-bound
   (implies (and (fn-lg-writes-within ops bound)
                 (<= (len (cdr (assoc-equal 0 inodes))) bound))
            (<= (len (cdr (assoc-equal 0 (mv-nth 0 (fn-bs-apply-ops inodes dirs ops)))))
                bound))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-bs-apply-ops fn-lg-apply-writes-len-bound)
            :use fn-lg-apply-writes-len-bound))))

; One floor fact for the unit arithmetic, as byte-store-invariants takes its
; own: arithmetic-5 inside a local encapsulate so that its rules reach
; nothing else in this book.
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lg-floor-times-unit-below
     (implies (and (integerp a) (posp unit))
              (<= (* (floor a unit) unit) a))
     :rule-classes :linear)
   (defthm fn-lg-times-unit-monotone
     (implies (and (integerp i) (integerp f) (<= i f) (posp unit))
              (<= (* i unit) (* f unit)))
     :rule-classes nil)))

; A unit index below the write's unit count starts within the write.
(local
 (defthm fn-lg-unit-index-within
   (implies (and (natp i) (posp unit) (natp len)
                 (< i (fn-bs-unit-count 0 len unit)))
            (<= (* i unit) len))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bs-unit-count) (floor fn-lg-floor-times-unit-below))
            :use ((:instance fn-lg-floor-times-unit-below (a (+ len -1)))
                  (:instance fn-lg-times-unit-monotone
                             (f (floor (+ len -1) unit))))))))

; The same bound with the write's own length, so that the rule has no free
; variable and fires under the induction below.
(local
 (defthm fn-lg-unit-index-within-op
   (implies (and (natp i) (posp unit)
                 (< i (fn-bs-unit-count 0 (len (nth 3 op)) unit)))
            (<= (* i unit) (len (nth 3 op))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-bs-unit-count)
            :use ((:instance fn-lg-unit-index-within (len (len (nth 3 op)))))))))

(local
 (defthm fn-lg-tear-write-pieces-within
   (implies (equal (nth 2 op) 0)
            (fn-lg-writes-within (fn-bs-tear-write op selectors i unit)
                                 (len (nth 3 op))))
   :hints (("Goal" :induct (fn-bs-tear-write op selectors i unit)
            :in-theory (e/d (fn-bs-tear-write) (fn-bs-unit-count))))))

; The content inode 0 holds after any crash of the one-inode store with the
; one pending write WRITTEN at offset 0 is no longer than WRITTEN.
(local
 (defthm fn-lg-one-inode-crash-len
   (<= (len (cdr (assoc-equal
                  0 (fn-bs-inodes
                     (fn-bs-crash (fn-bs-make unit (list (cons 0 nil)) nil
                                              (list (list :write 0 0 written)) 1)
                                  choices)))))
       (len written))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bs-crash fn-bs-crash-select)
                            (fn-lg-apply-ops-len-bound fn-lg-tear-write-pieces-within
                             fn-bs-tear-write fn-bs-apply-ops))
            :use ((:instance fn-lg-apply-ops-len-bound
                             (inodes (list (cons 0 nil))) (dirs nil) (bound (len written))
                             (ops (fn-bs-crash-select (list (list :write 0 0 written))
                                                      choices unit)))
                  (:instance fn-lg-tear-write-pieces-within
                             (op (list :write 0 0 written)) (i 0)
                             (selectors (if (consp choices) (car choices) nil))))))))

(defthm fn-lg-torn-variant-len
  (implies (fn-bs-torn-variantp unit observed written)
           (<= (len observed) (len written)))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-torn-variantp fn-bs-crash-imagep)
                           (fn-bs-crash fn-lg-one-inode-crash-len))
           :use ((:instance fn-lg-one-inode-crash-len
                            (choices (fn-bs-crash-imagep-witness
                                      (fn-bs-make unit (list (cons 0 nil)) nil
                                                  (list (list :write 0 0 written)) 1)
                                      (fn-bs-make unit (list (cons 0 observed)) nil nil 1))))))))

(local
 (defthm fn-lg-scan-of-atom
   (implies (atom x) (equal (fn-lg-scan x prev unit max) (cons nil 0)))))

(local
 (defthm fn-lg-nthcdr-past-end-is-atom
   (implies (<= (len x) (nfix k)) (atom (nthcdr k x)))))

(defthm fn-lg-scan-of-torn-entry
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max)
                (fn-bs-torn-variantp unit observed (fn-lg-entry prev chunk unit)))
           (or (equal (fn-lg-scan observed prev unit max) (cons nil 0))
               (equal (fn-lg-scan observed prev unit max)
                      (cons chunk (len (fn-lg-entry prev chunk unit))))
               (fn-lg-forgeryp observed prev max (fn-lg-frame prev chunk))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((equal (fn-lg-slice observed) (fn-lg-frame prev chunk)))
           :expand ((fn-lg-scan observed prev unit max))
           :use ((:instance fn-lg-slice-len (octets observed))
                 (:instance fn-lg-torn-variant-len
                            (written (fn-lg-entry prev chunk unit)))
                 (:instance fn-lg-entry-len)
                 (:instance fn-lg-nthcdr-past-end-is-atom
                            (x observed)
                            (k (+ (fn-lg-declared-len observed)
                                  (fn-lg-pad-len (fn-lg-declared-len observed) unit))))
                 (:instance fn-lg-scan-of-atom
                            (x (nthcdr (+ (fn-lg-declared-len observed)
                                          (fn-lg-pad-len (fn-lg-declared-len observed) unit))
                                       observed))
                            (prev (fn-lg-trailer (fn-lg-slice observed)))))
           :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-records
                               fn-lg-declared-len fn-lg-trailer fn-lg-entry
                               fn-lg-pad-len fn-lg-slice-len fn-lg-entry-len
                               fn-lg-torn-variant-len fn-lg-nthcdr-past-end-is-atom
                               fn-lg-scan-of-atom fn-bs-torn-variantp fn-lg-chunkp))))

; A log's last trailer is a digest: the chain hands the next append a
; predecessor the keystones' hypothesis admits.
(defthm fn-lg-last-trailer-digestp
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (fn-frame-digestp (fn-lg-last-trailer records prev)))
  :hints (("Goal" :induct (fn-lg-last-trailer records prev)
           :in-theory (disable fn-lg-frame fn-lg-trailer fn-lg-recordp fn-lg-recordsp
                               fn-lg-chunkp (:definition fn-lg-last-trailer)
                               fn-lg-trailer-of-frame-digestp))
          ("Subgoal *1/2" :expand ((fn-lg-last-trailer records prev)
                                   (fn-lg-last-trailer nil prev)))
          ("Subgoal *1/1"
           :use ((:instance fn-lg-chunkp-of-first-chunk)
                 (:instance fn-lg-recordsp-of-nthcdr (k (fn-lg-chunk-len records)))
                 (:instance fn-lg-trailer-of-frame-digestp
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))))))

; Composed: a log and then a torn append.
(defthm fn-lg-scan-of-log-then-torn-entry
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max)
                (fn-lg-chunkp chunk max)
                (fn-bs-torn-variantp unit observed
                                     (fn-lg-entry (fn-lg-last-trailer records prev)
                                                  chunk unit)))
           (let ((scan (fn-lg-scan (append (fn-lg-log records prev unit) observed)
                                   prev unit max)))
             (or (equal scan (cons records (len (fn-lg-log records prev unit))))
                 (equal scan (cons (append records chunk)
                                   (+ (len (fn-lg-log records prev unit))
                                      (len (fn-lg-entry (fn-lg-last-trailer records prev)
                                                        chunk unit)))))
                 (fn-lg-forgeryp observed (fn-lg-last-trailer records prev) max
                                 (fn-lg-frame (fn-lg-last-trailer records prev) chunk)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lg-scan-of-torn-entry
                            (prev (fn-lg-last-trailer records prev)))
                 (:instance fn-lg-scan-of-log-append (x observed)))
           :in-theory (disable fn-lg-scan fn-lg-log fn-lg-entry fn-lg-frame
                               fn-lg-last-trailer fn-lg-scan-of-log-append
                               fn-lg-forgeryp fn-bs-torn-variantp fn-lg-recordsp
                               fn-lg-recordp fn-lg-chunkp))))

; The unfolding rules stay available by name (the crash book enables them
; where it steps a batch chunk by chunk).
(in-theory (disable fn-lg-log-unfolds fn-lg-last-trailer-unfolds))
