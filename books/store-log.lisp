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

(defun fn-lg-frame (prev record)
  (declare (xargs :guard (and (fn-frame-digestp prev)
                              (fn-cbor-octet-listp record)
                              (<= (+ *fn-frame-trailer-octets* (len record))
                                  *fn-cbor-max-uint*))
                  :verify-guards nil))
  (fn-frame-seal *fn-lg-magic* *fn-lg-version* *fn-lg-record-kind*
                 (append prev record)))

(defun fn-lg-entry (prev record unit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-lg-frame prev record)))
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

; The slice validates as a chained record frame of this log.
(defun fn-lg-entry-okp (slice prev max)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp slice)
       (let ((r (fn-frame-open slice max)))
         (and (fn-frame-result-okp r)
              (equal (fn-frame-result-magic r) *fn-lg-magic*)
              (equal (fn-frame-result-version r) *fn-lg-version*)
              (equal (fn-frame-result-kind r) *fn-lg-record-kind*)
              (equal (fn-bs-take *fn-frame-trailer-octets*
                                 (fn-frame-result-payload r))
                     prev)))))

(defun fn-lg-slice-record (slice max)
  (declare (xargs :guard t :verify-guards nil))
  (nthcdr *fn-frame-trailer-octets*
          (fn-frame-result-payload (fn-frame-open slice max))))

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
        (cons (cons (fn-lg-slice-record slice max) (car rest))
              (+ step (cdr rest)))))))

(defthm fn-lg-scan-of-empty
  (equal (fn-lg-scan nil prev unit max) (cons nil 0)))

; -----------------------------------------------------------------------------
; A well-formed log: the chained entries of RECORDS from PREV.

(defun fn-lg-log (records prev unit)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (append (fn-lg-entry prev (car records) unit)
              (fn-lg-log (cdr records)
                         (fn-lg-trailer (fn-lg-frame prev (car records)))
                         unit))
    nil))

(defun fn-lg-last-trailer (records prev)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (fn-lg-last-trailer (cdr records)
                          (fn-lg-trailer (fn-lg-frame prev (car records))))
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

(defthm fn-lg-frame-len
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp record))
           (equal (len (fn-lg-frame prev record))
                  (+ *fn-frame-overhead-octets* *fn-frame-trailer-octets*
                     (len record))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-lg-frame-octets
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
           (fn-cbor-octet-listp (fn-lg-frame prev record)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cbor-u32-bytes-are-octets
                            (n (+ *fn-frame-trailer-octets* (len record))))))))

(defthm fn-lg-frame-true-listp
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp record))
           (true-listp (fn-lg-frame prev record)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-lg-frame-consp
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp record))
           (consp (fn-lg-frame prev record)))
  :hints (("Goal" :do-not-induct t
           :use fn-lg-frame-len
           :expand ((len (fn-lg-frame prev record)))
           :in-theory (disable fn-lg-frame fn-lg-frame-len))))

(local
 (defthm fn-lg-u32-bytes-true-listp
   (true-listp (fn-cbor-u32-bytes n))
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

; The header of a frame of this log declares the frame's own length, so the
; scan's slice of the frame followed by anything is the frame.
(defthm fn-lg-declared-len-of-frame-append
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
           (equal (fn-lg-declared-len (append (fn-lg-frame prev record) x))
                  (len (fn-lg-frame prev record))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-declared-len fn-lg-frame)
                           (fn-cbor-u32-bytes fn-cbor-u32-from
                            fn-lg-frame-len fn-lg-frame-octets))
           :use ((:instance fn-cbor-u32-from-u32-bytes
                            (n (+ *fn-frame-trailer-octets* (len record))))
                 (:instance fn-lg-frame-len)
                 (:instance fn-lg-frame-octets)
                 (:instance fn-cbor-u32-bytes-are-octets
                            (n (+ *fn-frame-trailer-octets* (len record))))))))

(defthm fn-lg-slice-of-frame-append
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
           (equal (fn-lg-slice (append (fn-lg-frame prev record) x))
                  (fn-lg-frame prev record)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-slice) (fn-lg-frame fn-lg-declared-len))
           :use (fn-lg-declared-len-of-frame-append fn-lg-frame-true-listp
                 fn-lg-frame-len))))

; The frame validates against its predecessor and yields its record.
(defthm fn-lg-entry-okp-of-frame
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
           (fn-lg-entry-okp (fn-lg-frame prev record) prev max))
  :hints (("Goal" :in-theory (e/d (fn-lg-frame)
                                  (fn-frame-seal fn-frame-open fn-frame-encode
                                   fn-frame-protected))
           :use (fn-lg-frame-consp
                 (:instance fn-frame-open-of-seal
                            (magic *fn-lg-magic*) (version *fn-lg-version*)
                            (kind *fn-lg-record-kind*)
                            (payload (append prev record))
                            (max-payload max))))))

(defthm fn-lg-slice-record-of-frame
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
           (equal (fn-lg-slice-record (fn-lg-frame prev record) max) record))
  :hints (("Goal" :in-theory (e/d (fn-lg-frame)
                                  (fn-frame-seal fn-frame-open fn-frame-encode
                                   fn-frame-protected))
           :use (fn-lg-frame-consp
                 (:instance fn-frame-open-of-seal
                            (magic *fn-lg-magic*) (version *fn-lg-version*)
                            (kind *fn-lg-record-kind*)
                            (payload (append prev record))
                            (max-payload max))))))

(local
 (defthm fn-lg-zeros-len
   (equal (len (fn-bs-zeros n)) (nfix n))))

(local
 (defthm fn-lg-zeros-true-listp
   (true-listp (fn-bs-zeros n))))

; An entry is its frame and its padding; its length is the aligned step.
(defthm fn-lg-entry-len
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp record))
           (equal (len (fn-lg-entry prev record unit))
                  (+ (len (fn-lg-frame prev record))
                     (fn-lg-pad-len (len (fn-lg-frame prev record)) unit))))
  :hints (("Goal" :in-theory (disable fn-lg-frame fn-lg-frame-len fn-lg-pad-len))))

(defthm fn-lg-entry-true-listp
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp record))
           (true-listp (fn-lg-entry prev record unit)))
  :hints (("Goal" :in-theory (disable fn-lg-frame))))

(local
 (defthm fn-lg-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; An entry followed by anything: the scan's slice is the entry's frame, and
; the aligned step past the frame lands on the rest.
(defthm fn-lg-slice-of-entry-append
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
           (equal (fn-lg-slice (append (fn-lg-entry prev record unit) x))
                  (fn-lg-frame prev record)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-entry)
                           (fn-lg-frame fn-lg-slice fn-lg-declared-len fn-lg-pad-len
                            fn-lg-slice-of-frame-append))
           :use ((:instance fn-lg-slice-of-frame-append
                            (x (append (fn-bs-zeros
                                        (fn-lg-pad-len (len (fn-lg-frame prev record))
                                                       unit))
                                       x)))))))

(defthm fn-lg-nthcdr-of-entry-append
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp record))
           (equal (nthcdr (+ (len (fn-lg-frame prev record))
                             (fn-lg-pad-len (len (fn-lg-frame prev record)) unit))
                          (append (fn-lg-entry prev record unit) x))
                  x))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-frame fn-lg-entry fn-lg-pad-len fn-lg-frame-len
                               fn-lg-entry-len)
           :use (fn-lg-entry-len
                 (:instance fn-lg-nthcdr-of-append-exact
                            (n (len (fn-lg-entry prev record unit)))
                            (a (fn-lg-entry prev record unit)) (b x))))))

(local (in-theory (disable fn-frame-seal fn-frame-encode fn-frame-protected
                           fn-frame-header fn-frame-inputp fn-frame-magicp
                           fn-frame-digestp fn-frame-item fn-lg-frame)))

; -----------------------------------------------------------------------------
; Keystone 1: the scan of a log followed by X.

(local
 (defthm fn-lg-scan-step
   (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
            (equal (fn-lg-scan (append (fn-lg-entry prev record unit) x) prev unit max)
                   (let ((rest (fn-lg-scan x (fn-lg-trailer (fn-lg-frame prev record))
                                           unit max)))
                     (cons (cons record (car rest))
                           (+ (len (fn-lg-entry prev record unit)) (cdr rest))))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-lg-scan (append (fn-lg-entry prev record unit) x)
                                 prev unit max))
            :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-record
                                fn-lg-declared-len fn-lg-frame-len fn-lg-trailer
                                fn-lg-entry fn-lg-pad-len fn-lg-frame fn-lg-recordp)))))

; The consumed count is a natural, and a frame's trailer is a digest (so the
; chain's next predecessor satisfies the keystone's hypothesis).
(defthm fn-lg-scan-consumed-natp
  (natp (cdr (fn-lg-scan octets prev unit max)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-lg-scan octets prev unit max)
           :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-record
                               fn-lg-declared-len fn-lg-trailer fn-lg-pad-len))))

(defthm fn-lg-trailer-of-frame-digestp
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max))
           (fn-frame-digestp (fn-lg-trailer (fn-lg-frame prev record))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-trailer fn-lg-frame fn-frame-seal fn-frame-encode
                            fn-frame-digestp)
                           (fn-lg-frame-len fn-frame-protected fn-lg-recordp))
           :use ((:instance fn-lg-nthcdr-of-append-exact
                            (n (len (fn-frame-protected *fn-lg-magic* *fn-lg-version*
                                                        *fn-lg-record-kind*
                                                        (append prev record))))
                            (a (fn-frame-protected *fn-lg-magic* *fn-lg-version*
                                                   *fn-lg-record-kind*
                                                   (append prev record)))
                            (b (fn-frame-digest
                                (fn-frame-protected *fn-lg-magic* *fn-lg-version*
                                                    *fn-lg-record-kind*
                                                    (append prev record)))))))))

(defthm fn-lg-scan-of-log-append
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (equal (fn-lg-scan (append (fn-lg-log records prev unit) x) prev unit max)
                  (let ((rest (fn-lg-scan x (fn-lg-last-trailer records prev) unit max)))
                    (cons (append records (car rest))
                          (+ (len (fn-lg-log records prev unit)) (cdr rest))))))
  :hints (("Goal" :induct (fn-lg-log records prev unit)
           :in-theory (disable fn-lg-scan fn-lg-entry fn-lg-trailer fn-lg-entry-len
                               fn-lg-recordp fn-lg-frame fn-lg-pad-len))))

(defthm fn-lg-recordsp-true-listp
  (implies (fn-lg-recordsp records max) (true-listp records))
  :rule-classes :forward-chaining)
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
  (implies (and (fn-frame-digestp prev) (fn-lg-recordp record max)
                (fn-bs-torn-variantp unit observed (fn-lg-entry prev record unit)))
           (or (equal (fn-lg-scan observed prev unit max) (cons nil 0))
               (equal (fn-lg-scan observed prev unit max)
                      (cons (list record) (len (fn-lg-entry prev record unit))))
               (fn-lg-forgeryp observed prev max (fn-lg-frame prev record))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((equal (fn-lg-slice observed) (fn-lg-frame prev record)))
           :expand ((fn-lg-scan observed prev unit max))
           :use ((:instance fn-lg-slice-len (octets observed))
                 (:instance fn-lg-torn-variant-len
                            (written (fn-lg-entry prev record unit)))
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
           :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-record
                               fn-lg-declared-len fn-lg-trailer fn-lg-entry
                               fn-lg-pad-len fn-lg-slice-len fn-lg-entry-len
                               fn-lg-torn-variant-len fn-lg-nthcdr-past-end-is-atom
                               fn-lg-scan-of-atom fn-bs-torn-variantp))))

; A log's last trailer is a digest: the chain hands the next append a
; predecessor the keystones' hypothesis admits.
(defthm fn-lg-last-trailer-digestp
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (fn-frame-digestp (fn-lg-last-trailer records prev)))
  :hints (("Goal" :induct (fn-lg-last-trailer records prev)
           :in-theory (disable fn-lg-frame fn-lg-trailer fn-lg-recordp))))

; Composed: a log and then a torn append.
(defthm fn-lg-scan-of-log-then-torn-entry
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max)
                (fn-lg-recordp record max)
                (fn-bs-torn-variantp unit observed
                                     (fn-lg-entry (fn-lg-last-trailer records prev)
                                                  record unit)))
           (let ((scan (fn-lg-scan (append (fn-lg-log records prev unit) observed)
                                   prev unit max)))
             (or (equal scan (cons records (len (fn-lg-log records prev unit))))
                 (equal scan (cons (append records (list record))
                                   (+ (len (fn-lg-log records prev unit))
                                      (len (fn-lg-entry (fn-lg-last-trailer records prev)
                                                        record unit)))))
                 (fn-lg-forgeryp observed (fn-lg-last-trailer records prev) max
                                 (fn-lg-frame (fn-lg-last-trailer records prev) record)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lg-scan-of-torn-entry
                            (prev (fn-lg-last-trailer records prev)))
                 (:instance fn-lg-scan-of-log-append (x observed)))
           :in-theory (disable fn-lg-scan fn-lg-log fn-lg-entry fn-lg-frame
                               fn-lg-last-trailer fn-lg-scan-of-log-append
                               fn-lg-forgeryp fn-bs-torn-variantp fn-lg-recordsp
                               fn-lg-recordp))))
