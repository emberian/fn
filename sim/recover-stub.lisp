(in-package "ACL2")
(include-book "../books/profile")
(include-book "../books/columns")
(include-book "../books/fnv")
(include-book "prng")

; Layer A scribe format v1, little endian, 4096 bytes per sector:
; 0..3 magic #x324e4653 ("SFN2"), 4..7 version 1, 8..11 sector
; address, 12..15 sequence=address+1, 16..19 FNV-1a checksum; 20..4095
; payload. The checksum covers all 4096 bytes with bytes 16..19 treated
; as zero, binding magic, version, identity and sequence as well as payload.
; This is an append-only probe format, not layer B's log or a crypto hash.
;
(include-book "../books/assumptions-integrity")

(defcolumns fn2-recovery-image
  nil
  :rows-bound 4294967296
  :init-name fn2-recovery-columns-init
  :extra-fields
  ((fn2-recovery-bytes :type (array (unsigned-byte 8) (0))
                       :initially 0 :resizable t :why "Contiguous recovery bytes have no row identity or per-sector columns.")))

(defun fn2-recovery-init (sectors fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image
                  :guard (unsigned-byte-p 32 sectors)))
  (resize-fn2-recovery-bytes (* sectors *fn2-format-sector-bytes*) fn2-recovery-image))

(defthm fn2-recovery-init-type
  (implies (and (fn2-recovery-imagep fn2-recovery-image) (unsigned-byte-p 32 sectors))
           (fn2-recovery-imagep (fn2-recovery-init sectors fn2-recovery-image))))

; Native loader writes one octet at a time with this same bounded entry.
(defun fn2-recovery-put-byte (i byte fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (unsigned-byte-p 8 byte)))
  (if (and (natp i) (< i (fn2-recovery-bytes-length fn2-recovery-image)))
      (update-fn2-recovery-bytesi i byte fn2-recovery-image)
    fn2-recovery-image))
(defthm fn2-recovery-put-byte-type
  (implies (and (fn2-recovery-imagep fn2-recovery-image) (unsigned-byte-p 8 byte))
           (fn2-recovery-imagep (fn2-recovery-put-byte i byte fn2-recovery-image))))
(defthm fn2-recovery-put-byte-length
  (equal (fn2-recovery-bytes-length (fn2-recovery-put-byte i byte fn2-recovery-image))
         (fn2-recovery-bytes-length fn2-recovery-image)))
(in-theory (disable fn2-recovery-put-byte))

(defun fn2-recovery-byte (i fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image
                  :guard (and (natp i) (< i (fn2-recovery-bytes-length fn2-recovery-image)))))
  (if (and (natp i) (< i (fn2-recovery-bytes-length fn2-recovery-image)))
      (fn2-recovery-bytesi i fn2-recovery-image)
    (prog2$ (er hard? 'fn2-recovery-byte "Invalid recovery byte index ~x0" i) 0)))
(defthm fn2-recovery-byte-type
  (implies (fn2-recovery-imagep fn2-recovery-image)
           (unsigned-byte-p 8 (fn2-recovery-byte i fn2-recovery-image))))
(in-theory (disable fn2-recovery-byte fn2-recovery-bytes-length))
(fn2-word-facts fn2-recovery-byte (fn2-recovery-byte i fn2-recovery-image)
  fn2-recovery-byte-type (fn2-recovery-imagep fn2-recovery-image) 256)

; External byte probes carry refusal separately from the byte value.
(defun fn2-recovery-read-byte (i fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image))
  (if (and (natp i) (< i (fn2-recovery-bytes-length fn2-recovery-image)))
      (mv :ok (fn2-recovery-byte i fn2-recovery-image)) (mv :bounds 0)))

(defun fn2-recovery-u32 (i fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (and (natp i) (<= (+ i *fn2-format-word-bytes*) (fn2-recovery-bytes-length fn2-recovery-image)))))
  (+ (fn2-recovery-byte i fn2-recovery-image)
     (* 256 (fn2-recovery-byte (+ 1 i) fn2-recovery-image))
     (* 65536 (fn2-recovery-byte (+ 2 i) fn2-recovery-image))
     (* 16777216 (fn2-recovery-byte (+ 3 i) fn2-recovery-image))))
(defthm fn2-recovery-u32-type
  (implies (fn2-recovery-imagep fn2-recovery-image)
           (unsigned-byte-p 32 (fn2-recovery-u32 i fn2-recovery-image))))
(in-theory (disable fn2-recovery-u32))
(fn2-word-facts fn2-recovery-u32 (fn2-recovery-u32 i fn2-recovery-image)
  fn2-recovery-u32-type (fn2-recovery-imagep fn2-recovery-image) 4294967296)

(defun fn2-recovery-hash-loop (base j hash fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :measure (nfix (- *fn2-format-sector-bytes* (nfix j)))
                  :guard (and (natp base) (natp j) (<= (+ base *fn2-format-sector-bytes*) (fn2-recovery-bytes-length fn2-recovery-image)) (unsigned-byte-p 32 hash))))
  (if (or (not (natp j)) (>= j *fn2-format-sector-bytes*)) hash
    (fn2-recovery-hash-loop
     base (+ j 1)
     (fn2-fnv-step hash (if (and (<= *fn2-format-checksum-offset* j) (< j *fn2-format-payload-offset*)) 0
                                 (fn2-recovery-byte (+ base j) fn2-recovery-image)))
     fn2-recovery-image)))
(defthm fn2-recovery-hash-loop-type
  (implies (unsigned-byte-p 32 hash)
           (unsigned-byte-p 32 (fn2-recovery-hash-loop base j hash fn2-recovery-image)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p))))
(in-theory (disable fn2-recovery-hash-loop))

(defun fn2-recovery-checksum (sector fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (and (unsigned-byte-p 32 sector)
                              (<= (* *fn2-format-sector-bytes* (+ sector 1)) (fn2-recovery-bytes-length fn2-recovery-image)))))
  (fn2-recovery-hash-loop (* *fn2-format-sector-bytes* sector) 0 *fn2-fnv-offset-basis* fn2-recovery-image))
(defthm fn2-recovery-checksum-type
  (unsigned-byte-p 32 (fn2-recovery-checksum sector fn2-recovery-image))
  :hints (("Goal" :in-theory (disable unsigned-byte-p))))
(in-theory (disable fn2-recovery-checksum))
(fn2-word-facts fn2-recovery-checksum (fn2-recovery-checksum sector fn2-recovery-image) fn2-recovery-checksum-type)

(defun fn2-recovery-zero-loop (base j fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :measure (nfix (- *fn2-format-sector-bytes* (nfix j)))
                  :guard (and (natp base) (natp j) (<= (+ base *fn2-format-sector-bytes*) (fn2-recovery-bytes-length fn2-recovery-image)))))
  (if (or (not (natp j)) (>= j *fn2-format-sector-bytes*)) t
    (and (= 0 (fn2-recovery-byte (+ base j) fn2-recovery-image))
         (fn2-recovery-zero-loop base (+ j 1) fn2-recovery-image))))

(defun fn2-recovery-sector (sector fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (unsigned-byte-p 32 sector)))
  (let ((base (* sector *fn2-format-sector-bytes*)))
    (cond ((> (+ base *fn2-format-sector-bytes*) (fn2-recovery-bytes-length fn2-recovery-image)) :torn-corrupt)
          ((fn2-recovery-zero-loop base 0 fn2-recovery-image) :never-written)
          ((or (not (= (fn2-recovery-u32 base fn2-recovery-image) *fn2-format-magic*))
               (not (= (fn2-recovery-u32 (+ base *fn2-format-version-offset*) fn2-recovery-image) 1))) :torn-corrupt)
          ((not (= (fn2-recovery-u32 (+ base *fn2-format-address-offset*) fn2-recovery-image) sector)) :misdirected)
          ((or (not (= (fn2-recovery-u32 (+ base *fn2-format-sequence-offset*) fn2-recovery-image) (+ sector 1)))
               (not (= (fn2-recovery-u32 (+ base *fn2-format-checksum-offset*) fn2-recovery-image)
                       (fn2-recovery-checksum sector fn2-recovery-image)))) :torn-corrupt)
          (t :valid))))
(in-theory (disable fn2-recovery-sector))

; Recovery progress is scalar and disposable. The simulator may die after
; any step; no step mutates the image, so restart discards only these scalars.
(defun fn2-recover-start (ack-seq fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (unsigned-byte-p 32 ack-seq)))
  (let* ((len (fn2-recovery-bytes-length fn2-recovery-image)) (n (floor len *fn2-format-sector-bytes*)))
    (if (not (unsigned-byte-p 32 n)) (mv :bounds 0 t nil)
      (mv :ok n (not (= (mod len *fn2-format-sector-bytes*) 0)) (> ack-seq n)))))

(defthm fn2-recover-start-n-type
  (unsigned-byte-p 32 (mv-nth 1 (fn2-recover-start ack-seq fn2-recovery-image))))
(fn2-word-facts fn2-recover-start-n (mv-nth 1 (fn2-recover-start ack-seq fn2-recovery-image))
  fn2-recover-start-n-type)
(in-theory (disable fn2-recover-start))

; One sector, at most 4096 zero checks plus 4096 checksum-byte visits.
; n is the image sector count from start, fixed for this recovery attempt.
(defun fn2-recover-step (i n ack-seq bad-tail damaged valid never bad misplaced fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image
                  :guard (and (natp i) (unsigned-byte-p 32 n) (natp ack-seq)
                              (natp valid) (natp never) (natp bad) (natp misplaced))))
  (if (or (not (natp i)) (not (natp n)) (>= i n))
      (mv t i bad-tail damaged valid never bad misplaced)
    (let ((class (fn2-recovery-sector i fn2-recovery-image)))
      (mv nil (+ i 1)
          (or bad-tail (and (eq class :valid) (< 0 never))
              (and (not (eq class :valid)) (not (eq class :never-written))))
          (or damaged (and (< i ack-seq) (not (eq class :valid))))
          (+ valid (if (eq class :valid) 1 0))
          (+ never (if (eq class :never-written) 1 0))
          (+ bad (if (eq class :torn-corrupt) 1 0))
          (+ misplaced (if (eq class :misdirected) 1 0))))))

(defmacro fn2-recover-count-fact (name index)
  `(defthm ,name
     (implies (and (natp valid) (natp never) (natp bad) (natp misplaced))
              (natp (mv-nth ,index
                     (fn2-recover-step i n ack-seq bad-tail damaged valid never bad misplaced fn2-recovery-image))))
     :rule-classes :type-prescription))
(fn2-recover-count-fact fn2-recover-step-valid-type 4)
(fn2-recover-count-fact fn2-recover-step-never-type 5)
(fn2-recover-count-fact fn2-recover-step-bad-type 6)
(fn2-recover-count-fact fn2-recover-step-misplaced-type 7)
(defthm fn2-recover-step-next-type
  (implies (natp i)
           (natp (mv-nth 1 (fn2-recover-step i n ack-seq bad-tail damaged valid never bad misplaced fn2-recovery-image))))
  :rule-classes :type-prescription)
(defthm fn2-recover-step-next
  (implies (and (natp i) (natp n) (< i n))
           (equal (mv-nth 1 (fn2-recover-step i n ack-seq bad-tail damaged valid never bad misplaced fn2-recovery-image))
                  (+ i 1))))
(in-theory (disable fn2-recover-step))

; Scan everything using exactly the resumable step, never selecting a shorter
; candidate history. ack-seq is EXTERNAL acknowledged-prefix evidence.
(defun fn2-recover-scan (i n ack-seq bad-tail damaged valid never bad misplaced fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :measure (nfix (- (nfix n) (nfix i)))
                  :guard (and (natp i) (unsigned-byte-p 32 n) (natp ack-seq)
                              (natp valid) (natp never) (natp bad) (natp misplaced))))
  (if (or (not (natp i)) (not (natp n)) (>= i n))
      (mv bad-tail damaged valid never bad misplaced)
    (mv-let (done next bad-tail damaged valid never bad misplaced)
      (fn2-recover-step i n ack-seq bad-tail damaged valid never bad misplaced fn2-recovery-image)
      (declare (ignore done next))
      (fn2-recover-scan (+ i 1) n ack-seq bad-tail damaged valid never bad misplaced fn2-recovery-image))))
(in-theory (disable fn2-recover-scan))

(defun fn2-recover-classification (crash-only bad-tail damaged)
  (declare (xargs :guard t))
  (cond (damaged :damaged)
        (bad-tail (if crash-only :torn-tail :unknown))
        (t :intact)))

(defun fn2-recover-stub (ack-seq crash-only fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image
                  :guard (and (unsigned-byte-p 32 ack-seq) (booleanp crash-only))))
  (mv-let (code n bad-tail damaged) (fn2-recover-start ack-seq fn2-recovery-image)
    (if (not (eq code :ok)) (mv :unknown 0 0 0 0)
      (mv-let (bad-tail damaged valid never bad misplaced)
        (fn2-recover-scan 0 n ack-seq bad-tail damaged 0 0 0 0 fn2-recovery-image)
        (mv (fn2-recover-classification crash-only bad-tail damaged) valid never bad misplaced)))))

(defun fn2-recovery-put-u32 (i value fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image
                  :guard (and (natp i) (unsigned-byte-p 32 value))))
  (let* ((fn2-recovery-image (fn2-recovery-put-byte i (mod value 256) fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-byte (+ i 1) (mod (floor value 256) 256) fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-byte (+ i 2) (mod (floor value 65536) 256) fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-byte (+ i 3) (mod (floor value 16777216) 256) fn2-recovery-image)))
    fn2-recovery-image))

(defun fn2-recovery-stamp (sector fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image
                  :guard (and (unsigned-byte-p 32 sector) (< sector *fn2-none*)
                              (<= (* *fn2-format-sector-bytes* (+ sector 1)) (fn2-recovery-bytes-length fn2-recovery-image)))))
  (let* ((base (* sector *fn2-format-sector-bytes*))
         (fn2-recovery-image (fn2-recovery-put-u32 base *fn2-format-magic* fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base *fn2-format-version-offset*) 1 fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base *fn2-format-address-offset*) sector fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base *fn2-format-sequence-offset*) (+ 1 sector) fn2-recovery-image))
         (hash (fn2-recovery-checksum sector fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base *fn2-format-checksum-offset*) hash fn2-recovery-image)))
    fn2-recovery-image))

(assert-event (fn2-assert-compliant-p
  '(fn2-recover-start fn2-recover-step fn2-recover-stub fn2-recovery-sector
    fn2-recovery-stamp fn2-recovery-put-byte) (w state)))

(defun fn2-recovery-read-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-recovery-image
  (mv-let (ok fn2-recovery-image)
    (let ((fn2-recovery-image (fn2-recovery-init 1 fn2-recovery-image)))
      (mv-let (valid zero) (fn2-recovery-read-byte 0 fn2-recovery-image)
        (mv-let (invalid absent) (fn2-recovery-read-byte *fn2-format-sector-bytes* fn2-recovery-image)
          (declare (ignore absent))
          (mv (and (eq valid :ok) (= zero 0) (eq invalid :bounds)) fn2-recovery-image)))) ok)))
(assert-event (fn2-recovery-read-control))
