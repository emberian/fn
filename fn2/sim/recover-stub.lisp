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
  ((tag :u8))
  :rows-bound 4294967296
  :init-name fn2-recovery-columns-init
  :extra-fields
  ((fn2-recovery-bytes :type (array (unsigned-byte 8) (0))
                       :initially 0 :resizable t :why "Byte image contains 4096 bytes per sector row.")))

(defun fn2-recovery-init (sectors fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image
                  :guard (unsigned-byte-p 32 sectors)))
  (let* ((fn2-recovery-image (fn2-recovery-columns-init sectors fn2-recovery-image))
         (fn2-recovery-image
          (resize-fn2-recovery-bytes (* sectors 4096) fn2-recovery-image)))
    fn2-recovery-image))

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
  (declare (xargs :stobjs fn2-recovery-image))
  (if (and (natp i) (< i (fn2-recovery-bytes-length fn2-recovery-image)))
      (fn2-recovery-bytesi i fn2-recovery-image)
    0))
(defthm fn2-recovery-byte-type
  (implies (fn2-recovery-imagep fn2-recovery-image)
           (unsigned-byte-p 8 (fn2-recovery-byte i fn2-recovery-image)))
  )
(in-theory (disable fn2-recovery-byte))
(fn2-word-facts fn2-recovery-byte (fn2-recovery-byte i fn2-recovery-image)
  fn2-recovery-byte-type (fn2-recovery-imagep fn2-recovery-image) 256)

(defun fn2-recovery-u32 (i fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (natp i)))
  (+ (fn2-recovery-byte i fn2-recovery-image)
     (* 256 (fn2-recovery-byte (+ 1 i) fn2-recovery-image))
     (* 65536 (fn2-recovery-byte (+ 2 i) fn2-recovery-image))
     (* 16777216 (fn2-recovery-byte (+ 3 i) fn2-recovery-image))))
(defthm fn2-recovery-u32-type
  (implies (fn2-recovery-imagep fn2-recovery-image)
           (unsigned-byte-p 32 (fn2-recovery-u32 i fn2-recovery-image)))
  )
(in-theory (disable fn2-recovery-u32))
(fn2-word-facts fn2-recovery-u32 (fn2-recovery-u32 i fn2-recovery-image)
  fn2-recovery-u32-type (fn2-recovery-imagep fn2-recovery-image) 4294967296)

(defun fn2-recovery-hash-loop (base j hash fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :measure (nfix (- 4096 (nfix j)))
                  :guard (and (natp base) (natp j) (unsigned-byte-p 32 hash))))
  (if (or (not (natp j)) (>= j 4096)) hash
    (fn2-recovery-hash-loop
     base (+ j 1)
     (fn2-fnv-step hash (if (and (<= 16 j) (< j 20)) 0
                                 (fn2-recovery-byte (+ base j) fn2-recovery-image)))
     fn2-recovery-image)))
(defthm fn2-recovery-hash-loop-type
  (implies (unsigned-byte-p 32 hash)
           (unsigned-byte-p 32 (fn2-recovery-hash-loop base j hash fn2-recovery-image)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p))))
(in-theory (disable fn2-recovery-hash-loop))

(defun fn2-recovery-checksum (sector fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (unsigned-byte-p 32 sector)))
  (fn2-recovery-hash-loop (* 4096 sector) 0 2166136261 fn2-recovery-image))
(defthm fn2-recovery-checksum-type
  (unsigned-byte-p 32 (fn2-recovery-checksum sector fn2-recovery-image))
  :hints (("Goal" :in-theory (disable unsigned-byte-p))))
(in-theory (disable fn2-recovery-checksum))
(fn2-word-facts fn2-recovery-checksum (fn2-recovery-checksum sector fn2-recovery-image) fn2-recovery-checksum-type)

(defun fn2-recovery-zero-loop (base j fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :measure (nfix (- 4096 (nfix j)))
                  :guard (and (natp base) (natp j))))
  (if (or (not (natp j)) (>= j 4096)) t
    (and (= 0 (fn2-recovery-byte (+ base j) fn2-recovery-image))
         (fn2-recovery-zero-loop base (+ j 1) fn2-recovery-image))))

(defun fn2-recovery-sector (sector fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (unsigned-byte-p 32 sector)))
  (let ((base (* sector 4096)))
    (cond ((> (+ base 4096) (fn2-recovery-bytes-length fn2-recovery-image)) :torn-corrupt)
          ((fn2-recovery-zero-loop base 0 fn2-recovery-image) :never-written)
          ((or (not (= (fn2-recovery-u32 base fn2-recovery-image) 843990611))
               (not (= (fn2-recovery-u32 (+ base 4) fn2-recovery-image) 1))) :torn-corrupt)
          ((not (= (fn2-recovery-u32 (+ base 8) fn2-recovery-image) sector)) :misdirected)
          ((or (not (= (fn2-recovery-u32 (+ base 12) fn2-recovery-image) (+ sector 1)))
               (not (= (fn2-recovery-u32 (+ base 16) fn2-recovery-image)
                       (fn2-recovery-checksum sector fn2-recovery-image)))) :torn-corrupt)
          (t :valid))))
(in-theory (disable fn2-recovery-sector))

; Recovery progress is scalar and disposable. The simulator may die after
; any step; no step mutates the image, so restart discards only these scalars.
(defun fn2-recover-start (ack-seq fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :guard (unsigned-byte-p 32 ack-seq)))
  (let* ((len (fn2-recovery-bytes-length fn2-recovery-image)) (n (floor len 4096)))
    (if (not (unsigned-byte-p 32 n)) (mv :bounds 0 t nil)
      (mv :ok n (not (= (mod len 4096) 0)) (> ack-seq n)))))

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
                  :guard (and (unsigned-byte-p 32 sector) (< sector 4294967295))))
  (let* ((base (* sector 4096))
         (fn2-recovery-image (fn2-recovery-put-u32 base 843990611 fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base 4) 1 fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base 8) sector fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base 12) (+ 1 sector) fn2-recovery-image))
         (hash (fn2-recovery-checksum sector fn2-recovery-image))
         (fn2-recovery-image (fn2-recovery-put-u32 (+ base 16) hash fn2-recovery-image)))
    fn2-recovery-image))

(assert-event (fn2-profile-exports-compliant-p
  '(fn2-recover-start fn2-recover-step fn2-recover-stub fn2-recovery-sector
    fn2-recovery-stamp fn2-recovery-put-byte) (w state)))
