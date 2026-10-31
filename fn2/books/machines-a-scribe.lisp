; Scribe is the layer-A storage probe, not a persistence implementation.
; Each byte loop yields after sixteen bytes. Its only acknowledgement point
; is its own successful FenceResult; a failed write/fence result never retries I/O.
(in-package "ACL2")
(include-book "machines-a-costs")
(include-book "fnv")

(defmacro fn2-scribe-events ()
 '(progn
(defun fn2-scribe-u32-byte (word index)
  (declare (xargs :guard (and (natp word) (natp index))))
  (mod (floor word (case index (0 1) (1 256) (2 65536)
                        (otherwise 16777216))) 256))
(defthm fn2-scribe-u32-byte-type
  (unsigned-byte-p 8 (fn2-scribe-u32-byte word index)))
(defthm fn2-scribe-u32-byte-bound
  (< (fn2-scribe-u32-byte word index) 256)
  :rule-classes :linear)
(in-theory (disable fn2-scribe-u32-byte))

; Identical v1 wire format to the independent A3 recovery decoder: magic,
; version, sector address, sequence, checksum, then zero payload. Sequence
; zero is never written; exhaustion stops the probe without wrapping.
(defun fn2-scribe-byte (sequence checksum index)
  (declare (xargs :guard (and (natp sequence) (natp checksum) (natp index))))
  (cond ((< index *fn2-format-version-offset*) (fn2-scribe-u32-byte *fn2-format-magic* index))
        ((< index *fn2-format-address-offset*) (fn2-scribe-u32-byte 1 (- index *fn2-format-version-offset*)))
        ((< index *fn2-format-sequence-offset*) (fn2-scribe-u32-byte (nfix (- sequence 1)) (- index *fn2-format-address-offset*)))
        ((< index *fn2-format-checksum-offset*) (fn2-scribe-u32-byte sequence (- index *fn2-format-sequence-offset*)))
        ((< index *fn2-format-payload-offset*) (fn2-scribe-u32-byte checksum (- index *fn2-format-checksum-offset*)))
        (t 0)))
(defthm fn2-scribe-byte-type
  (unsigned-byte-p 8 (fn2-scribe-byte sequence checksum index)))
(defthm fn2-scribe-byte-bound
  (< (fn2-scribe-byte sequence checksum index) 256)
  :rule-classes :linear)
(in-theory (disable fn2-scribe-byte))

(defun fn2-scribe-fill (left cursor sequence hash slot gen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp cursor)
                              (natp sequence) (unsigned-byte-p 32 hash))))
  (if (or (zp left) (>= cursor *fn2-format-sector-bytes*))
      (mv :ok cursor hash fn2-core)
    (let ((byte (fn2-scribe-byte sequence 0 cursor)))
      (mv-let (code fn2-core)
        (fn2-core-write slot gen cursor byte *fn2-scribe-kind* id owner-gen fn2-core)
        (if (not (eq code :ok)) (mv code cursor hash fn2-core)
          (fn2-scribe-fill (- left 1) (+ cursor 1) sequence
                           (fn2-fnv-step hash byte) slot gen id owner-gen fn2-core))))))
(fn2-core-preserves fn2-scribe-fill (left cursor sequence hash slot gen id owner-gen fn2-core) :position 3 :rows nil)

(defun fn2-scribe-verify (left cursor sequence checksum slot gen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp cursor)
                              (natp sequence) (natp checksum))))
  (if (or (zp left) (>= cursor *fn2-format-sector-bytes*)) (mv t cursor)
    (mv-let (code byte) (fn2-core-read slot gen cursor *fn2-scribe-kind* id owner-gen fn2-core)
      (if (or (not (eq code :ok))
              (not (equal byte (fn2-scribe-byte sequence checksum cursor))))
          (mv nil cursor)
        (fn2-scribe-verify (- left 1) (+ cursor 1) sequence checksum
                           slot gen id owner-gen fn2-core)))))
(in-theory (disable fn2-scribe-verify))

(defun fn2-scribe-start (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((id (fn2-machine-scribe-id fn2-core)))
    ; Starting an already active or stopped probe must never erase a lease
    ; or permit a write/fence retry. Only init makes the row inactive again.
    (if (not (eq (fn2-scribe-snapshot-read-code id fn2-core) :ok))
        (fn2-core-stop *fn2-stop-reason-machine-phase* fn2-core)
      (if (equal (fn2-machine-phase id fn2-core) *fn2-scribe-state-free*)
        (let ((fn2-core (fn2-scribe-put-core id
                          (phase *fn2-scribe-state-reserve*) (sequence 1) (cursor 0)
                          (checksum *fn2-fnv-offset-basis*) (completed 0) (verified 0)
                          (stopped 0) (event-ready 0))))
          (fn2-machine-set-wake-id id fn2-core))
      fn2-core))))
(defthm fn2-scribe-start-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-corep (fn2-scribe-start fn2-core))))
(defthm fn2-scribe-start-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-core-wfp (fn2-scribe-start fn2-core))))
(in-theory (disable fn2-scribe-start))

(defun fn2-scribe-window-class (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (class) (fn2-pool-class-for *fn2-format-sector-bytes* fn2-pool) class))
(in-theory (disable fn2-scribe-window-class))

(defun fn2-scribe-patch-loop (left cursor hash slot gen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left)
                              (natp cursor) (natp hash))))
  (if (or (zp left) (>= cursor 4)) (mv :ok fn2-core)
    (mv-let (code fn2-core)
      (fn2-core-write slot gen (+ *fn2-format-checksum-offset* cursor)
        (fn2-scribe-u32-byte hash cursor) *fn2-scribe-kind* id owner-gen fn2-core)
      (if (not (eq code :ok)) (mv code fn2-core)
        (fn2-scribe-patch-loop (- left 1) (+ cursor 1) hash slot gen id owner-gen fn2-core)))))
(fn2-core-preserves fn2-scribe-patch-loop (left cursor hash slot gen id owner-gen fn2-core) :position 1 :rows nil)



(defmachine-arms fn2-scribe)
(defmachine-run fn2-scribe)

(assert-event
 (fn2-assert-compliant-p
  '(fn2-scribe-start fn2-scribe-run fn2-scribe-byte fn2-fnv-step
    fn2-scribe-fill fn2-scribe-verify fn2-scribe-window-class fn2-scribe-patch-loop
    fn2-scribe-sub-stop fn2-scribe-sub-result fn2-scribe-run-reserve fn2-scribe-run-fill
    fn2-scribe-run-patch fn2-scribe-run-write fn2-scribe-run-fence fn2-scribe-run-reset
    fn2-scribe-run-read fn2-scribe-run-verify fn2-scribe-run-next fn2-scribe-on-write-result) (w state)))

))
