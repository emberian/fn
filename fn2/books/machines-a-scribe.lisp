; Scribe is the layer-A storage probe, not a persistence implementation.
; Each byte loop yields after sixteen bytes. Its only acknowledgement point
; is its own successful FenceResult; a failed write/fence result never retries I/O.
(in-package "ACL2")
(include-book "machines-a-access")
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
  (cond ((< index 4) (fn2-scribe-u32-byte 843990611 index))
        ((< index 8) (fn2-scribe-u32-byte 1 (- index 4)))
        ((< index 12) (fn2-scribe-u32-byte (nfix (- sequence 1)) (- index 8)))
        ((< index 16) (fn2-scribe-u32-byte sequence (- index 12)))
        ((< index 20) (fn2-scribe-u32-byte checksum (- index 16)))
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
  (if (or (zp left) (>= cursor 4096))
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
  (if (or (zp left) (>= cursor 4096)) (mv t cursor)
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
    (if (equal (fn2-machine-phase id fn2-core) *fn2-scribe-state-free*)
        (let ((fn2-core (fn2-scribe-put-core id
                          (phase *fn2-scribe-state-reserve*) (sequence 1) (cursor 0)
                          (checksum 2166136261) (completed 0) (verified 0)
                          (stopped 0) (event-ready 0))))
          (fn2-machine-set-wake-id id fn2-core))
      fn2-core)))
(defthm fn2-scribe-start-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-corep (fn2-scribe-start fn2-core))))
(defthm fn2-scribe-start-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-core-wfp (fn2-scribe-start fn2-core))))
(in-theory (disable fn2-scribe-start))

(defmachine-callback fn2-scribe-stop fn2-scribe (id budget) 4
  (let ((fn2-core (fn2-scribe-put-core id
                    (phase *fn2-scribe-state-stopped*) (stopped 1) (event-ready 0))))
    (fn2-machine-result 0 4 0 nil fn2-core)))


(defmachine-callback fn2-scribe-park fn2-scribe (id budget) 4
  (let ((fn2-core (fn2-machine-park id fn2-core)))
    (fn2-machine-result 0 8 0 nil fn2-core)))


(defmachine-callback fn2-scribe-refused fn2-scribe (code id budget) 4
  (if (eq code :exhausted)
      (fn2-call fn2-scribe-park id budget)
    (fn2-call fn2-scribe-stop id budget)))


(defun fn2-scribe-window-class (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (class) (fn2-pool-class-for 4096 fn2-pool) class))
(in-theory (disable fn2-scribe-window-class))

(defmachine-callback fn2-scribe-reserve fn2-scribe (id budget) 4
  (let ((owner-gen row-generation)
        (class (fn2-scribe-window-class fn2-core)))
    (if (null class)
        (let ((fn2-core (fn2-scribe-put-core id (phase *fn2-scribe-state-stopped*) (stopped 1))))
          (fn2-machine-result 0 20 0 nil fn2-core))
      (mv-let (code slot gen fn2-core)
        (fn2-core-reserve class *fn2-scribe-kind* id owner-gen fn2-core)
        (if (not (eq code :ok))
            (if (eq code :exhausted)
                (let ((fn2-core (fn2-machine-park-pool id class fn2-core)))
                  (fn2-machine-result 0 24 0 nil fn2-core))
              (mv-let (bytes steps descriptors runnable fn2-core)
                (fn2-call fn2-scribe-stop id budget)
                (declare (ignore bytes steps descriptors))
                (fn2-machine-result 0 24 0 runnable fn2-core)))
          (let ((fn2-core (fn2-scribe-put-core id
                            (pool-slot slot) (pool-gen gen) (cursor 0)
                            (checksum 2166136261) (phase *fn2-scribe-state-fill*))))
            (fn2-machine-result 0 24 0 t fn2-core)))))))


(defmachine-callback fn2-scribe-fill-run fn2-scribe (id budget) 4
  (fn2-machine-with-work 16 24 0
  (mv-let (code cursor hash fn2-core)
    (fn2-scribe-fill 16 row-cursor
      row-sequence
      row-checksum
      row-pool-slot
      row-pool-gen id
      row-generation fn2-core)
    (let ((fn2-core (fn2-scribe-put-core id
                      (cursor cursor) (checksum hash)
                      (phase (if (eq code :ok) (if (equal cursor 4096) *fn2-scribe-state-patch* *fn2-scribe-state-fill*) *fn2-scribe-state-stopped*))
                      (stopped (if (eq code :ok) 0 1)))))
      ; Conservative byte work includes an attempted access on refusal.
      (fn2-machine-result 16 24 0 (eq code :ok) fn2-core)))))


(defun fn2-scribe-patch-loop (left cursor hash slot gen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left)
                              (natp cursor) (natp hash))))
  (if (or (zp left) (>= cursor 4)) (mv :ok fn2-core)
    (mv-let (code fn2-core)
      (fn2-core-write slot gen (+ 16 cursor)
        (fn2-scribe-u32-byte hash cursor) *fn2-scribe-kind* id owner-gen fn2-core)
      (if (not (eq code :ok)) (mv code fn2-core)
        (fn2-scribe-patch-loop (- left 1) (+ cursor 1) hash slot gen id owner-gen fn2-core)))))
(fn2-core-preserves fn2-scribe-patch-loop (left cursor hash slot gen id owner-gen fn2-core) :position 1 :rows nil)

(defmachine-callback fn2-scribe-patch fn2-scribe (id budget) 4
  (fn2-machine-with-work 4 12 0
  (mv-let (code fn2-core)
    (fn2-scribe-patch-loop 4 0 row-checksum
      row-pool-slot
      row-pool-gen id
      row-generation fn2-core)
    (let ((fn2-core (fn2-scribe-put-core id
                      (phase (if (eq code :ok) *fn2-scribe-state-write* *fn2-scribe-state-stopped*))
                      (stopped (if (eq code :ok) 0 1)))))
      (fn2-machine-result 4 12 0 (eq code :ok) fn2-core)))))


(defmachine-callback fn2-scribe-write fn2-scribe (id budget) 4
  (fn2-machine-with-work 4096 12 1
  (if (not (and (natp budget) (< 0 budget))) (fn2-machine-yield id fn2-core)
    (mv-let (code opslot opgen fn2-core)
    (fn2-issue-write (* 4096 (nfix (- row-sequence 1)))
      row-pool-slot
      row-pool-gen 0 4096 0 *fn2-scribe-kind* id
      row-generation
      row-principal-slot fn2-core)
    (declare (ignore opslot opgen))
    (if (not (eq code :ok)) (fn2-call fn2-scribe-refused code id budget)
      (let ((fn2-core (fn2-scribe-put-core id
                        (phase *fn2-scribe-state-write-result*) (pending 1) (event-ready 0))))
        (fn2-machine-result 4096 12 1 nil fn2-core)))))))


(defmachine-callback fn2-scribe-fence fn2-scribe (id budget) 4
  (fn2-machine-with-work 0 12 1
  (if (not (and (natp budget) (< 0 budget))) (fn2-machine-yield id fn2-core)
    (mv-let (code opslot opgen fn2-core)
    (fn2-issue-fence *fn2-scribe-kind* id row-generation
      row-principal-slot fn2-core)
    (declare (ignore opslot opgen))
    (if (not (eq code :ok)) (fn2-call fn2-scribe-refused code id budget)
      (let ((fn2-core (fn2-scribe-put-core id
                        (phase *fn2-scribe-state-fence-result*) (pending 1) (event-ready 0))))
        (fn2-machine-result 0 12 1 nil fn2-core)))))))


(defmachine-callback fn2-scribe-reset fn2-scribe (id budget) 4
  (mv-let (code fn2-core)
    (fn2-core-reset row-pool-slot
      row-pool-gen *fn2-scribe-kind* id
      row-generation fn2-core)
    (let ((fn2-core (fn2-scribe-put-core id
                      (cursor 0) (phase (if (eq code :ok) *fn2-scribe-state-read* *fn2-scribe-state-stopped*))
                      (stopped (if (eq code :ok) 0 1)))))
      (fn2-machine-result 0 8 0 (eq code :ok) fn2-core))))


(defmachine-callback fn2-scribe-read fn2-scribe (id budget) 4
  (fn2-machine-with-work 4096 12 1
  (if (not (and (natp budget) (< 0 budget))) (fn2-machine-yield id fn2-core)
    (let ((cursor row-cursor))
    (if (>= cursor 4096) (fn2-call fn2-scribe-stop id budget)
      (mv-let (code opslot opgen fn2-core)
        (fn2-issue-read
          (+ (* 4096 (nfix (- row-sequence 1))) cursor)
          row-pool-slot
          row-pool-gen (- 4096 cursor) *fn2-scribe-kind* id
          row-generation
          row-principal-slot fn2-core)
        (declare (ignore opslot opgen))
        (if (not (eq code :ok)) (fn2-call fn2-scribe-refused code id budget)
          (let ((fn2-core (fn2-scribe-put-core id
                            (phase *fn2-scribe-state-read-result*) (pending 1) (event-ready 0))))
            (fn2-machine-result (- 4096 cursor) 12 1 nil fn2-core)))))))))


(defmachine-callback fn2-scribe-result fn2-scribe (id budget) 4
  (let* ((phase row-phase)
         (event row-event)
         (count row-count)
         (cursor row-cursor)
         (seq row-sequence))
    (cond
      ((equal row-event-ready 0)
       (fn2-machine-result 0 2 0 nil fn2-core))
      ((not (or (equal row-outcome *fn2-outcome-done*)
                 (and (equal phase *fn2-scribe-state-read-result*)
                      (equal row-outcome *fn2-outcome-short*))))
       (fn2-call fn2-scribe-stop id budget))
      ((and (equal phase *fn2-scribe-state-write-result*) (equal event *fn2-event-write-result*) (equal count 4096))
       (let ((fn2-core (fn2-scribe-put-core id (phase *fn2-scribe-state-fence*) (event-ready 0))))
         (fn2-machine-result 0 6 0 t fn2-core)))
      ((and (equal phase *fn2-scribe-state-fence-result*) (equal event *fn2-event-fence-result*))
       (let ((fn2-core (fn2-scribe-put-core id
                         (phase *fn2-scribe-state-reset*) (completed seq) (event-ready 0))))
         (fn2-machine-result 0 8 0 t fn2-core)))
      ((and (equal phase *fn2-scribe-state-read-result*) (equal event *fn2-event-read-result*)
             (< 0 count) (<= (+ cursor count) 4096))
       (let ((fn2-core (fn2-scribe-put-core id
                         (phase (if (equal (+ cursor count) 4096) *fn2-scribe-state-verify* *fn2-scribe-state-read*))
                         (cursor (if (equal (+ cursor count) 4096) 0 (+ cursor count)))
                         (event-ready 0))))
         (fn2-machine-result 0 8 0 t fn2-core)))
      (t (fn2-call fn2-scribe-stop id budget)))))


(defmachine-callback fn2-scribe-verify-run fn2-scribe (id budget) 4
  (fn2-machine-with-work 16 24 0
  (mv-let (ok cursor)
    (fn2-scribe-verify 16 row-cursor
      row-sequence
      row-checksum
      row-pool-slot
      row-pool-gen id
      row-generation fn2-core)
    (let ((fn2-core (fn2-scribe-put-core id
                      (cursor cursor) (phase (if ok (if (equal cursor 4096) *fn2-scribe-state-next* *fn2-scribe-state-verify*) *fn2-scribe-state-stopped*))
                      (stopped (if ok 0 1)))))
      (fn2-machine-result 16 24 0 ok fn2-core)))))


(defmachine-callback fn2-scribe-next fn2-scribe (id budget) 4
  (let ((seq row-sequence))
    (if (>= seq 4294967295) (fn2-call fn2-scribe-stop id budget)
      (mv-let (code fn2-core)
        (fn2-core-reset row-pool-slot
          row-pool-gen *fn2-scribe-kind* id
          row-generation fn2-core)
        (let ((fn2-core (fn2-scribe-put-core id
                          (verified seq) (sequence (+ 1 seq)) (cursor 0)
                          (checksum 2166136261) (phase (if (eq code :ok) *fn2-scribe-state-fill* *fn2-scribe-state-stopped*))
                          (stopped (if (eq code :ok) 0 1)))))
          (fn2-machine-result 0 12 0 (eq code :ok) fn2-core))))))


(defmachine-callback fn2-scribe-idle fn2-scribe (id budget) 4
  (fn2-machine-idle id fn2-core))

(defmachine-run fn2-scribe)


(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-scribe-start fn2-scribe-run fn2-scribe-byte fn2-fnv-step
    fn2-scribe-fill fn2-scribe-verify fn2-scribe-stop fn2-scribe-park
    fn2-scribe-refused fn2-scribe-window-class fn2-scribe-reserve
    fn2-scribe-fill-run fn2-scribe-patch-loop fn2-scribe-patch
    fn2-scribe-write fn2-scribe-fence fn2-scribe-reset fn2-scribe-read
    fn2-scribe-result fn2-scribe-verify-run fn2-scribe-next) (w state)))

))
