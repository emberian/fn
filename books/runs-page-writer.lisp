; Open a run page, check available space, and write its restart offsets.
(in-package "ACL2")
(include-book "runs-page-format")
(include-book "pool-ranges")
(fn2-book-layer :c)

(defun fn2-run-writerp (w fn2-run-writers fn2-run-restarts fn2-fields)
 (declare (xargs :stobjs (fn2-run-writers fn2-run-restarts fn2-fields) :guard t))
 (and (fn2-run-writers-wfp fn2-run-writers) (fn2-run-restarts-wfp fn2-run-restarts)
      (fn2-fields-wfp fn2-fields)
      (natp w) (< w (fn2-run-writers-rows fn2-run-writers))
      (<= (* (+ 1 w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows fn2-run-restarts))
      (<= (+ (fn2-run-writers-fields w fn2-run-writers) *fn2-run-writer-fields*)
          (fn2-fields-rows fn2-fields))))

; Zero bytes [pos, end) of the writer's page, at most BUDGET of them. The
; pool's append discipline (write at or below fill) holds because the page
; is filled in order from zero.
(defun fn2-run-zero (n slot gen pos okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix n)
  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp pos))))
 (if (zp n) (mv :ok fn2-pool)
  (mv-let (code fn2-pool) (fn2-pool-write slot gen pos 0 okind oslot ogen fn2-pool)
   (if (eq code :ok) (fn2-run-zero (- n 1) slot gen (+ 1 pos) okind oslot ogen fn2-pool)
    (mv code fn2-pool)))))
(fn2-pool-preserves fn2-run-zero (n slot gen pos okind oslot ogen fn2-pool) :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-rows))))

; Open a page in a fresh C-owned workspace: reset it, zero the header area and
; the reserved C header region. Entries start at *fn2-run-entries-base*.
(defun fn2-run-open (w slot gen schema version level run ordinal page-kind
                       unit epoch counter history incarnation okind oslot ogen fields limit
                       fn2-run-writers fn2-pool)
 (declare (xargs :stobjs (fn2-run-writers fn2-pool)
  :guard (and (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))
              (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 60 schema)
                    (unsigned-byte-p 8 version) (unsigned-byte-p 8 level) (unsigned-byte-p 60 run)
                    (unsigned-byte-p 60 ordinal) (unsigned-byte-p 8 page-kind)
                    (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 counter)
                    (unsigned-byte-p 60 history) (unsigned-byte-p 60 incarnation)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                    (unsigned-byte-p 32 fields) (unsigned-byte-p 32 limit)
                    (<= (+ *fn2-run-entries-base* *fn2-run-min-fill*) limit) (<= limit *fn2-run-page-size*)))
       (mv :bounds fn2-run-writers fn2-pool))
      ((unless (equal (fn2-run-writers-phase w fn2-run-writers) *fn2-run-writer-phase-idle*))
       (mv :state fn2-run-writers fn2-pool))
      ((unless (and (< slot (fn2-pool-rows fn2-pool))
                    (let ((cap (fn2-pool-slot-cap slot fn2-pool)))
                      (and (natp cap) (<= *fn2-run-page-size* cap)))))
       (mv :capacity fn2-run-writers fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset slot gen okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-run-writers fn2-pool))
      ((mv code fn2-pool) (fn2-run-zero *fn2-run-entries-base* slot gen 0 okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-run-writers fn2-pool))
      (fn2-run-writers (fn2-run-writers-put w
        (phase *fn2-run-writer-phase-open*) (schema schema) (schema-version version) (level level)
        (run run) (ordinal ordinal) (page-kind page-kind) (slot slot) (gen gen)
        (cursor *fn2-run-entries-base*) (entries 0) (restarts 0) (pos 0) (prev 0) (fields fields) (limit limit)
        (unit unit) (epoch epoch) (counter counter) (history history) (incarnation incarnation)
        (okind okind) (oslot oslot) (ogen ogen))))
  (mv :ok fn2-run-writers fn2-pool)))

; One restart is recorded when entry number ENTRIES starts an interval. The
; buffer row is w * capacity + j; the writer owns that range.
(defun fn2-run-note-restart (w fn2-run-writers fn2-run-restarts)
 (declare (xargs :stobjs (fn2-run-writers fn2-run-restarts)
  :guard (and (fn2-run-writers-wfp fn2-run-writers) (fn2-run-restarts-wfp fn2-run-restarts)
              (natp w) (< w (fn2-run-writers-rows fn2-run-writers))
              (<= (* (+ 1 w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows fn2-run-restarts)))))
 (b* ((entries (fn2-run-writers-entries w fn2-run-writers))
      ((unless (equal (mod entries *fn2-run-restart-interval*) 0))
       (mv :ok fn2-run-writers fn2-run-restarts))
      (j (fn2-run-writers-restarts w fn2-run-writers))
      ((unless (< j *fn2-run-restart-capacity*)) (mv :capacity fn2-run-writers fn2-run-restarts))
      (row (+ (* w *fn2-run-restart-capacity*) j))
      ((unless (< row (fn2-run-restarts-rows fn2-run-restarts))) (mv :bounds fn2-run-writers fn2-run-restarts))
      (fn2-run-restarts (fn2-run-restarts-set-offset row
                          (fn2-run-writers-cursor w fn2-run-writers) fn2-run-restarts))
      (fn2-run-writers (fn2-run-writers-set-restarts w (+ 1 j) fn2-run-writers)))
  (mv :ok fn2-run-writers fn2-run-restarts)))

; Room for an entry of SIZE bytes, counting the restart it may add.
; Exact occupied end after this entry and its possible restart. This is the
; served packing decision, also exposed for bounded layout observation. It
; predicts no page identity, ordering, encoding success or physical completion.
(defun fn2-run-pack-bound (size cursor entries restarts limit)
 (declare (xargs :guard (and (natp size) (natp cursor) (natp entries) (natp restarts) (natp limit))))
 (let* ((next-restarts (+ restarts (if (equal (mod entries *fn2-run-restart-interval*) 0) 1 0)))
        (end (+ cursor size (* *fn2-run-restart-bytes* next-restarts))))
  (mv (<= end (min limit *fn2-run-page-size*)) end next-restarts)))

(defun fn2-run-roomp (w size fn2-run-writers)
 (declare (xargs :stobjs fn2-run-writers
  :guard (and (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))
              (natp size))))
 (mv-let (fits end restarts)
  (fn2-run-pack-bound size (fn2-run-writers-cursor w fn2-run-writers)
   (fn2-run-writers-entries w fn2-run-writers) (fn2-run-writers-restarts w fn2-run-writers)
   (fn2-run-writers-limit w fn2-run-writers))
  (declare (ignore end restarts)) fits))

; The old room predicate is unchanged, including its logical totalization.
(defthm fn2-run-roomp-by-definition
 (equal (fn2-run-roomp w size fn2-run-writers)
  (let* ((entries (fn2-run-writers-entries w fn2-run-writers))
         (restarts (+ (fn2-run-writers-restarts w fn2-run-writers)
                      (if (equal (mod entries *fn2-run-restart-interval*) 0) 1 0))))
   (<= (+ (fn2-run-writers-cursor w fn2-run-writers) size (* *fn2-run-restart-bytes* restarts))
       (min (fn2-run-writers-limit w fn2-run-writers) *fn2-run-page-size*))))
 :hints (("Goal" :in-theory (enable fn2-run-roomp fn2-run-pack-bound))))

; Restarts J .. J+K-1 of writer W, encoded at CURSOR + 4j through the
; generated restart codec (one scratch field row).
(defun fn2-run-write-restarts (k j w cursor scratch slot gen okind oslot ogen fn2-run-restarts fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-run-restarts fn2-fields fn2-pool) :measure (nfix k)
  :guard (and (fn2-run-restarts-wfp fn2-run-restarts) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp k) (natp j) (natp w) (natp cursor) (natp scratch) (< scratch (fn2-fields-rows fn2-fields)))))
 (if (zp k) (mv :ok fn2-fields fn2-pool)
  (b* ((row (+ (* w *fn2-run-restart-capacity*) j))
       ((unless (and (< j *fn2-run-restart-capacity*) (< row (fn2-run-restarts-rows fn2-run-restarts))))
        (mv :bounds fn2-fields fn2-pool))
       (off (fn2-run-restarts-offset row fn2-run-restarts))
       ((unless (unsigned-byte-p 32 off)) (mv :bounds fn2-fields fn2-pool))
       (fn2-fields (fn2-fields-set-value scratch off fn2-fields))
       ((mv code & fn2-pool) (fn2-run-restart-encode scratch slot gen (+ cursor (* *fn2-run-restart-bytes* j))
                                                    okind oslot ogen fn2-fields fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-pool)))
   (fn2-run-write-restarts (- k 1) (+ 1 j) w cursor scratch slot gen okind oslot ogen fn2-run-restarts fn2-fields fn2-pool))))
(fn2-fields-preserves fn2-run-write-restarts (k j w cursor scratch slot gen okind oslot ogen fn2-run-restarts fn2-fields fn2-pool)
 :position 1 :disable nil :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (natp scratch) (< scratch (fn2-fields-rows fn2-fields)))
 :hints (("Goal" :in-theory (disable fn2-fields-rows))))
(fn2-pool-preserves fn2-run-write-restarts (k j w cursor scratch slot gen okind oslot ogen fn2-run-restarts fn2-fields fn2-pool)
 :position 2 :prefix "-POOL-PRESERVES"
 :hints (("Goal" :in-theory (disable fn2-pool-rows))))
(fn2-run-writers-preserves fn2-run-open (w slot gen schema version level run ordinal page-kind unit epoch counter history incarnation okind oslot ogen fields limit fn2-run-writers fn2-pool) :position 1 :raw-rows t :disable nil
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
(fn2-pool-preserves fn2-run-open (w slot gen schema version level run ordinal page-kind unit epoch counter history incarnation okind oslot ogen fields limit fn2-run-writers fn2-pool) :position 2 :prefix "-POOL-PRESERVES"
 :hints (("Goal" :in-theory (disable fn2-pool-rows))))
(fn2-run-writers-preserves fn2-run-note-restart (w fn2-run-writers fn2-run-restarts) :position 1 :raw-rows t :disable nil
 :hyps ((fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))))
(fn2-run-restarts-preserves fn2-run-note-restart (w fn2-run-writers fn2-run-restarts) :position 2 :prefix "-RESTARTS-PRESERVES" :raw-rows t
 :hyps ((fn2-run-restartsp fn2-run-restarts) (fn2-run-restarts-wfp fn2-run-restarts) (fn2-run-writersp fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers) (natp w) (< w (fn2-run-writers-rows fn2-run-writers))
        (<= (* (+ 1 w) *fn2-run-restart-capacity*) (fn2-run-restarts-rows fn2-run-restarts))))
