; Layer C: the active overlay, one bounded in-memory sorted run per schema.
; Entries are encoded by the schema's entry codec into one C-owned pool
; workspace (the arena), in arrival order; a resident index of their arena
; offsets is kept in key order. An overlay is :active while it takes inserts,
; :frozen while its run is being sealed (still readable), then :free. A
; batch's private successor (C-S2) is :private, taking that batch's facts and
; invisible to every reader until the batch's publication freezes it; a
; :spare overlay holds an arena for the next batch that needs one. The
; overlay's SEQ is the order it was taken in (C-S3: an engine counter, set
; when a spare becomes a batch's), so it follows batch order: of two overlays
; holding a key, the one with the greater SEQ holds its newest row. The
; operations that decode, encode or compare entries are generated at the run
; assembly (runs-assemble.lisp); this book holds the tables and the parts that
; touch only them.
(in-package "ACL2")
(include-book "runs")
(fn2-book-layer :c)

(defcolumns fn2-overlays
 ((phase (:enum fn2-overlay-phase (:free :active :frozen :private :spare)))
  (schema :u60) (slot :u32) (gen :u60) (fill :u32) (cap :u32)
  (count :u32) (ibase :u32) (icap :u32) (okind :u8) (oslot :u32) (ogen :u60) (cov :u60) (batch :u60) (seq :u60)))
(defcolumns fn2-overlay-index ((off :u32)))

; An overlay row whose index range lies inside the index table.
(defun fn2-ov-okp (o fn2-overlays fn2-overlay-index)
 (declare (xargs :stobjs (fn2-overlays fn2-overlay-index) :guard t))
 (and (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
      (natp o) (< o (fn2-overlays-rows fn2-overlays))
      (<= (+ (fn2-overlays-ibase o fn2-overlays) (fn2-overlays-icap o fn2-overlays))
          (fn2-overlay-index-rows fn2-overlay-index))
      (<= (fn2-overlays-count o fn2-overlays) (fn2-overlays-icap o fn2-overlays))))

; Start an overlay of SCHEMA in a fresh C-owned workspace SLOT/GEN (reset
; here; its capacity is the arena's) with index rows IBASE .. IBASE+ICAP-1.
; COV is the schema's coverage: the commit position through which its
; overlays and runs reflect every commit (the read contract's cov).
(defun fn2-ov-start (o schema slot gen ibase icap okind oslot ogen cov fn2-overlays fn2-overlay-index fn2-pool)
 (declare (xargs :stobjs (fn2-overlays fn2-overlay-index fn2-pool)
  :guard (and (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp o) (< o (fn2-overlays-rows fn2-overlays))
                    (unsigned-byte-p 60 schema) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                    (unsigned-byte-p 32 ibase) (unsigned-byte-p 32 icap)
                    (<= (+ ibase icap) (fn2-overlay-index-rows fn2-overlay-index))
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                    (unsigned-byte-p 60 cov) (< slot (fn2-pool-rows fn2-pool))))
       (mv :bounds fn2-overlays fn2-pool))
      ((unless (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-free*))
       (mv :state fn2-overlays fn2-pool))
      (cap (fn2-pool-slot-cap slot fn2-pool))
      ((unless (unsigned-byte-p 32 cap)) (mv :capacity fn2-overlays fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset slot gen okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-pool))
      (fn2-overlays (fn2-overlays-put o (phase *fn2-overlay-phase-active*) (schema schema) (slot slot) (gen gen)
                      (fill 0) (cap cap) (count 0) (ibase ibase) (icap icap)
                      (okind okind) (oslot oslot) (ogen ogen) (cov cov) (batch 0) (seq 0))))
  (mv :ok fn2-overlays fn2-pool)))

; Advance active overlay O's coverage to P (the commit install that fed it
; reached P). Coverage never moves back.
(defun fn2-ov-cover (o p fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :guard (fn2-overlays-wfp fn2-overlays)))
 (cond ((not (and (natp o) (< o (fn2-overlays-rows fn2-overlays)) (unsigned-byte-p 60 p))) (mv :bounds fn2-overlays))
       ((not (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-active*)) (mv :state fn2-overlays))
       ((< p (fn2-overlays-cov o fn2-overlays)) (mv :regress fn2-overlays))
       (t (let ((fn2-overlays (fn2-overlays-set-cov o p fn2-overlays))) (mv :ok fn2-overlays)))))
; :active -> :frozen (its run is being sealed); :frozen -> :free (the run is
; installed; the caller releases the arena).
(defun fn2-ov-advance (o from to fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :guard (fn2-overlays-wfp fn2-overlays)))
 (cond ((not (and (natp o) (< o (fn2-overlays-rows fn2-overlays)))) (mv :bounds fn2-overlays))
       ((not (equal (fn2-overlays-phase o fn2-overlays) from)) (mv :state fn2-overlays))
       ((not (and (natp to) (< to *fn2-overlay-phase-count*))) (mv :bounds fn2-overlays))
       (t (let ((fn2-overlays (fn2-overlays-set-phase o to fn2-overlays))) (mv :ok fn2-overlays)))))
(defun fn2-ov-freeze (o fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :guard (fn2-overlays-wfp fn2-overlays)))
 (fn2-ov-advance o *fn2-overlay-phase-active* *fn2-overlay-phase-frozen* fn2-overlays))
(defun fn2-ov-retire (o fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :guard (fn2-overlays-wfp fn2-overlays)))
 (fn2-ov-advance o *fn2-overlay-phase-frozen* *fn2-overlay-phase-free* fn2-overlays))

; Insert OFF at index row AT, moving rows AT .. AT+N-1 up one, top first.
(defun fn2-ov-insert-at (n at off fn2-overlay-index)
 (declare (xargs :stobjs fn2-overlay-index :measure (nfix n)
  :guard (and (fn2-overlay-index-wfp fn2-overlay-index) (natp n) (natp at))))
 (cond ((not (and (natp at) (< (+ at (nfix n)) (fn2-overlay-index-rows fn2-overlay-index)) (unsigned-byte-p 32 off)))
        (mv :bounds fn2-overlay-index))
       ((zp n) (let ((fn2-overlay-index (fn2-overlay-index-set-off at off fn2-overlay-index))) (mv :ok fn2-overlay-index)))
       (t (let* ((j (+ at n -1))
                 (fn2-overlay-index (fn2-overlay-index-set-off (+ j 1) (fn2-overlay-index-off j fn2-overlay-index) fn2-overlay-index)))
           (fn2-ov-insert-at (- n 1) at off fn2-overlay-index)))))
(fn2-overlay-index-preserves fn2-ov-insert-at (n at off fn2-overlay-index) :position 1 :raw-rows t)

; Record an entry encoded at arena offset OFF, ending at END, at sorted
; position POS: open the gap, write the offset, count it.
(defun fn2-ov-place (o pos off end fn2-overlays fn2-overlay-index)
 (declare (xargs :stobjs (fn2-overlays fn2-overlay-index) :guard t))
 (b* (((unless (fn2-ov-okp o fn2-overlays fn2-overlay-index)) (mv :bounds fn2-overlays fn2-overlay-index))
      (count (fn2-overlays-count o fn2-overlays)) (ibase (fn2-overlays-ibase o fn2-overlays))
      ((unless (and (natp pos) (<= pos count) (< count (fn2-overlays-icap o fn2-overlays))
                    (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)))
       (mv :bounds fn2-overlays fn2-overlay-index))
      ((mv code fn2-overlay-index) (fn2-ov-insert-at (- count pos) (+ ibase pos) off fn2-overlay-index))
      ((unless (eq code :ok)) (mv code fn2-overlays fn2-overlay-index))
      (fn2-overlays (fn2-overlays-put o (count (+ 1 count)) (fill end))))
  (mv :ok fn2-overlays fn2-overlay-index)))
(fn2-overlays-preserves fn2-ov-place (o pos off end fn2-overlays fn2-overlay-index) :position 1 :raw-rows t :disable nil)
(fn2-overlay-index-preserves fn2-ov-place (o pos off end fn2-overlays fn2-overlay-index) :position 2 :prefix "-INDEX-PRESERVES" :raw-rows t)
(in-theory (disable fn2-ov-place))

; Point sorted position POS at an entry encoded at arena offset OFF, ending
; at END, in place of the equal-keyed entry there (a :latest schema,
; C-RANGE-NEWEST): the count stays; the replaced bytes stay in the arena
; until the overlay is sealed, so its capacity bounds the replacements too.
(defun fn2-ov-reput (o pos off end fn2-overlays fn2-overlay-index)
 (declare (xargs :stobjs (fn2-overlays fn2-overlay-index) :guard t))
 (b* (((unless (fn2-ov-okp o fn2-overlays fn2-overlay-index)) (mv :bounds fn2-overlays fn2-overlay-index))
      (ibase (fn2-overlays-ibase o fn2-overlays))
      ((unless (and (natp pos) (natp ibase) (< pos (fn2-overlays-count o fn2-overlays)) (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
                    (< (+ ibase pos) (fn2-overlay-index-rows fn2-overlay-index))))
       (mv :bounds fn2-overlays fn2-overlay-index))
      (fn2-overlay-index (fn2-overlay-index-set-off (+ ibase pos) off fn2-overlay-index))
      (fn2-overlays (fn2-overlays-set-fill o end fn2-overlays)))
  (mv :ok fn2-overlays fn2-overlay-index)))
(fn2-overlays-preserves fn2-ov-reput (o pos off end fn2-overlays fn2-overlay-index) :position 1 :raw-rows t :disable nil)
(fn2-overlay-index-preserves fn2-ov-reput (o pos off end fn2-overlays fn2-overlay-index) :position 2 :prefix "-INDEX-PRESERVES" :raw-rows t)
(in-theory (disable fn2-ov-reput))

; Specification (logic only): the overlay reads back its entries sorted by
; key; inserts of distinct keys all succeed.
(defun fn2-ov-sort-insert-spec (key e sorted)
 (declare (xargs :verify-guards nil))
 (cond ((atom sorted) (list e))
       ((eq (fn2-run-key-order-spec key (car sorted) e) :lt) (cons (car sorted) (fn2-ov-sort-insert-spec key e (cdr sorted))))
       (t (cons e sorted))))
(defun fn2-ov-sort-spec (key entries)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil (fn2-ov-sort-insert-spec key (car entries) (fn2-ov-sort-spec key (cdr entries)))))
(defun fn2-ov-key-absent-spec (key e entries)
 (declare (xargs :verify-guards nil))
 (or (atom entries)
     (and (not (eq (fn2-run-key-order-spec key e (car entries)) :eq))
          (fn2-ov-key-absent-spec key e (cdr entries)))))
(defun fn2-ov-distinct-spec (key entries)
 (declare (xargs :verify-guards nil))
 (or (atom entries)
     (and (fn2-ov-key-absent-spec key (car entries) (cdr entries)) (fn2-ov-distinct-spec key (cdr entries)))))
; At most 64 well-formed entries with distinct keys (the adapter's arena is
; one 64 KiB workspace).
(defun fn2-ov-inputp (layout key entries)
 (declare (xargs :verify-guards nil))
 (and (fn2-layoutp layout) (<= (len entries) 64) (fn2-run-entries-layoutp layout entries)
      (fn2-ov-distinct-spec key entries)))
(defun fn2-ov-image-spec (key entries)
 (declare (xargs :verify-guards nil))
 (list (make-list (len entries) :initial-element :ok) (fn2-ov-sort-spec key entries)))
