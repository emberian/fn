; Actual storage-read hash decisions, independent of machine declarations.
(in-package "ACL2")
(include-book "blake3-word-frames")
(include-book "pool-digest")
(include-book "commit-geometry")
(fn2-book-layer :b)
(local (in-theory (disable tau-system)))
;; LEFT octets from OFF of the lease SLOT GEN (owner OKIND OSLOT OGEN) into
;; hasher row ROW, one fn2-b3-update (at most 4,096 octets) a step, FUEL
;; steps at most: (mv code fn2-digests fn2-b3).
;; LEFT octets from OFF of the lease SLOT GEN (owner OKIND OSLOT OGEN) into
;; hasher row ROW, one fn2-b3-update (at most 4,096 octets) a step, FUEL
;; steps at most: (mv code fn2-digests fn2-b3).
(defun fn2-b-block-read-row (rows)
 (declare (xargs :guard t))
 (nfix (- (nfix rows) 2)))

(defun fn2-block-hash-span (fuel row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :measure (nfix fuel)
                 :guard (and (fn2-pool-wfp fn2-pool) (natp off) (natp left))))
 (cond ((zp left) (mv :ok fn2-digests fn2-b3))
       ((not (and (posp fuel) (fn2-b3-ready row fn2-b3 fn2-digests)
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 left)))
        (mv :bounds fn2-digests fn2-b3))
       (t (mv-let (code used fn2-digests fn2-b3)
            (fn2-b3-update row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)
            (if (and (member-eq code '(:ok :more)) (posp used) (<= used left))
                (fn2-block-hash-span (- fuel 1) row slot gen (+ off (nfix used)) (nfix (- left (nfix used)))
                                     okind oslot ogen fn2-digests fn2-b3 fn2-pool)
              (mv :bounds fn2-digests fn2-b3))))))
(local
 (defthm fn2-block-hash-span-update-shape
  (implies (and (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-pool-wfp fn2-pool)
                (integerp off) (<= 0 off) (< off 4294967296) (integerp left) (<= 0 left) (< left 4294967296)
                (fn2-digestsp fn2-digests) (fn2-b3p fn2-b3) (fn2-poolp fn2-pool))
   (b* (((mv & & d b) (fn2-b3-update row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)))
    (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
         (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
         (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
  :hints (("Goal" :use ((:instance fn2-b3-update-shape (len left)))
                  :in-theory (disable fn2-b3-update-shape fn2-b3-ready fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                      fn2-b3p fn2-b3-wfp fn2-b3-rows)))))
(defthm fn2-block-hash-span-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & d b) (fn2-block-hash-span fuel row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :induct (fn2-block-hash-span fuel row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)
                 :in-theory (disable fn2-b3-ready fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                     fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-b3-update-shape))))
(fn2-hash-row-frames fn2-block-hash-span fn2-digests fn2-b3)
(fn2-b3-word-frame fn2-block-hash-span)
(in-theory (disable fn2-block-hash-span))
;; The LEN octets at BOFF of the lease LSLOT LGEN hashed in hasher row ROW
;; into its result slot: (mv code fn2-b3 fn2-digests).
(defun fn2-block-hash-into (row lslot lgen boff len okind oslot ogen fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)
                 :guard-hints (("Goal" :in-theory (enable fn2-b3-ready)))))
 (b* ((key (fn2-digest-slot (nfix row) *fn2-b3-key*))
      (got (fn2-digest-slot (nfix row) *fn2-b3-result*))
      ((unless (and (natp row) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp key fn2-digests)
                    (natp boff) (natp len)))
       (mv :bounds fn2-b3 fn2-digests))
      ((mv fn2-digests fn2-b3) (fn2-b3-init row 0 key fn2-digests fn2-b3))
      ((mv code fn2-digests fn2-b3)
       (fn2-block-hash-span 8 row lslot lgen boff len okind oslot ogen fn2-digests fn2-b3 fn2-pool))
      ((unless (and (eq code :ok) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp got fn2-digests)))
       (mv :bounds fn2-b3 fn2-digests))
      (fn2-digests (fn2-b3-finalize got row fn2-digests fn2-b3)))
  (mv :ok fn2-b3 fn2-digests)))
(defthm fn2-block-hash-into-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & b d) (fn2-block-hash-into row lslot lgen boff len okind oslot ogen fn2-b3 fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :in-theory (e/d (fn2-b3-ready) (fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                                   fn2-b3p fn2-b3-wfp fn2-b3-rows)))))
(fn2-hash-row-frames fn2-block-hash-into fn2-b3 fn2-digests)
(fn2-b3-word-frame fn2-block-hash-into)
(in-theory (disable fn2-block-hash-into))
;; Whether digest row GOT equals the 32 octets at OFF of the lease (loaded
;; into digest row SCRATCH): (mv same fn2-digests).
(defun fn2-block-digest-at (got scratch lslot lgen off okind oslot ogen fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (b* (((unless (and (natp off) (fn2-digest-rowp got fn2-digests) (fn2-digest-rowp scratch fn2-digests)))
       (mv nil fn2-digests))
      ((mv code fn2-digests) (fn2-rec-fetch 0 scratch lslot lgen off okind oslot ogen fn2-pool fn2-digests)))
  (mv (and (eq code :ok) (fn2-digest-rowp got fn2-digests) (fn2-digest-rowp scratch fn2-digests)
           (fn2-digest-equal got scratch fn2-digests))
      fn2-digests)))
(defthm fn2-block-digest-at-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
  (b* (((mv & d) (fn2-block-digest-at got scratch lslot lgen off okind oslot ogen fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests)))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows))))
(fn2-hash-row-frames fn2-block-digest-at fn2-digests)
(in-theory (disable fn2-block-digest-at))
;; Digest row CV: the chaining value of the unit at absolute pool octet AT
;; (chunk counter COUNTER) when LEN is a whole unit, else row GOT again.
(defun fn2-block-cv-into (cv got at len counter fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (cond ((not (and (fn2-digest-rowp cv fn2-digests) (fn2-digest-rowp got fn2-digests))) fn2-digests)
       ((not (equal len *fn2-commit-unit-bytes*)) (fn2-digest-copy cv got fn2-digests))
       ((and (natp at) (<= (+ at *fn2-commit-unit-bytes*) (fn2-pool-data-length fn2-pool))
             (unsigned-byte-p 48 counter))
        (fn2-b3-subtree-cv-into cv at *fn2-commit-unit-bytes* counter fn2-digests fn2-pool))
       (t fn2-digests)))
(defthm fn2-block-cv-into-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
  (let ((d (fn2-block-cv-into cv got at len counter fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests)))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows))))
(fn2-hash-row-frames fn2-block-cv-into fn2-digests)
(in-theory (disable fn2-block-cv-into))
 ;; A location commitment from a published article/metadata row. BOFF is
;; the returned unit and HSLOT/HGEN/HOFF the retained expected digest.
;; These can be separate workspaces. Callers own the binding and separation of those spans.
(defun fn2-block-read-commitment-children (bytes len lslot lgen boff hslot hgen hoff okind oslot ogen fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (b* (((unless (and (natp bytes) (natp len) (equal bytes len))) (mv :io fn2-b3 fn2-digests))
      ((unless (and (posp len) (<= len *fn2-commit-unit-bytes*)
                    (natp boff) (natp hoff)))
       (mv :bounds fn2-b3 fn2-digests))
      (row (fn2-b-block-read-row (fn2-b3-rows fn2-b3)))
      (got (fn2-digest-slot row *fn2-b3-result*))
      (want (fn2-digest-slot row *fn2-fc-hash*))
      ((mv code fn2-b3 fn2-digests)
       (fn2-block-hash-into row lslot lgen boff len
                            okind oslot ogen fn2-b3 fn2-digests fn2-pool))
      ((unless (eq code :ok)) (mv :bounds fn2-b3 fn2-digests))
      ((mv same fn2-digests)
       (fn2-block-digest-at got want hslot hgen hoff okind oslot ogen fn2-digests fn2-pool)))
  (mv (if same :ok :hash) fn2-b3 fn2-digests)))
(defthm fn2-block-read-commitment-children-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & b d) (fn2-block-read-commitment-children bytes len lslot lgen boff hslot hgen hoff okind oslot ogen fn2-b3 fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                    fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-digest-rowp))))
(fn2-b3-word-frame fn2-block-read-commitment-children)
(in-theory (disable fn2-block-read-commitment-children))

; B-S2 S10: the read's completion. Every requested octet arrived (BYTES =
; LEN; :io otherwise). A block named through a source manifest (VERIFY 1)
; is then checked against its entry, whose two digests the caller's lease
; LSLOT LGEN holds at HOFF (the block's own BLAKE3) and CVOFF (its chaining
; value at chunk counter 4 BLOCK; a block shorter than a unit carries its
; BLAKE3 there again, article-manifest.lisp): the LEN octets at BOFF of the
; lease are hashed in the format table's penultimate row (fn2-b-block-read-row), the
; read-side check's, initialized, fed and finalized within this one call,
; so one row serves every cursor row; either digest unequal answers :hash.
; :bounds: the row or the lease range is not there (the core contradicts
; its own layout). (mv code fn2-b3 fn2-digests).
(defun fn2-block-read-done-from-children (bytes len verify lslot lgen boff proof-slot proof-gen hoff cvoff block okind oslot ogen
                                           fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (b* (((unless (and (natp bytes) (natp len) (equal bytes len))) (mv :io fn2-b3 fn2-digests))
      ((unless (equal verify 1)) (mv :ok fn2-b3 fn2-digests))
      (row (fn2-b-block-read-row (fn2-b3-rows fn2-b3)))
      (got (fn2-digest-slot row *fn2-b3-result*))
      (want (fn2-digest-slot row *fn2-fc-hash*))
      (cv (fn2-digest-slot row *fn2-fc-geometry*))
      ((unless (and (posp len) (<= len *fn2-commit-unit-bytes*) (natp boff) (natp hoff) (natp cvoff)
                    (natp lslot) (< lslot (fn2-pool-rows fn2-pool))))
       (mv :bounds fn2-b3 fn2-digests))
      ((mv code fn2-b3 fn2-digests)
       (fn2-block-hash-into row lslot lgen boff len okind oslot ogen fn2-b3 fn2-digests fn2-pool))
      ((unless (and (eq code :ok) (fn2-digest-rowp got fn2-digests) (fn2-digest-rowp want fn2-digests)
                    (fn2-digest-rowp cv fn2-digests)))
       (mv :bounds fn2-b3 fn2-digests))
      ((mv same fn2-digests) (fn2-block-digest-at got want proof-slot proof-gen hoff okind oslot ogen fn2-digests fn2-pool))
      ((unless same) (mv :hash fn2-b3 fn2-digests))
      (fn2-digests (fn2-block-cv-into cv got (+ (nfix (fn2-pool-slot-base lslot fn2-pool)) boff) len
                                      (* 4 (nfix block)) fn2-digests fn2-pool))
      ((mv same fn2-digests) (fn2-block-digest-at cv want proof-slot proof-gen cvoff okind oslot ogen fn2-digests fn2-pool)))
  (mv (if same :ok :hash) fn2-b3 fn2-digests)))
(defthm fn2-block-read-done-from-children-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & b d) (fn2-block-read-done-from-children bytes len verify lslot lgen boff proof-slot proof-gen hoff cvoff block okind oslot ogen
                                                 fn2-b3 fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                    fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-digest-rowp))))
(fn2-b3-preserves fn2-block-read-done-from-children
 (bytes len verify lslot lgen boff proof-slot proof-gen hoff cvoff block okind oslot ogen fn2-b3 fn2-digests fn2-pool)
 :hyps ((fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
        (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 :specs (("-B3-TYPE" fn2-b3p 1) ("-B3-WFP" fn2-b3-wfp 1) ("-B3-ROWS" fn2-b3-rows 1 :frame fn2-b3
          :hints (("Goal" :in-theory (e/d (fn2-block-read-done-from-children)
                                         (fn2-b3-rows fn2-digests-rows)))))
         ("-DIGESTS-TYPE" fn2-digestsp 2) ("-DIGESTS-WFP" fn2-digests-wfp 2)
         ("-DIGESTS-ROWS" fn2-digests-rows 2 :frame fn2-digests
          :hints (("Goal" :in-theory (e/d (fn2-block-read-done-from-children)
                                         (fn2-b3-rows fn2-digests-rows))))))
 :hints (("Goal" :use fn2-block-read-done-from-children-shape
          :in-theory (disable fn2-block-read-done-from-children fn2-digestsp fn2-digests-wfp fn2-digests-rows fn2-b3p fn2-b3-wfp fn2-b3-rows))))

; Existing cursors carry proof and block bytes in one lease. The checkpoint
; source walker uses separate stable windows through the same implementation.
(defun fn2-block-read-done-children (bytes len verify lslot lgen boff hoff cvoff block okind oslot ogen fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (fn2-block-read-done-from-children bytes len verify lslot lgen boff lslot lgen hoff cvoff block okind oslot ogen fn2-b3 fn2-digests fn2-pool))

(defthm fn2-block-read-done-children-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & b d) (fn2-block-read-done-children bytes len verify lslot lgen boff hoff cvoff block okind oslot ogen
                                                 fn2-b3 fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :use ((:instance fn2-block-read-done-from-children-shape (proof-slot lslot) (proof-gen lgen)))
          :in-theory (enable fn2-block-read-done-children))))
(in-theory (disable fn2-block-read-done-children))
