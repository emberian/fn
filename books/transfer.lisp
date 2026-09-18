; fn M4 transfer experiment: bounded, resumable assembly of opaque octets.
;
; This is a pure staging kernel.  It chooses no portable wire grammar, object
; identity, hash, signature, receipt, acceptance action, or persistence queue.
; A complete result is only an unverified candidate byte string for a later
; bounded codec/verification/acceptance composition.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Bounded primitive values and explicit local profile

(defun fn-transfer-octetp (x)
  (and (integerp x) (<= 0 x) (<= x 255)))

(defun fn-transfer-octet-listp (xs)
  (if (consp xs)
      (and (fn-transfer-octetp (car xs))
           (fn-transfer-octet-listp (cdr xs)))
    (null xs)))

; This preflight stops after at most bound + 1 cons cells.  It is used before
; octet validation, so a remote overlong label or chunk cannot force an
; unbounded traversal merely to discover that it exceeds the local profile.
(defun fn-transfer-at-mostp (xs bound)
  (if (consp xs)
      (if (zp bound)
          nil
        (fn-transfer-at-mostp (cdr xs) (1- bound)))
    t))

; Profile: (capacity max-object max-chunk max-chunks max-label
;           max-reservations).  Capacity is charged by declared object bytes at
; reservation time; reservation count separately bounds zero-byte staging work.
(defun fn-transfer-capacity (p) (car p))
(defun fn-transfer-max-object (p) (car (cdr p)))
(defun fn-transfer-max-chunk (p) (car (cdr (cdr p))))
(defun fn-transfer-max-chunks (p) (car (cdr (cdr (cdr p)))))
(defun fn-transfer-max-label (p) (car (cdr (cdr (cdr (cdr p))))))
(defun fn-transfer-max-reservations (p)
  (car (cdr (cdr (cdr (cdr (cdr p)))))))

(defun fn-transfer-make-profile
  (capacity max-object max-chunk max-chunks max-label max-reservations)
  (list capacity max-object max-chunk max-chunks max-label max-reservations))

(defun fn-transfer-profilep (p)
  (and (true-listp p)
       (equal (len p) 6)
       (natp (fn-transfer-capacity p))
       (natp (fn-transfer-max-object p))
       (natp (fn-transfer-max-chunk p))
       (natp (fn-transfer-max-chunks p))
       (natp (fn-transfer-max-label p))
       (natp (fn-transfer-max-reservations p))))

(defun fn-transfer-labelp (label profile)
  (and (fn-transfer-at-mostp label (fn-transfer-max-label profile))
       (fn-transfer-octet-listp label)))

(defun fn-transfer-chunk-inputp (octets profile)
  (and (fn-transfer-at-mostp octets (fn-transfer-max-chunk profile))
       (fn-transfer-octet-listp octets)))

; -----------------------------------------------------------------------------
; Reservation state.  Entry: (label declared-length chunks), where chunk is
; (offset octets).  Chunks are retained as evidence in arrival order; no
; winner is selected for a non-identical overlap.

(defun fn-transfer-entry-label (entry) (car entry))
(defun fn-transfer-entry-length (entry) (car (cdr entry)))
(defun fn-transfer-entry-chunks (entry) (car (cdr (cdr entry))))

(defun fn-transfer-make-entry (label declared-length chunks)
  (list label declared-length chunks))

(defun fn-transfer-chunk-offset (chunk) (car chunk))
(defun fn-transfer-chunk-octets (chunk) (car (cdr chunk)))

(defun fn-transfer-make-chunk (offset octets)
  (list offset octets))

(defun fn-transfer-chunkp (chunk declared-length profile)
  (and (true-listp chunk)
       (equal (len chunk) 2)
       (natp (fn-transfer-chunk-offset chunk))
       (fn-transfer-chunk-inputp (fn-transfer-chunk-octets chunk) profile)
       (<= (+ (fn-transfer-chunk-offset chunk)
              (len (fn-transfer-chunk-octets chunk)))
           declared-length)))

(defun fn-transfer-ranges-overlapp (left right)
  (and (< (fn-transfer-chunk-offset left)
          (+ (fn-transfer-chunk-offset right)
             (len (fn-transfer-chunk-octets right))))
       (< (fn-transfer-chunk-offset right)
          (+ (fn-transfer-chunk-offset left)
             (len (fn-transfer-chunk-octets left))))))

(defun fn-transfer-no-overlaps-withp (chunk chunks)
  (if (consp chunks)
      (and (not (fn-transfer-ranges-overlapp chunk (car chunks)))
           (fn-transfer-no-overlaps-withp chunk (cdr chunks)))
    t))

(defun fn-transfer-chunk-listp (chunks declared-length profile)
  (if (consp chunks)
      (and (fn-transfer-chunkp (car chunks) declared-length profile)
           (fn-transfer-no-overlaps-withp (car chunks) (cdr chunks))
           (fn-transfer-chunk-listp (cdr chunks) declared-length profile))
    (null chunks)))

(defun fn-transfer-entryp (entry profile)
  (and (true-listp entry)
       (equal (len entry) 3)
       (fn-transfer-labelp (fn-transfer-entry-label entry) profile)
       (natp (fn-transfer-entry-length entry))
       (<= (fn-transfer-entry-length entry)
           (fn-transfer-max-object profile))
       (fn-transfer-at-mostp (fn-transfer-entry-chunks entry)
                             (fn-transfer-max-chunks profile))
       (fn-transfer-chunk-listp (fn-transfer-entry-chunks entry)
                                (fn-transfer-entry-length entry) profile)))

(defun fn-transfer-entriesp (entries profile)
  (if (consp entries)
      (and (fn-transfer-entryp (car entries) profile)
           (fn-transfer-entriesp (cdr entries) profile))
    (null entries)))

(defun fn-transfer-label-absentp (label entries)
  (if (consp entries)
      (and (not (equal label (fn-transfer-entry-label (car entries))))
           (fn-transfer-label-absentp label (cdr entries)))
    t))

(defun fn-transfer-distinct-labelsp (entries)
  (if (consp entries)
      (and (fn-transfer-label-absentp (fn-transfer-entry-label (car entries))
                                      (cdr entries))
           (fn-transfer-distinct-labelsp (cdr entries)))
    t))

(defun fn-transfer-reserved-bytes (entries)
  (if (consp entries)
      (+ (fn-transfer-entry-length (car entries))
         (fn-transfer-reserved-bytes (cdr entries)))
    0))

; State: (profile entries).  This logical state is volatile staging state; it
; deliberately makes no assertion about a disk commit or restart recovery.
(defun fn-transfer-state-profile (st) (car st))
(defun fn-transfer-state-entries (st) (car (cdr st)))

(defun fn-transfer-make-state (profile entries)
  (list profile entries))

(defun fn-transfer-statep (st)
  (and (true-listp st)
       (equal (len st) 2)
       (fn-transfer-profilep (fn-transfer-state-profile st))
       ; Bound entry count before validating entries or pairwise labels.
       (fn-transfer-at-mostp
        (fn-transfer-state-entries st)
        (fn-transfer-max-reservations (fn-transfer-state-profile st)))
       (fn-transfer-entriesp (fn-transfer-state-entries st)
                             (fn-transfer-state-profile st))
       (fn-transfer-distinct-labelsp (fn-transfer-state-entries st))
       (<= (fn-transfer-reserved-bytes (fn-transfer-state-entries st))
           (fn-transfer-capacity (fn-transfer-state-profile st)))))

(defun fn-transfer-initial-state (profile)
  (fn-transfer-make-state profile nil))

(defun fn-transfer-find-entry (label entries)
  (if (consp entries)
      (if (equal label (fn-transfer-entry-label (car entries)))
          (car entries)
        (fn-transfer-find-entry label (cdr entries)))
    nil))

; -----------------------------------------------------------------------------
; Results and candidates

; Result: (outcome state diagnostic candidate).  Diagnostics are data, never
; effects: overlap diagnostics preserve the already retained chunk and do not
; overwrite it.  Candidate is either nil or (:candidate octets).
(defun fn-transfer-make-result (outcome st diagnostic candidate)
  (list outcome st diagnostic candidate))
(defun fn-transfer-result-outcome (result) (car result))
(defun fn-transfer-result-state (result) (car (cdr result)))
(defun fn-transfer-result-diagnostic (result) (car (cdr (cdr result))))
(defun fn-transfer-result-candidate (result)
  (car (cdr (cdr (cdr result)))))

(defun fn-transfer-present-atp (position chunks)
  (if (consp chunks)
      (or (and (<= (fn-transfer-chunk-offset (car chunks)) position)
               (< position
                  (+ (fn-transfer-chunk-offset (car chunks))
                     (len (fn-transfer-chunk-octets (car chunks))))))
          (fn-transfer-present-atp position (cdr chunks)))
    nil))

(defun fn-transfer-byte-at (position chunks)
  (if (consp chunks)
      (if (and (<= (fn-transfer-chunk-offset (car chunks)) position)
               (< position
                  (+ (fn-transfer-chunk-offset (car chunks))
                     (len (fn-transfer-chunk-octets (car chunks))))))
          (nth (- position (fn-transfer-chunk-offset (car chunks)))
               (fn-transfer-chunk-octets (car chunks)))
        (fn-transfer-byte-at position (cdr chunks)))
    nil))

(defun fn-transfer-complete-fromp (position declared-length chunks)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length))
      t
    (and (fn-transfer-present-atp position chunks)
         (fn-transfer-complete-fromp (1+ position) declared-length chunks))))

(defun fn-transfer-entry-completep (entry)
  (fn-transfer-complete-fromp 0 (fn-transfer-entry-length entry)
                              (fn-transfer-entry-chunks entry)))

(defun fn-transfer-assemble-from (position declared-length chunks)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length))
      nil
    (cons (fn-transfer-byte-at position chunks)
          (fn-transfer-assemble-from (1+ position) declared-length chunks))))

(defun fn-transfer-entry-candidate (entry)
  (if (fn-transfer-entry-completep entry)
      (list :candidate
            (fn-transfer-assemble-from 0 (fn-transfer-entry-length entry)
                                       (fn-transfer-entry-chunks entry)))
    nil))

; Missing ranges are explicit (offset length) pairs.  This small experiment
; reports each absent octet as a length-one range; a later scheduling layer may
; coalesce adjacent pairs without changing which bytes are requested.
(defun fn-transfer-missing-from (position declared-length chunks)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length))
      nil
    (if (fn-transfer-present-atp position chunks)
        (fn-transfer-missing-from (1+ position) declared-length chunks)
      (cons (list position 1)
            (fn-transfer-missing-from (1+ position) declared-length chunks)))))

(defun fn-transfer-missing-ranges (st label)
  (if (not (fn-transfer-statep st))
      (list :error :invalid-state)
    (let ((entry (fn-transfer-find-entry label (fn-transfer-state-entries st))))
      (if (not entry)
          (list :error :unknown-label)
        (list :ok (fn-transfer-missing-from
                   0 (fn-transfer-entry-length entry)
                   (fn-transfer-entry-chunks entry)))))))

; -----------------------------------------------------------------------------
; Reservation and chunk transitions

(defun fn-transfer-new-reservation-admissiblep (st label declared-length)
  (and (fn-transfer-statep st)
       (fn-transfer-labelp label (fn-transfer-state-profile st))
       (natp declared-length)
       (<= declared-length
           (fn-transfer-max-object (fn-transfer-state-profile st)))
       (not (zp (fn-transfer-max-reservations
                 (fn-transfer-state-profile st))))
       (fn-transfer-at-mostp
        (fn-transfer-state-entries st)
        (1- (fn-transfer-max-reservations
             (fn-transfer-state-profile st))))
       (not (fn-transfer-find-entry label (fn-transfer-state-entries st)))
       (<= (+ (fn-transfer-reserved-bytes (fn-transfer-state-entries st))
              declared-length)
           (fn-transfer-capacity (fn-transfer-state-profile st)))))

; Reserve the entire declaration before accepting any chunk.  Reserving an
; empty object is immediately complete, yielding (:candidate nil), but still
; is neither application acceptance nor a receipt.
(defun fn-transfer-reserve (st label declared-length)
  (if (not (fn-transfer-statep st))
      (fn-transfer-make-result :invalid-state st :invalid-state nil)
    (let ((profile (fn-transfer-state-profile st)))
      (if (not (fn-transfer-labelp label profile))
          (fn-transfer-make-result :invalid-label st :invalid-label nil)
        (let ((entry (fn-transfer-find-entry label
                                             (fn-transfer-state-entries st))))
          (if (not (natp declared-length))
              (fn-transfer-make-result :invalid-length st :invalid-length nil)
            (if (< (fn-transfer-max-object profile) declared-length)
                (fn-transfer-make-result :object-limit st :object-limit nil)
              (if entry
                  (if (equal declared-length (fn-transfer-entry-length entry))
                      (fn-transfer-make-result :already-reserved st nil
                                               (fn-transfer-entry-candidate entry))
                    (fn-transfer-make-result :label-conflict st
                                             (list :existing-declaration entry) nil))
                (if (or (zp (fn-transfer-max-reservations profile))
                        (not (fn-transfer-at-mostp
                              (fn-transfer-state-entries st)
                              (1- (fn-transfer-max-reservations profile)))))
                    (fn-transfer-make-result :reservation-limit st
                                             :reservation-limit nil)
                  (if (not (fn-transfer-new-reservation-admissiblep
                            st label declared-length))
                      (fn-transfer-make-result :capacity st :capacity nil)
                    (let* ((new-entry (fn-transfer-make-entry label declared-length nil))
                           (new-state
                            (fn-transfer-make-state
                             profile
                             (cons new-entry (fn-transfer-state-entries st)))))
                      (fn-transfer-make-result :reserved new-state nil
                                               (fn-transfer-entry-candidate new-entry)))))))))))))

(defun fn-transfer-first-overlap (chunk chunks)
  (if (consp chunks)
      (if (fn-transfer-ranges-overlapp chunk (car chunks))
          (car chunks)
        (fn-transfer-first-overlap chunk (cdr chunks)))
    nil))

(defun fn-transfer-replace-entry-with-chunk (label chunk entries)
  (if (consp entries)
      (if (equal label (fn-transfer-entry-label (car entries)))
          (cons (fn-transfer-make-entry
                 (fn-transfer-entry-label (car entries))
                 (fn-transfer-entry-length (car entries))
                 (cons chunk (fn-transfer-entry-chunks (car entries))))
                (cdr entries))
        (cons (car entries)
              (fn-transfer-replace-entry-with-chunk label chunk (cdr entries))))
    nil))

; Exact range-and-byte duplicates are no-ops.  Any other overlap is a
; conservative local conflict: the result identifies the retained conflicting
; chunk and leaves all retained fragments exact.  Thus arrival order cannot
; silently choose a byte winner.
(defun fn-transfer-add-chunk (st label offset octets)
  (if (not (fn-transfer-statep st))
      (fn-transfer-make-result :invalid-state st :invalid-state nil)
    (let ((profile (fn-transfer-state-profile st)))
      (if (not (fn-transfer-labelp label profile))
          (fn-transfer-make-result :invalid-label st :invalid-label nil)
        (if (not (fn-transfer-chunk-inputp octets profile))
            (fn-transfer-make-result :invalid-chunk st :invalid-chunk nil)
          (if (not (natp offset))
              (fn-transfer-make-result :invalid-offset st :invalid-offset nil)
            (let ((entry (fn-transfer-find-entry label
                                                 (fn-transfer-state-entries st))))
              (if (not entry)
                  (fn-transfer-make-result :unknown-label st :unknown-label nil)
                (let ((chunk (fn-transfer-make-chunk offset octets)))
                  (if (< (fn-transfer-entry-length entry) offset)
                      (fn-transfer-make-result :bounds st :bounds nil)
                    (if (< (fn-transfer-entry-length entry) (+ offset (len octets)))
                        (fn-transfer-make-result :bounds st :bounds nil)
                      (if (endp octets)
                          (fn-transfer-make-result :empty-chunk st nil
                                                   (fn-transfer-entry-candidate entry))
                        (if (member-equal chunk (fn-transfer-entry-chunks entry))
                            (fn-transfer-make-result :duplicate st nil
                                                     (fn-transfer-entry-candidate entry))
                          (let ((overlap (fn-transfer-first-overlap
                                          chunk (fn-transfer-entry-chunks entry))))
                            (if overlap
                                (fn-transfer-make-result
                                 :overlap-conflict st
                                 (list :retained-overlap overlap) nil)
                              ; A zero maximum admits no nonempty fragment.
                              ; Keep this after the duplicate branch: replaying
                              ; an already retained fragment remains a no-op at
                              ; a full positive limit.
                              (if (or (zp (fn-transfer-max-chunks profile))
                                      (not (fn-transfer-at-mostp
                                            (fn-transfer-entry-chunks entry)
                                            (1- (fn-transfer-max-chunks profile)))))
                                  (fn-transfer-make-result :chunk-limit st
                                                           :chunk-limit nil)
                                (let* ((new-entries
                                        (fn-transfer-replace-entry-with-chunk
                                         label chunk
                                         (fn-transfer-state-entries st)))
                                       (new-state
                                        (fn-transfer-make-state profile new-entries))
                                       (new-entry
                                        (fn-transfer-find-entry label new-entries)))
                                  (fn-transfer-make-result
                                   :stored new-state nil
                                   (fn-transfer-entry-candidate new-entry)))))))))))))))))))

; -----------------------------------------------------------------------------
; Initial certified properties.  These establish transition no-overwrite cases
; only; they are not proofs of persistence, parsing, cryptographic validation,
; application acceptance, or exchange-fact convergence.

(defthm fn-transfer-initial-statep
  (implies (fn-transfer-profilep profile)
           (fn-transfer-statep (fn-transfer-initial-state profile)))
  :hints (("Goal" :in-theory (enable fn-transfer-initial-state
                                      fn-transfer-statep
                                      fn-transfer-entriesp
                                      fn-transfer-distinct-labelsp
                                      fn-transfer-reserved-bytes))))

(defthm fn-transfer-reserve-refusal-no-overwrite
  (implies (not (fn-transfer-statep st))
           (equal (fn-transfer-result-state
                   (fn-transfer-reserve st label declared-length))
                  st))
  :hints (("Goal" :in-theory (enable fn-transfer-reserve
                                      fn-transfer-result-state))))

(defthm fn-transfer-invalid-chunk-no-overwrite
  (implies (and (fn-transfer-statep st)
                (fn-transfer-labelp label (fn-transfer-state-profile st))
                (not (fn-transfer-chunk-inputp
                      octets (fn-transfer-state-profile st))))
           (equal (fn-transfer-result-state
                   (fn-transfer-add-chunk st label offset octets))
                  st))
  :hints (("Goal" :in-theory (enable fn-transfer-add-chunk
                                      fn-transfer-result-state))))

(defthm fn-transfer-exact-duplicate-no-overwrite
  (implies (and (fn-transfer-statep st)
                (fn-transfer-labelp label (fn-transfer-state-profile st))
                (fn-transfer-chunk-inputp octets (fn-transfer-state-profile st))
                (natp offset)
                (let ((entry (fn-transfer-find-entry
                              label (fn-transfer-state-entries st))))
                  (and entry
                       (member-equal (fn-transfer-make-chunk offset octets)
                                     (fn-transfer-entry-chunks entry)))))
           (equal (fn-transfer-result-state
                   (fn-transfer-add-chunk st label offset octets))
                  st))
  :hints (("Goal" :in-theory (enable fn-transfer-add-chunk
                                      fn-transfer-result-state))))
