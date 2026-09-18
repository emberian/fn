; fn M4 transfer experiment: bounded, resumable assembly of opaque octets.
;
; This is a pure staging kernel.  It chooses no portable wire grammar, object
; identity, hash, signature, receipt, acceptance action, or persistence queue.
; A complete result is only an unverified candidate byte string for a later
; bounded codec/verification/acceptance composition.

(in-package "ACL2")

(include-book "acceptance")

; Guard-safe executable counterparts for ACL2's total logical primitives.
; Each macro expands to the original primitive in logic, so existing transfer
; definitions and proofs retain their exact logical meaning.
(defun fn-transfer-guard-leq (x y)
  (declare (xargs :guard t))
  (not (fn-ag-less y x)))

(defthm fn-transfer-guard-leq-is-leq
  (equal (fn-transfer-guard-leq x y) (<= x y))
  :hints (("Goal" :use ((:instance fn-ag-less-is-less (x y) (y x))))))

(defun fn-transfer-guard-geq (x y)
  (declare (xargs :guard t))
  (not (fn-ag-less x y)))

(defthm fn-transfer-guard-geq-is-geq
  (equal (fn-transfer-guard-geq x y) (>= x y))
  :hints (("Goal" :use ((:instance fn-ag-less-is-less)))))

(defun fn-transfer-guard-add (x y)
  (declare (xargs :guard t))
  (+ (fix x) (fix y)))

(defthm fn-transfer-guard-add-is-add
  (equal (fn-transfer-guard-add x y) (+ x y)))

(defun fn-transfer-guard-sub (x y)
  (declare (xargs :guard t))
  (- (fix x) (fix y)))

(defthm fn-transfer-guard-sub-is-sub
  (equal (fn-transfer-guard-sub x y) (- x y)))

(defun fn-transfer-guard-inc (x)
  (declare (xargs :guard t))
  (+ 1 (fix x)))

(defthm fn-transfer-guard-inc-is-inc
  (equal (fn-transfer-guard-inc x) (1+ x)))

(defun fn-transfer-guard-dec (x)
  (declare (xargs :guard t))
  (+ -1 (fix x)))

(defthm fn-transfer-guard-dec-is-dec
  (equal (fn-transfer-guard-dec x) (1- x)))

(defun fn-transfer-guard-zp (x)
  (declare (xargs :guard t))
  (not (and (integerp x) (fn-ag-less 0 x))))

(defthm fn-transfer-guard-zp-is-zp
  (equal (fn-transfer-guard-zp x) (zp x))
  :hints (("Goal" :use ((:instance fn-ag-less-is-less (x 0) (y x))))))

(defun fn-transfer-guard-len (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (1+ (fn-transfer-guard-len (cdr xs)))
    0))

(defthm fn-transfer-guard-len-is-len
  (equal (fn-transfer-guard-len xs) (len xs)))

(defun fn-transfer-guard-nth (n xs)
  (declare (xargs :guard t
                  :measure (nfix n)))
  (if (not (and (integerp n) (fn-ag-less 0 n)))
      (fn-ag-car xs)
    (fn-transfer-guard-nth (1- n) (fn-ag-cdr xs))))

(defthm fn-transfer-guard-nth-is-nth
  (equal (fn-transfer-guard-nth n xs) (nth n xs))
  :hints (("Goal" :induct (nth n xs))))

(defmacro fn-transfer-safe-car (x)
  (list 'mbe :logic (list 'car x) :exec (list 'fn-ag-car x)))

(defmacro fn-transfer-safe-cdr (x)
  (list 'mbe :logic (list 'cdr x) :exec (list 'fn-ag-cdr x)))

(defmacro fn-transfer-safe-leq (x y)
  (list 'mbe :logic (list '<= x y)
        :exec (list 'fn-transfer-guard-leq x y)))

(defmacro fn-transfer-safe-less (x y)
  (list 'mbe :logic (list '< x y)
        :exec (list 'fn-ag-less x y)))

(defmacro fn-transfer-safe-geq (x y)
  (list 'mbe :logic (list '>= x y)
        :exec (list 'fn-transfer-guard-geq x y)))

(defmacro fn-transfer-safe-add (x y)
  (list 'mbe :logic (list '+ x y)
        :exec (list 'fn-transfer-guard-add x y)))

(defmacro fn-transfer-safe-sub (x y)
  (list 'mbe :logic (list '- x y)
        :exec (list 'fn-transfer-guard-sub x y)))

(defmacro fn-transfer-safe-inc (x)
  (list 'mbe :logic (list '1+ x)
        :exec (list 'fn-transfer-guard-inc x)))

(defmacro fn-transfer-safe-dec (x)
  (list 'mbe :logic (list '1- x)
        :exec (list 'fn-transfer-guard-dec x)))

(defmacro fn-transfer-safe-zp (x)
  (list 'mbe :logic (list 'zp x)
        :exec (list 'fn-transfer-guard-zp x)))

(defmacro fn-transfer-safe-len (x)
  (list 'mbe :logic (list 'len x)
        :exec (list 'fn-transfer-guard-len x)))

(defmacro fn-transfer-safe-nth (n x)
  (list 'mbe :logic (list 'nth n x)
        :exec (list 'fn-transfer-guard-nth n x)))

(defmacro fn-transfer-safe-endp (x)
  (list 'mbe :logic (list 'endp x)
        :exec (list 'not (list 'consp x))))

(defmacro fn-transfer-safe-member (x xs)
  (list 'mbe :logic (list 'member-equal x xs)
        :exec (list 'fn-ag-member x xs)))

; -----------------------------------------------------------------------------
; Bounded primitive values and explicit local profile

(defun fn-transfer-octetp (x)
  (and (integerp x)
       (fn-transfer-safe-leq 0 x)
       (fn-transfer-safe-leq x 255)))

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
      (if (fn-transfer-safe-zp bound)
          nil
        (fn-transfer-at-mostp (cdr xs) (fn-transfer-safe-dec bound)))
    t))

; Profile: (capacity max-object max-chunk max-chunks max-label
;           max-reservations).  Capacity is charged by declared object bytes at
; reservation time; reservation count separately bounds zero-byte staging work.
(defun fn-transfer-capacity (p) (fn-transfer-safe-car p))
(defun fn-transfer-max-object (p)
  (fn-transfer-safe-car (fn-transfer-safe-cdr p)))
(defun fn-transfer-max-chunk (p)
  (fn-transfer-safe-car (fn-transfer-safe-cdr (fn-transfer-safe-cdr p))))
(defun fn-transfer-max-chunks (p)
  (fn-transfer-safe-car
   (fn-transfer-safe-cdr (fn-transfer-safe-cdr (fn-transfer-safe-cdr p)))))
(defun fn-transfer-max-label (p)
  (fn-transfer-safe-car
   (fn-transfer-safe-cdr
    (fn-transfer-safe-cdr (fn-transfer-safe-cdr (fn-transfer-safe-cdr p))))))
(defun fn-transfer-max-reservations (p)
  (fn-transfer-safe-car
   (fn-transfer-safe-cdr
    (fn-transfer-safe-cdr
     (fn-transfer-safe-cdr
      (fn-transfer-safe-cdr (fn-transfer-safe-cdr p)))))))

(defun fn-transfer-make-profile
  (capacity max-object max-chunk max-chunks max-label max-reservations)
  (list capacity max-object max-chunk max-chunks max-label max-reservations))

(defun fn-transfer-profilep (p)
  (and (true-listp p)
       (equal (fn-transfer-safe-len p) 6)
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

(defun fn-transfer-entry-label (entry) (fn-transfer-safe-car entry))
(defun fn-transfer-entry-length (entry)
  (fn-transfer-safe-car (fn-transfer-safe-cdr entry)))
(defun fn-transfer-entry-chunks (entry)
  (fn-transfer-safe-car
   (fn-transfer-safe-cdr (fn-transfer-safe-cdr entry))))

(defun fn-transfer-make-entry (label declared-length chunks)
  (list label declared-length chunks))

(defun fn-transfer-chunk-offset (chunk) (fn-transfer-safe-car chunk))
(defun fn-transfer-chunk-octets (chunk)
  (fn-transfer-safe-car (fn-transfer-safe-cdr chunk)))

(defun fn-transfer-make-chunk (offset octets)
  (list offset octets))

(defun fn-transfer-chunkp (chunk declared-length profile)
  (and (true-listp chunk)
       (equal (fn-transfer-safe-len chunk) 2)
       (natp (fn-transfer-chunk-offset chunk))
       (fn-transfer-chunk-inputp (fn-transfer-chunk-octets chunk) profile)
       (fn-transfer-safe-leq
        (fn-transfer-safe-add
         (fn-transfer-chunk-offset chunk)
         (fn-transfer-safe-len (fn-transfer-chunk-octets chunk)))
        declared-length)))

(defun fn-transfer-ranges-overlapp (left right)
  (and (fn-transfer-safe-less
        (fn-transfer-chunk-offset left)
        (fn-transfer-safe-add
         (fn-transfer-chunk-offset right)
         (fn-transfer-safe-len (fn-transfer-chunk-octets right))))
       (fn-transfer-safe-less
        (fn-transfer-chunk-offset right)
        (fn-transfer-safe-add
         (fn-transfer-chunk-offset left)
         (fn-transfer-safe-len (fn-transfer-chunk-octets left))))))

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
       (equal (fn-transfer-safe-len entry) 3)
       (fn-transfer-labelp (fn-transfer-entry-label entry) profile)
       (natp (fn-transfer-entry-length entry))
       (fn-transfer-safe-leq (fn-transfer-entry-length entry)
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
      (fn-transfer-safe-add
       (fn-transfer-entry-length (car entries))
       (fn-transfer-reserved-bytes (cdr entries)))
    0))

; State: (profile entries).  This logical state is volatile staging state; it
; deliberately makes no assertion about a disk commit or restart recovery.
(defun fn-transfer-state-profile (st) (fn-transfer-safe-car st))
(defun fn-transfer-state-entries (st)
  (fn-transfer-safe-car (fn-transfer-safe-cdr st)))

(defun fn-transfer-make-state (profile entries)
  (list profile entries))

(defun fn-transfer-statep (st)
  (and (true-listp st)
       (equal (fn-transfer-safe-len st) 2)
       (fn-transfer-profilep (fn-transfer-state-profile st))
       ; Bound entry count before validating entries or pairwise labels.
       (fn-transfer-at-mostp
        (fn-transfer-state-entries st)
        (fn-transfer-max-reservations (fn-transfer-state-profile st)))
       (fn-transfer-entriesp (fn-transfer-state-entries st)
                             (fn-transfer-state-profile st))
       (fn-transfer-distinct-labelsp (fn-transfer-state-entries st))
       (fn-transfer-safe-leq
        (fn-transfer-reserved-bytes (fn-transfer-state-entries st))
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
(defun fn-transfer-result-outcome (result) (fn-transfer-safe-car result))
(defun fn-transfer-result-state (result)
  (fn-transfer-safe-car (fn-transfer-safe-cdr result)))
(defun fn-transfer-result-diagnostic (result)
  (fn-transfer-safe-car
   (fn-transfer-safe-cdr (fn-transfer-safe-cdr result))))
(defun fn-transfer-result-candidate (result)
  (fn-transfer-safe-car
   (fn-transfer-safe-cdr
    (fn-transfer-safe-cdr (fn-transfer-safe-cdr result)))))

(defun fn-transfer-present-atp (position chunks)
  (if (consp chunks)
      (or (and (fn-transfer-safe-leq
                (fn-transfer-chunk-offset (car chunks)) position)
               (fn-transfer-safe-less
                position
                (fn-transfer-safe-add
                 (fn-transfer-chunk-offset (car chunks))
                 (fn-transfer-safe-len
                  (fn-transfer-chunk-octets (car chunks))))))
          (fn-transfer-present-atp position (cdr chunks)))
    nil))

(defun fn-transfer-byte-at (position chunks)
  (if (consp chunks)
      (if (and (fn-transfer-safe-leq
                (fn-transfer-chunk-offset (car chunks)) position)
               (fn-transfer-safe-less
                position
                (fn-transfer-safe-add
                 (fn-transfer-chunk-offset (car chunks))
                 (fn-transfer-safe-len
                  (fn-transfer-chunk-octets (car chunks))))))
          (fn-transfer-safe-nth
           (fn-transfer-safe-sub
            position (fn-transfer-chunk-offset (car chunks)))
           (fn-transfer-chunk-octets (car chunks)))
        (fn-transfer-byte-at position (cdr chunks)))
    nil))

(defun fn-transfer-complete-fromp (position declared-length chunks)
  (declare (xargs :measure
                  (nfix (fn-transfer-safe-sub declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (fn-transfer-safe-geq position declared-length))
      t
    (and (fn-transfer-present-atp position chunks)
         (fn-transfer-complete-fromp (fn-transfer-safe-inc position)
                                     declared-length chunks))))

(defun fn-transfer-entry-completep (entry)
  (fn-transfer-complete-fromp 0 (fn-transfer-entry-length entry)
                              (fn-transfer-entry-chunks entry)))

(defun fn-transfer-assemble-from (position declared-length chunks)
  (declare (xargs :measure
                  (nfix (fn-transfer-safe-sub declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (fn-transfer-safe-geq position declared-length))
      nil
    (cons (fn-transfer-byte-at position chunks)
          (fn-transfer-assemble-from (fn-transfer-safe-inc position)
                                     declared-length chunks))))

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
  (declare (xargs :measure
                  (nfix (fn-transfer-safe-sub declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (fn-transfer-safe-geq position declared-length))
      nil
    (if (fn-transfer-present-atp position chunks)
        (fn-transfer-missing-from (fn-transfer-safe-inc position)
                                  declared-length chunks)
      (cons (list position 1)
            (fn-transfer-missing-from (fn-transfer-safe-inc position)
                                      declared-length chunks)))))

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
       (fn-transfer-safe-leq
        declared-length
        (fn-transfer-max-object (fn-transfer-state-profile st)))
       (not (fn-transfer-safe-zp
             (fn-transfer-max-reservations
              (fn-transfer-state-profile st))))
       (fn-transfer-at-mostp
        (fn-transfer-state-entries st)
        (fn-transfer-safe-dec
         (fn-transfer-max-reservations
          (fn-transfer-state-profile st))))
       (not (fn-transfer-find-entry label (fn-transfer-state-entries st)))
       (fn-transfer-safe-leq
        (fn-transfer-safe-add
         (fn-transfer-reserved-bytes (fn-transfer-state-entries st))
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
            (if (fn-transfer-safe-less
                 (fn-transfer-max-object profile) declared-length)
                (fn-transfer-make-result :object-limit st :object-limit nil)
              (if entry
                  (if (equal declared-length (fn-transfer-entry-length entry))
                      (fn-transfer-make-result :already-reserved st nil
                                               (fn-transfer-entry-candidate entry))
                    (fn-transfer-make-result :label-conflict st
                                             (list :existing-declaration entry) nil))
                (if (or (fn-transfer-safe-zp
                         (fn-transfer-max-reservations profile))
                        (not (fn-transfer-at-mostp
                              (fn-transfer-state-entries st)
                              (fn-transfer-safe-dec
                               (fn-transfer-max-reservations profile)))))
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
                  (if (fn-transfer-safe-less
                       (fn-transfer-entry-length entry) offset)
                      (fn-transfer-make-result :bounds st :bounds nil)
                    (if (fn-transfer-safe-less
                         (fn-transfer-entry-length entry)
                         (fn-transfer-safe-add
                          offset (fn-transfer-safe-len octets)))
                        (fn-transfer-make-result :bounds st :bounds nil)
                      (if (fn-transfer-safe-endp octets)
                          (fn-transfer-make-result :empty-chunk st nil
                                                   (fn-transfer-entry-candidate entry))
                        (if (fn-transfer-safe-member
                             chunk (fn-transfer-entry-chunks entry))
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
                              (if (or (fn-transfer-safe-zp
                                       (fn-transfer-max-chunks profile))
                                      (not (fn-transfer-at-mostp
                                            (fn-transfer-entry-chunks entry)
                                            (fn-transfer-safe-dec
                                             (fn-transfer-max-chunks profile)))))
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
; Executable guard closure.  All original transfer functions retain guard T;
; malformed logical inputs therefore keep the same total results.

(verify-guards fn-transfer-octetp)
(verify-guards fn-transfer-octet-listp)
(verify-guards fn-transfer-at-mostp)
(verify-guards fn-transfer-capacity)
(verify-guards fn-transfer-max-object)
(verify-guards fn-transfer-max-chunk)
(verify-guards fn-transfer-max-chunks)
(verify-guards fn-transfer-max-label)
(verify-guards fn-transfer-max-reservations)
(verify-guards fn-transfer-make-profile)
(verify-guards fn-transfer-profilep)
(verify-guards fn-transfer-labelp)
(verify-guards fn-transfer-chunk-inputp)
(verify-guards fn-transfer-entry-label)
(verify-guards fn-transfer-entry-length)
(verify-guards fn-transfer-entry-chunks)
(verify-guards fn-transfer-make-entry)
(verify-guards fn-transfer-chunk-offset)
(verify-guards fn-transfer-chunk-octets)
(verify-guards fn-transfer-make-chunk)
(verify-guards fn-transfer-chunkp)
(verify-guards fn-transfer-ranges-overlapp)
(verify-guards fn-transfer-no-overlaps-withp)
(verify-guards fn-transfer-chunk-listp)
(verify-guards fn-transfer-entryp)
(verify-guards fn-transfer-entriesp)
(verify-guards fn-transfer-label-absentp)
(verify-guards fn-transfer-distinct-labelsp)
(verify-guards fn-transfer-reserved-bytes)
(verify-guards fn-transfer-state-profile)
(verify-guards fn-transfer-state-entries)
(verify-guards fn-transfer-make-state)
(verify-guards fn-transfer-statep)
(verify-guards fn-transfer-initial-state)
(verify-guards fn-transfer-find-entry)
(verify-guards fn-transfer-make-result)
(verify-guards fn-transfer-result-outcome)
(verify-guards fn-transfer-result-state)
(verify-guards fn-transfer-result-diagnostic)
(verify-guards fn-transfer-result-candidate)
(verify-guards fn-transfer-present-atp)
(verify-guards fn-transfer-byte-at)
(verify-guards fn-transfer-complete-fromp)
(verify-guards fn-transfer-entry-completep)
(verify-guards fn-transfer-assemble-from)
(verify-guards fn-transfer-entry-candidate)
(verify-guards fn-transfer-missing-from)
(verify-guards fn-transfer-missing-ranges)
(verify-guards fn-transfer-new-reservation-admissiblep)
(verify-guards fn-transfer-reserve)
(verify-guards fn-transfer-first-overlap)
(verify-guards fn-transfer-replace-entry-with-chunk)
(verify-guards fn-transfer-add-chunk)

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
