; General preservation and accounting theorems for bounded transfer staging.
; This book proves properties of the pure transfer kernel only.  It makes no
; persistence, object-validation, cryptographic, receipt, or acceptance claim.

(in-package "ACL2")
(include-book "transfer")

; -----------------------------------------------------------------------------
; Small structural facts used by both transitions.

(defthm fn-transfer-result-state-of-make-result
  (equal (fn-transfer-result-state
          (fn-transfer-make-result outcome st diagnostic candidate))
         st)
  :hints (("Goal" :in-theory (enable fn-transfer-make-result
                                      fn-transfer-result-state))))

(defthm fn-transfer-at-mostp-cons-positive
  (implies (and (natp bound) (not (zp bound)))
           (equal (fn-transfer-at-mostp (cons x xs) bound)
                  (fn-transfer-at-mostp xs (1- bound))))
  :hints (("Goal" :in-theory (enable fn-transfer-at-mostp))))

(defthm fn-transfer-empty-entry-is-entryp
  (implies (and (fn-transfer-profilep profile)
                (fn-transfer-labelp label profile)
                (natp declared-length)
                (<= declared-length (fn-transfer-max-object profile)))
           (fn-transfer-entryp
            (fn-transfer-make-entry label declared-length nil) profile))
  :hints (("Goal" :in-theory (enable fn-transfer-entryp
                                      fn-transfer-chunk-listp
                                      fn-transfer-at-mostp))))

(defthm fn-transfer-entries-cons
  (implies (and (fn-transfer-entryp entry profile)
                (fn-transfer-entriesp entries profile))
           (fn-transfer-entriesp (cons entry entries) profile))
  :hints (("Goal" :in-theory (enable fn-transfer-entriesp))))

(defthm fn-transfer-entriesp-implies-true-listp
  (implies (fn-transfer-entriesp entries profile)
           (true-listp entries))
  :hints (("Goal" :induct (fn-transfer-entriesp entries profile)
           :in-theory (enable fn-transfer-entriesp))))

(defthm fn-transfer-distinct-labels-cons
  (implies (and (fn-transfer-label-absentp label entries)
                (fn-transfer-distinct-labelsp entries))
           (fn-transfer-distinct-labelsp
            (cons (fn-transfer-make-entry label declared-length chunks) entries)))
  :hints (("Goal" :in-theory (enable fn-transfer-distinct-labelsp))))

(defthm fn-transfer-reserved-bytes-cons
  (equal (fn-transfer-reserved-bytes
          (cons (fn-transfer-make-entry label declared-length chunks) entries))
         (+ declared-length (fn-transfer-reserved-bytes entries)))
  :hints (("Goal" :in-theory (enable fn-transfer-reserved-bytes))))

(defthm fn-transfer-find-absent-is-nil
  (implies (fn-transfer-label-absentp label entries)
           (equal (fn-transfer-find-entry label entries) nil))
  :hints (("Goal" :induct (fn-transfer-label-absentp label entries)
           :in-theory (enable fn-transfer-find-entry
                               fn-transfer-label-absentp))))

(defthm fn-transfer-find-nil-means-label-absent
  (implies (and (fn-transfer-entriesp entries profile)
                (not (fn-transfer-find-entry label entries)))
           (fn-transfer-label-absentp label entries))
  :hints (("Goal" :induct (fn-transfer-entriesp entries profile)
           :in-theory (enable fn-transfer-entriesp
                               fn-transfer-entryp
                               fn-transfer-find-entry
                               fn-transfer-label-absentp))))

(defthm fn-transfer-find-entry-is-entryp
  (implies (and (fn-transfer-entriesp entries profile)
                (consp (fn-transfer-find-entry label entries)))
           (fn-transfer-entryp (fn-transfer-find-entry label entries) profile))
  :hints (("Goal" :induct (fn-transfer-find-entry label entries)
           :in-theory (enable fn-transfer-find-entry
                               fn-transfer-entriesp))))

(defthm fn-transfer-statep-implies-profilep
  (implies (fn-transfer-statep st)
           (fn-transfer-profilep (fn-transfer-state-profile st)))
  :hints (("Goal" :in-theory (enable fn-transfer-statep))))

(defthm fn-transfer-statep-implies-entriesp
  (implies (fn-transfer-statep st)
           (fn-transfer-entriesp (fn-transfer-state-entries st)
                                 (fn-transfer-state-profile st)))
  :hints (("Goal" :in-theory (enable fn-transfer-statep))))

(defthm fn-transfer-entryp-implies-chunk-listp
  (implies (fn-transfer-entryp entry profile)
           (fn-transfer-chunk-listp (fn-transfer-entry-chunks entry)
                                    (fn-transfer-entry-length entry)
                                    profile))
  :hints (("Goal" :in-theory (enable fn-transfer-entryp))))

; -----------------------------------------------------------------------------
; Reservation transition.

(defthm fn-transfer-reserve-admitted-statep
  (implies (fn-transfer-new-reservation-admissiblep st label declared-length)
           (fn-transfer-statep
            (fn-transfer-make-state
             (fn-transfer-state-profile st)
             (cons (fn-transfer-make-entry label declared-length nil)
                   (fn-transfer-state-entries st)))))
  :hints (("Goal"
           :use ((:instance fn-transfer-empty-entry-is-entryp
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-entries-cons
                            (entry (fn-transfer-make-entry
                                    label declared-length nil))
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-distinct-labels-cons
                            (entries (fn-transfer-state-entries st))
                            (chunks nil))
                 (:instance fn-transfer-find-nil-means-label-absent
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-reserved-bytes-cons
                            (entries (fn-transfer-state-entries st))
                            (chunks nil)))
           :in-theory (enable fn-transfer-new-reservation-admissiblep
                               fn-transfer-statep
                               fn-transfer-at-mostp))))

(defthm fn-transfer-reserve-preserves-statep
  (implies (fn-transfer-statep st)
           (fn-transfer-statep
            (fn-transfer-result-state
             (fn-transfer-reserve st label declared-length))))
  :hints (("Goal"
           :use ((:instance fn-transfer-reserve-admitted-statep))
           :in-theory (enable fn-transfer-reserve
                               fn-transfer-result-state))))

(defthm fn-transfer-reserve-admitted-byte-accounting
  (implies (fn-transfer-new-reservation-admissiblep st label declared-length)
           (equal (fn-transfer-reserved-bytes
                   (fn-transfer-state-entries
                    (fn-transfer-result-state
                     (fn-transfer-reserve st label declared-length))))
                  (+ declared-length
                     (fn-transfer-reserved-bytes
                      (fn-transfer-state-entries st)))))
  :hints (("Goal" :in-theory (enable fn-transfer-reserve
                                      fn-transfer-result-state
                                      fn-transfer-reserved-bytes))))

(defthm fn-transfer-reserve-result-reserved-bytes-bounded
  (implies (fn-transfer-statep st)
           (<= (fn-transfer-reserved-bytes
                (fn-transfer-state-entries
                 (fn-transfer-result-state
                  (fn-transfer-reserve st label declared-length))))
               (fn-transfer-capacity (fn-transfer-state-profile st))))
  :hints (("Goal"
           :use ((:instance fn-transfer-reserve-preserves-statep))
           :in-theory (enable fn-transfer-statep))))

(defthm fn-transfer-reserve-refusal-no-overwrite-general
  (implies (and (fn-transfer-statep st)
                (not (equal (fn-transfer-result-outcome
                             (fn-transfer-reserve st label declared-length))
                            :reserved)))
           (equal (fn-transfer-result-state
                   (fn-transfer-reserve st label declared-length))
                  st))
  :hints (("Goal" :in-theory (enable fn-transfer-reserve
                                      fn-transfer-result-outcome
                                      fn-transfer-result-state))))

; -----------------------------------------------------------------------------
; Chunk insertion structural facts.

(defthm fn-transfer-entry-add-chunk-is-entryp
  (implies (and (fn-transfer-entryp entry profile)
                (fn-transfer-chunkp chunk (fn-transfer-entry-length entry) profile)
                (fn-transfer-no-overlaps-withp
                 chunk (fn-transfer-entry-chunks entry))
                (not (zp (fn-transfer-max-chunks profile)))
                (fn-transfer-at-mostp
                 (fn-transfer-entry-chunks entry)
                 (1- (fn-transfer-max-chunks profile))))
           (fn-transfer-entryp
            (fn-transfer-make-entry
             (fn-transfer-entry-label entry)
             (fn-transfer-entry-length entry)
             (cons chunk (fn-transfer-entry-chunks entry)))
            profile))
  :hints (("Goal" :in-theory (enable fn-transfer-entryp
                                      fn-transfer-chunk-listp
                                      fn-transfer-at-mostp))))

(defthm fn-transfer-at-mostp-is-length-bound
  (implies (and (true-listp xs) (natp bound))
           (equal (fn-transfer-at-mostp xs bound)
                  (<= (len xs) bound)))
  :hints (("Goal" :induct (fn-transfer-at-mostp xs bound)
           :in-theory (enable fn-transfer-at-mostp))))

(defthm fn-transfer-replace-preserves-true-listp
  (implies (true-listp entries)
           (true-listp
            (fn-transfer-replace-entry-with-chunk label chunk entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunk
                            label chunk entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunk))))

(defthm fn-transfer-replace-preserves-len
  (implies (true-listp entries)
           (equal (len (fn-transfer-replace-entry-with-chunk label chunk entries))
                  (len entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunk
                            label chunk entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunk))))

(defthm fn-transfer-replace-preserves-at-mostp
  (implies (and (true-listp entries) (natp bound))
           (equal (fn-transfer-at-mostp
                   (fn-transfer-replace-entry-with-chunk label chunk entries) bound)
                  (fn-transfer-at-mostp entries bound)))
  :hints (("Goal"
           :use ((:instance fn-transfer-at-mostp-is-length-bound
                            (xs entries))
                 (:instance fn-transfer-at-mostp-is-length-bound
                            (xs (fn-transfer-replace-entry-with-chunk
                                 label chunk entries)))
                 (:instance fn-transfer-replace-preserves-true-listp)
                 (:instance fn-transfer-replace-preserves-len)))))

(defthm fn-transfer-replace-preserves-reserved-bytes
  (implies (consp (fn-transfer-find-entry label entries))
           (equal (fn-transfer-reserved-bytes
                   (fn-transfer-replace-entry-with-chunk label chunk entries))
                  (fn-transfer-reserved-bytes entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunk
                            label chunk entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunk
                               fn-transfer-find-entry
                               fn-transfer-reserved-bytes))))

(defthm fn-transfer-label-absentp-replace
  (equal (fn-transfer-label-absentp
          other
          (fn-transfer-replace-entry-with-chunk label chunk entries))
         (fn-transfer-label-absentp other entries))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunk
                            label chunk entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunk
                               fn-transfer-label-absentp))))

(defthm fn-transfer-replace-preserves-distinct-labels
  (implies (fn-transfer-distinct-labelsp entries)
           (fn-transfer-distinct-labelsp
            (fn-transfer-replace-entry-with-chunk label chunk entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunk
                            label chunk entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunk
                               fn-transfer-distinct-labelsp))))

(defthm fn-transfer-replace-preserves-entriesp
  (implies
   (and (fn-transfer-entriesp entries profile)
        (consp (fn-transfer-find-entry label entries))
        (fn-transfer-entryp
         (fn-transfer-make-entry
          (fn-transfer-entry-label (fn-transfer-find-entry label entries))
          (fn-transfer-entry-length (fn-transfer-find-entry label entries))
          (cons chunk
                (fn-transfer-entry-chunks (fn-transfer-find-entry label entries))))
         profile))
   (fn-transfer-entriesp
    (fn-transfer-replace-entry-with-chunk label chunk entries) profile))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunk
                            label chunk entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunk
                               fn-transfer-find-entry
                               fn-transfer-entriesp))))

(defthm fn-transfer-first-overlap-nil-is-no-overlap
  (implies (and (fn-transfer-chunk-listp chunks declared-length profile)
                (not (fn-transfer-first-overlap chunk chunks)))
           (fn-transfer-no-overlaps-withp chunk chunks))
  :hints (("Goal" :induct (fn-transfer-first-overlap chunk chunks)
           :in-theory (enable fn-transfer-first-overlap
                               fn-transfer-no-overlaps-withp
                               fn-transfer-chunk-listp
                               fn-transfer-chunkp))))

(defthm fn-transfer-chunk-input-and-bounds-is-chunkp
  (implies (and (fn-transfer-chunk-inputp octets profile)
                (natp offset)
                (<= (+ offset (len octets)) declared-length))
           (fn-transfer-chunkp
            (fn-transfer-make-chunk offset octets) declared-length profile))
  :hints (("Goal" :in-theory (enable fn-transfer-chunkp
                                      fn-transfer-make-chunk))))

; This proof-side predicate names exactly the nonempty, nonduplicate,
; nonoverlapping insertion branch of fn-transfer-add-chunk.  It is not a
; second host implementation: it exists only to state the transition normal
; form and is proved against the executable kernel below.
(defun fn-transfer-add-chunk-admissiblep (st label offset octets)
  (let* ((profile (fn-transfer-state-profile st))
         (entry (fn-transfer-find-entry label (fn-transfer-state-entries st))))
    (and (fn-transfer-labelp label profile)
         (fn-transfer-chunk-inputp octets profile)
         (natp offset)
         (consp entry)
         (<= offset (fn-transfer-entry-length entry))
         (<= (+ offset (len octets)) (fn-transfer-entry-length entry))
         (consp octets)
         (not (member-equal (fn-transfer-make-chunk offset octets)
                            (fn-transfer-entry-chunks entry)))
         (not (fn-transfer-first-overlap
               (fn-transfer-make-chunk offset octets)
               (fn-transfer-entry-chunks entry)))
         (not (zp (fn-transfer-max-chunks profile)))
         (fn-transfer-at-mostp
          (fn-transfer-entry-chunks entry)
          (1- (fn-transfer-max-chunks profile))))))

(defthm fn-transfer-find-entry-non-nil-is-consp
  (implies (and (fn-transfer-entriesp entries profile)
                (fn-transfer-find-entry label entries))
           (consp (fn-transfer-find-entry label entries)))
  :hints (("Goal" :induct (fn-transfer-find-entry label entries)
           :in-theory (enable fn-transfer-find-entry
                               fn-transfer-entriesp
                               fn-transfer-entryp))))

(defthm fn-transfer-add-chunk-result-state-normal-form
  (implies (fn-transfer-statep st)
           (equal (fn-transfer-result-state
                   (fn-transfer-add-chunk st label offset octets))
                  (if (fn-transfer-add-chunk-admissiblep st label offset octets)
                      (fn-transfer-make-state
                       (fn-transfer-state-profile st)
                       (fn-transfer-replace-entry-with-chunk
                        label (fn-transfer-make-chunk offset octets)
                        (fn-transfer-state-entries st)))
                    st)))
  :hints (("Goal"
           :use ((:instance fn-transfer-statep-implies-entriesp)
                 (:instance fn-transfer-find-entry-non-nil-is-consp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st))))
           :in-theory (e/d (fn-transfer-add-chunk
                             fn-transfer-add-chunk-admissiblep
                             fn-transfer-result-state)
                            (fn-transfer-statep
                             fn-transfer-entry-candidate
                             fn-transfer-complete-fromp
                             fn-transfer-assemble-from
                             fn-transfer-byte-at)))))

(defthm fn-transfer-replace-entry-preserves-statep
  (implies
   (and (fn-transfer-statep st)
        (consp (fn-transfer-find-entry label (fn-transfer-state-entries st)))
        (fn-transfer-entryp
         (fn-transfer-make-entry
          (fn-transfer-entry-label
           (fn-transfer-find-entry label (fn-transfer-state-entries st)))
          (fn-transfer-entry-length
           (fn-transfer-find-entry label (fn-transfer-state-entries st)))
          (cons chunk
                (fn-transfer-entry-chunks
                 (fn-transfer-find-entry label (fn-transfer-state-entries st)))))
         (fn-transfer-state-profile st)))
   (fn-transfer-statep
    (fn-transfer-make-state
     (fn-transfer-state-profile st)
     (fn-transfer-replace-entry-with-chunk
      label chunk (fn-transfer-state-entries st)))))
  :hints (("Goal"
           :use ((:instance fn-transfer-replace-preserves-entriesp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-replace-preserves-at-mostp
                            (entries (fn-transfer-state-entries st))
                            (bound (fn-transfer-max-reservations
                                    (fn-transfer-state-profile st))))
                 (:instance fn-transfer-replace-preserves-distinct-labels
                            (entries (fn-transfer-state-entries st)))
                 (:instance fn-transfer-replace-preserves-reserved-bytes
                            (entries (fn-transfer-state-entries st)))
                 (:instance fn-transfer-entriesp-implies-true-listp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st))))
           :in-theory (enable fn-transfer-statep))))

(defthm fn-transfer-add-chunk-stored-entryp
  (implies
   (and (fn-transfer-statep st)
        (fn-transfer-labelp label (fn-transfer-state-profile st))
        (fn-transfer-chunk-inputp octets (fn-transfer-state-profile st))
        (natp offset)
        (consp (fn-transfer-find-entry label (fn-transfer-state-entries st)))
        (<= offset
            (fn-transfer-entry-length
             (fn-transfer-find-entry label (fn-transfer-state-entries st))))
        (<= (+ offset (len octets))
            (fn-transfer-entry-length
             (fn-transfer-find-entry label (fn-transfer-state-entries st))))
        (consp octets)
        (not (member-equal
              (fn-transfer-make-chunk offset octets)
              (fn-transfer-entry-chunks
               (fn-transfer-find-entry label (fn-transfer-state-entries st)))))
        (not (fn-transfer-first-overlap
              (fn-transfer-make-chunk offset octets)
              (fn-transfer-entry-chunks
               (fn-transfer-find-entry label (fn-transfer-state-entries st)))))
        (not (zp (fn-transfer-max-chunks
                  (fn-transfer-state-profile st))))
        (fn-transfer-at-mostp
         (fn-transfer-entry-chunks
          (fn-transfer-find-entry label (fn-transfer-state-entries st)))
         (1- (fn-transfer-max-chunks
              (fn-transfer-state-profile st)))))
   (fn-transfer-entryp
    (fn-transfer-make-entry
     (fn-transfer-entry-label
      (fn-transfer-find-entry label (fn-transfer-state-entries st)))
     (fn-transfer-entry-length
      (fn-transfer-find-entry label (fn-transfer-state-entries st)))
     (cons (fn-transfer-make-chunk offset octets)
           (fn-transfer-entry-chunks
            (fn-transfer-find-entry label (fn-transfer-state-entries st)))))
    (fn-transfer-state-profile st)))
  :hints (("Goal"
           :use ((:instance fn-transfer-statep-implies-entriesp)
                 (:instance fn-transfer-find-entry-is-entryp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-entryp-implies-chunk-listp
                            (entry (fn-transfer-find-entry
                                    label (fn-transfer-state-entries st)))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-first-overlap-nil-is-no-overlap
                            (chunk (fn-transfer-make-chunk offset octets))
                            (chunks (fn-transfer-entry-chunks
                                     (fn-transfer-find-entry
                                      label (fn-transfer-state-entries st))))
                            (declared-length
                             (fn-transfer-entry-length
                              (fn-transfer-find-entry
                               label (fn-transfer-state-entries st))))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-chunk-input-and-bounds-is-chunkp
                            (profile (fn-transfer-state-profile st))
                            (declared-length
                             (fn-transfer-entry-length
                              (fn-transfer-find-entry
                               label (fn-transfer-state-entries st)))))
                 (:instance fn-transfer-entry-add-chunk-is-entryp
                            (entry (fn-transfer-find-entry
                                    label (fn-transfer-state-entries st)))
                            (profile (fn-transfer-state-profile st))
                            (chunk (fn-transfer-make-chunk offset octets)))
                 )
           :in-theory nil)))

(defthm fn-transfer-add-chunk-stored-statep
  (implies
   (and (fn-transfer-statep st)
        (fn-transfer-add-chunk-admissiblep st label offset octets))
   (fn-transfer-statep
    (fn-transfer-make-state
     (fn-transfer-state-profile st)
     (fn-transfer-replace-entry-with-chunk
      label (fn-transfer-make-chunk offset octets)
      (fn-transfer-state-entries st)))))
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-stored-entryp)
                 (:instance fn-transfer-replace-entry-preserves-statep
                            (chunk (fn-transfer-make-chunk offset octets)))
                 )
           :in-theory (enable fn-transfer-add-chunk-admissiblep))))

(defthm fn-transfer-add-chunk-preserves-statep
  (implies (fn-transfer-statep st)
           (fn-transfer-statep
            (fn-transfer-result-state
             (fn-transfer-add-chunk st label offset octets))))
  :hints (("Goal"
           :cases ((fn-transfer-add-chunk-admissiblep st label offset octets))
           :use ((:instance fn-transfer-add-chunk-stored-statep)
                 (:instance fn-transfer-add-chunk-result-state-normal-form))
           :in-theory (enable fn-transfer-add-chunk-admissiblep))))

(defthm fn-transfer-add-chunk-preserves-reserved-bytes
  (implies (fn-transfer-statep st)
           (equal (fn-transfer-reserved-bytes
                   (fn-transfer-state-entries
                    (fn-transfer-result-state
                     (fn-transfer-add-chunk st label offset octets))))
                  (fn-transfer-reserved-bytes (fn-transfer-state-entries st))))
  :hints (("Goal"
           :use ((:instance fn-transfer-replace-preserves-reserved-bytes
                            (entries (fn-transfer-state-entries st)))
                 (:instance fn-transfer-add-chunk-preserves-statep))
           :in-theory (enable fn-transfer-add-chunk
                               fn-transfer-result-state))))

(defthm fn-transfer-add-chunk-result-reserved-bytes-bounded
  (implies (fn-transfer-statep st)
           (<= (fn-transfer-reserved-bytes
                (fn-transfer-state-entries
                 (fn-transfer-result-state
                  (fn-transfer-add-chunk st label offset octets))))
               (fn-transfer-capacity (fn-transfer-state-profile st))))
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-preserves-statep))
           :in-theory (enable fn-transfer-statep))))

(defthm fn-transfer-add-chunk-nonadmissible-no-overwrite
  (implies (and (fn-transfer-statep st)
                (not (fn-transfer-add-chunk-admissiblep st label offset octets)))
           (equal (fn-transfer-result-state
                   (fn-transfer-add-chunk st label offset octets))
                  st))
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-result-state-normal-form))
           :in-theory (enable fn-transfer-add-chunk-admissiblep))))

(defthm fn-transfer-add-chunk-refusal-or-conflict-no-overwrite
  (implies (and (fn-transfer-statep st)
                (not (equal (fn-transfer-result-outcome
                             (fn-transfer-add-chunk st label offset octets))
                            :stored)))
           (equal (fn-transfer-result-state
                   (fn-transfer-add-chunk st label offset octets))
                  st))
  :hints (("Goal" :in-theory (enable fn-transfer-add-chunk
                                      fn-transfer-result-outcome
                                      fn-transfer-result-state))))
