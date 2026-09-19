; Structural facts about the transfer store and the reservation transition.
;
; Split out of books/transfer-invariants.lisp (2026-09-19); that book is still
; the top of the chain and its includers see every name unchanged.

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

(defthm fn-transfer-at-mostp-is-length-bound
  (implies (and (true-listp xs) (natp bound))
           (equal (fn-transfer-at-mostp xs bound)
                  (<= (len xs) bound)))
  :hints (("Goal" :induct (fn-transfer-at-mostp xs bound)
           :in-theory (enable fn-transfer-at-mostp))))

(defthm fn-transfer-chunk-listp-implies-true-listp
  (implies (fn-transfer-chunk-listp chunks declared-length profile)
           (true-listp chunks))
  :hints (("Goal" :induct (fn-transfer-chunk-listp chunks declared-length profile)
           :in-theory (enable fn-transfer-chunk-listp))))

(defthm fn-transfer-chunk-listp-head-chunkp
  (implies (and (fn-transfer-chunk-listp chunks declared-length profile)
                (consp chunks))
           (fn-transfer-chunkp (car chunks) declared-length profile))
  :hints (("Goal" :in-theory (enable fn-transfer-chunk-listp))))

(defthm fn-transfer-chunkp-offset-natp
  (implies (fn-transfer-chunkp chunk declared-length profile)
           (natp (fn-transfer-chunk-offset chunk)))
  :hints (("Goal" :in-theory (enable fn-transfer-chunkp))))

(defthm fn-transfer-chunk-input-and-bounds-is-chunkp
  (implies (and (fn-transfer-chunk-inputp octets profile)
                (natp offset)
                (<= (+ offset (len octets)) declared-length))
           (fn-transfer-chunkp
            (fn-transfer-make-chunk offset octets) declared-length profile))
  :hints (("Goal" :in-theory (enable fn-transfer-chunkp
                                      fn-transfer-make-chunk))))
