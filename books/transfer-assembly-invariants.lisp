; General assembly invariants for the bounded fn transfer staging kernel.
;
; These theorems concern only a well-formed volatile transfer entry.  A
; candidate remains unverified octets: this book makes no claim about a wire
; grammar, content identity, authorization, persistence, receipt, or
; application acceptance.

(in-package "ACL2")
(include-book "transfer")

; A candidate has the sole representation emitted by fn-transfer-entry-candidate.
(defun fn-transfer-candidatep (candidate)
  (and (true-listp candidate)
       (equal (len candidate) 2)
       (equal (car candidate) :candidate)
       (fn-transfer-octet-listp (car (cdr candidate)))))

(defun fn-transfer-candidate-octets (candidate)
  (car (cdr candidate)))

; Missing ranges in this experiment are one-octet requests.  This predicate
; says their positions are exactly the uncovered declared positions.
(defun fn-transfer-missing-ranges-correct-fromp (position declared-length chunks ranges)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length))
      (null ranges)
    (if (fn-transfer-present-atp position chunks)
        (fn-transfer-missing-ranges-correct-fromp
         (1+ position) declared-length chunks ranges)
      (and (consp ranges)
           (equal (car ranges) (list position 1))
           (fn-transfer-missing-ranges-correct-fromp
            (1+ position) declared-length chunks (cdr ranges))))))

(defthm fn-transfer-at-mostp-is-length-bound
  (implies (and (true-listp xs) (natp bound))
           (equal (fn-transfer-at-mostp xs bound)
                  (<= (len xs) bound)))
  :hints (("Goal" :induct (fn-transfer-at-mostp xs bound))))

(defthm fn-transfer-chunk-listp-cdr
  (implies (fn-transfer-chunk-listp (cons chunk chunks) declared-length profile)
           (fn-transfer-chunk-listp chunks declared-length profile))
  :hints (("Goal" :in-theory (enable fn-transfer-chunk-listp))))

(defthm fn-transfer-chunk-listp-head
  (implies (fn-transfer-chunk-listp (cons chunk chunks) declared-length profile)
           (fn-transfer-chunkp chunk declared-length profile))
  :hints (("Goal" :in-theory (enable fn-transfer-chunk-listp))))

(defthm fn-transfer-chunk-listp-member-is-chunkp
  (implies (and (fn-transfer-chunk-listp chunks declared-length profile)
                (member-equal chunk chunks))
           (fn-transfer-chunkp chunk declared-length profile))
  :hints (("Goal" :induct (fn-transfer-chunk-listp chunks declared-length profile)
           :in-theory (enable fn-transfer-chunk-listp))))

(defthm fn-transfer-entriesp-find-entry-is-entryp
  (implies (and (fn-transfer-entriesp entries profile)
                (consp (fn-transfer-find-entry label entries)))
           (fn-transfer-entryp (fn-transfer-find-entry label entries) profile))
  :hints (("Goal" :induct (fn-transfer-find-entry label entries)
           :in-theory (enable fn-transfer-entriesp
                              fn-transfer-find-entry))))

(defthm fn-transfer-octet-listp-nth
  (implies (and (fn-transfer-octet-listp xs)
                (natp index)
                (< index (len xs)))
           (fn-transfer-octetp (nth index xs)))
  :hints (("Goal" :induct (nth index xs)
           :in-theory (enable fn-transfer-octet-listp))))

(defthm fn-transfer-no-overlaps-withp-member
  (implies (and (fn-transfer-no-overlaps-withp chunk chunks)
                (member-equal other chunks))
           (not (fn-transfer-ranges-overlapp chunk other)))
  :hints (("Goal" :induct (fn-transfer-no-overlaps-withp chunk chunks))))

(defthm fn-transfer-ranges-overlapp-symmetric
  (equal (fn-transfer-ranges-overlapp left right)
         (fn-transfer-ranges-overlapp right left))
  :hints (("Goal" :in-theory (enable fn-transfer-ranges-overlapp))))

(defthm fn-transfer-ranges-overlapp-at-common-position
  (implies (and (<= (fn-transfer-chunk-offset left) position)
                (< position (+ (fn-transfer-chunk-offset left)
                               (len (fn-transfer-chunk-octets left))))
                (<= (fn-transfer-chunk-offset right) position)
                (< position (+ (fn-transfer-chunk-offset right)
                               (len (fn-transfer-chunk-octets right)))))
           (fn-transfer-ranges-overlapp left right))
  :hints (("Goal" :in-theory (enable fn-transfer-ranges-overlapp))))

(defthm fn-transfer-chunkp-byte-is-octet
  (implies (and (fn-transfer-chunkp chunk declared-length profile)
                (<= (fn-transfer-chunk-offset chunk) position)
                (< position (+ (fn-transfer-chunk-offset chunk)
                               (len (fn-transfer-chunk-octets chunk)))))
           (fn-transfer-octetp
            (nth (- position (fn-transfer-chunk-offset chunk))
                 (fn-transfer-chunk-octets chunk))))
  :hints (("Goal"
           :use ((:instance fn-transfer-octet-listp-nth
                            (xs (fn-transfer-chunk-octets chunk))
                            (index (- position
                                      (fn-transfer-chunk-offset chunk)))))
           :in-theory (e/d (fn-transfer-chunkp) (fn-transfer-octetp)))))

(defthm fn-transfer-chunk-listp-member-index-in-bounds
  (implies (and (fn-transfer-chunk-listp chunks declared-length profile)
                (member-equal chunk chunks)
                (natp index)
                (< index (len (fn-transfer-chunk-octets chunk))))
           (and (natp (+ (fn-transfer-chunk-offset chunk) index))
                (< (+ (fn-transfer-chunk-offset chunk) index)
                   declared-length)))
  :hints (("Goal"
           :use ((:instance fn-transfer-chunk-listp-member-is-chunkp))
           :in-theory (enable fn-transfer-chunkp))))

(defthm fn-transfer-byte-at-head
  (implies (and (fn-transfer-chunkp chunk declared-length profile)
                (<= (fn-transfer-chunk-offset chunk) position)
                (< position (+ (fn-transfer-chunk-offset chunk)
                               (len (fn-transfer-chunk-octets chunk)))))
           (equal (fn-transfer-byte-at position (cons chunk chunks))
                  (nth (- position (fn-transfer-chunk-offset chunk))
                       (fn-transfer-chunk-octets chunk))))
  :hints (("Goal" :in-theory (enable fn-transfer-byte-at))))

(defthm fn-transfer-byte-at-skips-noncovering-head
  (implies (or (< position (fn-transfer-chunk-offset chunk))
               (<= (+ (fn-transfer-chunk-offset chunk)
                      (len (fn-transfer-chunk-octets chunk)))
                   position))
           (equal (fn-transfer-byte-at position (cons chunk chunks))
                  (fn-transfer-byte-at position chunks)))
  :hints (("Goal" :in-theory (enable fn-transfer-byte-at))))

(defthm fn-transfer-byte-at-octetp
  (implies (and (fn-transfer-chunk-listp chunks declared-length profile)
                (fn-transfer-present-atp position chunks))
           (fn-transfer-octetp (fn-transfer-byte-at position chunks)))
  :hints (("Goal" :induct (fn-transfer-byte-at position chunks)
           :in-theory (e/d (fn-transfer-chunk-listp
                             fn-transfer-present-atp
                             fn-transfer-byte-at)
                            (fn-transfer-octetp))
           :do-not '(generalize fertilize)
           :expand ((fn-transfer-octet-listp
                     (fn-transfer-chunk-octets (car chunks)))))
          ("Subgoal *1/1''"
           :use ((:instance fn-transfer-chunkp-byte-is-octet
                            (chunk (car chunks)))))))

(defthm fn-transfer-assemble-from-length
  (implies (and (natp position)
                (natp declared-length)
                (< position declared-length))
           (equal (len (fn-transfer-assemble-from position declared-length chunks))
                  (- declared-length position)))
  :hints (("Goal" :induct (fn-transfer-assemble-from position declared-length chunks))))

(defun fn-transfer-nat-induct (n)
  (if (zp n)
      nil
    (cons n (fn-transfer-nat-induct (1- n)))))

(defthm fn-transfer-assemble-from-zero-length
  (implies (natp declared-length)
           (equal (len (fn-transfer-assemble-from 0 declared-length chunks))
                  declared-length))
  :hints (("Goal" :induct (fn-transfer-nat-induct declared-length))))

(defun fn-transfer-assemble-from-nth-induct (position index declared-length)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length)
          (equal position index))
      nil
    (fn-transfer-assemble-from-nth-induct (1+ position) index declared-length)))

(defthm fn-transfer-nat-between-next-is-equal
  (implies (and (natp position)
                (natp index)
                (<= position index)
                (< index (1+ position)))
           (equal position index))
  :rule-classes nil)

(defthm fn-transfer-assemble-from-nth
  (implies (and (natp position)
                (natp declared-length)
                (natp index)
                (<= position index)
                (< index declared-length))
           (equal (nth (- index position)
                       (fn-transfer-assemble-from position declared-length chunks))
                  (fn-transfer-byte-at index chunks)))
  :hints (("Goal"
           :induct (fn-transfer-assemble-from-nth-induct
                    position index declared-length)
           :do-not '(generalize fertilize))
          ("Subgoal *1/2.3"
           :use ((:instance fn-transfer-nat-between-next-is-equal)))))

(defthm fn-transfer-assemble-from-octets
  (implies (and (natp position)
                (natp declared-length)
                (<= position declared-length)
                (fn-transfer-chunk-listp chunks declared-length profile)
                (fn-transfer-complete-fromp position declared-length chunks))
           (fn-transfer-octet-listp
            (fn-transfer-assemble-from position declared-length chunks)))
  :hints (("Goal" :induct (fn-transfer-assemble-from position declared-length chunks)
           :in-theory (enable fn-transfer-complete-fromp
                              fn-transfer-octet-listp))))

; Any position supplied by a particular retained chunk reads that chunk's
; byte, even when the chunk appears later in arrival order.
(defthm fn-transfer-byte-at-agrees-with-retained-chunk
  (implies (and (fn-transfer-chunk-listp chunks declared-length profile)
                (member-equal chunk chunks)
                (<= (fn-transfer-chunk-offset chunk) position)
                (< position (+ (fn-transfer-chunk-offset chunk)
                               (len (fn-transfer-chunk-octets chunk)))))
           (equal (fn-transfer-byte-at position chunks)
                  (nth (- position (fn-transfer-chunk-offset chunk))
                       (fn-transfer-chunk-octets chunk))))
  :hints (("Goal"
           :induct (fn-transfer-chunk-listp chunks declared-length profile)
           :in-theory (enable fn-transfer-chunk-listp
                              fn-transfer-present-atp))
          ("Subgoal *1/1''"
           :use ((:instance fn-transfer-no-overlaps-withp-member
                            (chunk (car chunks))
                            (chunks (cdr chunks))
                            (other chunk))
                 (:instance fn-transfer-ranges-overlapp-at-common-position
                            (left (car chunks))
                            (right chunk))))))


; Each index in each retained chunk maps to its declared absolute candidate
; index.  Universally quantifying INDEX states byte-for-byte agreement without
; treating the arrival-order list as a canonical assembly order.
(defthm fn-transfer-assembled-byte-agrees-with-retained-chunk
  (implies (and (natp declared-length)
                (fn-transfer-chunk-listp chunks declared-length profile)
                (member-equal chunk chunks)
                (natp index)
                (< index (len (fn-transfer-chunk-octets chunk))))
           (equal (nth (+ (fn-transfer-chunk-offset chunk) index)
                       (fn-transfer-assemble-from 0 declared-length chunks))
                  (nth index (fn-transfer-chunk-octets chunk))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-transfer-assemble-from-nth
                            (position 0)
                            (index (+ (fn-transfer-chunk-offset chunk) index)))
                 (:instance fn-transfer-byte-at-agrees-with-retained-chunk
                            (position (+ (fn-transfer-chunk-offset chunk) index)))
                 (:instance fn-transfer-chunk-listp-member-index-in-bounds))
           :in-theory (disable fn-transfer-assemble-from-nth
                               fn-transfer-byte-at-agrees-with-retained-chunk
                               fn-transfer-chunk-listp-member-index-in-bounds
                               fn-transfer-assemble-from
                               fn-transfer-byte-at))))

(defthm fn-transfer-missing-from-is-correct
  (implies (and (natp position)
                (natp declared-length)
                (<= position declared-length))
           (fn-transfer-missing-ranges-correct-fromp
            position declared-length chunks
            (fn-transfer-missing-from position declared-length chunks)))
  :hints (("Goal" :induct (fn-transfer-missing-from position declared-length chunks)
           :in-theory (enable fn-transfer-missing-from
                              fn-transfer-missing-ranges-correct-fromp))))

(defthm fn-transfer-missing-ranges-is-correct
  (implies (and (fn-transfer-statep st)
                (consp (fn-transfer-find-entry
                        label (fn-transfer-state-entries st))))
           (fn-transfer-missing-ranges-correct-fromp
            0
            (fn-transfer-entry-length
             (fn-transfer-find-entry label (fn-transfer-state-entries st)))
            (fn-transfer-entry-chunks
             (fn-transfer-find-entry label (fn-transfer-state-entries st)))
            (car (cdr (fn-transfer-missing-ranges st label)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-transfer-missing-from-is-correct
                            (position 0)
                            (declared-length
                             (fn-transfer-entry-length
                              (fn-transfer-find-entry
                               label (fn-transfer-state-entries st))))
                            (chunks
                             (fn-transfer-entry-chunks
                              (fn-transfer-find-entry
                               label (fn-transfer-state-entries st)))))
                 (:instance fn-transfer-entriesp-find-entry-is-entryp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st))))
           :in-theory (enable fn-transfer-missing-ranges
                              fn-transfer-statep))))

; A complete well-formed entry emits exactly its declared number of octets,
; every one an octet.  The following theorem supplies its byte agreement.
(defthm fn-transfer-complete-entry-candidate-correct
  (implies (and (fn-transfer-entryp entry profile)
                (fn-transfer-entry-completep entry))
           (and (fn-transfer-candidatep (fn-transfer-entry-candidate entry))
                (equal (len (fn-transfer-candidate-octets
                             (fn-transfer-entry-candidate entry)))
                       (fn-transfer-entry-length entry))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable fn-transfer-entry-candidate
                              fn-transfer-candidatep
                              fn-transfer-candidate-octets
                              fn-transfer-entry-completep
                              fn-transfer-entryp))))

(defthm fn-transfer-complete-entry-candidate-byte-agreement
  (implies (and (fn-transfer-entryp entry profile)
                (fn-transfer-entry-completep entry)
                (member-equal chunk (fn-transfer-entry-chunks entry))
                (natp index)
                (< index (len (fn-transfer-chunk-octets chunk))))
           (equal
            (nth (+ (fn-transfer-chunk-offset chunk) index)
                 (fn-transfer-candidate-octets
                 (fn-transfer-entry-candidate entry)))
            (nth index (fn-transfer-chunk-octets chunk))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-transfer-assembled-byte-agrees-with-retained-chunk
                            (declared-length (fn-transfer-entry-length entry))
                            (chunks (fn-transfer-entry-chunks entry))))
           :in-theory (enable fn-transfer-entry-candidate
                              fn-transfer-candidate-octets
                              fn-transfer-entryp))))
