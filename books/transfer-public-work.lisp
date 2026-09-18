; Public missing-range work accounting for the bounded transfer kernel.
;
; Unlike transfer-work, this book follows the complete public read call:
; state/profile validation, entry lookup, and the declared-position missing
; traversal.  The public function deliberately accepts arbitrary ACL2 values,
; so raw state and query shape are separate bound parameters.

(in-package "ACL2")
(include-book "transfer-work")
(local (include-book "arithmetic/top" :dir :system))

; Results are inherited from transfer-work: (value work).  A work unit is a
; recursive list-cell visit or one primitive predicate/comparison invocation.

(defun fn-transfer-true-list-work (x)
  (if (consp x)
      (let ((tail (fn-transfer-true-list-work (cdr x))))
        (fn-transfer-work-result (fn-transfer-work-value tail)
                                 (1+ (fn-transfer-work-cost tail))))
    (fn-transfer-work-result (null x) 0)))

(defun fn-transfer-at-most-work (xs bound)
  (if (consp xs)
      (if (zp bound)
          (fn-transfer-work-result nil 1)
        (let ((tail (fn-transfer-at-most-work (cdr xs) (1- bound))))
          (fn-transfer-work-result (fn-transfer-work-value tail)
                                   (1+ (fn-transfer-work-cost tail)))))
    (fn-transfer-work-result t 0)))

(defun fn-transfer-octet-list-work (xs)
  (if (consp xs)
      (if (fn-transfer-octetp (car xs))
          (let ((tail (fn-transfer-octet-list-work (cdr xs))))
            (fn-transfer-work-result (fn-transfer-work-value tail)
                                     (+ 1 (fn-transfer-work-cost tail))))
        (fn-transfer-work-result nil 1))
    (fn-transfer-work-result (null xs) 0)))

(defun fn-transfer-profile-work (p)
  (let ((proper (fn-transfer-true-list-work p)))
    (if (not (fn-transfer-work-value proper))
        proper
      (let ((length-work (fn-transfer-len-work p)))
        (if (not (equal (fn-transfer-work-value length-work) 6))
            (fn-transfer-work-result nil
                                     (+ (fn-transfer-work-cost proper)
                                        (fn-transfer-work-cost length-work)
                                        1))
          (fn-transfer-work-result
           (and (natp (fn-transfer-capacity p))
                (natp (fn-transfer-max-object p))
                (natp (fn-transfer-max-chunk p))
                (natp (fn-transfer-max-chunks p))
                (natp (fn-transfer-max-label p))
                (natp (fn-transfer-max-reservations p)))
           (+ 7 (fn-transfer-work-cost proper)
              (fn-transfer-work-cost length-work))))))))

(defun fn-transfer-label-work (label profile)
  (let ((bounded (fn-transfer-at-most-work
                  label (fn-transfer-max-label profile))))
    (if (not (fn-transfer-work-value bounded))
        bounded
      (let ((octets (fn-transfer-octet-list-work label)))
        (fn-transfer-work-result
         (fn-transfer-work-value octets)
         (+ (fn-transfer-work-cost bounded)
            (fn-transfer-work-cost octets)))))))

(defun fn-transfer-chunk-input-work (octets profile)
  (let ((bounded (fn-transfer-at-most-work
                  octets (fn-transfer-max-chunk profile))))
    (if (not (fn-transfer-work-value bounded))
        bounded
      (let ((valid (fn-transfer-octet-list-work octets)))
        (fn-transfer-work-result
         (fn-transfer-work-value valid)
         (+ (fn-transfer-work-cost bounded)
            (fn-transfer-work-cost valid)))))))

(defun fn-transfer-chunk-work (chunk declared-length profile)
  (let ((proper (fn-transfer-true-list-work chunk)))
    (if (not (fn-transfer-work-value proper))
        proper
      (let ((length-work (fn-transfer-len-work chunk)))
        (if (not (equal (fn-transfer-work-value length-work) 2))
            (fn-transfer-work-result nil
              (+ 1 (fn-transfer-work-cost proper)
                 (fn-transfer-work-cost length-work)))
          (if (not (natp (fn-transfer-chunk-offset chunk)))
              (fn-transfer-work-result nil
                (+ 2 (fn-transfer-work-cost proper)
                   (fn-transfer-work-cost length-work)))
            (let ((input (fn-transfer-chunk-input-work
                          (fn-transfer-chunk-octets chunk) profile)))
              (if (not (fn-transfer-work-value input))
                  (fn-transfer-work-result nil
                    (+ 2 (fn-transfer-work-cost proper)
                       (fn-transfer-work-cost length-work)
                       (fn-transfer-work-cost input)))
                (let ((octet-length (fn-transfer-len-work
                                     (fn-transfer-chunk-octets chunk))))
                  (fn-transfer-work-result
                   (<= (+ (fn-transfer-chunk-offset chunk)
                          (fn-transfer-work-value octet-length))
                       declared-length)
                   (+ 3 (fn-transfer-work-cost proper)
                      (fn-transfer-work-cost length-work)
                      (fn-transfer-work-cost input)
                      (fn-transfer-work-cost octet-length))))))))))))

(defun fn-transfer-ranges-overlap-work (left right)
  (let ((right-length (fn-transfer-len-work
                       (fn-transfer-chunk-octets right))))
    (if (not (< (fn-transfer-chunk-offset left)
                (+ (fn-transfer-chunk-offset right)
                   (fn-transfer-work-value right-length))))
        (fn-transfer-work-result nil (+ 1 (fn-transfer-work-cost right-length)))
      (let ((left-length (fn-transfer-len-work
                          (fn-transfer-chunk-octets left))))
        (fn-transfer-work-result
         (< (fn-transfer-chunk-offset right)
            (+ (fn-transfer-chunk-offset left)
               (fn-transfer-work-value left-length)))
         (+ 2 (fn-transfer-work-cost right-length)
            (fn-transfer-work-cost left-length)))))))

(defun fn-transfer-no-overlaps-work (chunk chunks)
  (if (consp chunks)
      (let ((overlap (fn-transfer-ranges-overlap-work chunk (car chunks))))
        (if (fn-transfer-work-value overlap)
            (fn-transfer-work-result nil (fn-transfer-work-cost overlap))
          (let ((tail (fn-transfer-no-overlaps-work chunk (cdr chunks))))
            (fn-transfer-work-result
             (fn-transfer-work-value tail)
             (+ (fn-transfer-work-cost overlap)
                (fn-transfer-work-cost tail))))))
    (fn-transfer-work-result t 0)))

(defun fn-transfer-chunk-list-work (chunks declared-length profile)
  (if (consp chunks)
      (let ((head (fn-transfer-chunk-work (car chunks) declared-length profile)))
        (if (not (fn-transfer-work-value head))
            head
          (let ((separate (fn-transfer-no-overlaps-work (car chunks) (cdr chunks))))
            (if (not (fn-transfer-work-value separate))
                (fn-transfer-work-result nil
                  (+ (fn-transfer-work-cost head)
                     (fn-transfer-work-cost separate)))
              (let ((tail (fn-transfer-chunk-list-work
                           (cdr chunks) declared-length profile)))
                (fn-transfer-work-result
                 (fn-transfer-work-value tail)
                 (+ (fn-transfer-work-cost head)
                    (fn-transfer-work-cost separate)
                    (fn-transfer-work-cost tail))))))))
    (fn-transfer-work-result (null chunks) 0)))

(defun fn-transfer-entry-work (entry profile)
  (let ((proper (fn-transfer-true-list-work entry)))
    (if (not (fn-transfer-work-value proper))
        proper
      (let ((length-work (fn-transfer-len-work entry)))
        (if (not (equal (fn-transfer-work-value length-work) 3))
            (fn-transfer-work-result nil
              (+ 1 (fn-transfer-work-cost proper)
                 (fn-transfer-work-cost length-work)))
          (let ((label (fn-transfer-label-work
                        (fn-transfer-entry-label entry) profile)))
            (if (not (fn-transfer-work-value label))
                (fn-transfer-work-result nil
                  (+ 1 (fn-transfer-work-cost proper)
                     (fn-transfer-work-cost length-work)
                     (fn-transfer-work-cost label)))
              (if (not (natp (fn-transfer-entry-length entry)))
                  (fn-transfer-work-result nil
                    (+ 2 (fn-transfer-work-cost proper)
                       (fn-transfer-work-cost length-work)
                       (fn-transfer-work-cost label)))
                (if (not (<= (fn-transfer-entry-length entry)
                             (fn-transfer-max-object profile)))
                    (fn-transfer-work-result nil
                      (+ 3 (fn-transfer-work-cost proper)
                         (fn-transfer-work-cost length-work)
                         (fn-transfer-work-cost label)))
                  (let ((bounded (fn-transfer-at-most-work
                                  (fn-transfer-entry-chunks entry)
                                  (fn-transfer-max-chunks profile))))
                    (if (not (fn-transfer-work-value bounded))
                        (fn-transfer-work-result nil
                          (+ 3 (fn-transfer-work-cost proper)
                             (fn-transfer-work-cost length-work)
                             (fn-transfer-work-cost label)
                             (fn-transfer-work-cost bounded)))
                      (let ((chunks (fn-transfer-chunk-list-work
                                     (fn-transfer-entry-chunks entry)
                                     (fn-transfer-entry-length entry) profile)))
                        (fn-transfer-work-result
                         (fn-transfer-work-value chunks)
                         (+ 3 (fn-transfer-work-cost proper)
                            (fn-transfer-work-cost length-work)
                            (fn-transfer-work-cost label)
                            (fn-transfer-work-cost bounded)
                            (fn-transfer-work-cost chunks)))))))))))))))

(defun fn-transfer-entries-work (entries profile)
  (if (consp entries)
      (let ((head (fn-transfer-entry-work (car entries) profile)))
        (if (not (fn-transfer-work-value head))
            head
          (let ((tail (fn-transfer-entries-work (cdr entries) profile)))
            (fn-transfer-work-result (fn-transfer-work-value tail)
              (+ (fn-transfer-work-cost head) (fn-transfer-work-cost tail))))))
    (fn-transfer-work-result (null entries) 0)))

(defun fn-transfer-equal-work (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (if (consp right)
          (let ((head (fn-transfer-equal-work (car left) (car right))))
            (if (fn-transfer-work-value head)
                (let ((tail (fn-transfer-equal-work (cdr left) (cdr right))))
                  (fn-transfer-work-result
                   (fn-transfer-work-value tail)
                   (+ 1 (fn-transfer-work-cost head)
                      (fn-transfer-work-cost tail))))
              (fn-transfer-work-result nil
                                       (1+ (fn-transfer-work-cost head)))))
        (fn-transfer-work-result nil 1))
    (fn-transfer-work-result (equal left right) 1)))

; This worker follows ACL2 EQUAL's recursive cons comparison, charging every
; compared structural node.  Numeric length checks elsewhere remain unit-cost
; arithmetic operations under the model stated in the specification.
(defun fn-transfer-label-absent-work (label entries)
  (if (consp entries)
      (let ((match (fn-transfer-equal-work
                    label (fn-transfer-entry-label (car entries)))))
        (if (fn-transfer-work-value match)
            (fn-transfer-work-result nil (fn-transfer-work-cost match))
          (let ((tail (fn-transfer-label-absent-work label (cdr entries))))
            (fn-transfer-work-result (fn-transfer-work-value tail)
              (+ (fn-transfer-work-cost match)
                 (fn-transfer-work-cost tail))))))
    (fn-transfer-work-result t 0)))

(defun fn-transfer-distinct-labels-work (entries)
  (if (consp entries)
      (let ((absent (fn-transfer-label-absent-work
                     (fn-transfer-entry-label (car entries)) (cdr entries))))
        (if (not (fn-transfer-work-value absent))
            absent
          (let ((tail (fn-transfer-distinct-labels-work (cdr entries))))
            (fn-transfer-work-result (fn-transfer-work-value tail)
              (+ (fn-transfer-work-cost absent) (fn-transfer-work-cost tail))))))
    (fn-transfer-work-result t 0)))

(defun fn-transfer-reserved-bytes-work (entries)
  (if (consp entries)
      (let ((tail (fn-transfer-reserved-bytes-work (cdr entries))))
        (fn-transfer-work-result
         (+ (fn-transfer-entry-length (car entries))
            (fn-transfer-work-value tail))
         (1+ (fn-transfer-work-cost tail))))
    (fn-transfer-work-result 0 0)))

(defun fn-transfer-state-work (st)
  (let ((proper (fn-transfer-true-list-work st)))
    (if (not (fn-transfer-work-value proper))
        proper
      (let ((length-work (fn-transfer-len-work st)))
        (if (not (equal (fn-transfer-work-value length-work) 2))
            (fn-transfer-work-result nil
              (+ 1 (fn-transfer-work-cost proper) (fn-transfer-work-cost length-work)))
          (let ((profile (fn-transfer-profile-work (fn-transfer-state-profile st))))
            (if (not (fn-transfer-work-value profile))
                (fn-transfer-work-result nil
                  (+ 1 (fn-transfer-work-cost proper) (fn-transfer-work-cost length-work)
                     (fn-transfer-work-cost profile)))
              (let ((bounded (fn-transfer-at-most-work
                              (fn-transfer-state-entries st)
                              (fn-transfer-max-reservations
                               (fn-transfer-state-profile st)))))
                (if (not (fn-transfer-work-value bounded))
                    (fn-transfer-work-result nil
                      (+ 1 (fn-transfer-work-cost proper) (fn-transfer-work-cost length-work)
                         (fn-transfer-work-cost profile) (fn-transfer-work-cost bounded)))
                  (let ((entries (fn-transfer-entries-work
                                  (fn-transfer-state-entries st)
                                  (fn-transfer-state-profile st))))
                    (if (not (fn-transfer-work-value entries))
                        (fn-transfer-work-result nil
                          (+ 1 (fn-transfer-work-cost proper) (fn-transfer-work-cost length-work)
                             (fn-transfer-work-cost profile) (fn-transfer-work-cost bounded)
                             (fn-transfer-work-cost entries)))
                      (let ((distinct (fn-transfer-distinct-labels-work
                                       (fn-transfer-state-entries st))))
                        (if (not (fn-transfer-work-value distinct))
                            (fn-transfer-work-result nil
                              (+ 1 (fn-transfer-work-cost proper) (fn-transfer-work-cost length-work)
                                 (fn-transfer-work-cost profile) (fn-transfer-work-cost bounded)
                                 (fn-transfer-work-cost entries)
                                 (fn-transfer-work-cost distinct)))
                          (let ((reserved (fn-transfer-reserved-bytes-work
                                           (fn-transfer-state-entries st))))
                            (fn-transfer-work-result
                             (<= (fn-transfer-work-value reserved)
                                 (fn-transfer-capacity (fn-transfer-state-profile st)))
                             (+ 2 (fn-transfer-work-cost proper)
                                (fn-transfer-work-cost length-work)
                                (fn-transfer-work-cost profile)
                                (fn-transfer-work-cost bounded)
                                (fn-transfer-work-cost entries)
                                (fn-transfer-work-cost distinct)
                                (fn-transfer-work-cost reserved)))))))))))))))))

(defun fn-transfer-find-entry-work (label entries)
  (if (consp entries)
      (let ((match (fn-transfer-equal-work
                    label (fn-transfer-entry-label (car entries)))))
        (if (fn-transfer-work-value match)
            (fn-transfer-work-result (car entries)
                                     (fn-transfer-work-cost match))
          (let ((tail (fn-transfer-find-entry-work label (cdr entries))))
            (fn-transfer-work-result (fn-transfer-work-value tail)
              (+ (fn-transfer-work-cost match)
                 (fn-transfer-work-cost tail))))))
    (fn-transfer-work-result nil 0)))

(defun fn-transfer-missing-ranges-work (st label)
  (let ((state (fn-transfer-state-work st)))
    (if (not (fn-transfer-work-value state))
        (fn-transfer-work-result (list :error :invalid-state)
                                 (fn-transfer-work-cost state))
      (let ((entry (fn-transfer-find-entry-work
                    label (fn-transfer-state-entries st))))
        (if (not (fn-transfer-work-value entry))
            (fn-transfer-work-result (list :error :unknown-label)
                                     (+ (fn-transfer-work-cost state)
                                        (fn-transfer-work-cost entry)))
          (let ((missing (fn-transfer-missing-from-work
                          0
                          (fn-transfer-entry-length (fn-transfer-work-value entry))
                          (fn-transfer-entry-chunks (fn-transfer-work-value entry)))))
            (fn-transfer-work-result
             (list :ok (fn-transfer-work-value missing))
             (+ (fn-transfer-work-cost state)
                (fn-transfer-work-cost entry)
                (fn-transfer-work-cost missing)))))))))

; Value-projection theorem tranche.  Certification is intentionally deferred
; during the integrated shared-certification hold.

(defthm fn-transfer-true-list-work-value
  (equal (fn-transfer-work-value (fn-transfer-true-list-work x))
         (true-listp x))
  :hints (("Goal" :induct (fn-transfer-true-list-work x)
           :in-theory (enable fn-transfer-true-list-work
                               fn-transfer-work-value))))

(defthm fn-transfer-at-most-work-value
  (equal (fn-transfer-work-value (fn-transfer-at-most-work xs bound))
         (fn-transfer-at-mostp xs bound))
  :hints (("Goal" :induct (fn-transfer-at-most-work xs bound)
           :in-theory (enable fn-transfer-at-most-work
                               fn-transfer-at-mostp
                               fn-transfer-work-value))))

(defthm fn-transfer-octet-list-work-value
  (equal (fn-transfer-work-value (fn-transfer-octet-list-work xs))
         (fn-transfer-octet-listp xs))
  :hints (("Goal" :induct (fn-transfer-octet-list-work xs)
           :in-theory (enable fn-transfer-octet-list-work
                               fn-transfer-octet-listp
                               fn-transfer-work-value))))

(defthm fn-transfer-true-list-work-car-value
  (equal (car (fn-transfer-true-list-work x)) (true-listp x))
  :hints (("Goal" :use ((:instance fn-transfer-true-list-work-value)))))

(defthm fn-transfer-at-most-work-car-value
  (equal (car (fn-transfer-at-most-work xs bound))
         (fn-transfer-at-mostp xs bound))
  :hints (("Goal" :use ((:instance fn-transfer-at-most-work-value)))))

(defthm fn-transfer-octet-list-work-car-value
  (equal (car (fn-transfer-octet-list-work xs))
         (fn-transfer-octet-listp xs))
  :hints (("Goal" :use ((:instance fn-transfer-octet-list-work-value)))))

(defthm fn-transfer-profile-work-value
  (equal (fn-transfer-work-value (fn-transfer-profile-work p))
         (fn-transfer-profilep p))
  :hints (("Goal" :in-theory (enable fn-transfer-profile-work
                                      fn-transfer-profilep
                                      fn-transfer-work-value))))

(defthm fn-transfer-label-work-value
  (equal (fn-transfer-work-value (fn-transfer-label-work label profile))
         (fn-transfer-labelp label profile))
  :hints (("Goal" :in-theory (enable fn-transfer-label-work
                                      fn-transfer-labelp
                                      fn-transfer-work-value))))

(defthm fn-transfer-chunk-input-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-chunk-input-work octets profile))
         (fn-transfer-chunk-inputp octets profile))
  :hints (("Goal" :in-theory (enable fn-transfer-chunk-input-work
                                      fn-transfer-chunk-inputp
                                      fn-transfer-work-value))))

(defthm fn-transfer-chunk-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-chunk-work chunk declared-length profile))
         (fn-transfer-chunkp chunk declared-length profile))
  :hints (("Goal" :in-theory (enable fn-transfer-chunk-work
                                      fn-transfer-chunkp
                                      fn-transfer-work-value))))

(defthm fn-transfer-ranges-overlap-work-value
  (equal (fn-transfer-work-value (fn-transfer-ranges-overlap-work left right))
         (fn-transfer-ranges-overlapp left right))
  :hints (("Goal" :in-theory (enable fn-transfer-ranges-overlap-work
                                      fn-transfer-ranges-overlapp
                                      fn-transfer-work-value))))

(defthm fn-transfer-no-overlaps-work-value
  (equal (fn-transfer-work-value (fn-transfer-no-overlaps-work chunk chunks))
         (fn-transfer-no-overlaps-withp chunk chunks))
  :hints (("Goal" :induct (fn-transfer-no-overlaps-work chunk chunks)
           :in-theory (enable fn-transfer-no-overlaps-work
                               fn-transfer-no-overlaps-withp
                               fn-transfer-work-value))))

(defthm fn-transfer-chunk-list-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-chunk-list-work chunks declared-length profile))
         (fn-transfer-chunk-listp chunks declared-length profile))
  :hints (("Goal" :induct (fn-transfer-chunk-list-work
                            chunks declared-length profile)
           :in-theory (enable fn-transfer-chunk-list-work
                               fn-transfer-chunk-listp
                               fn-transfer-work-value))))

(defthm fn-transfer-chunk-list-work-car-value
  (equal (car (fn-transfer-chunk-list-work chunks declared-length profile))
         (fn-transfer-chunk-listp chunks declared-length profile))
  :hints (("Goal" :use ((:instance fn-transfer-chunk-list-work-value)))))

(defthm fn-transfer-entry-work-value
  (equal (fn-transfer-work-value (fn-transfer-entry-work entry profile))
         (fn-transfer-entryp entry profile))
  :hints (("Goal" :in-theory (enable fn-transfer-entry-work
                                      fn-transfer-entryp
                                      fn-transfer-work-value))))

(defthm fn-transfer-entries-work-value
  (equal (fn-transfer-work-value (fn-transfer-entries-work entries profile))
         (fn-transfer-entriesp entries profile))
  :hints (("Goal" :induct (fn-transfer-entries-work entries profile)
           :in-theory (enable fn-transfer-entries-work
                               fn-transfer-entriesp
                               fn-transfer-work-value))))

(defthm fn-transfer-entries-work-car-value
  (equal (car (fn-transfer-entries-work entries profile))
         (fn-transfer-entriesp entries profile))
  :hints (("Goal" :use ((:instance fn-transfer-entries-work-value)))))

(defthm fn-transfer-equal-work-value
  (equal (fn-transfer-work-value (fn-transfer-equal-work left right))
         (equal left right))
  :hints (("Goal" :induct (fn-transfer-equal-work left right)
           :in-theory (enable fn-transfer-equal-work
                               fn-transfer-work-value))))

(defthm fn-transfer-equal-work-car-value
  (equal (car (fn-transfer-equal-work left right)) (equal left right))
  :hints (("Goal" :use ((:instance fn-transfer-equal-work-value)))))

(defthm fn-transfer-label-absent-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-label-absent-work label entries))
         (fn-transfer-label-absentp label entries))
  :hints (("Goal" :induct (fn-transfer-label-absent-work label entries)
           :in-theory (enable fn-transfer-label-absent-work
                               fn-transfer-label-absentp
                               fn-transfer-work-value))))

(defthm fn-transfer-distinct-labels-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-distinct-labels-work entries))
         (fn-transfer-distinct-labelsp entries))
  :hints (("Goal" :induct (fn-transfer-distinct-labels-work entries)
           :in-theory (enable fn-transfer-distinct-labels-work
                               fn-transfer-distinct-labelsp
                               fn-transfer-work-value))))

(defthm fn-transfer-distinct-labels-work-car-value
  (equal (car (fn-transfer-distinct-labels-work entries))
         (fn-transfer-distinct-labelsp entries))
  :hints (("Goal" :use ((:instance fn-transfer-distinct-labels-work-value)))))

(defthm fn-transfer-reserved-bytes-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-reserved-bytes-work entries))
         (fn-transfer-reserved-bytes entries))
  :hints (("Goal" :induct (fn-transfer-reserved-bytes-work entries)
           :in-theory (enable fn-transfer-reserved-bytes-work
                               fn-transfer-reserved-bytes
                               fn-transfer-work-value))))

(defthm fn-transfer-reserved-bytes-work-car-value
  (equal (car (fn-transfer-reserved-bytes-work entries))
         (fn-transfer-reserved-bytes entries))
  :hints (("Goal" :use ((:instance fn-transfer-reserved-bytes-work-value)))))

(defthm fn-transfer-state-work-value
  (equal (fn-transfer-work-value (fn-transfer-state-work st))
         (fn-transfer-statep st))
  :hints (("Goal" :in-theory (enable fn-transfer-state-work
                                      fn-transfer-statep
                                      fn-transfer-work-value))))

(defthm fn-transfer-find-entry-work-value
  (equal (fn-transfer-work-value (fn-transfer-find-entry-work label entries))
         (fn-transfer-find-entry label entries))
  :hints (("Goal" :induct (fn-transfer-find-entry-work label entries)
           :in-theory (enable fn-transfer-find-entry-work
                               fn-transfer-find-entry
                               fn-transfer-work-value))))

(defthm fn-transfer-find-entry-work-car-value
  (equal (car (fn-transfer-find-entry-work label entries))
         (fn-transfer-find-entry label entries))
  :hints (("Goal" :use ((:instance fn-transfer-find-entry-work-value)))))

(defthm fn-transfer-missing-ranges-work-value
  (equal (fn-transfer-work-value (fn-transfer-missing-ranges-work st label))
         (fn-transfer-missing-ranges st label))
  :hints (("Goal" :in-theory (enable fn-transfer-missing-ranges-work
                                      fn-transfer-missing-ranges
                                      fn-transfer-work-value))))
