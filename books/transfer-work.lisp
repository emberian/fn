; Work bounds for the executable bounded transfer assembly hot paths.
; Costs count recursive list-cell inspections in the logical ACL2 execution of
; length, nth, chunk scans, and declared-position walks.  They do not model
; host bignum bit complexity, allocation, GC, cache behavior, persistence, or
; input/state validation before a valid entry reaches these hot paths.

(in-package "ACL2")
(include-book "transfer")
(local (include-book "arithmetic/top" :dir :system))

; A costed result is (value work), with a natural-number unit count.
(defun fn-transfer-work-result (value work) (list value work))
(defun fn-transfer-work-value (result) (car result))
(defun fn-transfer-work-cost (result) (car (cdr result)))

; -----------------------------------------------------------------------------
; Costed list primitives.  Their values are the exact ACL2 LEN/NTH values.

(defun fn-transfer-len-work (xs)
  (if (consp xs)
      (let ((tail (fn-transfer-len-work (cdr xs))))
        (fn-transfer-work-result
         (1+ (fn-transfer-work-value tail))
         (1+ (fn-transfer-work-cost tail))))
    (fn-transfer-work-result 0 0)))

(defun fn-transfer-nth-work (n xs)
  (if (or (zp n) (not (consp xs)))
      (fn-transfer-work-result (car xs) 0)
    (let ((tail (fn-transfer-nth-work (1- n) (cdr xs))))
      (fn-transfer-work-result (fn-transfer-work-value tail)
                               (1+ (fn-transfer-work-cost tail))))))

; -----------------------------------------------------------------------------
; Costed versions of the two per-position chunk scans.

(defun fn-transfer-present-at-work (position chunks)
  (if (consp chunks)
      (let* ((chunk (car chunks))
             (length-work (fn-transfer-len-work
                           (fn-transfer-chunk-octets chunk))))
        (if (and (<= (fn-transfer-chunk-offset chunk) position)
                 (< position
                    (+ (fn-transfer-chunk-offset chunk)
                       (fn-transfer-work-value length-work))))
            (fn-transfer-work-result t
                                     (1+ (fn-transfer-work-cost length-work)))
          (let ((tail (fn-transfer-present-at-work position (cdr chunks))))
            (fn-transfer-work-result
             (fn-transfer-work-value tail)
             (+ 1 (fn-transfer-work-cost length-work)
                (fn-transfer-work-cost tail))))))
    (fn-transfer-work-result nil 0)))

(defun fn-transfer-byte-at-work (position chunks)
  (if (consp chunks)
      (let* ((chunk (car chunks))
             (octets (fn-transfer-chunk-octets chunk))
             (length-work (fn-transfer-len-work octets)))
        (if (and (<= (fn-transfer-chunk-offset chunk) position)
                 (< position
                    (+ (fn-transfer-chunk-offset chunk)
                       (fn-transfer-work-value length-work))))
            (let ((nth-work (fn-transfer-nth-work
                             (- position (fn-transfer-chunk-offset chunk))
                             octets)))
              (fn-transfer-work-result
               (fn-transfer-work-value nth-work)
               (+ 1 (fn-transfer-work-cost length-work)
                  (fn-transfer-work-cost nth-work))))
          (let ((tail (fn-transfer-byte-at-work position (cdr chunks))))
            (fn-transfer-work-result
             (fn-transfer-work-value tail)
             (+ 1 (fn-transfer-work-cost length-work)
                (fn-transfer-work-cost tail))))))
    (fn-transfer-work-result nil 0)))

; -----------------------------------------------------------------------------
; Costed copies of the frozen declared-position walks.

(defun fn-transfer-complete-from-work (position declared-length chunks)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length))
      (fn-transfer-work-result t 0)
    (let ((present (fn-transfer-present-at-work position chunks)))
      (if (not (fn-transfer-work-value present))
          (fn-transfer-work-result nil (fn-transfer-work-cost present))
        (let ((tail (fn-transfer-complete-from-work
                     (1+ position) declared-length chunks)))
          (fn-transfer-work-result
           (fn-transfer-work-value tail)
           (+ (fn-transfer-work-cost present)
              (fn-transfer-work-cost tail))))))))

(defun fn-transfer-assemble-from-work (position declared-length chunks)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length))
      (fn-transfer-work-result nil 0)
    (let* ((byte (fn-transfer-byte-at-work position chunks))
           (tail (fn-transfer-assemble-from-work
                  (1+ position) declared-length chunks)))
      (fn-transfer-work-result
       (cons (fn-transfer-work-value byte)
             (fn-transfer-work-value tail))
       (+ (fn-transfer-work-cost byte)
          (fn-transfer-work-cost tail))))))

(defun fn-transfer-entry-candidate-work (entry)
  (let ((complete (fn-transfer-complete-from-work
                   0 (fn-transfer-entry-length entry)
                   (fn-transfer-entry-chunks entry))))
    (if (fn-transfer-work-value complete)
        (let ((assembled (fn-transfer-assemble-from-work
                          0 (fn-transfer-entry-length entry)
                          (fn-transfer-entry-chunks entry))))
          (fn-transfer-work-result
           (list :candidate (fn-transfer-work-value assembled))
           (+ (fn-transfer-work-cost complete)
              (fn-transfer-work-cost assembled))))
      (fn-transfer-work-result nil (fn-transfer-work-cost complete)))))

(defun fn-transfer-missing-from-work (position declared-length chunks)
  (declare (xargs :measure (nfix (- declared-length position))))
  (if (or (not (natp position))
          (not (natp declared-length))
          (>= position declared-length))
      (fn-transfer-work-result nil 0)
    (let* ((present (fn-transfer-present-at-work position chunks))
           (tail (fn-transfer-missing-from-work
                  (1+ position) declared-length chunks)))
      (if (fn-transfer-work-value present)
          (fn-transfer-work-result
           (fn-transfer-work-value tail)
           (+ (fn-transfer-work-cost present)
              (fn-transfer-work-cost tail)))
        (fn-transfer-work-result
         (cons (list position 1) (fn-transfer-work-value tail))
         (+ (fn-transfer-work-cost present)
            (fn-transfer-work-cost tail)))))))

; -----------------------------------------------------------------------------
; Exact projections to the frozen executable values.

(defthm fn-transfer-len-work-value
  (equal (fn-transfer-work-value (fn-transfer-len-work xs)) (len xs))
  :hints (("Goal" :induct (fn-transfer-len-work xs)
           :in-theory (enable fn-transfer-len-work
                               fn-transfer-work-value))))

(defthm fn-transfer-nth-work-value
  (equal (fn-transfer-work-value (fn-transfer-nth-work n xs)) (nth n xs))
  :hints (("Goal" :induct (fn-transfer-nth-work n xs)
           :in-theory (enable fn-transfer-nth-work
                               fn-transfer-work-value))))

(defthm fn-transfer-present-at-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-present-at-work position chunks))
         (fn-transfer-present-atp position chunks))
  :hints (("Goal" :induct (fn-transfer-present-at-work position chunks)
           :in-theory (enable fn-transfer-present-at-work
                               fn-transfer-present-atp
                               fn-transfer-work-value))))

(defthm fn-transfer-byte-at-work-value
  (equal (fn-transfer-work-value (fn-transfer-byte-at-work position chunks))
         (fn-transfer-byte-at position chunks))
  :hints (("Goal" :induct (fn-transfer-byte-at-work position chunks)
           :in-theory (enable fn-transfer-byte-at-work
                               fn-transfer-byte-at
                               fn-transfer-work-value))))

(defthm fn-transfer-complete-from-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-complete-from-work position declared-length chunks))
         (fn-transfer-complete-fromp position declared-length chunks))
  :hints (("Goal" :induct (fn-transfer-complete-from-work
                            position declared-length chunks)
           :in-theory (enable fn-transfer-complete-from-work
                               fn-transfer-complete-fromp
                               fn-transfer-work-value))))

(defthm fn-transfer-assemble-from-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-assemble-from-work position declared-length chunks))
         (fn-transfer-assemble-from position declared-length chunks))
  :hints (("Goal" :induct (fn-transfer-assemble-from-work
                            position declared-length chunks)
           :in-theory (enable fn-transfer-assemble-from-work
                               fn-transfer-assemble-from
                               fn-transfer-work-value))))

(defthm fn-transfer-entry-candidate-work-value
  (equal (fn-transfer-work-value (fn-transfer-entry-candidate-work entry))
         (fn-transfer-entry-candidate entry))
  :hints (("Goal" :in-theory (enable fn-transfer-entry-candidate-work
                                      fn-transfer-entry-candidate
                                      fn-transfer-work-value))))

(defthm fn-transfer-missing-from-work-value
  (equal (fn-transfer-work-value
          (fn-transfer-missing-from-work position declared-length chunks))
         (fn-transfer-missing-from position declared-length chunks))
  :hints (("Goal" :induct (fn-transfer-missing-from-work
                            position declared-length chunks)
           :in-theory (enable fn-transfer-missing-from-work
                               fn-transfer-missing-from
                               fn-transfer-work-value))))

; -----------------------------------------------------------------------------
; Cost bounds.  Each chunk inspection recomputes LEN on that chunk, matching
; the frozen scan definitions.  The unit bound below is parameterized by the
; maximum stored chunk byte length rather than treating a storage cap as work.

(defun fn-transfer-chunks-at-most-lengthp (chunks maximum)
  (if (consp chunks)
      (and (true-listp (fn-transfer-chunk-octets (car chunks)))
           (<= (len (fn-transfer-chunk-octets (car chunks))) maximum)
           (fn-transfer-chunks-at-most-lengthp (cdr chunks) maximum))
    t))

(defthm fn-transfer-chunks-at-most-lengthp-head-true-listp
  (implies (and (consp chunks)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (true-listp (fn-transfer-chunk-octets (car chunks))))
  :hints (("Goal" :in-theory (enable fn-transfer-chunks-at-most-lengthp))))

(defthm fn-transfer-chunks-at-most-lengthp-head-bound
  (implies (and (consp chunks)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (len (fn-transfer-chunk-octets (car chunks))) maximum))
  :hints (("Goal" :in-theory (enable fn-transfer-chunks-at-most-lengthp))))

(defthm fn-transfer-len-work-cost
  (equal (fn-transfer-work-cost (fn-transfer-len-work xs)) (len xs))
  :hints (("Goal" :induct (fn-transfer-len-work xs)
           :in-theory (enable fn-transfer-len-work
                               fn-transfer-work-cost))))

(defthm fn-transfer-nth-work-cost-bound
  (implies (true-listp xs)
           (<= (fn-transfer-work-cost (fn-transfer-nth-work n xs))
               (len xs)))
  :hints (("Goal" :induct (fn-transfer-nth-work n xs)
           :in-theory (enable fn-transfer-nth-work
                               fn-transfer-work-cost))))

(defthm fn-transfer-nth-work-cadr-bound
  (<= (cadr (fn-transfer-nth-work n xs)) (len xs))
  :hints (("Goal" :induct (fn-transfer-nth-work n xs)
           :in-theory (enable fn-transfer-nth-work))))

(defthm fn-transfer-nth-work-cadr-exact
  (equal (cadr (fn-transfer-nth-work n xs))
         (min (nfix n) (len xs)))
  :hints (("Goal" :induct (fn-transfer-nth-work n xs)
           :in-theory (enable fn-transfer-nth-work))))

(defthm fn-transfer-present-at-work-cost-bound
  (implies (and (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-present-at-work position chunks))
               (* (len chunks) (1+ maximum))))
  :hints (("Goal" :induct (fn-transfer-present-at-work position chunks)
           :in-theory (enable fn-transfer-present-at-work
                               fn-transfer-work-cost
                               fn-transfer-chunks-at-most-lengthp))))

(defthm fn-transfer-present-at-work-cadr-cost-bound
  (implies (and (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (cadr (fn-transfer-present-at-work position chunks))
               (* (len chunks) (1+ maximum))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-present-at-work-cost-bound)))))

(defthm fn-transfer-byte-at-work-cost-bound
  (implies (and (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-byte-at-work position chunks))
               (* (1+ (len chunks)) (1+ maximum))))
  :hints (("Goal" :induct (fn-transfer-byte-at-work position chunks)
           :in-theory (enable fn-transfer-byte-at-work
                               fn-transfer-work-cost
                               fn-transfer-nth-work-cadr-bound
                               fn-transfer-nth-work-cadr-exact
                               fn-transfer-chunks-at-most-lengthp))))

(defthm fn-transfer-byte-at-work-cadr-cost-bound
  (implies (and (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (cadr (fn-transfer-byte-at-work position chunks))
               (* (1+ (len chunks)) (1+ maximum))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-byte-at-work-cost-bound)))))

; The remaining budget counts one bounded chunk scan for each declared
; position still to visit.  It is an executable arithmetic expression, used
; as a proved upper bound rather than returned by the frozen functions.
(defun fn-transfer-position-work-budget (position declared-length scan-cost)
  (* (nfix (- declared-length position)) (nfix scan-cost)))

(defthm fn-transfer-position-work-budget-step
  (implies (and (natp position)
                (natp declared-length)
                (natp scan-cost)
                (< position declared-length))
           (equal (fn-transfer-position-work-budget
                   position declared-length scan-cost)
                  (+ scan-cost
                     (fn-transfer-position-work-budget
                      (1+ position) declared-length scan-cost))))
  :hints (("Goal" :in-theory (enable fn-transfer-position-work-budget))))

(defthm fn-transfer-position-work-budget-zero
  (implies (and (natp position)
                (natp declared-length)
                (<= declared-length position))
           (equal (fn-transfer-position-work-budget
                   position declared-length scan-cost)
                  0))
  :hints (("Goal" :in-theory (enable fn-transfer-position-work-budget))))

(defthm fn-transfer-position-work-budget-natp
  (natp (fn-transfer-position-work-budget
         position declared-length scan-cost))
  :hints (("Goal" :in-theory (enable fn-transfer-position-work-budget))))

(defthm fn-transfer-position-work-budget-nonnegative
  (<= 0 (fn-transfer-position-work-budget
         position declared-length scan-cost))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-transfer-position-work-budget))))

(defthm fn-transfer-present-at-work-cost-natp
  (natp (fn-transfer-work-cost
         (fn-transfer-present-at-work position chunks)))
  :hints (("Goal" :induct (fn-transfer-present-at-work position chunks)
           :in-theory (enable fn-transfer-present-at-work
                               fn-transfer-work-cost))))

(defthm fn-transfer-byte-at-work-cost-natp
  (natp (fn-transfer-work-cost
         (fn-transfer-byte-at-work position chunks)))
  :hints (("Goal" :induct (fn-transfer-byte-at-work position chunks)
           :in-theory (enable fn-transfer-byte-at-work
                               fn-transfer-work-cost))))

(defthm fn-transfer-complete-from-work-cost-bound
  (implies (and (natp position)
                (natp declared-length)
                (<= position declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-complete-from-work
                 position declared-length chunks))
               (fn-transfer-position-work-budget
                position declared-length
                (* (1+ (len chunks)) (1+ maximum)))))
  :hints (("Goal"
           :induct (fn-transfer-complete-from-work
                    position declared-length chunks)
           :in-theory (e/d (fn-transfer-complete-from-work
                             fn-transfer-work-cost
                             fn-transfer-present-at-work-cadr-cost-bound
                             fn-transfer-position-work-budget-step
                             fn-transfer-position-work-budget-zero
                             fn-transfer-position-work-budget-natp)
                            (fn-transfer-position-work-budget)))
          ("Subgoal *1/3.1"
           :use ((:instance fn-transfer-present-at-work-cadr-cost-bound)))
          ("Subgoal *1/2''"
           :use ((:instance fn-transfer-present-at-work-cadr-cost-bound)))))

(defthm fn-transfer-assemble-from-work-cost-bound
  (implies (and (natp position)
                (natp declared-length)
                (<= position declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-assemble-from-work
                 position declared-length chunks))
               (fn-transfer-position-work-budget
                position declared-length
                (* (1+ (len chunks)) (1+ maximum)))))
  :hints (("Goal"
           :induct (fn-transfer-assemble-from-work
                    position declared-length chunks)
           :in-theory (e/d (fn-transfer-assemble-from-work
                             fn-transfer-work-cost
                             fn-transfer-byte-at-work-cadr-cost-bound
                             fn-transfer-position-work-budget-step
                             fn-transfer-position-work-budget-zero)
                            (fn-transfer-position-work-budget)))
          ("Subgoal *1/2.1"
           :use ((:instance fn-transfer-byte-at-work-cadr-cost-bound)))))

(defthm fn-transfer-missing-from-work-cost-bound
  (implies (and (natp position)
                (natp declared-length)
                (<= position declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-missing-from-work
                 position declared-length chunks))
               (fn-transfer-position-work-budget
                position declared-length
                (* (1+ (len chunks)) (1+ maximum)))))
  :hints (("Goal"
           :induct (fn-transfer-missing-from-work
                    position declared-length chunks)
           :in-theory (e/d (fn-transfer-missing-from-work
                             fn-transfer-work-cost
                             fn-transfer-present-at-work-cadr-cost-bound
                             fn-transfer-position-work-budget-step
                             fn-transfer-position-work-budget-zero)
                            (fn-transfer-position-work-budget)))
          ("Subgoal *1/3.1"
           :use ((:instance fn-transfer-present-at-work-cadr-cost-bound)))
          ("Subgoal *1/2.1"
           :use ((:instance fn-transfer-present-at-work-cadr-cost-bound)))))

(defthm fn-transfer-complete-work-cost-bound
  (implies (and (natp declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-complete-from-work 0 declared-length chunks))
               (* declared-length
                  (1+ (len chunks))
                  (1+ maximum))))
  :hints (("Goal"
           :use ((:instance fn-transfer-complete-from-work-cost-bound
                            (position 0))))))

(defthm fn-transfer-assemble-work-cost-bound
  (implies (and (natp declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-assemble-from-work 0 declared-length chunks))
               (* declared-length
                  (1+ (len chunks))
                  (1+ maximum))))
  :hints (("Goal"
           :use ((:instance fn-transfer-assemble-from-work-cost-bound
                            (position 0))))))

(defthm fn-transfer-missing-work-cost-bound
  (implies (and (natp declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-missing-from-work 0 declared-length chunks))
               (* declared-length
                  (1+ (len chunks))
                  (1+ maximum))))
  :hints (("Goal"
           :use ((:instance fn-transfer-missing-from-work-cost-bound
                            (position 0))))))

(defthm fn-transfer-complete-work-cadr-cost-bound
  (implies (and (natp declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (cadr (fn-transfer-complete-from-work 0 declared-length chunks))
               (* declared-length (1+ (len chunks)) (1+ maximum))))
  :hints (("Goal" :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-complete-work-cost-bound)))))

(defthm fn-transfer-assemble-work-cadr-cost-bound
  (implies (and (natp declared-length)
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp chunks maximum))
           (<= (cadr (fn-transfer-assemble-from-work 0 declared-length chunks))
               (* declared-length (1+ (len chunks)) (1+ maximum))))
  :hints (("Goal" :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-assemble-work-cost-bound)))))

(defthm fn-transfer-entry-candidate-work-cost-bound
  (implies (and (natp (fn-transfer-entry-length entry))
                (natp maximum)
                (fn-transfer-chunks-at-most-lengthp
                 (fn-transfer-entry-chunks entry) maximum))
           (<= (fn-transfer-work-cost
                (fn-transfer-entry-candidate-work entry))
               (* 2
                  (fn-transfer-entry-length entry)
                  (1+ (len (fn-transfer-entry-chunks entry)))
                  (1+ maximum))))
  :hints (("Goal"
           :in-theory (e/d (fn-transfer-entry-candidate-work
                             fn-transfer-work-cost)
                            (fn-transfer-complete-from-work
                             fn-transfer-assemble-from-work))
           :use ((:instance fn-transfer-complete-work-cadr-cost-bound
                            (declared-length (fn-transfer-entry-length entry))
                            (chunks (fn-transfer-entry-chunks entry)))
                 (:instance fn-transfer-assemble-work-cadr-cost-bound
                            (declared-length (fn-transfer-entry-length entry))
                            (chunks (fn-transfer-entry-chunks entry)))))))

(defthm fn-transfer-entry-candidate-empty-work
  (implies (equal (fn-transfer-entry-length entry) 0)
           (equal (fn-transfer-work-cost
                   (fn-transfer-entry-candidate-work entry))
                  0))
  :hints (("Goal"
           :in-theory (enable fn-transfer-entry-candidate-work
                               fn-transfer-complete-from-work
                               fn-transfer-assemble-from-work
                               fn-transfer-work-cost))))

(defthm fn-transfer-missing-empty-work
  (implies (equal declared-length 0)
           (equal (fn-transfer-work-cost
                   (fn-transfer-missing-from-work
                    position declared-length chunks))
                  0))
  :hints (("Goal"
           :in-theory (enable fn-transfer-missing-from-work
                               fn-transfer-work-cost))))
