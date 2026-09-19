; The retained union: which arriving octets are new, why retaining exactly
; those keeps the retained fragments pairwise nonoverlapping, and the
; entry-list replacement that installs them.
;
; Split out of books/transfer-invariants.lisp (2026-09-19).

(in-package "ACL2")
(include-book "transfer-reservation")
; -----------------------------------------------------------------------------
; The retained union: which arriving octets are new, and why retaining exactly
; those keeps the retained fragments pairwise nonoverlapping.

; The declared positions of an arriving run that no retained fragment covers.
(defun fn-transfer-uncoveredp (position octets chunks)
  (declare (xargs :measure (acl2-count octets)))
  (if (consp octets)
      (and (not (fn-transfer-present-atp position chunks))
           (fn-transfer-uncoveredp (1+ position) (cdr octets) chunks))
    t))

(defthm fn-transfer-uncoveredp-at-position
  (implies (and (fn-transfer-uncoveredp position octets chunks)
                (natp position)
                (natp query)
                (<= position query)
                (< query (+ position (len octets))))
           (not (fn-transfer-present-atp query chunks)))
  :hints (("Goal" :induct (fn-transfer-uncoveredp position octets chunks))))

(defthm fn-transfer-present-atp-cdr
  (implies (not (fn-transfer-present-atp query chunks))
           (not (fn-transfer-present-atp query (cdr chunks))))
  :hints (("Goal" :in-theory (enable fn-transfer-present-atp))))

(defthm fn-transfer-uncoveredp-cdr-chunks
  (implies (fn-transfer-uncoveredp position octets chunks)
           (fn-transfer-uncoveredp position octets (cdr chunks)))
  :hints (("Goal" :induct (fn-transfer-uncoveredp position octets chunks))))

(defthm fn-transfer-consp-has-positive-len
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear)
; A nonempty retained fragment whose range meets an arriving run shares a
; declared position with it; this names that position.
(defun fn-transfer-overlap-position (position chunk)
  (if (< position (fn-transfer-chunk-offset chunk))
      (fn-transfer-chunk-offset chunk)
    position))

(defthm fn-transfer-overlap-position-is-common
  (implies (and (natp (fn-transfer-chunk-offset left))
                (consp (fn-transfer-chunk-octets left))
                (natp (fn-transfer-chunk-offset right))
                (consp (fn-transfer-chunk-octets right))
                (fn-transfer-ranges-overlapp left right))
           (and (natp (fn-transfer-overlap-position
                       (fn-transfer-chunk-offset left) right))
                (<= (fn-transfer-chunk-offset left)
                    (fn-transfer-overlap-position
                     (fn-transfer-chunk-offset left) right))
                (< (fn-transfer-overlap-position
                    (fn-transfer-chunk-offset left) right)
                   (+ (fn-transfer-chunk-offset left)
                      (len (fn-transfer-chunk-octets left))))
                (<= (fn-transfer-chunk-offset right)
                    (fn-transfer-overlap-position
                     (fn-transfer-chunk-offset left) right))
                (< (fn-transfer-overlap-position
                    (fn-transfer-chunk-offset left) right)
                   (+ (fn-transfer-chunk-offset right)
                      (len (fn-transfer-chunk-octets right))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-transfer-ranges-overlapp
                                      fn-transfer-overlap-position))))

(defthm fn-transfer-head-covers-is-present
  (implies (and (consp chunks)
                (<= (fn-transfer-chunk-offset (car chunks)) query)
                (< query (+ (fn-transfer-chunk-offset (car chunks))
                            (len (fn-transfer-chunk-octets (car chunks))))))
           (fn-transfer-present-atp query chunks))
  :hints (("Goal" :in-theory (enable fn-transfer-present-atp))))
; No degenerate empty retained fragment has its offset strictly inside the
; window an arrival occupies.  An empty fragment covers no declared position,
; so it cannot be byte-compared, and the retained-list invariant still counts
; it as an overlap; fn-transfer-add-chunk refuses such an arrival.
(defun fn-transfer-window-clearp (window-start window-end chunks)
  (declare (xargs :measure (acl2-count chunks)))
  (if (consp chunks)
      (and (or (consp (fn-transfer-chunk-octets (car chunks)))
               (not (and (< window-start (fn-transfer-chunk-offset (car chunks)))
                         (< (fn-transfer-chunk-offset (car chunks)) window-end))))
           (fn-transfer-window-clearp window-start window-end (cdr chunks)))
    t))

(defthm fn-transfer-window-clearp-cdr
  (implies (fn-transfer-window-clearp window-start window-end chunks)
           (fn-transfer-window-clearp window-start window-end (cdr chunks)))
  :hints (("Goal" :in-theory (enable fn-transfer-window-clearp))))

(defthm fn-transfer-window-clearp-narrows
  (implies (and (fn-transfer-window-clearp window-start window-end chunks)
                (<= window-start inner-start)
                (<= inner-end window-end))
           (fn-transfer-window-clearp inner-start inner-end chunks))
  :hints (("Goal" :induct (fn-transfer-window-clearp window-start window-end chunks)
           :in-theory (enable fn-transfer-window-clearp))))

(defthm fn-transfer-no-empty-overlap-is-window-clear
  (implies (and (natp (fn-transfer-chunk-offset chunk))
                (not (fn-transfer-first-empty-overlap chunk chunks)))
           (fn-transfer-window-clearp
            (fn-transfer-chunk-offset chunk)
            (+ (fn-transfer-chunk-offset chunk)
               (len (fn-transfer-chunk-octets chunk)))
            chunks))
  :hints (("Goal" :induct (fn-transfer-first-empty-overlap chunk chunks)
           :in-theory (enable fn-transfer-first-empty-overlap
                               fn-transfer-window-clearp
                               fn-transfer-ranges-overlapp))))
; An uncovered run cannot meet a nonempty retained fragment: they would share a
; declared position, which the run's uncoveredness forbids.
(defthm fn-transfer-uncovered-chunk-misses-head
  (implies (and (natp (fn-transfer-chunk-offset chunk))
                (consp (fn-transfer-chunk-octets chunk))
                (consp chunks)
                (natp (fn-transfer-chunk-offset (car chunks)))
                (consp (fn-transfer-chunk-octets (car chunks)))
                (fn-transfer-uncoveredp (fn-transfer-chunk-offset chunk)
                                        (fn-transfer-chunk-octets chunk)
                                        chunks))
           (not (fn-transfer-ranges-overlapp chunk (car chunks))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-transfer-overlap-position-is-common
                            (left chunk) (right (car chunks)))
                 (:instance fn-transfer-uncoveredp-at-position
                            (position (fn-transfer-chunk-offset chunk))
                            (octets (fn-transfer-chunk-octets chunk))
                            (query (fn-transfer-overlap-position
                                    (fn-transfer-chunk-offset chunk)
                                    (car chunks))))
                 (:instance fn-transfer-head-covers-is-present
                            (query (fn-transfer-overlap-position
                                    (fn-transfer-chunk-offset chunk)
                                    (car chunks)))))
           :in-theory (disable fn-transfer-present-atp
                               fn-transfer-ranges-overlapp
                               fn-transfer-uncoveredp
                               fn-transfer-overlap-position))))
; And it cannot meet a degenerate empty retained fragment either, because a
; clear window has no empty fragment strictly inside it.
(defthm fn-transfer-uncovered-chunk-misses-empty-head
  (implies (and (natp window-start)
                (consp chunks)
                (not (consp (fn-transfer-chunk-octets (car chunks))))
                (<= window-start (fn-transfer-chunk-offset chunk))
                (<= (+ (fn-transfer-chunk-offset chunk)
                       (len (fn-transfer-chunk-octets chunk)))
                    window-end)
                (fn-transfer-window-clearp window-start window-end chunks))
           (not (fn-transfer-ranges-overlapp chunk (car chunks))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-transfer-window-clearp
                                      fn-transfer-ranges-overlapp))))
; The two cases together, in the shape the list induction leaves behind.
(defthm fn-transfer-uncovered-chunk-misses-head-in-clear-window
  (implies (and (natp (fn-transfer-chunk-offset chunk))
                (consp (fn-transfer-chunk-octets chunk))
                (natp window-start)
                (consp chunks)
                (natp (fn-transfer-chunk-offset (car chunks)))
                (<= window-start (fn-transfer-chunk-offset chunk))
                (<= (+ (fn-transfer-chunk-offset chunk)
                       (len (fn-transfer-chunk-octets chunk)))
                    window-end)
                (fn-transfer-uncoveredp (fn-transfer-chunk-offset chunk)
                                        (fn-transfer-chunk-octets chunk)
                                        chunks)
                (fn-transfer-window-clearp window-start window-end chunks))
           (not (fn-transfer-ranges-overlapp chunk (car chunks))))
  :hints (("Goal"
           :cases ((consp (fn-transfer-chunk-octets (car chunks))))
           :use ((:instance fn-transfer-uncovered-chunk-misses-head)
                 (:instance fn-transfer-uncovered-chunk-misses-empty-head))
           :in-theory (e/d (fn-transfer-window-clearp)
                           (fn-transfer-ranges-overlapp
                            fn-transfer-uncoveredp
                            fn-transfer-present-atp
                            fn-transfer-overlap-position)))))

(defthm fn-transfer-chunkp-octets-octet-listp
  (implies (fn-transfer-chunkp chunk declared-length profile)
           (fn-transfer-octet-listp (fn-transfer-chunk-octets chunk)))
  :hints (("Goal" :in-theory (enable fn-transfer-chunkp
                                      fn-transfer-chunk-inputp))))

(defthm fn-transfer-octet-listp-is-true-listp
  (implies (fn-transfer-octet-listp octets)
           (true-listp octets))
  :hints (("Goal" :induct (fn-transfer-octet-listp octets)
           :in-theory (enable fn-transfer-octet-listp))))

(defthm fn-transfer-uncovered-chunk-has-no-overlap
  (implies (and (natp (fn-transfer-chunk-offset chunk))
                (consp (fn-transfer-chunk-octets chunk))
                (natp window-start)
                (<= window-start (fn-transfer-chunk-offset chunk))
                (<= (+ (fn-transfer-chunk-offset chunk)
                       (len (fn-transfer-chunk-octets chunk)))
                    window-end)
                (fn-transfer-uncoveredp (fn-transfer-chunk-offset chunk)
                                        (fn-transfer-chunk-octets chunk)
                                        chunks)
                (fn-transfer-window-clearp window-start window-end chunks)
                (fn-transfer-chunk-listp chunks declared-length profile))
           (fn-transfer-no-overlaps-withp chunk chunks))
  :hints (("Goal"
           :induct (fn-transfer-chunk-listp chunks declared-length profile)
           :in-theory (e/d (fn-transfer-chunk-listp
                            fn-transfer-chunkp
                            fn-transfer-no-overlaps-withp)
                           (fn-transfer-present-atp
                            fn-transfer-ranges-overlapp
                            fn-transfer-uncoveredp
                            fn-transfer-window-clearp
                            fn-transfer-overlap-position
                            fn-transfer-chunk-inputp
                            ; Keep the goal in accessor form: the combined head
                            ; rule is stated with fn-transfer-chunk-offset and
                            ; fn-transfer-chunk-octets, and its free window
                            ; variables can only be bound by matching those
                            ; hypotheses, which car/cadr forms defeat.
                            fn-transfer-chunk-offset
                            fn-transfer-chunk-octets)))))
; The shape of the retained union: well-formed, nonempty, uncovered, ordered
; runs inside the arriving window.
(defun fn-transfer-run-listp (position runs limit chunks)
  (declare (xargs :measure (acl2-count runs)))
  (if (consp runs)
      (and (true-listp (car runs))
           (equal (len (car runs)) 2)
           (natp (fn-transfer-chunk-offset (car runs)))
           (<= position (fn-transfer-chunk-offset (car runs)))
           (consp (fn-transfer-chunk-octets (car runs)))
           (fn-transfer-octet-listp (fn-transfer-chunk-octets (car runs)))
           (<= (+ (fn-transfer-chunk-offset (car runs))
                  (len (fn-transfer-chunk-octets (car runs))))
               limit)
           (fn-transfer-uncoveredp (fn-transfer-chunk-offset (car runs))
                                   (fn-transfer-chunk-octets (car runs))
                                   chunks)
           (fn-transfer-run-listp
            (+ (fn-transfer-chunk-offset (car runs))
               (len (fn-transfer-chunk-octets (car runs))))
            (cdr runs) limit chunks))
    (null runs)))

(defthm fn-transfer-run-listp-relaxes-start
  (implies (and (fn-transfer-run-listp position runs limit chunks)
                (<= start position))
           (fn-transfer-run-listp start runs limit chunks))
  :hints (("Goal" :in-theory (enable fn-transfer-run-listp))))

(defthm fn-transfer-uncovered-chunks-is-run-listp
  (implies (and (natp position)
                (fn-transfer-octet-listp octets))
           (fn-transfer-run-listp
            position
            (fn-transfer-uncovered-chunks position octets chunks)
            (+ position (len octets))
            chunks))
  :hints (("Goal"
           :induct (fn-transfer-uncovered-chunks position octets chunks)
           :in-theory (enable fn-transfer-uncovered-chunks
                              fn-transfer-run-listp
                              fn-transfer-uncoveredp
                              fn-transfer-octet-listp
                              fn-transfer-make-chunk
                              fn-transfer-chunk-offset
                              fn-transfer-chunk-octets)
           :do-not '(generalize fertilize))))

(defthm fn-transfer-no-overlaps-withp-append
  (equal (fn-transfer-no-overlaps-withp chunk (append left right))
         (and (fn-transfer-no-overlaps-withp chunk left)
              (fn-transfer-no-overlaps-withp chunk right)))
  :hints (("Goal" :induct (fn-transfer-no-overlaps-withp chunk left)
           :in-theory (enable fn-transfer-no-overlaps-withp))))

(defthm fn-transfer-run-listp-after-is-no-overlap
  (implies (and (fn-transfer-run-listp position runs limit chunks)
                (natp (fn-transfer-chunk-offset chunk))
                (<= (+ (fn-transfer-chunk-offset chunk)
                       (len (fn-transfer-chunk-octets chunk)))
                    position))
           (fn-transfer-no-overlaps-withp chunk runs))
  :hints (("Goal" :induct (fn-transfer-run-listp position runs limit chunks)
           :in-theory (enable fn-transfer-run-listp
                              fn-transfer-no-overlaps-withp
                              fn-transfer-ranges-overlapp))))

(defthm fn-transfer-run-listp-append-is-chunk-listp
  (implies (and (fn-transfer-run-listp position runs limit chunks)
                (natp position)
                (natp limit)
                (<= position limit)
                (<= limit declared-length)
                (natp (fn-transfer-max-chunk profile))
                (<= (- limit position) (fn-transfer-max-chunk profile))
                (fn-transfer-window-clearp position limit chunks)
                (fn-transfer-chunk-listp chunks declared-length profile))
           (fn-transfer-chunk-listp (append runs chunks)
                                    declared-length profile))
  :hints (("Goal"
           :induct (fn-transfer-run-listp position runs limit chunks)
           :in-theory (e/d (fn-transfer-run-listp
                            fn-transfer-chunk-listp
                            fn-transfer-chunkp
                            fn-transfer-chunk-inputp)
                           (fn-transfer-present-atp
                            fn-transfer-ranges-overlapp
                            fn-transfer-uncoveredp
                            fn-transfer-overlap-position
                            fn-transfer-no-overlaps-withp
                            ; Same accessor-form discipline as
                            ; fn-transfer-uncovered-chunk-has-no-overlap, whose
                            ; free window variables this proof must let ACL2
                            ; bind.
                            fn-transfer-chunk-offset
                            fn-transfer-chunk-octets)))))

(defthm fn-transfer-uncovered-chunks-append-is-chunk-listp
  (implies (and (natp position)
                (fn-transfer-octet-listp octets)
                (fn-transfer-at-mostp octets (fn-transfer-max-chunk profile))
                (natp (fn-transfer-max-chunk profile))
                (<= (+ position (len octets)) declared-length)
                (not (fn-transfer-first-empty-overlap
                      (fn-transfer-make-chunk position octets) chunks))
                (fn-transfer-chunk-listp chunks declared-length profile))
           (fn-transfer-chunk-listp
            (append (fn-transfer-uncovered-chunks position octets chunks)
                    chunks)
            declared-length profile))
  :hints (("Goal"
           :use ((:instance fn-transfer-uncovered-chunks-is-run-listp)
                 (:instance fn-transfer-run-listp-append-is-chunk-listp
                            (runs (fn-transfer-uncovered-chunks
                                   position octets chunks))
                            (limit (+ position (len octets))))
                 (:instance fn-transfer-no-empty-overlap-is-window-clear
                            (chunk (fn-transfer-make-chunk position octets)))
                 (:instance fn-transfer-at-mostp-is-length-bound
                            (xs octets)
                            (bound (fn-transfer-max-chunk profile))))
           :in-theory (e/d (fn-transfer-make-chunk
                            fn-transfer-chunk-offset
                            fn-transfer-chunk-octets)
                           (fn-transfer-uncovered-chunks
                            fn-transfer-run-listp
                            fn-transfer-window-clearp
                            fn-transfer-first-empty-overlap
                            fn-transfer-chunk-listp
                            fn-transfer-at-mostp)))))

(defthm fn-transfer-entry-add-chunks-is-entryp
  (implies (and (fn-transfer-entryp entry profile)
                (fn-transfer-chunk-listp
                 (append new-chunks (fn-transfer-entry-chunks entry))
                 (fn-transfer-entry-length entry) profile)
                (fn-transfer-at-mostp
                 (append new-chunks (fn-transfer-entry-chunks entry))
                 (fn-transfer-max-chunks profile)))
           (fn-transfer-entryp
            (fn-transfer-make-entry
             (fn-transfer-entry-label entry)
             (fn-transfer-entry-length entry)
             (append new-chunks (fn-transfer-entry-chunks entry)))
            profile))
  :hints (("Goal" :in-theory (enable fn-transfer-entryp))))
; -----------------------------------------------------------------------------
; Entry-list replacement.

(defthm fn-transfer-replace-preserves-true-listp
  (implies (true-listp entries)
           (true-listp
            (fn-transfer-replace-entry-with-chunks label new-chunks entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunks
                            label new-chunks entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunks))))

(defthm fn-transfer-replace-preserves-len
  (implies (true-listp entries)
           (equal (len (fn-transfer-replace-entry-with-chunks
                        label new-chunks entries))
                  (len entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunks
                            label new-chunks entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunks))))

(defthm fn-transfer-replace-preserves-at-mostp
  (implies (and (true-listp entries) (natp bound))
           (equal (fn-transfer-at-mostp
                   (fn-transfer-replace-entry-with-chunks
                    label new-chunks entries)
                   bound)
                  (fn-transfer-at-mostp entries bound)))
  :hints (("Goal"
           :use ((:instance fn-transfer-at-mostp-is-length-bound
                            (xs entries))
                 (:instance fn-transfer-at-mostp-is-length-bound
                            (xs (fn-transfer-replace-entry-with-chunks
                                 label new-chunks entries)))
                 (:instance fn-transfer-replace-preserves-true-listp)
                 (:instance fn-transfer-replace-preserves-len)))))

(defthm fn-transfer-replace-preserves-reserved-bytes
  (implies (consp (fn-transfer-find-entry label entries))
           (equal (fn-transfer-reserved-bytes
                   (fn-transfer-replace-entry-with-chunks
                    label new-chunks entries))
                  (fn-transfer-reserved-bytes entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunks
                            label new-chunks entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunks
                               fn-transfer-find-entry
                               fn-transfer-reserved-bytes))))

(defthm fn-transfer-label-absentp-replace
  (equal (fn-transfer-label-absentp
          other
          (fn-transfer-replace-entry-with-chunks label new-chunks entries))
         (fn-transfer-label-absentp other entries))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunks
                            label new-chunks entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunks
                               fn-transfer-label-absentp))))

(defthm fn-transfer-replace-preserves-distinct-labels
  (implies (fn-transfer-distinct-labelsp entries)
           (fn-transfer-distinct-labelsp
            (fn-transfer-replace-entry-with-chunks label new-chunks entries)))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunks
                            label new-chunks entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunks
                               fn-transfer-distinct-labelsp))))

(defthm fn-transfer-replace-preserves-entriesp
  (implies
   (and (fn-transfer-entriesp entries profile)
        (consp (fn-transfer-find-entry label entries))
        (fn-transfer-entryp
         (fn-transfer-make-entry
          (fn-transfer-entry-label (fn-transfer-find-entry label entries))
          (fn-transfer-entry-length (fn-transfer-find-entry label entries))
          (append new-chunks
                  (fn-transfer-entry-chunks
                   (fn-transfer-find-entry label entries))))
         profile))
   (fn-transfer-entriesp
    (fn-transfer-replace-entry-with-chunks label new-chunks entries) profile))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunks
                            label new-chunks entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunks
                               fn-transfer-find-entry
                               fn-transfer-entriesp))))
