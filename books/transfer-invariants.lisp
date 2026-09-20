; Preservation keystones for the transfer store: the chunk transition and
; retaining the union.
;
; This is the top of the transfer invariants chain.  The structural facts and
; the reservation transition are in books/transfer-reservation.lisp and the
; union machinery in books/transfer-union.lisp (2026-09-19 split); a book that
; included "transfer-invariants" still sees every name.

(in-package "ACL2")
(include-book "transfer-union")
; -----------------------------------------------------------------------------
; The chunk transition.

; This proof-side predicate names exactly the storing branch of
; fn-transfer-add-chunk.  It is not a second host implementation: it exists
; only to state the transition normal form and is proved against the
; executable kernel below.
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
         (not (fn-transfer-first-disagreement
               offset octets (fn-transfer-entry-chunks entry)))
         (not (fn-transfer-first-empty-overlap
               (fn-transfer-make-chunk offset octets)
               (fn-transfer-entry-chunks entry)))
         (consp (fn-transfer-uncovered-chunks
                 offset octets (fn-transfer-entry-chunks entry)))
         (fn-transfer-at-mostp
          (append (fn-transfer-uncovered-chunks
                   offset octets (fn-transfer-entry-chunks entry))
                  (fn-transfer-entry-chunks entry))
          (fn-transfer-max-chunks profile)))))

(defthm fn-transfer-find-entry-non-nil-is-consp
  (implies (and (fn-transfer-entriesp entries profile)
                (fn-transfer-find-entry label entries))
           (consp (fn-transfer-find-entry label entries)))
  :hints (("Goal" :induct (fn-transfer-find-entry label entries)
           :in-theory (enable fn-transfer-find-entry
                               fn-transfer-entriesp
                               fn-transfer-entryp))))

; A definitional restatement of the stored branch of fn-transfer-add-chunk,
; kept for the four proofs below that cite it by :use.  It is NOT a rule:
; exported enabled it rewrote the stored branch into its constructor form
; before this cluster's own preservation keystones could fire, in every
; includer (w3/fragment-container lost two proofs to it).  -by-definition.
(defthm fn-transfer-add-chunk-result-state-normal-form
  (implies (fn-transfer-statep st)
           (equal (fn-transfer-result-state
                   (fn-transfer-add-chunk st label offset octets))
                  (if (fn-transfer-add-chunk-admissiblep st label offset octets)
                      (fn-transfer-make-state
                       (fn-transfer-state-profile st)
                       (fn-transfer-replace-entry-with-chunks
                        label
                        (fn-transfer-uncovered-chunks
                         offset octets
                         (fn-transfer-entry-chunks
                          (fn-transfer-find-entry
                           label (fn-transfer-state-entries st))))
                        (fn-transfer-state-entries st)))
                    st)))
  :rule-classes nil
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
                             fn-transfer-uncovered-chunks
                             fn-transfer-first-disagreement
                             fn-transfer-first-empty-overlap
                             fn-transfer-byte-at)))))

(defthm fn-transfer-add-chunk-stored-entryp
  (implies (and (fn-transfer-statep st)
                (fn-transfer-add-chunk-admissiblep st label offset octets))
           (fn-transfer-entryp
            (fn-transfer-make-entry
             (fn-transfer-entry-label
              (fn-transfer-find-entry label (fn-transfer-state-entries st)))
             (fn-transfer-entry-length
              (fn-transfer-find-entry label (fn-transfer-state-entries st)))
             (append (fn-transfer-uncovered-chunks
                      offset octets
                      (fn-transfer-entry-chunks
                       (fn-transfer-find-entry
                        label (fn-transfer-state-entries st))))
                     (fn-transfer-entry-chunks
                      (fn-transfer-find-entry
                       label (fn-transfer-state-entries st)))))
            (fn-transfer-state-profile st)))
  :hints (("Goal"
           :use ((:instance fn-transfer-statep-implies-entriesp)
                 (:instance fn-transfer-statep-implies-profilep)
                 (:instance fn-transfer-find-entry-is-entryp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-entryp-implies-chunk-listp
                            (entry (fn-transfer-find-entry
                                    label (fn-transfer-state-entries st)))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-uncovered-chunks-append-is-chunk-listp
                            (position offset)
                            (chunks (fn-transfer-entry-chunks
                                     (fn-transfer-find-entry
                                      label (fn-transfer-state-entries st))))
                            (declared-length
                             (fn-transfer-entry-length
                              (fn-transfer-find-entry
                               label (fn-transfer-state-entries st))))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-entry-add-chunks-is-entryp
                            (entry (fn-transfer-find-entry
                                    label (fn-transfer-state-entries st)))
                            (profile (fn-transfer-state-profile st))
                            (new-chunks
                             (fn-transfer-uncovered-chunks
                              offset octets
                              (fn-transfer-entry-chunks
                               (fn-transfer-find-entry
                                label (fn-transfer-state-entries st)))))))
           :in-theory (e/d (fn-transfer-add-chunk-admissiblep
                            fn-transfer-chunk-inputp
                            fn-transfer-profilep)
                           (fn-transfer-statep
                            fn-transfer-entryp
                            fn-transfer-chunk-listp
                            fn-transfer-uncovered-chunks
                            fn-transfer-at-mostp)))))

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
          (append new-chunks
                  (fn-transfer-entry-chunks
                   (fn-transfer-find-entry
                    label (fn-transfer-state-entries st)))))
         (fn-transfer-state-profile st)))
   (fn-transfer-statep
    (fn-transfer-make-state
     (fn-transfer-state-profile st)
     (fn-transfer-replace-entry-with-chunks
      label new-chunks (fn-transfer-state-entries st)))))
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

(defthm fn-transfer-add-chunk-stored-statep
  (implies (and (fn-transfer-statep st)
                (fn-transfer-add-chunk-admissiblep st label offset octets))
           (fn-transfer-statep
            (fn-transfer-make-state
             (fn-transfer-state-profile st)
             (fn-transfer-replace-entry-with-chunks
              label
              (fn-transfer-uncovered-chunks
               offset octets
               (fn-transfer-entry-chunks
                (fn-transfer-find-entry label (fn-transfer-state-entries st))))
              (fn-transfer-state-entries st)))))
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-stored-entryp)
                 (:instance fn-transfer-replace-entry-preserves-statep
                            (new-chunks
                             (fn-transfer-uncovered-chunks
                              offset octets
                              (fn-transfer-entry-chunks
                               (fn-transfer-find-entry
                                label (fn-transfer-state-entries st)))))))
           :in-theory (e/d (fn-transfer-add-chunk-admissiblep)
                           (fn-transfer-statep
                            fn-transfer-entryp
                            fn-transfer-uncovered-chunks)))))

(defthm fn-transfer-add-chunk-preserves-statep
  (implies (fn-transfer-statep st)
           (fn-transfer-statep
            (fn-transfer-result-state
             (fn-transfer-add-chunk st label offset octets))))
  :hints (("Goal"
           :cases ((fn-transfer-add-chunk-admissiblep st label offset octets))
           :use ((:instance fn-transfer-add-chunk-stored-statep)
                 (:instance fn-transfer-add-chunk-result-state-normal-form))
           :in-theory (disable fn-transfer-statep
                               fn-transfer-add-chunk
                               fn-transfer-add-chunk-admissiblep
                               fn-transfer-uncovered-chunks))))

(defthm fn-transfer-add-chunk-preserves-reserved-bytes
  (implies (fn-transfer-statep st)
           (equal (fn-transfer-reserved-bytes
                   (fn-transfer-state-entries
                    (fn-transfer-result-state
                     (fn-transfer-add-chunk st label offset octets))))
                  (fn-transfer-reserved-bytes (fn-transfer-state-entries st))))
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-result-state-normal-form)
                 (:instance fn-transfer-replace-preserves-reserved-bytes
                            (entries (fn-transfer-state-entries st))
                            (new-chunks
                             (fn-transfer-uncovered-chunks
                              offset octets
                              (fn-transfer-entry-chunks
                               (fn-transfer-find-entry
                                label (fn-transfer-state-entries st))))))
                 (:instance fn-transfer-statep-implies-entriesp)
                 (:instance fn-transfer-find-entry-non-nil-is-consp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st))))
           :in-theory (e/d (fn-transfer-add-chunk-admissiblep
                            fn-transfer-state-entries
                            fn-transfer-make-state)
                           (fn-transfer-statep
                            fn-transfer-add-chunk
                            fn-transfer-uncovered-chunks
                            fn-transfer-first-disagreement
                            fn-transfer-first-empty-overlap)))))

(defthm fn-transfer-add-chunk-result-reserved-bytes-bounded
  (implies (fn-transfer-statep st)
           (<= (fn-transfer-reserved-bytes
                (fn-transfer-state-entries
                 (fn-transfer-result-state
                  (fn-transfer-add-chunk st label offset octets))))
               (fn-transfer-capacity (fn-transfer-state-profile st))))
  :hints (("Goal"
           ; The reserved bytes are unchanged by the transition, so the bound
           ; is the one fn-transfer-statep already carries for st; the
           ; accessors stay closed so both sides keep the same shape.
           :use ((:instance fn-transfer-add-chunk-preserves-reserved-bytes))
           :in-theory (e/d (fn-transfer-statep)
                           (fn-transfer-add-chunk
                            fn-transfer-state-profile
                            fn-transfer-state-entries
                            fn-transfer-result-state
                            fn-transfer-capacity
                            fn-transfer-reserved-bytes)))))

(defthm fn-transfer-add-chunk-nonadmissible-no-overwrite
  (implies (and (fn-transfer-statep st)
                (not (fn-transfer-add-chunk-admissiblep st label offset octets)))
           (equal (fn-transfer-result-state
                   (fn-transfer-add-chunk st label offset octets))
                  st))
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-result-state-normal-form))
           :in-theory (disable fn-transfer-statep
                               fn-transfer-add-chunk
                               fn-transfer-add-chunk-admissiblep))))

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
; -----------------------------------------------------------------------------
; Retaining the union.

(defthm fn-transfer-replace-finds-appended-chunks
  (implies (consp (fn-transfer-find-entry label entries))
           (equal (fn-transfer-entry-chunks
                   (fn-transfer-find-entry
                    label
                    (fn-transfer-replace-entry-with-chunks
                     label new-chunks entries)))
                  (append new-chunks
                          (fn-transfer-entry-chunks
                           (fn-transfer-find-entry label entries)))))
  :hints (("Goal" :induct (fn-transfer-replace-entry-with-chunks
                            label new-chunks entries)
           :in-theory (enable fn-transfer-replace-entry-with-chunks
                               fn-transfer-find-entry
                               fn-transfer-make-entry
                               fn-transfer-entry-chunks
                               fn-transfer-entry-label))))

(defthm fn-transfer-present-atp-append
  (equal (fn-transfer-present-atp query (append left right))
         (or (fn-transfer-present-atp query left)
             (fn-transfer-present-atp query right)))
  :hints (("Goal" :induct (fn-transfer-present-atp query left)
           :in-theory (enable fn-transfer-present-atp))))

(defthm fn-transfer-uncovered-chunks-cover-uncovered-positions
  (implies (and (natp position)
                (natp query)
                (<= position query)
                (< query (+ position (len octets)))
                (not (fn-transfer-present-atp query chunks)))
           (fn-transfer-present-atp
            query (fn-transfer-uncovered-chunks position octets chunks)))
  :hints (("Goal"
           :induct (fn-transfer-uncovered-chunks position octets chunks)
           :in-theory (enable fn-transfer-uncovered-chunks
                              fn-transfer-present-atp
                              fn-transfer-make-chunk
                              fn-transfer-chunk-offset
                              fn-transfer-chunk-octets)
           :do-not '(generalize fertilize))))
; The stored transition retains the union of what was already covered and the
; whole arriving range: no retained position is lost and every arriving
; position is present afterwards.  A byte-identical partial overlap therefore
; makes progress instead of stalling.
(defthm fn-transfer-add-chunk-retains-union
  (implies (and (fn-transfer-statep st)
                (fn-transfer-add-chunk-admissiblep st label offset octets)
                (natp query))
           (let ((before (fn-transfer-entry-chunks
                          (fn-transfer-find-entry
                           label (fn-transfer-state-entries st))))
                 (after (fn-transfer-entry-chunks
                         (fn-transfer-find-entry
                          label
                          (fn-transfer-state-entries
                           (fn-transfer-result-state
                            (fn-transfer-add-chunk st label offset octets)))))))
             (and (implies (fn-transfer-present-atp query before)
                           (fn-transfer-present-atp query after))
                  (implies (and (<= offset query)
                                (< query (+ offset (len octets))))
                           (fn-transfer-present-atp query after)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-result-state-normal-form)
                 (:instance fn-transfer-uncovered-chunks-cover-uncovered-positions
                            (position offset)
                            (chunks (fn-transfer-entry-chunks
                                     (fn-transfer-find-entry
                                      label (fn-transfer-state-entries st)))))
                 (:instance fn-transfer-replace-finds-appended-chunks
                            (entries (fn-transfer-state-entries st))
                            (new-chunks
                             (fn-transfer-uncovered-chunks
                              offset octets
                              (fn-transfer-entry-chunks
                               (fn-transfer-find-entry
                                label (fn-transfer-state-entries st)))))))
           :in-theory (e/d (fn-transfer-add-chunk-admissiblep
                            fn-transfer-state-entries
                            fn-transfer-make-state)
                           (fn-transfer-statep
                            fn-transfer-add-chunk
                            fn-transfer-uncovered-chunks
                            fn-transfer-present-atp
                            fn-transfer-first-disagreement
                            fn-transfer-first-empty-overlap)))))
