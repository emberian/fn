; fn: the reservation itemised, term by term (lane f8-reservation,
; 2026-09-28; D35 F8, PRF-198's figure).
;
; `init' prints one number (books/heap-reservation.lisp
; fn-heap-init-reservation-octets: 1,187 MB for the small preset on the
; d5ab87aec production image) and the launcher another (fn-heap-status-
; decide's heap, 780 MB for the same store empty).  Neither says what it is
; made of, so every proposal to lower F8 re-derived the terms by hand
; (reservation-figure's record, section 1; init-reservation-2026-09-28).
; `fn-heap-breakdown' names each term of the model as the model computes it
; -- the image, the state at the profile's bounds (the history: payload and
; memberships, which share H; handles; records), the open's transient, the
; request in flight, the two octet
; buffers, the collector's room, the megabyte rounding, the image outside the
; dynamic space and the threads -- and the keystone says the terms add up to
; exactly the reservation the host is handed: a breakdown that cannot drift
; from the figure.  tools/f8_breakdown.py evaluates it (no hand arithmetic).

(in-package "ACL2")
(include-book "heap-reservation")

; The terms of the heap figure's BASE (books/heap-store-figure.lisp
; fn-heap-store-base-octets) for a store-figure action, in the base's order.
(defun fn-heap-breakdown-base (profile core observed)
  (declare (xargs :guard t))
  (let* ((tt (nfix (fn-bs-profile-max-transactions profile)))
         (r (nfix (fn-bs-profile-max-record-octets profile)))
         (hdr (nfix (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))
         (ou (fn-heap-open-octets-bound profile observed))
         (on (fn-heap-open-records-bound profile observed)))
    (list (cons :image-dynamic (fn-heap-core-dynamic core))
          ;; the payload in the arena and the memberships' rows, which share
          ;; the history budget H (fn-heap-store-history-holds-payload-and-memberships)
          (cons :state-history (fn-heap-store-history-octets profile))
          (cons :state-handles (* *fn-heap-handle-octets* tt))
          (cons :state-records (* 2 tt *fn-heap-record-octets*))
          ;; the records' header columns (lane heap-bounds, B2), charged to
          ;; the history budget since lane heap-pool: 8 heap octets a
          ;; charged octet, at most H of them
          (cons :state-record-headers
                (* *fn-heap-charge-heap-octets*
                   (nfix (fn-bs-profile-max-history-octets profile))))
          (cons :open-chunk-lists (* 2 *fn-heap-list-octets-per-octet* *fn-heap-open-list-copies*
                                     (fn-heap-open-chunk-bound profile ou)))
          (cons :open-suffix-vectors (* 2 ou))
          (cons :open-per-record (* 2 *fn-heap-open-record-octets* on))
          (cons :inflight-lists (* 2 *fn-heap-list-octets-per-octet*
                                   (+ r (* *fn-heap-inflight-header-copies* hdr))))
          (cons :octet-buffers (* 2 (fn-ock-capture-budget profile)))
          ;; the articles in flight (lane zero-copy-commit): the slots' pool
          (cons :articles (fn-heap-articles-octets profile)))))

(defun fn-heap-breakdown-sum (terms)
  (declare (xargs :guard t))
  (if (consp terms)
      (+ (if (consp (car terms)) (nfix (cdar terms)) 0)
         (fn-heap-breakdown-sum (cdr terms)))
    0))

; The whole reservation of a store-figure ACTION (every action but the
; offline list verbs :recover, :compact, :reclaim, whose figure is the
; larger of two) at CONNECTIONS, itemised.  The heap's own terms, then the
; collector's room (the figure less the base), the rounding to SBCL's
; megabytes, the image outside the dynamic space and the threads.
(defun fn-heap-breakdown (action profile core nursery observed connections)
  (declare (xargs :guard t))
  (let* ((obs (fn-heap-operation-observation action observed))
         (base-terms (fn-heap-breakdown-base profile core obs))
         (base (fn-heap-store-base-octets profile core obs))
         (fig (fn-heap-store-figure-octets profile core nursery obs))
         (mb (fn-heap-mb-of fig))
         (threads (fn-heap-thread-count connections))
         (stack-kib (fn-heap-stack-kib profile)))
    (append base-terms
            (list (cons :collector-room (- fig base))
                  (cons :megabyte-rounding (- (* *fn-heap-mib* mb) fig))
                  (cons :image-outside-heap (fn-heap-core-file core))
                  (cons :thread-stacks (* threads 1024 stack-kib))
                  (cons :thread-runtime (* threads *fn-heap-thread-runtime-octets*))))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-heap-breakdown-sum-of-append
   (equal (fn-heap-breakdown-sum (append a b))
          (+ (fn-heap-breakdown-sum a) (fn-heap-breakdown-sum b)))))

(local
 (defthm fn-heap-breakdown-base-sums-to-the-base
   (equal (fn-heap-breakdown-sum (fn-heap-breakdown-base profile core observed))
          (fn-heap-store-base-octets profile core observed))
   :hints (("Goal" :in-theory (e/d (fn-heap-store-base-octets fn-heap-store-state-bound
                                    fn-heap-store-open-octets fn-heap-store-inflight-octets)
                                   (fn-ock-capture-budget fn-heap-store-history-octets fn-heap-open-chunk-bound
                                    fn-heap-articles-octets fn-heap-core-dynamic
                                    fn-heap-open-octets-bound fn-heap-open-records-bound
                                    fn-bs-profile-max-history-octets
                                    fn-bs-profile-max-transactions
                                    fn-bs-profile-max-record-octets fn-bs-profile-field))))))

(local
 (defthm fn-heap-breakdown-figure-covers-base
   (<= (fn-heap-store-base-octets profile core observed)
       (fn-heap-store-figure-octets profile core nursery observed))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-heap-store-figure-octets)
            :use ((:instance fn-heap-with-nursery-covers-base
                             (base (fn-heap-store-base-octets profile core observed))))))))

(local
 (defthm fn-heap-breakdown-mb-covers-figure
   (<= (fn-heap-store-figure-octets profile core nursery observed)
       (* *fn-heap-mib* (fn-heap-mb-of (fn-heap-store-figure-octets profile core nursery observed))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-heap-mb-of-covers
                                    (octets (fn-heap-store-figure-octets profile core nursery observed))))))))

; KEYSTONE.  For every store-figure action the terms add up to exactly the
; reservation the host is handed: fn-heap-reservation-octets of the
; operation figure's megabytes, the core and the threads' stacks, as
; fn-heap-reserve-of computes it for an accepted decision (init's number is
; the :run action unobserved at init's connections:
; fn-heap-breakdown-is-inits-reservation below).
(defthm fn-heap-breakdown-sums-to-the-reservation
  (implies (not (member-equal action *fn-heap-list-actions*))
           (equal (fn-heap-breakdown-sum
                   (fn-heap-breakdown action profile core nursery observed connections))
                  (fn-heap-reservation-octets
                   (fn-heap-mb-of (fn-heap-operation-figure-octets action profile core nursery observed))
                   core (fn-heap-stack-kib profile) (fn-heap-thread-count connections))))
  :hints (("Goal" :in-theory (e/d (fn-heap-operation-figure-octets fn-heap-reservation-octets)
                                  (fn-heap-breakdown-base fn-heap-store-base-octets
                                   fn-heap-store-figure-octets fn-heap-thread-count
                                   fn-heap-stack-kib fn-heap-core-file)))))

; `init's number is the :run action's, unobserved, at init's connections.
(defthm fn-heap-breakdown-is-inits-reservation
  (equal (fn-heap-breakdown-sum
          (fn-heap-breakdown :run profile core nursery nil (fn-heap-reserve-init-connections)))
         (fn-heap-init-reservation-octets profile core nursery))
  :hints (("Goal" :in-theory (e/d (fn-heap-init-reservation-octets)
                                  (fn-heap-breakdown fn-heap-breakdown-sum
                                   fn-heap-operation-figure-octets fn-heap-reservation-octets
                                   fn-heap-reserve-init-connections))
           :use ((:instance fn-heap-breakdown-sums-to-the-reservation
                            (action :run) (observed nil)
                            (connections (fn-heap-reserve-init-connections)))))))
