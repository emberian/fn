; The history-root reserve covers what the roots ask (lane mem10-hroot,
; 2026-10-07; MEM-010, MEM-011; planning/design/history-root-reserve-2026-10-07.md).
;
; books/heap-store-figure.lisp holds a reserve for the live P3 history roots
; (fn-heap-hroot-reserve-octets: two generations, each at most
; fn-heap-hroot-demand-bound), and books/memory-credits.lisp fn-mcr-hroot-resize
; draws it.  This book says the demands the host funds a generation with
; (books/history-root-credit.lisp) stay within that bound at the profile's
; bounds, so retained + candidate always fit the reserve.
;
; KEYSTONES (each over the demand function the host calls)
;   fn-hroot-event-demand-within-the-bound, fn-hroot-grow-demand-within-the-bound,
;   fn-hroot-retain-demand-within-the-bound, fn-hroot-tail-demand-within-the-bound
;       a demand of a root within the profile's bounds is at most the bound
;   fn-hroot-two-generations-fit-the-reserve
;       two generations, each asking at most the bound, fit the reserve
;
; The premises are the profile's bounds on the root's SHAPE: its memory
; (<= fn-heap-hroot-memory-bound) and the ordinal and row count (<= T).  The
; memory bound is not proved of the running root here; it is OWED
; (planning/design/history-root-reserve-2026-10-07.md, "Owed items"): from
; the nested page store's array lengths and the store budget.
;
; What the reserve covers: two generations' images at the profile's bound.
; What it does not: the per-event decode transient
; (fn-hroot-event-transient), which draws the article pool as an ops credit.
(in-package "ACL2")
(include-book "history-root-credit")
(include-book "heap-store-figure")
(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-hroot-ntables-is-the-figures
  (implies (natp np) (equal (pgs-ntables np) (fn-heap-hroot-ntables np)))
  :hints (("Goal" :use ((:instance pgs-ntables-as-tq (n np)))
           :in-theory (e/d (fn-heap-hroot-ntables pgs-tq) (pgs-ntables-as-tq)))))

; The credit's page figure is within the figure's image.
(defthm fn-hroot-page-octets-within-the-figures-image
  (implies (natp np)
           (<= (fn-hroot-page-octets np) (fn-heap-hroot-image-octets np)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hroot-page-octets fn-heap-hroot-image-octets)
           :use fn-hroot-ntables-is-the-figures)))

(defthm fn-heap-hroot-npages-at-least-one
  (<= 1 (fn-heap-hroot-npages profile))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-npages)
                                  (fn-bs-profile-max-transactions fn-bs-profile-max-history-octets)))))

(defthm fn-hroot-one-page-within-the-figures-image
  (<= (fn-hroot-page-octets 1) (fn-heap-hroot-image-octets (fn-heap-hroot-npages profile)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hroot-page-octets-within-the-figures-image (np 1))
                        (:instance fn-heap-hroot-image-octets-monotone
                                   (a 1) (b (fn-heap-hroot-npages profile)))
                        fn-heap-hroot-npages-at-least-one)
           :in-theory (disable fn-hroot-page-octets fn-heap-hroot-image-octets
                               fn-heap-hroot-npages))))

(defthm fn-hroot-event-demand-within-the-bound
  (implies (and (<= (fn-hroot-memory-octets c) (fn-heap-hroot-memory-bound profile))
                (natp ordinal)
                (<= ordinal (nfix (fn-bs-profile-max-transactions profile))))
           (<= (fn-hroot-event-demand ev ordinal c) (fn-heap-hroot-demand-bound profile)))
  :rule-classes nil
  :hints (("Goal" :use fn-hroot-one-page-within-the-figures-image
           :in-theory (e/d (fn-hroot-event-demand fn-heap-hroot-demand-bound)
                           (fn-hroot-memory-octets fn-hroot-tree-octets fn-hroot-page-octets
                            fn-heap-hroot-image-octets fn-heap-hroot-memory-bound
                            fn-heap-hroot-npages fn-bs-profile-max-transactions
                            fn-bs-profile-max-record-octets)))))

(defthm fn-hroot-retain-demand-within-the-bound
  (implies (and (<= (fn-hroot-memory-octets c) (fn-heap-hroot-memory-bound profile))
                (<= (fn-hrc-count c) (nfix (fn-bs-profile-max-transactions profile))))
           (<= (fn-hroot-retain-demand c) (fn-heap-hroot-demand-bound profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hroot-retain-demand fn-heap-hroot-demand-bound)
                                  (fn-hroot-memory-octets fn-hroot-tree-octets fn-hroot-page-octets
                                   fn-heap-hroot-image-octets fn-heap-hroot-memory-bound
                                   fn-heap-hroot-npages fn-bs-profile-max-transactions
                                   fn-bs-profile-max-record-octets fn-hrc-count)))))

(defthm fn-hroot-grow-demand-within-the-bound
  (implies (and (<= (fn-hroot-memory-octets c) (fn-heap-hroot-memory-bound profile))
                (natp ordinal)
                (<= ordinal (nfix (fn-bs-profile-max-transactions profile)))
                (natp (cadr (fn-hpr-final-placement cursor)))
                (<= (cadr (fn-hpr-final-placement cursor)) (fn-heap-hroot-npages profile)))
           (<= (fn-hroot-grow-demand cursor ordinal c) (fn-heap-hroot-demand-bound profile)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hroot-page-octets-within-the-figures-image
                                   (np (cadr (fn-hpr-final-placement cursor))))
                        (:instance fn-heap-hroot-image-octets-monotone
                                   (a (cadr (fn-hpr-final-placement cursor)))
                                   (b (fn-heap-hroot-npages profile))))
           :in-theory (e/d (fn-hroot-grow-demand fn-heap-hroot-demand-bound)
                           (fn-hroot-memory-octets fn-hroot-tree-octets fn-hroot-page-octets
                            fn-heap-hroot-image-octets fn-heap-hroot-memory-bound
                            fn-heap-hroot-npages fn-bs-profile-max-transactions
                            fn-bs-profile-max-record-octets fn-hpr-final-placement
                            fn-hrc-sfxi fn-hrc-lo)))))

(defthm fn-hroot-tail-demand-within-the-bound
  (implies (and (<= (fn-hroot-memory-octets (fn-hist$p-root fn-hist$p))
                    (fn-heap-hroot-memory-bound profile))
                (natp ordinal)
                (<= ordinal (nfix (fn-bs-profile-max-transactions profile))))
           (<= (fn-hroot-tail-demand ev ordinal fn-hist$p) (fn-heap-hroot-demand-bound profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hroot-tail-demand fn-heap-hroot-demand-bound)
                                  (fn-hroot-memory-octets fn-hroot-tree-octets fn-hroot-page-octets
                                   fn-heap-hroot-image-octets fn-heap-hroot-memory-bound
                                   fn-heap-hroot-npages fn-bs-profile-max-transactions
                                   fn-bs-profile-max-record-octets fn-hist$p-root)))))

; KEYSTONE.  Two generations (the retained and the candidate), each asking at
; most the bound, fit the reserve.
(defthm fn-hroot-two-generations-fit-the-reserve
  (implies (and (natp retained) (natp candidate)
                (<= retained (fn-heap-hroot-demand-bound profile))
                (<= candidate (fn-heap-hroot-demand-bound profile)))
           (<= (+ retained candidate) (fn-heap-hroot-reserve-octets profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-hroot-reserve-octets))))

; TEETH.  The bound is reached: a root at the shape's memory at the last ordinal, asks the tail demand, which is the
; bound less the page term -- the bound is not slack beyond that page.
(defthm fn-hroot-bound-is-reached-by-the-tail-at-the-shape
  (equal (+ (fn-heap-hroot-image-octets (fn-heap-hroot-npages profile))
            (* 2 (fn-heap-hroot-memory-bound profile))
            (* 64 (+ 1 (nfix (fn-bs-profile-max-transactions profile)))))
         (fn-heap-hroot-demand-bound profile))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-hroot-demand-bound)
                                  (fn-heap-hroot-image-octets fn-heap-hroot-memory-bound
                                   fn-heap-hroot-npages fn-bs-profile-max-transactions
                                   fn-bs-profile-max-record-octets)))))

; TEETH.  The figure counts the arrays the credit's page formula does not (the
; table pages and the directory), so a figure sized from the credit's
; formula alone would fall short: at 545 pages (the small preset's bound) the
; image is larger than the credit's page figure.
(defthm fn-hroot-figure-image-exceeds-the-credits-page-figure
  (< (fn-hroot-page-octets 545) (fn-heap-hroot-image-octets 545))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hroot-page-octets fn-heap-hroot-image-octets
                                     fn-heap-hroot-ntables fn-heap-hroot-dir-pages
                                     pgs-ntables pgs-tq))))
