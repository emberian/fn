; Claiming another slot leaves each previously stored leaf or index readable,
; including its header, all row bytes, and its physical restart directory.
(in-package "ACL2")
(include-book "range-stored-restarts-proof")
(include-book "runs-stored-headers-proof")
(include-book "range-pool-reservation-proof")

(local
 (defthmd fn2-range-reserve-keeps-other-page-access
   (let* ((r (fn2-pool-reserve 0 owner os og p)) (after (mv-nth 3 r)))
     (implies (and (equal (car r) :ok) (natp (mv-nth 1 r)) (natp slot) (not (equal slot (mv-nth 1 r))))
              (and (equal (fn2-pool-base slot after) (fn2-pool-base slot p))
                   (equal (fn2-pool-read slot gen off pk ps pg after) (fn2-pool-read slot gen off pk ps pg p))
                   (equal (fn2-layout-range-code slot gen off end writep pk ps pg after)
                          (fn2-layout-range-code slot gen off end writep pk ps pg p)))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-layout-range-code fn2-pool-read fn2-pool-datai fn2-pool-readable-code
                fn2-pool-reserve fn2-pool-reserve-body fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp
                fn2-pool-slot-base fn2-pool-slot-cap fn2-pool-slot-fill fn2-pool-capacity-bytes fn2-pool-data-length
                fn2-pool-rows fn2-pool-gen fn2-pool-state fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen
                fn2-pool-query-ref-count fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-out-count
                fn2-pool-set-state fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen
                fn2-pool-set-out-count fn2-pool-set-query-ref-count fn2-pool-set-fill
                update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai update-fn2-pool-owner-slot$ai
                update-fn2-pool-owner-gen$ai update-fn2-pool-out-count$ai update-fn2-pool-query-ref-count$ai update-fn2-pool-fill$ai
                update-fn2-pool-class-headsi update-fn2-pool-class-countsi nth-update-nth)
                (fn2-pool-reservable-count fn2-pool-mrefp fn2-pool-nclasses fn2-pool-class-headsi
                 fn2-pool-class-countsi fn2-pool-next-free fn2-pool-class unsigned-byte-p nth update-nth))))))

(defmacro fn2-range-earlier-page-bindings (&rest body)
  `(let* ((r (fn2-pool-reserve 0 owner os og p)) (after (mv-nth 3 r)))
     (implies (and (posp free) (fn2-range-pool-available-p free p) (fn2-pool-mrefp owner os og)
                   (natp slot) (< slot (- 327 free))) ,@body)))

(defthm fn2-range-new-reservation-keeps-earlier-reads
   (fn2-range-earlier-page-bindings
    (and (equal (fn2-pool-base slot after) (fn2-pool-base slot p))
         (equal (fn2-pool-read slot gen off pk ps pg after) (fn2-pool-read slot gen off pk ps pg p))
         (equal (fn2-layout-range-code slot gen off end writep pk ps pg after)
                (fn2-layout-range-code slot gen off end writep pk ps pg p))))
   :hints (("Goal" :use ((:instance fn2-range-reserve-preserves-remaining-capacity (n free) (pk owner) (ps os) (pg og))
                        fn2-range-reserve-keeps-other-page-access)
            :in-theory (e/d (fn2-range-pool-available-p)
                      (fn2-range-free-suffix-p fn2-pool-reserve fn2-pool-base fn2-pool-read fn2-layout-range-code
                       fn2-pool-mrefp fn2-pool-rows fn2-pool-nclasses fn2-pool-capacity-bytes fn2-pool-credit-configured
                       fn2-pool-class-countsi fn2-pool-class-headsi)))))

(defthmd fn2-range-reserve-keeps-earlier-page-bytes
  (fn2-range-earlier-page-bindings
   (equal (fn2-run-read-bytes n slot gen off pk ps pg after) (fn2-run-read-bytes n slot gen off pk ps pg p)))
  :hints (("Goal" :induct (fn2-run-read-bytes n slot gen off pk ps pg p)
           :expand ((:free (pool) (fn2-run-read-bytes n slot gen off pk ps pg pool)))
           :in-theory (e/d (fn2-range-new-reservation-keeps-earlier-reads)
                       (fn2-range-pool-available-p fn2-pool-reserve fn2-pool-read fn2-pool-mrefp)))))

(local
 (defthmd fn2-range-reserve-keeps-earlier-page-row
   (fn2-range-earlier-page-bindings
    (implies (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f p)
             (fn2-run-overview-row-atp level row base slot gen off end pk ps pg f after)))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-run-overview-row-atp fn2-range-reserve-keeps-earlier-page-bytes
                             fn2-pool-reserve-preserves-type fn2-pool-reserve-preserves-wfp)
                         (fn2-pool-reserve fn2-range-pool-available-p fn2-pool-mrefp fn2-run-values-layoutp unsigned-byte-p
                          fn2-layout-octets fn2-run-read-bytes fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code
                          fn2-fields-rows))))))

(local
 (defthmd fn2-range-reserve-keeps-earlier-page-rows
   (fn2-range-earlier-page-bindings
    (implies (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f p)
             (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f after)))
   :hints (("Goal" :induct (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f p)
            :expand ((:free (pool) (fn2-run-overview-page-rowsp level rows base slot gen off end pk ps pg f pool)))
            :in-theory (e/d (fn2-range-reserve-keeps-earlier-page-row)
                       (fn2-run-overview-row-atp fn2-run-overview-next-offset fn2-pool-mrefp fn2-pool-reserve fn2-range-pool-available-p))))))

(defthmd fn2-range-reserve-keeps-stored-page
  (fn2-range-earlier-page-bindings
   (and (implies (fn2-run-stored-header-p layout vals slot gen off end pk ps pg p)
                 (fn2-run-stored-header-p layout vals slot gen off end pk ps pg after))
        (implies (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f p)
                 (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f after))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-run-stored-header-p fn2-run-stored-overview-page-p fn2-range-reserve-keeps-earlier-page-rows
                          fn2-range-reserve-keeps-earlier-page-bytes fn2-pool-reserve-preserves-type fn2-pool-reserve-preserves-wfp)
             (fn2-run-overview-page-rowsp fn2-pool-mrefp fn2-pool-reserve fn2-range-pool-available-p
              fn2-run-values-layoutp fn2-run-header-scalars-p fn2-run-directory fn2-run-header-value
              fn2-run-restart-offsets-spec fn2-run-directory-octets fn2-fields-rows fn2-layout-octets fn2-run-read-bytes
              fn2-poolp fn2-pool-wfp fn2-pool-base fn2-layout-range-code unsigned-byte-p len)))))
