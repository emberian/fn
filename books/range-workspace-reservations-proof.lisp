; Writing a row, resetting a workspace, and zeroing its header preserve
; all slots available for later range pages.
(in-package "ACL2")
(include-book "range-pool-reservation-proof")
(local (include-book "pool-copy"))

(local
 (defthm fn2-range-bytes-or-fill-keep-free-slot
   (implies (member-equal col (list *fn2-pool-datai* *fn2-pool-fill$ai*))
            (equal (fn2-range-free-slot-p i (update-nth col v p)) (fn2-range-free-slot-p i p)))
   :hints (("Goal" :in-theory (e/d (fn2-range-free-slot-p fn2-pool-state fn2-pool-class fn2-pool-gen fn2-pool-out-count
                           fn2-pool-query-ref-count fn2-pool-cap fn2-pool-base fn2-pool-next-free nth-update-nth)
                           (nth update-nth))))))

(local
 (defthm fn2-range-bytes-or-fill-keep-free-suffix
   (implies (member-equal col (list *fn2-pool-datai* *fn2-pool-fill$ai*))
            (equal (fn2-range-free-suffix-p n (update-nth col v p)) (fn2-range-free-suffix-p n p)))
   :hints (("Goal" :induct (fn2-range-free-suffix-p n p)
            :in-theory (disable fn2-range-free-slot-p update-nth)))))

(local
 (defthm fn2-range-fixed-storage-retains-reservations
   (implies (and (member-equal col (list *fn2-pool-datai* *fn2-pool-fill$ai*))
                 (equal (fn2-pool-capacity-bytes (update-nth col v p)) (fn2-pool-capacity-bytes p)))
            (equal (fn2-range-pool-available-p n (update-nth col v p)) (fn2-range-pool-available-p n p)))
   :hints (("Goal" :in-theory (e/d (fn2-range-pool-available-p fn2-pool-rows fn2-pool-nclasses fn2-pool-credit-configured
                               fn2-pool-class-countsi fn2-pool-class-headsi nth-update-nth)
                              (fn2-range-free-suffix-p fn2-pool-capacity-bytes nth update-nth))))))

(local
 (defthm fn2-range-filling-retains-reservations
   (equal (fn2-range-pool-available-p n (fn2-pool-set-fill slot v p)) (fn2-range-pool-available-p n p))
   :hints (("Goal" :in-theory (e/d (fn2-pool-set-fill update-fn2-pool-fill$ai fn2-pool-capacity-bytes
                                   fn2-pool-data-length nth-update-nth)
                                (fn2-range-pool-available-p nth update-nth))))))

(local
 (defthm fn2-range-octet-write-retains-reservations
   (implies (fn2-range-pool-available-p n p)
            (fn2-range-pool-available-p n (mv-nth 1 (fn2-pool-write slot gen off byte pk ps pg p))))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-pool-write-data-length-when-nonempty (fn2-pool p) (idx off) (okind pk) (oslot ps) (ogen pg)))
            :in-theory (e/d (fn2-pool-write fn2-range-pool-available-p fn2-pool-capacity-bytes fn2-pool-set-fill update-fn2-pool-fill$ai
                             update-fn2-pool-datai fn2-pool-rows fn2-pool-nclasses fn2-pool-credit-configured
                             fn2-pool-class-countsi fn2-pool-class-headsi nth-update-nth)
                            (fn2-range-free-suffix-p fn2-pool-workspace-code fn2-pool-data-length fn2-pool-base fn2-pool-fill fn2-pool-cap
                             fn2-pool-write-data-length-when-nonempty unsigned-byte-p nth update-nth))))))

(defthmd fn2-range-reset-retains-reservations
  (equal (fn2-range-pool-available-p n (mv-nth 1 (fn2-pool-reset slot gen pk ps pg p))) (fn2-range-pool-available-p n p))
  :hints (("Goal" :in-theory (e/d (fn2-pool-reset)
                        (fn2-range-pool-available-p fn2-pool-set-fill fn2-pool-workspace-code)))))

(defthmd fn2-range-zero-retains-reservations
  (implies (fn2-range-pool-available-p n p)
           (fn2-range-pool-available-p n (mv-nth 1 (fn2-run-zero k slot gen off pk ps pg p))))
  :hints (("Goal" :induct (fn2-run-zero k slot gen off pk ps pg p)
           :in-theory (e/d (fn2-run-zero) (fn2-pool-write fn2-range-pool-available-p)))))

(defthmd fn2-range-load-retains-reservations
  (implies (fn2-range-pool-available-p n p)
           (fn2-range-pool-available-p n (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg p))))
  :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg p)
           :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-write fn2-range-pool-available-p)))))

(defthmd fn2-range-row-load-retains-reservations
  (implies (fn2-range-pool-available-p n p)
           (fn2-range-pool-available-p n (mv-nth 3 (fn2-run-load-values layout row base slot gen off pk ps pg f p))))
  :hints (("Goal" :induct (fn2-run-load-values layout row base slot gen off pk ps pg f p)
           :in-theory (e/d (fn2-run-load-values fn2-run-load-ref fn2-range-load-retains-reservations)
                           (fn2-range-pool-available-p fn2-run-load-bytes fn2-fields-set-value fn2-fields-set-ref-slot
                            fn2-fields-set-ref-gen fn2-fields-set-ref-off fn2-fields-set-ref-len len)))))

(defthmd fn2-range-start-retains-page-reservations
  (implies (fn2-range-pool-available-p n p)
           (fn2-range-pool-available-p n
              (mv-nth 3 (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-run-build-start fn2-range-zero-retains-reservations fn2-range-reset-retains-reservations)
                           (fn2-run-reset-writers fn2-pool-reset fn2-run-zero fn2-range-pool-available-p
                            fn2-run-builds-rows fn2-run-builds-phase unsigned-byte-p)))))
