; A reservation takes exactly the head slot and preserves the rest of the
; contiguous free chain used by the overview builder.
(in-package "ACL2")
(include-book "range-pool-start-proof")

(local
 (defthm fn2-range-free-suffix-first
   (implies (and (posp n) (fn2-range-free-suffix-p n p))
            (and (fn2-range-free-slot-p (- 327 n) p)
                 (fn2-range-free-suffix-p (1- n) p)))
   :hints (("Goal" :expand ((fn2-range-free-suffix-p n p))
            :in-theory (disable fn2-range-free-slot-p)))))

(local
 (defthm fn2-range-reservation-takes-head
   (let ((r (fn2-pool-reserve 0 pk ps pg p)))
     (implies (and (fn2-range-pool-available-p n p) (posp n) (fn2-pool-mrefp pk ps pg))
              (and (equal (car r) :ok) (equal (mv-nth 1 r) (- 327 n)) (equal (mv-nth 2 r) 1))))
   :hints (("Goal" :use fn2-range-free-suffix-first
            :in-theory (e/d (fn2-range-pool-available-p fn2-range-free-slot-p fn2-pool-reserve
                          fn2-pool-reserve-body fn2-pool-reservable-count)
                         (fn2-range-free-suffix-p fn2-pool-class-headsi fn2-pool-class-countsi fn2-pool-credit-configured
                          fn2-pool-mrefp fn2-pool-nclasses fn2-pool-rows fn2-pool-capacity-bytes
                          fn2-pool-gen fn2-pool-base fn2-pool-cap fn2-pool-state fn2-pool-class fn2-pool-next-free
                          fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-credit-protected-length
                          fn2-pool-credit-protectedi fn2-pool-set-state fn2-pool-set-owner-kind fn2-pool-set-owner-slot
                          fn2-pool-set-owner-gen fn2-pool-set-fill fn2-pool-set-out-count fn2-pool-set-query-ref-count
                          update-fn2-pool-class-headsi update-fn2-pool-class-countsi))))))

(local
 (defthm fn2-range-reservation-keeps-other-slot
   (let* ((r (fn2-pool-reserve 0 pk ps pg p)) (after (mv-nth 3 r)))
     (implies (and (equal (car r) :ok) (natp i) (natp (mv-nth 1 r)) (not (equal i (mv-nth 1 r))))
              (equal (fn2-range-free-slot-p i after) (fn2-range-free-slot-p i p))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-pool-reserve fn2-pool-reserve-body fn2-range-free-slot-p
                   fn2-pool-state fn2-pool-class fn2-pool-gen fn2-pool-out-count fn2-pool-query-ref-count
                   fn2-pool-cap fn2-pool-base fn2-pool-next-free
                   fn2-pool-set-state fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen
                   fn2-pool-set-out-count fn2-pool-set-query-ref-count fn2-pool-set-fill
                   update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai update-fn2-pool-owner-slot$ai
                   update-fn2-pool-owner-gen$ai update-fn2-pool-out-count$ai update-fn2-pool-query-ref-count$ai update-fn2-pool-fill$ai
                   update-fn2-pool-class-headsi update-fn2-pool-class-countsi nth-update-nth)
                  (fn2-pool-rows fn2-pool-nclasses fn2-pool-reservable-count fn2-pool-mrefp fn2-pool-class-headsi
                   fn2-pool-class-countsi nth update-nth))))))

(local
 (defthm fn2-range-reservation-keeps-free-suffix
   (let ((r (fn2-pool-reserve 0 pk ps pg p)))
     (implies (and (natp m) (<= m 327) (equal (car r) :ok) (natp (mv-nth 1 r)) (< (mv-nth 1 r) (- 327 m)))
              (equal (fn2-range-free-suffix-p m (mv-nth 3 r)) (fn2-range-free-suffix-p m p))))
   :hints (("Goal" :induct (fn2-range-free-suffix-p m p)
            :expand ((:free (pool) (fn2-range-free-suffix-p m pool)))
            :in-theory (disable fn2-range-free-slot-p fn2-pool-reserve)))))

(local
 (defthm fn2-range-reservation-pool-metadata
   (let* ((r (fn2-pool-reserve 0 pk ps pg p)) (slot (mv-nth 1 r)) (after (mv-nth 3 r)))
     (implies (and (equal (car r) :ok) (natp slot))
              (and (equal (fn2-pool-class-headsi 0 after) (fn2-pool-next-free slot p))
                   (equal (fn2-pool-class-countsi 0 after) (1- (fn2-pool-class-countsi 0 p)))
                   (equal (fn2-pool-rows after) (fn2-pool-rows p))
                   (equal (fn2-pool-nclasses after) (fn2-pool-nclasses p))
                   (equal (fn2-pool-capacity-bytes after) (fn2-pool-capacity-bytes p))
                   (equal (fn2-pool-credit-configured after) (fn2-pool-credit-configured p)))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-pool-reserve fn2-pool-reserve-body fn2-pool-class-headsi fn2-pool-class-countsi
                     fn2-pool-nclasses fn2-pool-rows fn2-pool-capacity-bytes fn2-pool-data-length fn2-pool-credit-configured
                     fn2-pool-set-state fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen
                     fn2-pool-set-out-count fn2-pool-set-query-ref-count fn2-pool-set-fill
                     update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai update-fn2-pool-owner-slot$ai
                     update-fn2-pool-owner-gen$ai update-fn2-pool-out-count$ai update-fn2-pool-query-ref-count$ai update-fn2-pool-fill$ai
                     update-fn2-pool-class-headsi update-fn2-pool-class-countsi nth-update-nth)
                  (fn2-pool-reservable-count fn2-pool-mrefp fn2-pool-state fn2-pool-class fn2-pool-gen
                   fn2-pool-next-free fn2-pool-out-count fn2-pool-query-ref-count nth update-nth))))))

(defthm fn2-range-reserve-preserves-remaining-capacity
  (let ((r (fn2-pool-reserve 0 pk ps pg p)))
    (implies (and (fn2-range-pool-available-p n p) (posp n) (fn2-pool-mrefp pk ps pg))
             (and (equal (car r) :ok) (equal (mv-nth 1 r) (- 327 n)) (equal (mv-nth 2 r) 1)
                  (fn2-range-pool-available-p (1- n) (mv-nth 3 r)))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-range-reservation-takes-head fn2-range-free-suffix-first
                 (:instance fn2-range-reservation-keeps-free-suffix (m (1- n))))
           :in-theory (e/d (fn2-range-pool-available-p fn2-range-free-slot-p)
                          (fn2-pool-reserve fn2-pool-mrefp fn2-range-free-suffix-p fn2-pool-class-headsi
                           fn2-pool-class-countsi fn2-pool-credit-configured fn2-pool-nclasses fn2-pool-rows
                           fn2-pool-capacity-bytes fn2-pool-state fn2-pool-class fn2-pool-gen fn2-pool-base
                           fn2-pool-cap fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-next-free)))))

(local
 (defthm fn2-range-claimed-slot-writable
   (let* ((r (fn2-pool-reserve 0 pk ps pg p)) (s (mv-nth 1 r)) (g (mv-nth 2 r)) (after (mv-nth 3 r)))
     (implies (and (equal (car r) :ok) (natp s) (natp (fn2-pool-base s p)) (equal (fn2-pool-cap s p) 65536)
                   (<= (+ (fn2-pool-base s p) 65536) (fn2-pool-capacity-bytes p)))
              (and (equal (fn2-layout-range-code s g 0 65536 t pk ps pg after) :ok)
                   (equal (fn2-pool-base s after) (fn2-pool-base s p))
                   (equal (fn2-pool-slot-cap s after) 65536))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d (fn2-layout-range-code fn2-pool-reserve fn2-pool-reserve-body fn2-pool-workspace-code
                    fn2-pool-handle-code fn2-pool-ownerp fn2-pool-slot-base fn2-pool-slot-cap fn2-pool-slot-fill
                    fn2-pool-capacity-bytes fn2-pool-data-length fn2-pool-rows fn2-pool-gen fn2-pool-state fn2-pool-class
                    fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen fn2-pool-query-ref-count fn2-pool-out-count
                    fn2-pool-base fn2-pool-cap fn2-pool-fill
                    fn2-pool-set-state fn2-pool-set-owner-kind fn2-pool-set-owner-slot fn2-pool-set-owner-gen
                    fn2-pool-set-out-count fn2-pool-set-query-ref-count fn2-pool-set-fill
                    update-fn2-pool-state$ai update-fn2-pool-owner-kind$ai update-fn2-pool-owner-slot$ai
                    update-fn2-pool-owner-gen$ai update-fn2-pool-out-count$ai update-fn2-pool-query-ref-count$ai update-fn2-pool-fill$ai
                    update-fn2-pool-class-headsi update-fn2-pool-class-countsi nth-update-nth)
                 (fn2-pool-reservable-count fn2-pool-mrefp fn2-pool-nclasses fn2-pool-class-headsi
                  fn2-pool-class-countsi fn2-pool-next-free nth update-nth))))))

(defthm fn2-range-reservation-provides-workspace
  (let* ((r (fn2-pool-reserve 0 pk ps pg p)) (s (mv-nth 1 r)) (g (mv-nth 2 r)) (after (mv-nth 3 r)))
    (implies (and (fn2-range-pool-available-p n p) (posp n) (fn2-pool-mrefp pk ps pg))
             (and (equal (car r) :ok) (equal s (- 327 n)) (equal g 1)
                  (equal (fn2-layout-range-code s g 0 65536 t pk ps pg after) :ok)
                  (equal (fn2-pool-base s after) (* (- 327 n) 65536))
                  (equal (fn2-pool-slot-cap s after) 65536))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-range-reservation-takes-head fn2-range-free-suffix-first fn2-range-claimed-slot-writable)
           :in-theory (e/d (fn2-range-pool-available-p fn2-range-free-slot-p)
                         (fn2-pool-reserve fn2-pool-slot-cap fn2-pool-mrefp fn2-layout-range-code fn2-range-free-suffix-p
                          fn2-pool-class-headsi fn2-pool-class-countsi fn2-pool-credit-configured fn2-pool-nclasses
                          fn2-pool-rows fn2-pool-capacity-bytes fn2-pool-state fn2-pool-class fn2-pool-gen fn2-pool-base
                          fn2-pool-cap fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-next-free)))))
