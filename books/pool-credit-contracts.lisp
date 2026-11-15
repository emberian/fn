; Public carrier contracts for the SAME qualified credit API. No credit
; transition or geometry is duplicated here; actual consumers include this.
(in-package "ACL2")
(include-book "pool-credit")
(fn2-book-layer :b)

(defthm fn2-pool-credit-demand-keeps-available-length
 (equal (fn2-pool-credit-available-length
          (update-fn2-pool-credit-demandi i value fn2-pool))
        (fn2-pool-credit-available-length fn2-pool))
 :hints (("Goal" :in-theory (enable fn2-pool-credit-available-length update-fn2-pool-credit-demandi))))

; Configuration resizer ROWS contracts generated from actual API calls.
(fn2-pool-preserves resize-fn2-pool-credit-protected (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-protected))))
(fn2-pool-preserves resize-fn2-pool-credit-purpose (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-purpose))))
(fn2-pool-preserves resize-fn2-pool-credit-phase (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-phase))))
(fn2-pool-preserves resize-fn2-pool-credit-group-nonce (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-group-nonce))))
(fn2-pool-preserves resize-fn2-pool-credit-group-owner-kind (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-group-owner-kind))))
(fn2-pool-preserves resize-fn2-pool-credit-group-owner-slot (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-group-owner-slot))))
(fn2-pool-preserves resize-fn2-pool-credit-group-owner-gen (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-group-owner-gen))))
(fn2-pool-preserves resize-fn2-pool-credit-demand (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-demand))))
(fn2-pool-preserves resize-fn2-pool-credit-available (n fn2-pool)
 :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :in-theory (enable fn2-pool-rows resize-fn2-pool-credit-available))))
; End configuration resizer ROWS contracts.

; The API already exports these writers' WFP and scalar frame facts. Their
; TYPE results are the remaining producer facts needed by configuration.
(fn2-pool-preserves fn2-pool-credit-store-demands (xs i fn2-pool)
 :specs (("-PUBLIC-TYPE" fn2-poolp nil)
         ("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :induct (fn2-pool-credit-store-demands xs i fn2-pool))
         (fn2-columns-guard-hint '(fn2-pool) nil
                                 '(fn2-pool-credit-store-demands) world)))
(fn2-pool-preserves fn2-pool-credit-store-groups (groups i fn2-pool)
 :specs (("-PUBLIC-TYPE" fn2-poolp nil)
         ("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :induct (fn2-pool-credit-store-groups groups i fn2-pool))
         (fn2-columns-guard-hint '(fn2-pool) '(fn2-pool-credit-store-demands)
                                 '(fn2-pool-credit-store-groups) world)))
(fn2-pool-preserves fn2-pool-credit-store-protected (class groups fn2-pool)
 :specs (("-PUBLIC-TYPE" fn2-poolp nil)
         ("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil
 :hints (("Goal" :induct (fn2-pool-credit-store-protected class groups fn2-pool))
         (fn2-columns-guard-hint '(fn2-pool) nil
                                 '(fn2-pool-credit-store-protected) world)))

(fn2-pool-preserves fn2-pool-credit-configure (groups fn2-pool) :position 1
 :hints ((fn2-columns-guard-hint '(fn2-pool)
          '(fn2-pool-credit-store-groups fn2-pool-credit-store-protected)
          '(fn2-pool-credit-configure) world)))
(fn2-pool-preserves fn2-pool-credit-begin
 (group purpose nonce kind owner generation fn2-pool) :position 1
 :hints ((fn2-columns-guard-hint '(fn2-pool) nil '(fn2-pool-credit-begin) world)))
(fn2-pool-preserves fn2-pool-reserve-credit
 (group nonce class kind owner generation fn2-pool) :position 3
 :hints (("Goal" :use (fn2-pool-credit-shaped-index-bound))
         (fn2-columns-guard-hint '(fn2-pool) '(fn2-pool-reserve-body)
                                 '(fn2-pool-reserve-credit) world)))
(fn2-pool-preserves fn2-pool-credit-end
 (group nonce kind owner generation fn2-pool) :position 1
 :hints ((fn2-columns-guard-hint '(fn2-pool) '(fn2-pool-credit-emptyp)
                                 '(fn2-pool-credit-end) world)))
(fn2-pool-preserves fn2-pool-credit-abort-empty
 (group nonce kind owner generation fn2-pool) :position 1
 :hints ((fn2-columns-guard-hint '(fn2-pool) '(fn2-pool-credit-fullp)
                                 '(fn2-pool-credit-abort-empty) world)))
(fn2-pool-preserves fn2-pool-release-credit
 (slot gen group nonce kind owner generation fn2-pool) :position 1
 :specs (("-PRESERVES-TYPE" fn2-poolp 1)
         ("-PRESERVES-WFP" fn2-pool-wfp 1)
         ("-PRESERVES-ROWS" fn2-pool-rows 1 :frame fn2-pool
          :hints ((fn2-columns-guard-hint '(fn2-pool)
                   '(fn2-pool-release-body fn2-pool-credit-ownerp
                     fn2-pool-credit-fullp fn2-pool-release-countp)
                   '(fn2-pool-release-credit) world))))
 :hints (("Goal" :use ((:instance fn2-pool-credit-shaped-index-bound
                                  (class (fn2-pool-class slot fn2-pool)))
                            (:instance fn2-pool-credit-demandi-bound
                              (i (+ (* group (fn2-pool-nclasses fn2-pool))
                                    (fn2-pool-class slot fn2-pool))))
                            (:instance fn2-pool-credit-demandi-natp
                              (i (+ (* group (fn2-pool-nclasses fn2-pool))
                                    (fn2-pool-class slot fn2-pool))))
                            (:instance fn2-pool-credit-availablei-natp
                              (i (+ (* group (fn2-pool-nclasses fn2-pool))
                                    (fn2-pool-class slot fn2-pool))))))
  (fn2-columns-guard-hint '(fn2-pool) '(fn2-pool-release-body fn2-pool-credit-fullp) '(fn2-pool-release-credit) world)))
