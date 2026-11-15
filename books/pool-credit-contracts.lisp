; Public carrier contracts for the SAME qualified credit API. No credit
; transition or geometry is duplicated here; actual consumers include this.
(in-package "ACL2")
(include-book "pool-credit")
(fn2-book-layer :b)

; The API already exports these writers' WFP and scalar frame facts. Their
; TYPE results are the remaining producer facts needed by configuration.
(fn2-pool-preserves fn2-pool-credit-store-demands (xs i fn2-pool)
 :specs (("-PUBLIC-TYPE" fn2-poolp nil)) :disable nil
 :hints (("Goal" :induct (fn2-pool-credit-store-demands xs i fn2-pool))
         (fn2-columns-guard-hint '(fn2-pool) nil
                                 '(fn2-pool-credit-store-demands) world)))
(fn2-pool-preserves fn2-pool-credit-store-groups (groups i fn2-pool)
 :specs (("-PUBLIC-TYPE" fn2-poolp nil)) :disable nil
 :hints (("Goal" :induct (fn2-pool-credit-store-groups groups i fn2-pool))
         (fn2-columns-guard-hint '(fn2-pool) '(fn2-pool-credit-store-demands)
                                 '(fn2-pool-credit-store-groups) world)))
(fn2-pool-preserves fn2-pool-credit-store-protected (class groups fn2-pool)
 :specs (("-PUBLIC-TYPE" fn2-poolp nil)) :disable nil
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
 :hints ((fn2-columns-guard-hint '(fn2-pool) '(fn2-pool-reserve-body)
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
 :hints ((fn2-columns-guard-hint '(fn2-pool)
          '(fn2-pool-release-body fn2-pool-credit-fullp)
          '(fn2-pool-release-credit) world)))
