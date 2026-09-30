; PRF-1183: the actual scanner carries the full retained wire invariant.
; Old command tails / packed-body blocks remain carried values, not fresh
; objects. This logical carry is not a native alias-return receipt.
(in-package "ACL2")
(include-book "wire-scan")

(defthm fn-wire-span-fold-preserves-statep
 (implies (fn-wire-statep wire-state)
          (fn-wire-statep
           (fn-wsp-state (fn-wire-span-fold wire-state i end fn-octets))))
 :hints (("Goal" :induct (fn-wire-span-fold wire-state i end fn-octets)
          :in-theory (disable fn-wire-feed-byte fn-wire-statep))))

(defthm fn-wire-scan-preserves-statep
 (implies (fn-wire-statep wire-state)
          (fn-wire-statep
           (fn-wsp-state (fn-wire-scan wire-state i end fn-octets))))
 :hints (("Goal" :use ((:instance fn-wire-span-fold-preserves-statep))
          :in-theory (disable fn-wire-statep fn-wire-span-fold fn-wire-feed-byte)))
 :rule-classes nil)
