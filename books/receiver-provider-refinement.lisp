; Proof-only lift of the registered RX child abstraction. This relation does
; not establish a raw parent/child pointer association or admit a supplied pair.
(in-package "ACL2")
(include-book "receiver-provider-capacity")
(defun fn-rxp-child-corr (physical-child logical-provider)
 (declare (xargs :verify-guards nil))
 (fn-octets$corr physical-child (nth 0 logical-provider)))
(defthm fn-rxp-reference-fill-preserves-child-correspondence
 (implies (and (fn-rxp-child-corr fn-octets$c fn-rx-provider)
               (fn-cbor-octet-listp bytes)
               (equal (mv-nth 0 (fn-rxp-fill-range token (len bytes) limits fuel
                                                 fn-rx-provider)) :receive-copy))
          (fn-rxp-child-corr
             (fn-octets$c-from-list bytes fn-octets$c)
             (mv-nth 2 (fn-rxp-fill-reference token bytes limits fuel fn-rx-provider))))
 :hints (("Goal" :use ((:instance fn-octets-from-list{correspondence}
                                  (xs bytes) (fn-octets (nth 0 fn-rx-provider))))
                 :in-theory (e/d (fn-rxp-child-corr fn-octets$a-from-list)
                                 (fn-octets$c-from-list fn-octets$corr
                                  fn-rxp-fill-reference fn-rxp-fill-range)))))
