; LB keystones; private proof cuts are scoped, frozen terms unchanged.
(in-package "ACL2")
(include-book "log-verified-map-properties")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lb-verified-entries-invp-lookup
  (implies (and (fn-lb-verified-entries-invp bits log)
                (equal (cdr (hons-assoc-equal (cons seg entry) bits)) t))
           (fn-arx-entry-ok (fn-lb-entry-octets seg entry log)
                            (fn-lb-entry-protected-len seg entry log)))
  :hints (("Goal" :induct (fn-lb-verified-entries-invp bits log)
           :in-theory (e/d (fn-lb-verified-entries-invp hons-assoc-equal)
                           (fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len))))))

(defthm fn-lb-verified-bit-implies-trailer
  (implies (and (fn-lb-vmap-p fn-lb-vmap)
                (fn-lb-verified-invp log fn-lb-vmap)
                (fn-lb-verified-bit seg entry fn-lb-vmap))
           (fn-arx-entry-ok (fn-lb-entry-octets seg entry log)
                            (fn-lb-entry-protected-len seg entry log)))
  :hints (("Goal" :use ((:instance fn-lb-verified-entries-invp-lookup
                                  (bits (nth 0 fn-lb-vmap))))
           :in-theory (e/d (fn-lb-verified-invp fn-lb-verified-bit fn-lb-vmap-bits-get)
                           (fn-lb-vmap-p fn-lb-verified-entries-invp fn-arx-entry-ok
                            fn-lb-entry-octets fn-lb-entry-protected-len)))))

(local (defthm fn-lbp-index-covers-add-key
 (implies (fn-lb-vmap-index-covers bits keys)
  (fn-lb-vmap-index-covers bits (cons key keys)))
 :hints (("Goal" :induct (fn-lb-vmap-index-covers bits keys)
          :in-theory (enable fn-lb-vmap-index-covers)))))

; Logical model variable: ground predicate witnesses remain explicit proof evidence.
(local (defthm fn-lbp-covered-set-bit-has-index-cell
 (implies (and (fn-lb-vmap-index-covers (nth 0 vm) (nth 1 vm))
               (equal (cdr (hons-assoc-equal key (nth 0 vm))) t))
          (consp (cdr vm)))
 :rule-classes nil
 :hints (("Goal" :cases ((consp (cdr vm)))
  :use ((:instance fn-lb-vmap-index-covers-lookup (bits (nth 0 vm)) (keys (nth 1 vm))))
  :in-theory (union-theories (theory 'ground-zero) '(nth zp member-equal))))))

(defthm fn-lb-verified-invp-of-mark
 (implies (fn-lb-verified-invp log fn-lb-vmap-v)
  (fn-lb-verified-invp log (fn-lb-vmap-mark seg entry log fn-lb-vmap-v)))
 :hints (("Goal" :use ((:instance fn-lbp-covered-set-bit-has-index-cell (vm fn-lb-vmap-v) (key (cons seg entry)))
                         (:instance fn-lb-vmap-index-covers-lookup
                                  (bits (nth 0 fn-lb-vmap-v))
                                  (keys (nth 1 fn-lb-vmap-v)) (key (cons seg entry))))
 :in-theory (e/d (fn-lb-verified-invp fn-lb-vmap-mark fn-lb-vmap-bits-put
                 update-fn-lb-vmap-index fn-lb-vmap-index fn-lb-verified-bit
                 fn-lb-vmap-bits-get fn-lb-verified-entries-invp
                 fn-lb-vmap-index-covers)
                (fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len)))))
