; Finite symbols follow from the actual typed handoff acceptance grammar.
; This does not constrain held-row auxiliaries or activate a checkpoint reader.
(in-package "ACL2")
(include-book "bp-handoff-recovery-shape")

(local (defthm fn-bphsd-octets
 (implies (fn-cbor-octet-listp x) (fn-bphs-symbol-domain-p x))
 :hints (("Goal" :induct (fn-cbor-octet-listp x)
  :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-bphs-symbol-domain-p)))))
(local (defthm fn-bphsd-vchars
 (implies (fn-bpp-vchar-listp x) (fn-bphs-symbol-domain-p x))
 :hints (("Goal" :induct (fn-bpp-vchar-listp x)
  :in-theory (enable fn-bpp-vchar-listp fn-bpp-vcharp fn-bphs-symbol-domain-p)))))
(local (defthm fn-bphsd-three-list
 (implies (and (true-listp x) (equal (len x) 3))
  (equal x (list (nth 0 x) (nth 1 x) (nth 2 x))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
          (true-listp x) (true-listp (cdr x)) (true-listp (cddr x))
          (true-listp (cdddr x)))
 :in-theory (enable nth)))))
(local (defthm fn-bphsd-eid
 (implies (fn-bpp-eidp x) (fn-bphs-symbol-domain-p x))
 :hints (("Goal" :do-not-induct t
  :use fn-bphsd-three-list
  :in-theory (e/d (fn-bpp-eidp fn-bpp-dtn-sspp fn-bphs-symbol-domain-p)
                  (fn-bpp-vchar-listp fn-bpp-name-delim-at))))))

(defthm fn-bphs-accepted-handoff-has-finite-symbol-domain
 (implies (fn-bphs-handoffp handoff) (fn-bphs-symbol-domain-p handoff))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bphs-exact-listp handoff 4)
 (fn-bphs-symbol-domain-p handoff)
 (fn-bphs-exact-listp (cdr handoff) 3)
 (fn-bphs-symbol-domain-p (cdr handoff))
 (fn-bphs-exact-listp (cdr (cdr handoff)) 2)
 (fn-bphs-symbol-domain-p (cdr (cdr handoff)))
 (fn-bphs-exact-listp (cdr (cdr (cdr handoff))) 1)
 (fn-bphs-symbol-domain-p (cdr (cdr (cdr handoff))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr handoff)))) 0)
 (fn-bphs-symbol-domain-p (cdr (cdr (cdr (cdr handoff)))))
 (fn-bphs-exact-listp (nth 2 handoff) 2)
 (fn-bphs-symbol-domain-p (nth 2 handoff))
 (fn-bphs-exact-listp (cdr (nth 2 handoff)) 1)
 (fn-bphs-symbol-domain-p (cdr (nth 2 handoff)))
 (fn-bphs-exact-listp (cdr (cdr (nth 2 handoff))) 0)
 (fn-bphs-symbol-domain-p (cdr (cdr (nth 2 handoff))))
 (fn-bphs-exact-listp (nth 1 (nth 2 handoff)) 6)
 (fn-bphs-symbol-domain-p (nth 1 (nth 2 handoff)))
 (fn-bphs-exact-listp (cdr (nth 1 (nth 2 handoff))) 5)
 (fn-bphs-symbol-domain-p (cdr (nth 1 (nth 2 handoff))))
 (fn-bphs-exact-listp (cdr (cdr (nth 1 (nth 2 handoff)))) 4)
 (fn-bphs-symbol-domain-p (cdr (cdr (nth 1 (nth 2 handoff)))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (nth 1 (nth 2 handoff))))) 3)
 (fn-bphs-symbol-domain-p (cdr (cdr (cdr (nth 1 (nth 2 handoff))))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))) 2)
 (fn-bphs-symbol-domain-p (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff))))))) 1)
 (fn-bphs-symbol-domain-p (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff))))))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))))) 0)
 (fn-bphs-symbol-domain-p (cdr (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))))))
 (fn-bphs-exact-listp (nth 3 handoff) 2)
 (fn-bphs-symbol-domain-p (nth 3 handoff))
 (fn-bphs-exact-listp (cdr (nth 3 handoff)) 1)
 (fn-bphs-symbol-domain-p (cdr (nth 3 handoff)))
 (fn-bphs-exact-listp (cdr (cdr (nth 3 handoff))) 0)
 (fn-bphs-symbol-domain-p (cdr (cdr (nth 3 handoff)))))
  :in-theory (e/d (fn-bphs-handoffp fn-bphs-triggerp fn-bphs-bundle-idp
                  fn-bphs-exact-listp fn-bpn-machine-textp fn-frame-textp
                  fn-bpp-timep fn-bphs-symbol-domain-p nfix zp natp nth binary-+ unary--)
                 (fn-bpp-eidp fn-cbor-octet-listp fn-wildmat-decode-aux))))
 :rule-classes nil)

(local (defthm fn-bphsd-handoff-domain-by-definition
 (implies (fn-bphs-handoffp handoff) (fn-bphs-symbol-domain-p handoff))
 :hints (("Goal" :use fn-bphs-accepted-handoff-has-finite-symbol-domain
  :in-theory (theory 'minimal-theory)))))

(defthm fn-bphs-accepted-handoffs-have-finite-symbol-domain
 (implies (fn-bphs-handoffs-p handoffs) (fn-bphs-symbol-domain-p handoffs))
 :hints (("Goal" :induct (fn-bphs-handoffs-p handoffs)
  :in-theory (e/d (fn-bphs-handoffs-p fn-bphs-symbol-domain-p
                   fn-bphsd-handoff-domain-by-definition)
                  (fn-bphs-handoffp))))
 :rule-classes nil)
