; Complete CK7 leaf vocabulary derived from actual typed producer fields.
; Source WIP: no decoder activation until the actual full-domain proof joins.
(in-package "ACL2")
(include-book "bp-held-family-source")
(set-verify-guards-eagerness 2)
(defconst *fn-bpcv-keywords*
 '(:bpnr-checkpoint :bpnf-held :cl :fn-bp-bundle-id :fn-bpb-bundle
   :fn-bp-primary :fn-bpb-block :dtn :dtn-none :ipn :reassembled
   :wall :observed-age :dispatched :forward :delivered
   :request-accepted :request-duplicate :request-returned :request-refused
   :receipt-accepted :receipt-duplicate :receipt-refused
   :dispatch-pending :forward-pending :dispatch-done :busy :forwarding
   :uncertain :bpnf-deleted :lifetime-expired :bpnf-handoff :owed :handed-off))
(defun fn-bpcv-valuep (x)
 (declare (xargs :guard t))
 (if (consp x)
  (and (fn-bpcv-valuep (car x)) (fn-bpcv-valuep (cdr x)))
  (or (null x) (natp x) (member-eq x *fn-bpcv-keywords*))))
(local (defthm fn-bpcv-handoff-octets
 (implies (fn-cbor-octet-listp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :induct (fn-cbor-octet-listp x)
  :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-bpcv-valuep)))))
(local (defthm fn-bpcv-handoff-vchars
 (implies (fn-bpp-vchar-listp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :induct (fn-bpp-vchar-listp x)
  :in-theory (enable fn-bpp-vchar-listp fn-bpp-vcharp fn-bpcv-valuep)))))
(local (defthm fn-bpcv-handoff-three-list
 (implies (and (true-listp x) (equal (len x) 3))
  (equal x (list (nth 0 x) (nth 1 x) (nth 2 x))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
          (true-listp x) (true-listp (cdr x)) (true-listp (cddr x))
          (true-listp (cdddr x)))
 :in-theory (enable nth)))))
(local (defthm fn-bpcv-handoff-eid
 (implies (fn-bpp-eidp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
  :use fn-bpcv-handoff-three-list
  :in-theory (e/d (fn-bpp-eidp fn-bpp-dtn-sspp fn-bpcv-valuep)
                  (fn-bpp-vchar-listp fn-bpp-name-delim-at))))))

(defthm fn-bpcv-typed-handoff-has-value-domain
 (implies (fn-bphs-handoffp handoff) (fn-bpcv-valuep handoff))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bphs-exact-listp handoff 4)
 (fn-bpcv-valuep handoff)
 (fn-bphs-exact-listp (cdr handoff) 3)
 (fn-bpcv-valuep (cdr handoff))
 (fn-bphs-exact-listp (cdr (cdr handoff)) 2)
 (fn-bpcv-valuep (cdr (cdr handoff)))
 (fn-bphs-exact-listp (cdr (cdr (cdr handoff))) 1)
 (fn-bpcv-valuep (cdr (cdr (cdr handoff))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr handoff)))) 0)
 (fn-bpcv-valuep (cdr (cdr (cdr (cdr handoff)))))
 (fn-bphs-exact-listp (nth 2 handoff) 2)
 (fn-bpcv-valuep (nth 2 handoff))
 (fn-bphs-exact-listp (cdr (nth 2 handoff)) 1)
 (fn-bpcv-valuep (cdr (nth 2 handoff)))
 (fn-bphs-exact-listp (cdr (cdr (nth 2 handoff))) 0)
 (fn-bpcv-valuep (cdr (cdr (nth 2 handoff))))
 (fn-bphs-exact-listp (nth 1 (nth 2 handoff)) 6)
 (fn-bpcv-valuep (nth 1 (nth 2 handoff)))
 (fn-bphs-exact-listp (cdr (nth 1 (nth 2 handoff))) 5)
 (fn-bpcv-valuep (cdr (nth 1 (nth 2 handoff))))
 (fn-bphs-exact-listp (cdr (cdr (nth 1 (nth 2 handoff)))) 4)
 (fn-bpcv-valuep (cdr (cdr (nth 1 (nth 2 handoff)))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (nth 1 (nth 2 handoff))))) 3)
 (fn-bpcv-valuep (cdr (cdr (cdr (nth 1 (nth 2 handoff))))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))) 2)
 (fn-bpcv-valuep (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff))))))) 1)
 (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff))))))))
 (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))))) 0)
 (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (nth 1 (nth 2 handoff)))))))))
 (fn-bphs-exact-listp (nth 3 handoff) 2)
 (fn-bpcv-valuep (nth 3 handoff))
 (fn-bphs-exact-listp (cdr (nth 3 handoff)) 1)
 (fn-bpcv-valuep (cdr (nth 3 handoff)))
 (fn-bphs-exact-listp (cdr (cdr (nth 3 handoff))) 0)
 (fn-bpcv-valuep (cdr (cdr (nth 3 handoff)))))
  :in-theory (e/d (fn-bphs-handoffp fn-bphs-triggerp fn-bphs-bundle-idp
                  fn-bphs-exact-listp fn-bpn-machine-textp fn-frame-textp
                  fn-bpp-timep fn-bpcv-valuep nfix zp natp nth binary-+ unary--)
                 (fn-bpp-eidp fn-cbor-octet-listp fn-wildmat-decode-aux))))
 :rule-classes nil)

(local (defthm fn-bpcv-handoff-handoff-domain-by-definition
 (implies (fn-bphs-handoffp handoff) (fn-bpcv-valuep handoff))
 :hints (("Goal" :use fn-bpcv-typed-handoff-has-value-domain
  :in-theory (theory 'minimal-theory)))))

(defthm fn-bpcv-typed-handoffs-have-value-domain
 (implies (fn-bphs-handoffs-p handoffs) (fn-bpcv-valuep handoffs))
 :hints (("Goal" :induct (fn-bphs-handoffs-p handoffs)
  :in-theory (e/d (fn-bphs-handoffs-p fn-bpcv-valuep
                   fn-bpcv-handoff-handoff-domain-by-definition)
                  (fn-bphs-handoffp))))
 :rule-classes nil)

(local (defthm fn-bpcv-natural-by-definition
 (implies (natp x) (fn-bpcv-valuep x))
 :hints (("Goal" :in-theory (enable fn-bpcv-valuep)))))

(local (defthm fn-bpcv-primary
 (implies (fn-bpp-blockp b) (fn-bpcv-valuep b))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((len b) (true-listp b) (fn-bpcv-valuep b) (len (cdr b)) (true-listp (cdr b)) (fn-bpcv-valuep (cdr b)) (len (cdr (cdr b))) (true-listp (cdr (cdr b))) (fn-bpcv-valuep (cdr (cdr b))) (len (cdr (cdr (cdr b)))) (true-listp (cdr (cdr (cdr b)))) (fn-bpcv-valuep (cdr (cdr (cdr b)))) (len (cdr (cdr (cdr (cdr b))))) (true-listp (cdr (cdr (cdr (cdr b))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr b))))) (len (cdr (cdr (cdr (cdr (cdr b)))))) (true-listp (cdr (cdr (cdr (cdr (cdr b)))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr b)))))) (len (cdr (cdr (cdr (cdr (cdr (cdr b))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr b))))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr b))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b))))))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr b)))))))))))))
 :in-theory (e/d (fn-bpp-blockp fn-bpp-flag-setp fn-bpp-crc-typep
 fn-bpp-timep fn-bpp-flags fn-bpp-crc-type fn-bpp-destination
 fn-bpp-source fn-bpp-report-to fn-bpp-creation-time fn-bpp-sequence
 fn-bpp-lifetime fn-bpp-fragment-offset fn-bpp-total-adu-length)
 (fn-bpcv-valuep fn-bpp-eidp fn-bpp-fragmentp))))))

(local (defthm fn-bpcv-block-constructor-by-definition
 (implies (and (natp type) (natp number) (natp flags) (natp crc)
               (fn-cbor-octet-listp data))
  (fn-bpcv-valuep (fn-bpb-make-block type number flags crc data)))
 :hints (("Goal" :in-theory (e/d (fn-bpb-make-block fn-bpcv-valuep)
  (fn-cbor-octet-listp))))))
(local (defthm fn-bpcv-block
 (implies (fn-bpb-blockp b) (fn-bpcv-valuep b))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal"
 :use ((:instance fn-bpb-make-block-of-accessors (x b))
       (:instance fn-bpcv-block-constructor-by-definition
        (type (fn-bpb-block-type b)) (number (fn-bpb-block-number b))
        (flags (fn-bpb-block-flags b)) (crc (fn-bpb-block-crc-type b))
        (data (fn-bpb-block-data b))))
 :in-theory (e/d (fn-bpb-blockp fn-bpp-timep fn-bpp-flag-setp
                  fn-bpp-crc-typep fn-bpb-datap)
                 (fn-bpb-make-block fn-bpcv-valuep fn-cbor-octet-listp))))))

(local (defthm fn-bpcv-blocks
 (implies (fn-bpb-block-listp blocks) (fn-bpcv-valuep blocks))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :induct (fn-bpb-block-listp blocks)
  :in-theory (e/d (fn-bpb-block-listp fn-bpcv-valuep)
                   (fn-bpb-blockp))))))
(local (defthm fn-bpcv-bundle-constructor-by-definition
 (implies (and (fn-bpcv-valuep primary) (fn-bpcv-valuep blocks)
               (fn-bpcv-valuep payload))
  (fn-bpcv-valuep (fn-bpb-make-bundle primary blocks payload)))
 :hints (("Goal" :in-theory (enable fn-bpb-make-bundle fn-bpcv-valuep)))))
(local (defthm fn-bpcv-bundle
 (implies (fn-bpb-bundlep b) (fn-bpcv-valuep b))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal"
  :use ((:instance fn-bpb-make-bundle-of-accessors (x b))
        (:instance fn-bpcv-bundle-constructor-by-definition
          (primary (fn-bpb-bundle-primary b))
          (blocks (fn-bpb-bundle-blocks b))
          (payload (fn-bpb-bundle-payload b))))
  :in-theory (e/d (fn-bpb-bundlep fn-bpb-payload-blockp)
   (fn-bpb-make-bundle fn-bpcv-valuep fn-bpp-blockp fn-bpb-block-listp
    fn-bpb-blockp fn-bpb-splitp))))))

(local (defthm fn-bpcv-id
 (implies (fn-bphs-bundle-idp id) (fn-bpcv-valuep id))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bpcv-valuep id) (fn-bphs-exact-listp id 6) (fn-bpcv-valuep (cdr id)) (fn-bphs-exact-listp (cdr id) 5) (fn-bpcv-valuep (cdr (cdr id))) (fn-bphs-exact-listp (cdr (cdr id)) 4) (fn-bpcv-valuep (cdr (cdr (cdr id)))) (fn-bphs-exact-listp (cdr (cdr (cdr id))) 3) (fn-bpcv-valuep (cdr (cdr (cdr (cdr id))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr id)))) 2) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr id)))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr id))))) 1) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr id))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr id)))))) 0) )
 :in-theory (e/d (fn-bphs-bundle-idp fn-bpp-timep) (fn-bpcv-valuep fn-bpp-eidp))))))

(local (defthm fn-bpcv-consumed-row
 (implies (fn-bphg-consumed-rowp row) (fn-bpcv-valuep row))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bpcv-valuep row) (fn-bphs-exact-listp row 3) (fn-bpcv-valuep (cdr row)) (fn-bphs-exact-listp (cdr row) 2) (fn-bpcv-valuep (cdr (cdr row))) (fn-bphs-exact-listp (cdr (cdr row)) 1) (fn-bpcv-valuep (cdr (cdr (cdr row)))) (fn-bphs-exact-listp (cdr (cdr (cdr row))) 0) )
 :in-theory (e/d (fn-bphg-consumed-rowp fn-bpn-machine-textp fn-frame-textp) (fn-bpcv-valuep fn-bphs-bundle-idp fn-cbor-octet-listp fn-wildmat-decode-aux))))))

(local (defthm fn-bpcv-consumed-rows
 (implies (fn-bphg-consumed-rowsp rows) (fn-bpcv-valuep rows))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :induct (fn-bphg-consumed-rowsp rows)
 :in-theory (e/d (fn-bphg-consumed-rowsp fn-bpcv-valuep)
                  (fn-bphg-consumed-rowp))))))

(local (defthm fn-bpcv-lineage
 (implies (fn-bphg-lineagep x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bpcv-valuep x) (fn-bphs-exact-listp x 2) (fn-bpcv-valuep (cdr x)) (fn-bphs-exact-listp (cdr x) 1) (fn-bpcv-valuep (cdr (cdr x))) (fn-bphs-exact-listp (cdr (cdr x)) 0) )
 :in-theory (e/d (fn-bphg-lineagep ) (fn-bpcv-valuep fn-bphg-consumed-rowsp))))))

(local (defthm fn-bpcv-anchor
 (implies (fn-bphg-anchorp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bpcv-valuep x) (fn-bphs-exact-listp x 3) (fn-bpcv-valuep (cdr x)) (fn-bphs-exact-listp (cdr x) 2) (fn-bpcv-valuep (cdr (cdr x))) (fn-bphs-exact-listp (cdr (cdr x)) 1) (fn-bpcv-valuep (cdr (cdr (cdr x)))) (fn-bphs-exact-listp (cdr (cdr (cdr x))) 0) )
 :in-theory (e/d (fn-bphg-anchorp ) (fn-bpcv-valuep ))))))

(local (defthm fn-bpcv-dispatch
 (implies (fn-bphg-dispatchp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bpcv-valuep x) (fn-bphs-exact-listp x 3) (fn-bpcv-valuep (cdr x)) (fn-bphs-exact-listp (cdr x) 2) (fn-bpcv-valuep (cdr (cdr x))) (fn-bphs-exact-listp (cdr (cdr x)) 1) (fn-bpcv-valuep (cdr (cdr (cdr x)))) (fn-bphs-exact-listp (cdr (cdr (cdr x))) 0) )
 :in-theory (e/d (fn-bphg-dispatchp ) (fn-bpcv-valuep fn-cbor-octet-listp))))))

(local (defthm fn-bpcv-natural-pair-by-definition
 (implies (and (consp x) (natp (car x)) (natp (cdr x)))
  (fn-bpcv-valuep x))
 :hints (("Goal" :in-theory (enable fn-bpcv-valuep)))))

(local (defthm fn-bpcv-attempt
 (implies (fn-bphg-attemptp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bpcv-valuep x) (fn-bphs-exact-listp x 6) (fn-bpcv-valuep (cdr x)) (fn-bphs-exact-listp (cdr x) 5) (fn-bpcv-valuep (cdr (cdr x))) (fn-bphs-exact-listp (cdr (cdr x)) 4) (fn-bpcv-valuep (cdr (cdr (cdr x)))) (fn-bphs-exact-listp (cdr (cdr (cdr x))) 3) (fn-bpcv-valuep (cdr (cdr (cdr (cdr x))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr x)))) 2) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr x)))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr x))))) 1) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr x))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr x)))))) 0) (fn-bpcv-valuep (nth 4 x)))
 :in-theory (e/d (fn-bphg-attemptp ) (fn-bpcv-valuep fn-bpp-eidp))))))

(local (defthm fn-bpcv-deletion
 (implies (fn-bphg-deletionp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-bpcv-valuep x) (fn-bphs-exact-listp x 7) (fn-bpcv-valuep (cdr x)) (fn-bphs-exact-listp (cdr x) 6) (fn-bpcv-valuep (cdr (cdr x))) (fn-bphs-exact-listp (cdr (cdr x)) 5) (fn-bpcv-valuep (cdr (cdr (cdr x)))) (fn-bphs-exact-listp (cdr (cdr (cdr x))) 4) (fn-bpcv-valuep (cdr (cdr (cdr (cdr x))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr x)))) 3) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr x)))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr x))))) 2) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr x))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr x)))))) 1) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))) 0) )
 :in-theory (e/d (fn-bphg-deletionp ) (fn-bpcv-valuep fn-cbor-octet-listp))))))

(local (defthm fn-bpcv-ingress
 (implies (fn-bpnf-cl-ingressp x) (fn-bpcv-valuep x))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :expand ((len x) (true-listp x) (fn-bpcv-valuep x) (len (cdr x)) (true-listp (cdr x)) (fn-bpcv-valuep (cdr x)) (len (cdr (cdr x))) (true-listp (cdr (cdr x))) (fn-bpcv-valuep (cdr (cdr x))) (len (cdr (cdr (cdr x)))) (true-listp (cdr (cdr (cdr x)))) (fn-bpcv-valuep (cdr (cdr (cdr x)))) (len (cdr (cdr (cdr (cdr x))))) (true-listp (cdr (cdr (cdr (cdr x))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr x))))) (len (cdr (cdr (cdr (cdr (cdr x)))))) (true-listp (cdr (cdr (cdr (cdr (cdr x)))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr x)))))) (len (cdr (cdr (cdr (cdr (cdr (cdr x))))))) (true-listp (cdr (cdr (cdr (cdr (cdr (cdr x))))))) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr x))))))) (fn-bpcv-valuep (fn-bpn-nth 1 x)))
 :in-theory (e/d (fn-bpnf-cl-ingressp fn-bpn-machine-u64p
                  fn-bpn-machine-textp fn-frame-textp)
                 (fn-bpcv-valuep fn-bpp-eidp fn-cbor-octet-listp fn-wildmat-decode-aux))))))

(local (defthm fn-bpcv-real-bundle-id
 (implies (fn-bpb-bundlep bundle) (fn-bpcv-valuep (fn-bpb-bundle-id bundle)))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal"
 :use ((:instance fn-bphs-real-bundle-id-has-recovery-shape
         (primary (fn-bpb-bundle-primary bundle))
         (payload-length (len (fn-bpb-payload bundle)))))
 :in-theory (union-theories
  '(fn-bpb-bundlep fn-bpb-bundle-id fn-bpb-bundle-primary fn-bpcv-id
    natp integerp < (:type-prescription len) car-cons cdr-cons)
  (theory 'minimal-theory))))))
(local (defthm fn-bpcv-held-principal
 (implies (fn-bphs-held-sourcep h) (fn-bpcv-valuep (fn-bpnf-held-principal h)))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-bphs-held-sourcep fn-bpnf-heldp fn-bpnf-cl-ingressp
                   fn-bpnf-ingress-principal fn-bpn-machine-textp fn-frame-textp)
  (fn-bpcv-valuep fn-bpnf-held-principal fn-cbor-octet-listp
   fn-bpb-bundlep fn-bpb-bundle-id fn-bpb-encode fn-wildmat-decode-aux))))))

(defthm fn-bpcv-typed-held-has-value-domain
 (implies (and (fn-bphs-held-sourcep h) (fn-bphg-held-auxp h))
  (fn-bpcv-valuep h))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-bpcv-held-principal (h h)))
 :expand ((fn-bpcv-valuep h) (fn-bphs-exact-listp h 16) (fn-bpcv-valuep (cdr h)) (fn-bphs-exact-listp (cdr h) 15) (fn-bpcv-valuep (cdr (cdr h))) (fn-bphs-exact-listp (cdr (cdr h)) 14) (fn-bpcv-valuep (cdr (cdr (cdr h)))) (fn-bphs-exact-listp (cdr (cdr (cdr h))) 13) (fn-bpcv-valuep (cdr (cdr (cdr (cdr h))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr h)))) 12) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr h)))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr h))))) 11) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr h))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr h)))))) 10) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))) 9) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))) 8) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))) 7) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))) 6) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))))) 5) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))))) 4) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))))))) 3) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))))))) 2) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))))))))) 1) (fn-bpcv-valuep (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h))))))))))))))))) (fn-bphs-exact-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr h)))))))))))))))) 0))
 :in-theory (e/d (fn-bphs-held-sourcep fn-bpnf-heldp fn-bphg-held-auxp
                   fn-bpnf-held-principal fn-bpnf-held-id fn-bpnf-held-bundle
                   fn-bpnf-held-wire)
  (fn-bpcv-valuep fn-bpnf-cl-ingressp fn-bpb-bundlep fn-bpb-bundle-id
   fn-bpb-encode fn-cbor-octet-listp fn-bphg-lineagep fn-bphg-anchorp
   fn-bphg-dispatchp fn-bphg-attemptp fn-bphg-deletionp fn-bpp-eidp))))
 :rule-classes nil)

(local (defthm fn-bpcv-held-domain-by-definition
 (implies (and (fn-bphs-held-sourcep h) (fn-bphg-held-auxp h))
  (fn-bpcv-valuep h))
 :rule-classes ((:rewrite :backchain-limit-lst 0))
 :hints (("Goal" :use fn-bpcv-typed-held-has-value-domain
 :in-theory (theory 'minimal-theory)))))

(defthm fn-bpcv-typed-held-list-has-value-domain
 (implies (and (fn-bphs-held-sourcesp held) (fn-bphg-held-auxsp held))
  (fn-bpcv-valuep held))
 :hints (("Goal" :induct (fn-bphg-held-auxsp held)
  :in-theory (e/d (fn-bphs-held-sourcesp fn-bphg-held-auxsp fn-bpcv-valuep)
                   (fn-bphs-held-sourcep fn-bphg-held-auxp))))
 :rule-classes nil)

(defthm fn-bpcv-typed-checkpoint-has-value-domain
 (implies (and (fn-bpnr-checkpointp ck)
               (fn-bphs-held-sourcesp (fn-bpnr-checkpoint-held ck))
               (fn-bphg-held-auxsp (fn-bpnr-checkpoint-held ck))
               (fn-bphs-handoffs-p (fn-bpnr-checkpoint-handoffs ck)))
  (fn-bpcv-valuep ck))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-bpcv-typed-held-list-has-value-domain
         (held (fn-bpnr-checkpoint-held ck)))
        (:instance fn-bpcv-typed-handoffs-have-value-domain
         (handoffs (fn-bpnr-checkpoint-handoffs ck))))
  :expand ((fn-bpcv-valuep ck) (fn-bpcv-valuep (cdr ck))
           (fn-bpcv-valuep (cddr ck)) (fn-bpcv-valuep (cdddr ck))
           (fn-bpcv-valuep (cddddr ck)) (fn-bpcv-valuep (cdr (cddddr ck)))
           (fn-bpcv-valuep (cddr (cddddr ck))) (fn-bpcv-valuep (cdddr (cddddr ck)))
           (true-listp ck) (true-listp (cdr ck)) (true-listp (cddr ck))
           (true-listp (cdddr ck)) (true-listp (cddddr ck))
           (true-listp (cdr (cddddr ck))) (true-listp (cddr (cddddr ck)))
           (true-listp (cdddr (cddddr ck)))
           (len ck) (len (cdr ck)) (len (cddr ck)) (len (cdddr ck))
           (len (cddddr ck)) (len (cdr (cddddr ck)))
           (len (cddr (cddddr ck))) (len (cdddr (cddddr ck))))
  :in-theory (e/d (fn-bpnr-checkpointp fn-bpnr-checkpoint-held
                   fn-bpnr-checkpoint-handoffs)
   (fn-bpcv-valuep fn-bphs-held-sourcesp fn-bphg-held-auxsp fn-bphs-handoffs-p))))
 :rule-classes nil)
