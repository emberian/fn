; Actual saved configuration preflight carries existing adopted account roots.
; Proof-only correspondence never runs at serving or durable completion.
(in-package "ACL2")
(include-book "consumer-config-authority")
(include-book "consumer-account-metadata")

(local
 (defthm fn-ccam-success-preserves-authority-size-domain
  (implies (and (fn-caam-authority-sizep (fn-cp-nth 6 cp))
                (equal (car (fn-carv-semantic-step cp)) :ok))
           (fn-caam-authority-sizep
             (fn-cp-nth 6 (fn-cp-nth 1 (fn-carv-semantic-step cp)))))
  :hints (("Goal" :in-theory
    (e/d (fn-carv-semantic-step fn-carv-revision-state fn-carv-state-with-authority
          fn-caam-authority-sizep fn-caam-pending-sizep fn-cp-state-carry
          fn-cp-nth fn-cp-uintp)
         (fn-scc-octet-listp))))))

(defthm fn-ccam-actual-config-preflight-maintains-full-metadata
 (let* ((cp (fn-cp-state-carry h i frontier next entries a))
        (approved (fn-cca-preflight cp metadata)))
  (implies (and (integerp frontier)
                (fn-caam-authority-sizep a)
                (equal metadata (fn-caam-annotation cp))
                (equal (car approved) :ok))
   (fn-caam-correspondsp (fn-cp-nth 1 approved) (fn-cp-nth 2 approved))))
 :hints (("Goal"
  :use ((:instance fn-ccam-success-preserves-authority-size-domain
           (cp (fn-cp-state-carry h i frontier next entries a)))
        (:instance fn-caam-metadata-constructor-maintains-full-annotation
           (history h) (incarnation i) (old-frontier frontier)
           (frontier frontier) (next-epoch next) (entries entries)
           (old-authority a)
           (authority (fn-cp-nth 6 (fn-cp-nth 1 (fn-carv-semantic-step
                        (fn-cp-state-carry h i frontier next entries a)))))))
  :in-theory
   (e/d (fn-cca-preflight fn-carv-semantic-step fn-carv-revision-state
         fn-carv-state-with-authority fn-cp-state-carry fn-cp-nth
         fn-caam-correspondsp fn-caam-annotation)
        (fn-caam-authority-sizep fn-caam-field-annotation fn-caam-list-annotation
         fn-caam-preparation-annotation fn-caac-metadata fn-cp-uintp)))))
