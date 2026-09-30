; Proof-only establishment at the actual bounded account row planners.
; No served validation or behavior changes; PRF-1140 remains a joined target.
(in-package "ACL2")
(include-book "consumer-account-relation")

(local
 (defthm fn-caarr-successful-credential-selects-row-codec
   (implies (and (fn-cac-operationp op)
                 (fn-auth-credp (fn-caa-row-credential op)))
            (and (equal (fn-cp-nth 0 op) :authority-row)
                 (posp (fn-cp-nth 4 op))))
   :hints (("Goal" :in-theory
            (e/d (fn-cac-operationp fn-cac-kinds fn-cac-fields-validp
                  fn-cac-fieldp fn-cac-u64p fn-auth-credp fn-prin-idp
                  fn-caa-row-credential fn-cp-nth fn-cp-uintp)
                 (fn-authsec-verifier fn-authsec-verifierp
                  fn-nntp-printable-tokenp fn-cbor-octet-listp))))))

(local
 (defthm fn-caarr-row-codec-descriptor-fields
   (implies (and (fn-cac-operationp op)
                 (equal (fn-cp-nth 0 op) :authority-row))
            (fn-cac-fields-validp
             (list (fn-cp-nth 5 op) (fn-cp-nth 6 op) (fn-cp-nth 7 op)
                   (fn-cp-nth 8 op) (fn-cp-nth 9 op) (fn-cp-nth 10 op))
             '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag)))
   :hints (("Goal" :in-theory
            (enable fn-cac-operationp fn-cac-kinds fn-cac-fields-validp
                    fn-cp-nth)))))

(local
 (defthm fn-caarr-codec-descriptor-is-credential-descriptor
   (implies (fn-cac-fields-validp
             (list (fn-cp-nth 5 op) (fn-cp-nth 6 op) (fn-cp-nth 7 op)
                   (fn-cp-nth 8 op) (fn-cp-nth 9 op) (fn-cp-nth 10 op))
             '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag))
            (equal (fn-caa-row-descriptor op)
                   (fn-caar-credential-descriptor (fn-caa-row-credential op))))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-row-descriptor fn-caar-credential-descriptor
                  fn-caa-row-credential fn-authsec-verifier
                  fn-authsec-ver-salt fn-authsec-ver-digest
                  fn-authsec-ver-stored-key fn-authsec-ver-server-key
                  fn-cac-fields-validp fn-cac-fieldp fn-cp-nth)
                 (fn-cac-fields-encode fn-authsec-octets))))))

(local
 (defthm fn-caarr-codec-descriptor-is-octets-and-nonempty
   (implies (fn-cac-fields-validp
             (list (fn-cp-nth 5 op) (fn-cp-nth 6 op) (fn-cp-nth 7 op)
                   (fn-cp-nth 8 op) (fn-cp-nth 9 op) (fn-cp-nth 10 op))
             '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag))
            (and (fn-cbor-octet-listp (fn-caa-row-descriptor op))
                 (consp (fn-caa-row-descriptor op))
                 (equal (len (fn-caa-row-descriptor op)) 145)))
   :hints (("Goal" :use
            ((:instance fn-cac-fields-encoded-are-octets
                        (values (list (fn-cp-nth 5 op) (fn-cp-nth 6 op)
                                      (fn-cp-nth 7 op) (fn-cp-nth 8 op)
                                      (fn-cp-nth 9 op) (fn-cp-nth 10 op)))
                        (kinds '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag)))
             (:instance fn-cac-fields-charge-is-encoded-length
                        (values (list (fn-cp-nth 5 op) (fn-cp-nth 6 op)
                                      (fn-cp-nth 7 op) (fn-cp-nth 8 op)
                                      (fn-cp-nth 9 op) (fn-cp-nth 10 op)))
                        (kinds '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag))))
            :in-theory
            (e/d (fn-caa-row-descriptor fn-cac-fields-charge fn-cac-field-width
                  fn-cac-fields-validp fn-cac-fieldp fn-cp-nth)
                 (fn-cac-fields-encode fn-cbor-octet-listp
                  fn-caarr-codec-descriptor-is-credential-descriptor
                  fn-cac-fields-charge-is-encoded-length
                  fn-cac-fields-encoded-are-octets))))))

(local
 (defthm fn-caarr-printable-true-list-is-octets
   (implies (and (fn-nntp-printable-tokenp name) (true-listp name))
            (fn-cbor-octet-listp name))
   :hints (("Goal" :in-theory
            (enable fn-nntp-printable-tokenp fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-caarr-credential-name-is-bounded
   (implies (fn-auth-credp (fn-caa-row-credential op))
            (and (equal (fn-auth-cred-name (fn-caa-row-credential op))
                        (fn-cp-nth 3 op))
                 (fn-cai-namep (fn-cp-nth 3 op) *fn-auth-max-name-octets*)))
   :hints (("Goal" :in-theory
            (e/d (fn-auth-credp fn-caa-row-credential fn-cai-namep)
                 (fn-authsec-verifier fn-prin-idp fn-authsec-verifierp))))))

(local
 (defthm fn-caarr-creation-watermark-monotone
   (implies (and (fn-cp-account-creationp token old)
                 (<= (nfix old) (nfix new)))
            (fn-cp-account-creationp token new))
   :hints (("Goal" :in-theory
            (e/d (fn-cp-account-creationp) (fn-cp-creation-coordinate))))))

(local
 (defthm fn-caarr-new-creation-at-stage-watermark
   (implies (and (fn-cp-authority-namespacep namespace)
                 (fn-cp-uintp txid) (posp txid))
            (fn-cp-account-creationp
             (fn-cp-account-creation namespace txid)
             (max (nfix watermark) (1+ (nfix txid)))))
   :hints (("Goal" :use
            ((:instance fn-caa-account-creation-is-48-octets)
             (:instance fn-caa-account-creation-records-stage-coordinate))
            :in-theory
            (e/d (fn-cp-account-creationp fn-cp-uintp)
                 (fn-cp-account-creation fn-cp-authority-namespacep
                  fn-cp-creation-coordinate))))))

; The retained token premise is the pointwise projection of the old cursor
; invariant. It is needed only for a same-name live predecessor. A tombstone
; predecessor is a new birth and uses the captured namespace and stage txid.
; Kind=:authority-row and positive birth-coordinate hypotheses are omitted:
; the local codec lemma derives them from the actual bounded operation and
; the planner's required credential. The present creation encoder uses the
; separately explicit fn-cp-uintp coordinate domain; u64 parser validity does
; not imply that domain. This is a current codec boundary, not a new policy.
(defthm fn-caarr-row-plan-establishes-binding
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
         (name (fn-cp-nth 3 op)) (plan (fn-caa-row-plan a event op)))
    (implies
     (and (fn-cac-operationp op)
          (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
          (fn-cp-uintp (fn-cp-nth 2 event))
          (implies (and head (equal name (fn-cp-nth 1 head))
                        (fn-cp-nth 3 head))
                   (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p)))
          (equal (car plan) :stage))
     (fn-caar-bindingp
      (fn-cp-nth 1 plan)
      (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
      (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))
  :hints (("Goal"
           :use ((:instance fn-caarr-successful-credential-selects-row-codec)
                 (:instance fn-caarr-codec-descriptor-is-credential-descriptor)
                 (:instance fn-caarr-codec-descriptor-is-octets-and-nonempty)
                 (:instance fn-caarr-credential-name-is-bounded)
                 (:instance fn-caarr-new-creation-at-stage-watermark
                            (namespace (fn-cp-nth 6 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                            (txid (fn-cp-nth 2 event))
                            (watermark (fn-cp-nth 4 (fn-cp-nth 5 a))))
                 (:instance fn-caarr-creation-watermark-monotone
                            (token (fn-cp-nth 2
                                    (car (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))))
                            (old (fn-cp-nth 4 (fn-cp-nth 5 a)))
                            (new (max (nfix (fn-cp-nth 4 (fn-cp-nth 5 a)))
                                      (1+ (nfix (fn-cp-nth 2 event)))))))
           :in-theory
           (e/d (fn-caa-row-plan fn-caar-bindingp fn-cp-authority-rowp
                 fn-cai-namep fn-cp-nth)
                (fn-cp-account-creationp fn-cp-account-creation
                 fn-cp-creation-coordinate fn-cp-uintp fn-cac-operationp
                 fn-caa-row-credential fn-caa-row-descriptor fn-auth-credp
                 fn-caar-credential-descriptor
                 fn-caarr-codec-descriptor-is-credential-descriptor
                 fn-caarr-codec-descriptor-is-octets-and-nonempty
                 fn-caarr-credential-name-is-bounded
                 fn-cp-authority-namespacep fn-caa-name-lessp)))))

; A tombstone needs no credential or namespace. Its actual planner copies
; the old creation identity and replaces both live flag and descriptor.
(defthm fn-caarr-tombstone-plan-establishes-binding
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (old (fn-cp-nth 2 prep)) (head (if (consp old) (car old) nil))
         (plan (fn-caa-tombstone-plan a event op)))
    (implies
     (and (fn-cp-account-creationp (fn-cp-nth 2 head) (fn-cp-nth 4 p))
          (fn-cai-namep (fn-cp-nth 1 head) *fn-auth-max-name-octets*)
          (equal (car plan) :stage))
     (fn-caar-bindingp
      (fn-cp-nth 1 plan)
      (list :account-binding (fn-cp-nth 1 plan) (fn-cp-nth 2 plan))
      (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))))
  :hints (("Goal"
           :use ((:instance fn-caarr-creation-watermark-monotone
                            (token (fn-cp-nth 2
                                    (car (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))))
                            (old (fn-cp-nth 4 (fn-cp-nth 5 a)))
                            (new (max (nfix (fn-cp-nth 4 (fn-cp-nth 5 a)))
                                      (1+ (nfix (fn-cp-nth 2 event)))))))
           :in-theory
           (e/d (fn-caa-tombstone-plan fn-caar-bindingp fn-cp-authority-rowp
                 fn-cai-namep fn-cp-nth)
                (fn-cp-account-creationp fn-cp-creation-coordinate
                 fn-caa-name-lessp fn-auth-credp fn-caar-credential-descriptor)))))
