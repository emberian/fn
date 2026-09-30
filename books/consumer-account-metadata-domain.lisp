; Proof-only size domain of the actual account adoption transitions.
; This names fixed constructors and byte/list domains; it does not establish
; account authority, identity, credential semantics or allocation funding.
(in-package "ACL2")
(include-book "consumer-account-metadata")

(local
 (defthm fn-caamd-cbor-octets-are-scc-octets
   (equal (fn-scc-octet-listp x) (fn-cbor-octet-listp x))
   :hints (("Goal" :induct (fn-scc-octet-listp x)
            :in-theory (enable fn-scc-octet-listp fn-scc-octetp
                               fn-cbor-octet-listp fn-cbor-octetp)))))
(local
 (defthm fn-caamd-sha256-octets-are-scc-octets
   (equal (fn-scc-octet-listp x) (fn-sha256-octet-listp x))
   :hints (("Goal" :induct (fn-scc-octet-listp x)
            :in-theory (enable fn-scc-octet-listp fn-scc-octetp
                               fn-sha256-octet-listp)))))

(local
 (defthm fn-caamd-cbor-octets-are-sha256-octets
   (equal (fn-cbor-octet-listp x) (fn-sha256-octet-listp x))
   :hints (("Goal"
            :use ((:instance fn-caamd-cbor-octets-are-scc-octets)
                  (:instance fn-caamd-sha256-octets-are-scc-octets))
            :in-theory (disable fn-scc-octet-listp fn-cbor-octet-listp
                                fn-sha256-octet-listp
                                fn-caamd-cbor-octets-are-scc-octets
                                fn-caamd-sha256-octets-are-scc-octets)))))

(local
 (defthm fn-caamd-success-authority-by-definition
   (equal (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-success s a event root))) a)
   :hints (("Goal" :in-theory (enable fn-caa-success fn-cp-state-carry fn-cp-nth)))))

(defthm fn-caam-preparation-constructor-size-domain-by-definition
  (implies (and (symbolp phase) (integerp policy) (true-listp index)
                (true-listp old) (true-listp reversed) (true-listp forward)
                (fn-scc-octet-listp namespace) (equal (len namespace) 40)
                (integerp watermark))
           (fn-caam-preparation-sizep
            (fn-caa-preparation phase old reversed forward
                                (fn-caa-root policy index credentials)
                                namespace watermark)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-caam-preparation-sizep
                                     fn-caa-preparation fn-caa-root fn-cp-nth))))

(defthm fn-caam-pending-constructor-size-domain-by-definition
  (implies (and (fn-scc-octet-listp candidate) (integerp base)
                (integerp count) (integerp watermark)
                (fn-caam-preparation-sizep prep)
                (fn-scc-octet-listp last) (fn-scc-octet-listp digest)
                (equal (len digest) 32) (booleanp ready))
           (fn-caam-pending-sizep
            (fn-caa-pending candidate base count watermark prep last digest ready)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-caam-pending-sizep fn-caa-pending fn-cp-nth)
                                  (fn-caam-preparation-sizep)))))

(defthm fn-caam-authority-constructor-size-domain-by-definition
  (implies (and (integerp revision) (integerp watermark)
                (or (null namespace)
                    (and (fn-scc-octet-listp namespace) (equal (len namespace) 40)))
                (true-listp accounts) (fn-caam-pending-sizep pending))
           (fn-caam-authority-sizep
            (list :authority revision watermark namespace accounts pending)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-caam-authority-sizep fn-cp-nth)
                                  (fn-caam-pending-sizep)))))

(defthm fn-caam-begin-establishes-size-domain
  (let ((one (fn-caa-begin s a event op)))
    (implies (and (fn-caam-authority-sizep a)
                  (fn-scc-octet-listp (fn-cp-nth 1 op))
                  (integerp (fn-cp-nth 4 op))
                  (equal (fn-cp-nth 0 one) :ok))
             (fn-caam-authority-sizep (fn-cp-nth 6 (fn-cp-nth 1 one)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-caa-begin fn-caa-authority-pending
                 fn-caam-authority-sizep fn-caam-pending-sizep
                 fn-caam-preparation-sizep fn-caa-root fn-caa-preparation
                 fn-caa-pending fn-cp-nth fn-cp-authority-namespacep)
                (fn-caa-namespace fn-sha256 fn-cac-encode fn-caa-success
                 fn-scc-octet-listp fn-cbor-octet-listp fn-sha256-octet-listp)))))

(defthm fn-caam-stage-indexed-preserves-size-domain
  (let ((one (fn-caa-stage-indexed s a event row index old-rest)))
    (implies (and (fn-caam-authority-sizep a) (consp (fn-cp-nth 5 a))
                  (fn-scc-octet-listp (fn-cp-nth 1 row))
                  (true-listp index) (true-listp old-rest))
             (fn-caam-authority-sizep (fn-cp-nth 6 (fn-cp-nth 1 one)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-caa-stage-indexed fn-caa-authority-pending
                 fn-caam-authority-sizep fn-caam-pending-sizep
                 fn-caam-preparation-sizep fn-caa-root fn-caa-preparation
                 fn-caa-pending fn-cp-nth max nfix)
                (fn-sha256 fn-cac-encode fn-caa-success
                 fn-scc-octet-listp fn-cbor-octet-listp fn-sha256-octet-listp)))))

(defthm fn-caam-seal-preserves-size-domain
  (let ((one (fn-caa-seal s a event op)))
    (implies (and (fn-caam-authority-sizep a)
                  (equal (fn-cp-nth 0 one) :ok))
             (fn-caam-authority-sizep (fn-cp-nth 6 (fn-cp-nth 1 one)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-caa-seal fn-caa-authority-pending
                 fn-caam-authority-sizep fn-caam-pending-sizep
                 fn-caam-preparation-sizep fn-caa-preparation fn-caa-pending
                 fn-cp-nth fn-caa-count-digest-matchp)
                (fn-caa-success fn-caa-root fn-scc-octet-listp
                 fn-cbor-octet-listp fn-sha256-octet-listp)))))

(defthm fn-caam-prepare-preserves-size-domain
  (let ((one (fn-caa-prepare s a event)))
    (implies (and (fn-caam-authority-sizep a)
                  (equal (fn-cp-nth 0 one) :ok))
             (fn-caam-authority-sizep (fn-cp-nth 6 (fn-cp-nth 1 one)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-caa-prepare fn-caa-authority-pending
                 fn-caam-authority-sizep fn-caam-pending-sizep
                 fn-caam-preparation-sizep fn-caa-root fn-caa-preparation
                 fn-caa-pending fn-cp-nth)
                (fn-caa-success fn-cai-get-octets fn-scc-octet-listp
                 fn-cbor-octet-listp fn-sha256-octet-listp)))))

(defthm fn-caam-fence-preserves-size-domain
  (let ((one (fn-caa-fence s a event op)))
    (implies (and (fn-caam-authority-sizep a)
                  (equal (fn-cp-nth 0 one) :ok))
             (fn-caam-authority-sizep (fn-cp-nth 6 (fn-cp-nth 1 one)))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-caa-fence fn-caam-authority-sizep fn-caam-pending-sizep
                 fn-caam-preparation-sizep fn-cp-nth fn-caa-count-digest-matchp
                 fn-cp-uintp)
                (fn-caa-success fn-caa-root fn-caa-preparation fn-caa-pending
                 fn-scc-octet-listp fn-cbor-octet-listp fn-sha256-octet-listp)))))

(defthm fn-caam-discard-preserves-size-domain
  (implies (fn-caam-authority-sizep a)
           (fn-caam-authority-sizep (fn-caa-authority-pending a nil)))
  :hints (("Goal" :in-theory
           (e/d (fn-caam-authority-sizep fn-caam-pending-sizep
                 fn-caa-authority-pending fn-cp-nth)
                (fn-caam-preparation-sizep fn-scc-octet-listp
                 fn-cbor-octet-listp fn-sha256-octet-listp)))))
