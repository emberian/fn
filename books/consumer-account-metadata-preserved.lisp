(in-package "ACL2")
(include-book "consumer-account-metadata-domain")

(local
 (defthm fn-caamp-trie-has-alphabet
   (implies (fn-cais-triep trie) (fn-cais-alphabet-triep trie))
   :hints (("Goal" :in-theory (e/d (fn-cais-triep)
                                  (fn-cais-alphabet-triep))))))
(local
 (defthm fn-caamp-cbor-octets-are-size-octets
   (equal (fn-scc-octet-listp x) (fn-cbor-octet-listp x))
   :hints (("Goal" :induct (fn-scc-octet-listp x)
            :in-theory (enable fn-scc-octet-listp fn-scc-octetp
                               fn-cbor-octet-listp fn-cbor-octetp)))))
(local
 (defthm fn-caamp-alphabet-trie-is-list
   (implies (fn-cais-alphabet-triep trie) (true-listp trie))
   :hints (("Goal" :in-theory (enable fn-cais-alphabet-triep)))))
(local
 (defthm fn-caamp-produced-index-is-list
   (implies (and (fn-cais-triep trie) (fn-scc-octet-listp name))
            (true-listp (fn-cai-put-octets name value trie)))
   :hints (("Goal"
            :use ((:instance fn-cais-put-octets-preserves-trie (row value)))
            :in-theory (e/d (fn-cais-triep)
                             (fn-cai-put-octets fn-cai-put-is-existing-trie-put))))))

(local
 (defthm fn-caam-stage-preparation-annotation
  (let* ((a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (old (fn-cp-nth 2 prep)) (reversed (fn-cp-nth 3 prep))
         (one (mv-nth 0 (fn-caac-stage-selected s a event row credential
                          old-rest old-advancedp metadata)))
         (nm (mv-nth 1 (fn-caac-stage-selected s a event row credential
                         old-rest old-advancedp metadata))))
   (implies (and (equal metadata (fn-caam-annotation s))
                 (consp p) (integerp (fn-cp-nth 3 p)) (integerp (fn-cp-nth 4 p))
                 (true-listp old) (true-listp reversed)
                 (equal old-rest (if old-advancedp (cdr old) old))
                 (fn-cais-alphabet-triep (fn-cp-nth 2 root))
                 (equal (fn-caac-row-carry row) (fn-scs-summary row))
                 (implies credential
                          (equal (fn-caac-credential-carry (fn-cp-nth 4 event))
                                 (fn-scs-summary credential))))
            (equal (fn-cp-nth 3 nm)
                   (fn-caam-preparation-annotation
                    (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))))))))
  :hints (("Goal"
    :use ((:instance fn-caac-spine-keeps-canonical-size
           (xs (list :account-binding row credential))
           (cs (list (fn-caac-atom :account-binding)
                     (fn-caac-row-carry row)
                     (if credential (fn-caac-credential-carry (fn-cp-nth 4 event))
                       (fn-caac-atom nil)))))
          (:instance fn-cait-put-maintains-canonical-annotation
           (name (fn-cp-nth 1 row))
           (value (list :account-binding row credential))
           (value-carry (fn-caac-spine
                        (list (fn-caac-atom :account-binding)
                              (fn-caac-row-carry row)
                              (if credential (fn-caac-credential-carry (fn-cp-nth 4 event))
                                (fn-caac-atom nil)))))
           (trie (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 s))))))
           (metadata (fn-cait-annotation
                      (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 s)))))))))
    :in-theory
    (e/d (fn-caac-stage-selected fn-caac-metadata fn-caam-annotation
          fn-caam-preparation-annotation fn-caa-stage-indexed fn-caa-stage-selected
          fn-caa-root fn-caa-preparation fn-caa-pending fn-caa-success
          fn-caa-authority-pending fn-cp-state-carry fn-cp-nth
          fn-caam-list-annotation fn-caac-atom fn-scs-correspondsp)
         (fn-caac-authority-carry fn-caam-field-annotation
          fn-caac-spine fn-caac-row-carry fn-caac-credential-carry
          fn-cait-put-octets fn-cai-put-octets fn-cait-annotation
          fn-scs-summary fn-scs-atom fn-caac-list-cons fn-scs-cons
          fn-sha256 fn-cac-encode fn-cait-size fn-cai-put-is-existing-trie-put))))))

(local
 (defthm fn-caamp-stage-metadata-tuple-frame
  (let* ((one (mv-nth 0 (fn-caac-stage-selected s a event row credential
                          old-rest old-advancedp metadata)))
         (nm (mv-nth 1 (fn-caac-stage-selected s a event row credential
                         old-rest old-advancedp metadata))))
   (equal nm (fn-caac-metadata (fn-cp-nth 1 one) (fn-cp-nth 1 metadata)
                               (fn-cp-nth 2 metadata) (fn-cp-nth 3 nm))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caac-stage-selected fn-caac-metadata fn-cp-nth)
                (fn-caac-stage-selected-is-logical-stage fn-caa-stage-indexed
                 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
                 fn-caac-authority-carry fn-cait-put-octets fn-caac-list-cons
                 fn-caac-atom fn-cait-size))))))
(local
 (defthm fn-caamp-stage-state-frame
  (let ((next (fn-cp-nth 1 (fn-caa-stage-selected s a event row credential old-rest))))
   (equal next (fn-cp-state-carry (fn-cp-nth 1 s) (fn-cp-nth 2 s)
                    (1+ (nfix (fn-cp-nth 1 event)))
                    (fn-cp-nth 4 s) (fn-cp-nth 5 s) (fn-cp-nth 6 next))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caa-stage-selected fn-caa-stage-indexed fn-caa-success
                 fn-cp-state-carry fn-cp-nth)
                (fn-caa-authority-pending fn-caa-pending fn-caa-preparation
                 fn-caa-root fn-cai-put-octets fn-sha256 fn-cac-encode)))))
)

(local
 (defthm fn-caamp-authority-size-projections
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p)))
   (implies (and (fn-caam-authority-sizep a) (consp p))
    (and (integerp (fn-cp-nth 3 p)) (integerp (fn-cp-nth 4 p))
         (true-listp (fn-cp-nth 2 prep)) (true-listp (fn-cp-nth 3 prep)))))
  :hints (("Goal" :in-theory
           (e/d (fn-caam-authority-sizep fn-caam-pending-sizep fn-caam-preparation-sizep)
                (fn-cp-nth fn-caa-pending fn-caa-preparation fn-caa-root))))))
(local
 (defthm fn-caamp-annotation-projections
  (and (equal (fn-cp-nth 1 (fn-caam-annotation s)) (fn-caam-field-annotation s))
       (equal (fn-cp-nth 2 (fn-caam-annotation s))
              (fn-caam-list-annotation (fn-cp-nth 4 (fn-cp-nth 6 s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-caam-annotation fn-cp-nth)
                (fn-caam-field-annotation fn-caam-list-annotation
                 fn-caam-preparation-annotation))))))
(local
 (defthm fn-caamp-selected-stage-preserves-authority-size
  (let* ((root (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a))))
         (one (fn-caa-stage-selected s a event row credential old-rest)))
   (implies (and (fn-caam-authority-sizep a) (consp (fn-cp-nth 5 a))
                 (fn-scc-octet-listp (fn-cp-nth 1 row))
                 (fn-cais-triep (fn-cp-nth 2 root)) (true-listp old-rest))
            (fn-caam-authority-sizep (fn-cp-nth 6 (fn-cp-nth 1 one)))))
  :hints (("Goal"
           :use ((:instance fn-caam-stage-indexed-preserves-size-domain
                  (index (fn-cai-put-octets (fn-cp-nth 1 row)
                           (list :account-binding row credential)
                           (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a))))))))
           :in-theory
           (e/d (fn-caa-stage-selected)
                (fn-caam-authority-sizep fn-caa-stage-indexed fn-cp-nth
                 fn-cai-put-octets fn-cai-put-is-existing-trie-put))))))
(local
 (defthm fn-caamp-selected-stage-preserves-adopted-accounts
  (equal (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1
           (fn-caa-stage-selected s a event row credential old-rest))))
         (fn-cp-nth 4 a))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-stage-selected fn-caa-stage-indexed fn-caa-success
                 fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                (fn-caa-pending fn-caa-preparation fn-caa-root
                 fn-cai-put-octets fn-sha256 fn-cac-encode))))))

(local
 (defthm fn-caamp-selected-stage-has-pending
  (consp (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1
           (fn-caa-stage-selected s a event row credential old-rest)))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-stage-selected fn-caa-stage-indexed fn-caa-success
                 fn-caa-authority-pending fn-caa-pending fn-cp-state-carry fn-cp-nth)
                (fn-caa-preparation fn-caa-root fn-cai-put-octets
                 fn-sha256 fn-cac-encode))))))

(defthm fn-caam-selected-stage-maintains-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (root (fn-cp-nth 5 prep))
         (one (mv-nth 0 (fn-caac-stage-selected s a event row credential
                          old-rest old-advancedp metadata)))
         (nm (mv-nth 1 (fn-caac-stage-selected s a event row credential
                         old-rest old-advancedp metadata))))
   (implies (and (fn-caam-authority-sizep a) (consp p)
                 (equal metadata (fn-caam-annotation s))
                 (fn-cais-triep (fn-cp-nth 2 root))
                 (fn-scc-octet-listp (fn-cp-nth 1 row))
                 (equal old-rest (if old-advancedp (cdr (fn-cp-nth 2 prep))
                                  (fn-cp-nth 2 prep)))
                 (equal (fn-caac-row-carry row) (fn-scs-summary row))
                 (implies credential
                          (equal (fn-caac-credential-carry (fn-cp-nth 4 event))
                                 (fn-scs-summary credential))))
            (fn-caam-correspondsp (fn-cp-nth 1 one) nm)))
  :hints (("Goal"
    :use ((:instance fn-caamp-authority-size-projections)
          (:instance fn-caamp-stage-metadata-tuple-frame
           (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
          (:instance fn-caamp-stage-state-frame
           (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
          (:instance fn-caam-stage-preparation-annotation
           (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
          (:instance fn-caamp-selected-stage-has-pending
           (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
          (:instance fn-caamp-selected-stage-preserves-authority-size
           (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
          (:instance fn-caam-metadata-constructor-maintains-full-annotation
           (old-frontier frontier) (old-authority a)
           (frontier (1+ (nfix (fn-cp-nth 1 event))))
           (authority (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-stage-selected
                       (fn-cp-state-carry history incarnation frontier next-epoch entries a)
                       a event row credential old-rest))))))
    :in-theory
    (e/d (fn-caam-correspondsp fn-cp-state-carry fn-cp-nth)
         (fn-caam-annotation fn-caamp-authority-size-projections
          fn-caamp-selected-stage-has-pending fn-caam-authority-sizep fn-caam-pending-sizep
          fn-caam-preparation-sizep fn-cais-triep nfix
          fn-caac-stage-selected fn-caa-stage-selected fn-caa-stage-indexed
          fn-caa-success fn-caa-authority-pending fn-caac-metadata
          fn-caam-field-annotation fn-caam-preparation-annotation
          fn-caam-list-annotation fn-caac-row-carry fn-caac-credential-carry
          fn-caac-root-carry fn-caac-spine fn-caac-list-cons fn-caac-atom
          fn-cait-put-octets fn-cai-put-octets fn-cait-annotation
          fn-scs-summary fn-sha256 fn-cac-encode fn-cait-size
          fn-caa-pending fn-caa-preparation fn-caa-root
          fn-cai-put-is-existing-trie-put)))))
