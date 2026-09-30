; Same-pass full metadata composition for actual account transitions.
; Relations below are proof-only. No annotation is recomputed while serving.
(in-package "ACL2")
(include-book "consumer-account-metadata-preserved")

(local
 (defthm fn-caamt-old-field-projection
  (equal (fn-cp-nth 1 (fn-caam-annotation s)) (fn-caam-field-annotation s))
  :hints (("Goal" :in-theory
           (e/d (fn-caam-annotation fn-cp-nth)
                (fn-caam-field-annotation fn-caam-list-annotation
                 fn-caam-preparation-annotation))))))

(defthm fn-caamt-success-composes-full-metadata
 (let* ((s (fn-cp-state-carry history incarnation old-frontier next-epoch entries old-a))
        (one (fn-caa-success s a event root))
        (next (fn-cp-nth 1 one)) (p (fn-cp-nth 5 a)))
  (implies
   (and (fn-caam-authority-sizep a)
        (equal metadata (fn-caam-annotation s))
        (equal accounts-metadata (fn-caam-list-annotation (fn-cp-nth 4 a)))
        (equal prep-metadata (and p (fn-caam-preparation-annotation (fn-cp-nth 5 p)))))
   (fn-caam-correspondsp
    next (mv-nth 1 (fn-caac-finish one metadata accounts-metadata prep-metadata root-carry)))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-caam-metadata-constructor-maintains-full-annotation
                 (old-authority old-a) (authority a)
                 (frontier (1+ (nfix (fn-cp-nth 1 event))))))
          :in-theory
          (e/d (fn-caac-finish fn-caa-success fn-caam-correspondsp
                fn-cp-state-carry fn-cp-nth)
               (fn-caam-authority-sizep fn-caam-annotation fn-caam-field-annotation
                fn-caam-list-annotation fn-caam-preparation-annotation
                fn-caac-metadata nfix)))))

(local
 (defthm fn-caamt-begin-success-frame
  (let ((one (fn-caa-begin s a event op)))
   (implies (equal (fn-cp-nth 0 one) :ok)
    (equal one (fn-caa-success s (fn-cp-nth 6 (fn-cp-nth 1 one)) event nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caa-begin fn-caa-success fn-cp-state-carry fn-cp-nth)
                (fn-caa-namespace fn-cp-authority-namespacep fn-caa-authority-pending
                 fn-caa-preparation fn-caa-pending fn-caa-root fn-sha256 fn-cac-encode))))))
(local
 (defthm fn-caamt-begin-metadata-components
  (let ((one (fn-caa-begin s a event op)))
   (implies (equal (fn-cp-nth 0 one) :ok)
    (and
     (equal (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))
     (equal (and (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one)))
                  (fn-caam-preparation-annotation
                   (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))))))
            (list :prep-carries (fn-caam-list-annotation (fn-cp-nth 4 a))
                  nil nil nil (fn-caac-atom nil))))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-begin fn-caa-success fn-cp-state-carry fn-cp-nth
                 fn-caam-preparation-annotation fn-caa-authority-pending
                 fn-caa-preparation fn-caa-pending fn-caa-root)
                (fn-caa-namespace fn-cp-authority-namespacep
                 fn-caam-list-annotation fn-sha256 fn-cac-encode))))))

(defthm fn-caam-begin-maintains-full-metadata
 (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
        (one (fn-caa-begin s a event op))
        (am (fn-cp-nth 2 metadata))
        (pm (list :prep-carries am nil nil nil (fn-caac-atom nil))))
  (implies (and (fn-caam-authority-sizep a)
                (fn-scc-octet-listp (fn-cp-nth 1 op))
                (integerp (fn-cp-nth 4 op))
                (equal metadata (fn-caam-annotation s))
                (equal (fn-cp-nth 0 one) :ok))
   (fn-caam-correspondsp (fn-cp-nth 1 one)
    (mv-nth 1 (fn-caac-finish one metadata am pm nil)))))
 :hints (("Goal"
          :use ((:instance fn-caamt-begin-metadata-components
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-begin-success-frame
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caam-begin-establishes-size-domain
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-success-composes-full-metadata
                 (old-frontier frontier) (old-a a)
                 (a (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-begin
                     (fn-cp-state-carry history incarnation frontier next-epoch entries a) a event op))))
                 (root nil) (root-carry nil)
                 (accounts-metadata (fn-cp-nth 2 metadata))
                 (prep-metadata (list :prep-carries (fn-cp-nth 2 metadata)
                                      nil nil nil (fn-caac-atom nil)))))
          :in-theory
          (e/d (fn-caam-annotation fn-cp-state-carry fn-cp-nth)
               (fn-caamt-begin-metadata-components fn-caam-begin-establishes-size-domain
                fn-caa-begin fn-caa-success fn-caac-finish fn-caam-correspondsp
                fn-caam-authority-sizep fn-caam-field-annotation
                fn-caam-list-annotation fn-caam-preparation-annotation
                fn-caac-atom)))))

(local
 (defthm fn-caamt-seal-needs-pending
  (implies (equal (fn-cp-nth 0 (fn-caa-seal s a event op)) :ok)
           (consp (fn-cp-nth 5 a)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caa-seal fn-cp-nth)
                (fn-caa-success fn-caa-count-digest-matchp fn-caa-authority-pending
                 fn-caa-preparation fn-caa-pending))))))
(local
 (defthm fn-caamt-seal-success-frame
  (let ((one (fn-caa-seal s a event op)))
   (implies (equal (fn-cp-nth 0 one) :ok)
    (equal one (fn-caa-success s (fn-cp-nth 6 (fn-cp-nth 1 one)) event nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caa-seal fn-caa-success fn-cp-state-carry fn-cp-nth)
                (fn-caa-count-digest-matchp fn-caa-authority-pending
                 fn-caa-preparation fn-caa-pending fn-caa-root))))))
(local
 (defthm fn-caamt-seal-metadata-components
  (let ((one (fn-caa-seal s a event op))
        (pm (fn-caam-preparation-annotation (fn-cp-nth 5 (fn-cp-nth 5 a)))))
   (implies (equal (fn-cp-nth 0 one) :ok)
    (and
     (equal (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a))
     (equal (and (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one)))
                  (fn-caam-preparation-annotation
                   (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))))))
            (list :prep-carries nil (fn-cp-nth 2 pm) nil
                  (fn-cp-nth 4 pm) (fn-cp-nth 5 pm))))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-seal fn-caa-success fn-cp-state-carry fn-cp-nth
                 fn-caam-preparation-annotation fn-caa-authority-pending
                 fn-caa-preparation fn-caa-pending)
                (fn-caa-count-digest-matchp fn-caam-list-annotation fn-cait-annotation
                 fn-scs-summary))))))

(defthm fn-caam-seal-maintains-full-metadata
 (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
        (one (fn-caa-seal s a event op))
        (am (fn-cp-nth 2 metadata)) (pm (fn-cp-nth 3 metadata))
        (new-pm (list :prep-carries nil (fn-cp-nth 2 pm) nil
                      (fn-cp-nth 4 pm) (fn-cp-nth 5 pm))))
  (implies (and (fn-caam-authority-sizep a)
                (equal metadata (fn-caam-annotation s))
                (equal (fn-cp-nth 0 one) :ok))
   (fn-caam-correspondsp (fn-cp-nth 1 one)
    (mv-nth 1 (fn-caac-finish one metadata am new-pm nil)))))
 :hints (("Goal"
          :use ((:instance fn-caamt-seal-needs-pending
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-seal-metadata-components
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-seal-success-frame
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caam-seal-preserves-size-domain
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-success-composes-full-metadata
                 (old-frontier frontier) (old-a a)
                 (a (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-seal
                     (fn-cp-state-carry history incarnation frontier next-epoch entries a) a event op))))
                 (root nil) (root-carry nil)
                 (accounts-metadata (fn-cp-nth 2 metadata))
                 (prep-metadata (list :prep-carries nil (fn-cp-nth 2 (fn-cp-nth 3 metadata)) nil
                          (fn-cp-nth 4 (fn-cp-nth 3 metadata))
                          (fn-cp-nth 5 (fn-cp-nth 3 metadata))))))
          :in-theory
          (e/d (fn-caam-annotation fn-cp-state-carry fn-cp-nth)
               (fn-caamt-seal-metadata-components fn-caam-seal-preserves-size-domain
                fn-caa-seal fn-caa-success fn-caac-finish fn-caam-correspondsp
                fn-caam-authority-sizep fn-caam-field-annotation
                fn-caam-list-annotation fn-caam-preparation-annotation)))))

(local
 (defthm fn-caamt-fence-needs-pending
  (implies (equal (fn-cp-nth 0 (fn-caa-fence s a event op)) :ok)
           (consp (fn-cp-nth 5 a)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caa-fence fn-cp-nth)
                (fn-caa-success fn-caa-count-digest-matchp fn-cp-uintp))))))
(local
 (defthm fn-caamt-fence-success-frame
  (let* ((one (fn-caa-fence s a event op))
         (root (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
   (implies (equal (fn-cp-nth 0 one) :ok)
    (equal one (fn-caa-success s (fn-cp-nth 6 (fn-cp-nth 1 one)) event root))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caa-fence fn-caa-success fn-cp-state-carry fn-cp-nth)
                (fn-caa-count-digest-matchp fn-cp-uintp))))))
(local
 (defthm fn-caamt-fence-metadata-components
  (let ((one (fn-caa-fence s a event op)))
   (implies (equal (fn-cp-nth 0 one) :ok)
    (and
     (equal (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 one)))
            (fn-cp-nth 4 (fn-cp-nth 5 (fn-cp-nth 5 a))))
     (equal (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))) nil))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-fence fn-caa-success fn-cp-state-carry fn-cp-nth)
                (fn-caa-count-digest-matchp fn-cp-uintp))))))
(local
 (defthm fn-caamt-forward-annotation-projection
  (equal (fn-cp-nth 3 (fn-caam-preparation-annotation prep))
         (fn-caam-list-annotation (fn-cp-nth 4 prep)))
  :hints (("Goal" :in-theory
           (e/d (fn-caam-preparation-annotation fn-cp-nth)
                (fn-caam-list-annotation fn-cait-annotation fn-scs-summary))))))
(local
 (defthm fn-caamt-shaped-root-carry-is-exact
  (implies (fn-caam-preparation-sizep prep)
   (equal (fn-caac-root-carry (fn-cp-nth 5 prep) (fn-caam-preparation-annotation prep))
          (fn-scs-summary (fn-cp-nth 5 prep))))
  :hints (("Goal"
           :use ((:instance fn-caam-prepared-root-carry-is-exact
                  (policy (fn-cp-nth 1 (fn-cp-nth 5 prep)))
                  (index (fn-cp-nth 2 (fn-cp-nth 5 prep)))
                  (credentials (fn-cp-nth 3 (fn-cp-nth 5 prep)))
                  (phase (fn-cp-nth 1 prep)) (old (fn-cp-nth 2 prep))
                  (reversed (fn-cp-nth 3 prep)) (forward (fn-cp-nth 4 prep))
                  (namespace (fn-cp-nth 6 prep)) (watermark (fn-cp-nth 7 prep))))
           :in-theory
           (e/d (fn-caam-preparation-sizep)
                (fn-caa-preparation fn-caa-root fn-cp-nth fn-caac-root-carry
                 fn-caam-preparation-annotation fn-scs-summary))))))

(defthm fn-caam-fence-maintains-full-metadata-and-root
 (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
        (one (fn-caa-fence s a event op))
        (prep (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (pm (fn-cp-nth 3 metadata))
        (result (fn-caac-finish one metadata (fn-cp-nth 3 pm) nil
                                  (fn-caac-root-carry (fn-cp-nth 5 prep) pm))))
  (implies (and (fn-caam-authority-sizep a)
                (equal metadata (fn-caam-annotation s))
                (equal (fn-cp-nth 0 one) :ok))
   (and (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))
        (equal (mv-nth 2 result) (fn-scs-summary (fn-cp-nth 2 one))))))
 :hints (("Goal"
          :use ((:instance fn-caamt-fence-needs-pending
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-fence-metadata-components
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-fence-success-frame
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caam-fence-preserves-size-domain
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-success-composes-full-metadata
                 (old-frontier frontier) (old-a a)
                 (a (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-fence
                     (fn-cp-state-carry history incarnation frontier next-epoch entries a) a event op))))
                 (root (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                 (root-carry (fn-caac-root-carry (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a)))
                                               (fn-cp-nth 3 metadata)))
                 (accounts-metadata (fn-cp-nth 3 (fn-cp-nth 3 metadata)))
                 (prep-metadata nil)))
          :in-theory
          (e/d (fn-caam-annotation fn-caam-authority-sizep fn-caam-pending-sizep
                fn-cp-state-carry fn-cp-nth fn-caac-finish fn-caa-success)
               (fn-caamt-fence-metadata-components fn-caam-fence-preserves-size-domain
                fn-caa-fence fn-caam-correspondsp fn-caam-preparation-sizep
                fn-caam-field-annotation fn-caam-list-annotation
                fn-caam-preparation-annotation fn-caa-root fn-caa-preparation fn-caa-pending
                fn-scs-summary fn-caac-root-carry fn-caac-metadata nfix)))))

(local
 (defthm fn-caamt-list-annotation-projections
  (and (equal (fn-cp-nth 1 (fn-caam-list-annotation rows))
              (if (consp rows) (fn-scs-summary (car rows)) nil))
       (equal (fn-cp-nth 2 (fn-caam-list-annotation rows))
              (if (consp rows) (fn-caam-list-annotation (cdr rows)) nil)))
  :hints (("Goal" :in-theory
           (e/d (fn-caam-list-annotation fn-cp-nth) (fn-scs-summary))))))
(local
 (defthm fn-caamt-prepare-components-maintain-annotation
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (one (fn-caa-prepare s a event))
         (pm (fn-caam-preparation-annotation prep))
         (head (fn-cp-nth 0 (fn-cp-nth 3 prep)))
         (new-prep (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one)))))
         (new-root (fn-cp-nth 5 new-prep))
         (credential (fn-cp-nth 0 (fn-cp-nth 3 new-root)))
         (credentials-carry
           (if (fn-cp-nth 3 head)
               (fn-scs-cons (fn-caac-credential-value-carry credential)
                            (fn-cait-size (fn-cp-nth 5 pm)))
             (fn-cait-size (fn-cp-nth 5 pm))))
         (pm1 (list :prep-carries nil (fn-cp-nth 2 (fn-cp-nth 2 pm))
                    (fn-caac-list-cons (fn-cp-nth 1 (fn-cp-nth 2 pm)) (fn-cp-nth 3 pm))
                    (fn-cp-nth 4 pm) credentials-carry)))
   (implies
    (and (fn-caam-authority-sizep a) (equal (fn-cp-nth 0 one) :ok)
         (implies (fn-cp-nth 3 head)
                  (equal (fn-caac-credential-value-carry credential)
                         (fn-scs-summary credential))))
    (equal pm1 (fn-caam-preparation-annotation new-prep))))
  :hints (("Goal"
           :use ((:instance fn-caam-list-cons-maintains-annotation
                  (head (car (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a))))) (tail (fn-cp-nth 4 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                  (head-carry (fn-scs-summary (car (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a))))))
                  (tail-metadata (fn-caam-list-annotation (fn-cp-nth 4 (fn-cp-nth 5 (fn-cp-nth 5 a))))))
                 (:instance fn-scs-cons-preserves-canonical-size
                  (x (fn-cp-nth 2 (fn-cai-get-octets (fn-cp-nth 1 (car (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a))))) (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a)))))))
                  (y (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                  (a (fn-caac-credential-value-carry (fn-cp-nth 2 (fn-cai-get-octets (fn-cp-nth 1 (car (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a))))) (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a))))))))
                  (d (fn-scs-summary (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a))))))))
           :in-theory
           (e/d (fn-caa-prepare fn-caa-success fn-caa-authority-pending
                 fn-caa-preparation fn-caa-pending fn-caa-root fn-cp-state-carry fn-cp-nth
                 fn-caam-authority-sizep fn-caam-pending-sizep fn-caam-preparation-sizep
                 fn-caam-preparation-annotation)
                (fn-cai-get-octets fn-cai-get-is-existing-trie-get
                 fn-caam-list-annotation fn-caac-list-cons fn-cait-annotation fn-cait-size
                 fn-scs-summary fn-scs-cons fn-caac-credential-value-carry))))))

(local
 (defthm fn-caamt-prepare-success-frame
  (let ((one (fn-caa-prepare s a event)))
   (implies (equal (fn-cp-nth 0 one) :ok)
    (and (equal one (fn-caa-success s (fn-cp-nth 6 (fn-cp-nth 1 one)) event nil))
         (consp (fn-cp-nth 5 a))
         (consp (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))))
         (equal (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 one))) (fn-cp-nth 4 a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-caa-prepare fn-caa-success fn-caa-authority-pending
                 fn-caa-pending fn-cp-state-carry fn-cp-nth)
                (fn-caa-preparation fn-caa-root fn-cai-get-octets))))))

(defthm fn-caam-prepare-maintains-full-metadata
 (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
        (one (fn-caa-prepare s a event))
        (prep (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (head (fn-cp-nth 0 (fn-cp-nth 3 prep)))
        (pm (fn-cp-nth 3 metadata))
        (new-prep (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one)))))
        (credential (fn-cp-nth 0 (fn-cp-nth 3 (fn-cp-nth 5 new-prep))))
        (new-pm (list :prep-carries nil (fn-cp-nth 2 (fn-cp-nth 2 pm))
                 (fn-caac-list-cons (fn-cp-nth 1 (fn-cp-nth 2 pm)) (fn-cp-nth 3 pm))
                 (fn-cp-nth 4 pm)
                 (if (fn-cp-nth 3 head)
                     (fn-scs-cons (fn-caac-credential-value-carry credential)
                                  (fn-cait-size (fn-cp-nth 5 pm)))
                   (fn-cait-size (fn-cp-nth 5 pm))))))
  (implies (and (fn-caam-authority-sizep a)
                (equal metadata (fn-caam-annotation s))
                (equal (fn-cp-nth 0 one) :ok)
                (implies (fn-cp-nth 3 head)
                         (equal (fn-caac-credential-value-carry credential)
                                (fn-scs-summary credential))))
   (fn-caam-correspondsp (fn-cp-nth 1 one)
    (mv-nth 1 (fn-caac-finish one metadata (fn-cp-nth 2 metadata) new-pm nil)))))
 :hints (("Goal"
          :use ((:instance fn-caamt-prepare-success-frame
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-prepare-components-maintain-annotation
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caam-prepare-preserves-size-domain
                 (s (fn-cp-state-carry history incarnation frontier next-epoch entries a)))
                (:instance fn-caamt-success-composes-full-metadata
                 (old-frontier frontier) (old-a a)
                 (a (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-prepare
                     (fn-cp-state-carry history incarnation frontier next-epoch entries a) a event))))
                 (root nil) (root-carry nil)
                 (accounts-metadata (fn-cp-nth 2 metadata))
                 (prep-metadata
                  (let* ((pm (fn-cp-nth 3 metadata))
                         (prep (fn-cp-nth 5 (fn-cp-nth 5 a)))
                         (head (fn-cp-nth 0 (fn-cp-nth 3 prep)))
                         (one (fn-caa-prepare
                               (fn-cp-state-carry history incarnation frontier next-epoch entries a) a event))
                         (new-prep (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one)))))
                         (credential (fn-cp-nth 0 (fn-cp-nth 3 (fn-cp-nth 5 new-prep)))))
                    (list :prep-carries nil (fn-cp-nth 2 (fn-cp-nth 2 pm))
                      (fn-caac-list-cons (fn-cp-nth 1 (fn-cp-nth 2 pm)) (fn-cp-nth 3 pm))
                      (fn-cp-nth 4 pm)
                      (if (fn-cp-nth 3 head)
                          (fn-scs-cons (fn-caac-credential-value-carry credential)
                                       (fn-cait-size (fn-cp-nth 5 pm)))
                        (fn-cait-size (fn-cp-nth 5 pm))))))))
          :in-theory
          (e/d (fn-caam-annotation fn-cp-state-carry fn-cp-nth)
               (fn-caamt-prepare-components-maintain-annotation fn-caam-prepare-preserves-size-domain
                fn-caa-prepare fn-caa-success fn-caac-finish fn-caam-correspondsp
                fn-caam-authority-sizep fn-caam-field-annotation fn-caam-list-annotation
                fn-caam-preparation-annotation fn-caac-list-cons fn-cait-size
                fn-scs-summary fn-scs-cons fn-caac-credential-value-carry)))))

(defthm fn-caam-discard-maintains-full-metadata
 (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
        (new-a (fn-caa-authority-pending a nil))
        (one (fn-caa-success s new-a event nil)))
  (implies (and (fn-caam-authority-sizep a)
                (equal metadata (fn-caam-annotation s)))
   (fn-caam-correspondsp (fn-cp-nth 1 one)
    (mv-nth 1 (fn-caac-finish one metadata (fn-cp-nth 2 metadata) nil nil)))))
 :hints (("Goal"
          :use ((:instance fn-caam-discard-preserves-size-domain)
                (:instance fn-caamt-success-composes-full-metadata
                 (old-frontier frontier) (old-a a) (a (fn-caa-authority-pending a nil))
                 (root nil) (root-carry nil)
                 (accounts-metadata (fn-cp-nth 2 metadata)) (prep-metadata nil)))
          :in-theory
          (e/d (fn-caam-annotation fn-cp-state-carry fn-cp-nth fn-caa-authority-pending)
               (fn-caam-discard-preserves-size-domain fn-caa-success fn-caac-finish
                fn-caam-correspondsp fn-caam-authority-sizep fn-caam-field-annotation
                fn-caam-list-annotation fn-caam-preparation-annotation)))))
