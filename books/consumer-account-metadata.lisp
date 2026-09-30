; Proof-only full account metadata relation for the actual fn-caac-step.
; These annotation/relation traversals never run at admission, publication,
; authentication or recovery serving. They name the maintained constructor
; obligation; bounded producers must establish it in the same pass.
(in-package "ACL2")
(include-book "consumer-account-initial")
(include-book "consumer-account-relation")

(defun fn-caam-list-annotation (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (list (fn-scs-summary rows) (fn-scs-summary (car rows))
            (fn-caam-list-annotation (cdr rows)))
    nil))

(defun fn-caam-field-annotation (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fields)
      (cons (fn-scs-summary (car fields))
            (fn-caam-field-annotation (cdr fields)))
    nil))

(defun fn-caam-preparation-annotation (prep)
  (declare (xargs :guard t :verify-guards nil))
  (let ((root (fn-cp-nth 5 prep)))
    (list :prep-carries
          (fn-caam-list-annotation (fn-cp-nth 2 prep))
          (fn-caam-list-annotation (fn-cp-nth 3 prep))
          (fn-caam-list-annotation (fn-cp-nth 4 prep))
          (fn-cait-annotation (fn-cp-nth 2 root))
          (fn-scs-summary (fn-cp-nth 3 root)))))

(defun fn-caam-annotation (cp)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((a (fn-cp-nth 6 cp)) (p (fn-cp-nth 5 a)))
    (list :account-carries (fn-caam-field-annotation cp)
          (fn-caam-list-annotation (fn-cp-nth 4 a))
          (and p (fn-caam-preparation-annotation (fn-cp-nth 5 p))))))

(defun fn-caam-correspondsp (cp metadata)
  (declare (xargs :guard t :verify-guards nil))
  (equal metadata (fn-caam-annotation cp)))

(defthm fn-caam-list-carry-is-exact
  (implies (true-listp rows)
           (equal (fn-caac-list-carry (fn-caam-list-annotation rows))
                  (fn-scs-summary rows)))
  :hints (("Goal" :in-theory
           (e/d (fn-caac-list-carry fn-caam-list-annotation fn-cp-nth)
                (fn-scs-summary fn-cait-size)))))

(defthm fn-caam-list-cons-maintains-annotation
  (implies (and (true-listp tail)
                (equal head-carry (fn-scs-summary head))
                (equal tail-metadata (fn-caam-list-annotation tail)))
           (equal (fn-caac-list-cons head-carry tail-metadata)
                  (fn-caam-list-annotation (cons head tail))))
  :hints (("Goal"
           :use ((:instance fn-scs-cons-preserves-canonical-size
                            (x head) (y tail)
                            (a (fn-scs-summary head)) (d (fn-scs-summary tail))))
           :in-theory
           (e/d (fn-caac-list-cons fn-caam-list-annotation)
                (fn-caac-list-carry fn-cait-size fn-scs-summary fn-scs-cons)))))

(defthm fn-caam-field-annotation-corresponds
  (implies (true-listp fields)
           (fn-scs-correspondsp (fn-caam-field-annotation fields) fields))
  :hints (("Goal" :induct (fn-caam-field-annotation fields)
           :in-theory (e/d (fn-caam-field-annotation fn-scs-correspondsp)
                            (fn-scs-summary)))))

(defthm fn-caam-corresponding-fields-are-exact-annotations
  (implies (fn-scs-correspondsp carries fields)
           (equal carries (fn-caam-field-annotation fields)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scs-correspondsp carries fields)
           :in-theory (e/d (fn-caam-field-annotation fn-scs-correspondsp)
                            (fn-scs-summary)))))

(local
 (defthm fn-caam-initial-metadata-is-fixed-four
   (let ((metadata (mv-nth 1 (fn-caac-initial h in f hn inn))))
     (equal metadata (list :account-carries (fn-cp-nth 1 metadata) nil nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (e/d (fn-caac-initial fn-caac-metadata fn-cp-nth)
                 (fn-caac-authority-carry fn-caac-atom fn-cait-size))))))

(defthm fn-caam-initial-establishes-full-metadata
  (implies (and (fn-scc-octet-listp history)
                (equal hn (len history))
                (fn-scc-octet-listp incarnation)
                (equal in (len incarnation))
                (integerp frontier))
           (fn-caam-correspondsp
             (mv-nth 0 (fn-caac-initial history incarnation frontier hn in))
             (mv-nth 1 (fn-caac-initial history incarnation frontier hn in))))
  :hints (("Goal"
           :use ((:instance fn-caac-initial-seven-fields-correspond)
                 (:instance fn-caam-corresponding-fields-are-exact-annotations
                            (carries (fn-cp-nth 1 (mv-nth 1
                                       (fn-caac-initial history incarnation frontier hn in))))
                            (fields (fn-cp-initial history incarnation frontier)))
                 (:instance fn-caam-initial-metadata-is-fixed-four
                            (h history) (in incarnation) (f frontier)
                            (hn hn) (inn in)))
           :in-theory
           (e/d (fn-caam-correspondsp fn-caam-annotation
                 fn-caam-list-annotation fn-cp-initial fn-cp-state fn-cp-state-carry
                 fn-cp-nth)
                (fn-caac-initial fn-caac-metadata fn-caam-field-annotation
                 fn-scs-correspondsp fn-scs-summary)))))

(defthm fn-caam-prepared-root-carry-is-exact
  (let* ((root (fn-caa-root policy index credentials))
         (prep (fn-caa-preparation phase old reversed forward root namespace watermark)))
    (implies (and (integerp policy) (true-listp index))
             (equal (fn-caac-root-carry root (fn-caam-preparation-annotation prep))
                    (fn-scs-summary root))))
  :hints (("Goal"
           :use ((:instance fn-cait-carry-of-annotation (trie index))
                 (:instance fn-caac-spine-keeps-canonical-size
                            (cs (list (fn-caac-atom :account-root) (fn-caac-atom policy)
                                      (fn-cait-carry (fn-cait-annotation index))
                                      (fn-cait-size (fn-scs-summary credentials))))
                            (xs (list :account-root policy index credentials))))
           :in-theory
           (e/d (fn-caac-root-carry fn-caam-preparation-annotation
                 fn-caa-root fn-caa-preparation fn-cp-nth fn-scs-correspondsp
                 fn-caac-atom)
                (fn-caac-spine fn-cait-carry fn-cait-annotation
                 fn-scs-summary fn-cait-size fn-scs-atom)))))

(local
 (defthm fn-caam-supported-atom-carry-is-exact
   (implies (or (integerp x) (characterp x) (stringp x) (symbolp x))
            (equal (fn-caac-atom x) (fn-scs-summary x)))
   :hints (("Goal" :in-theory (enable fn-caac-atom)))))

(defthm fn-caam-preparation-carry-is-exact
  (let* ((root (fn-caa-root policy index credentials))
         (prep (fn-caa-preparation phase old reversed forward root namespace watermark)))
    (implies (and (symbolp phase) (integerp policy) (true-listp index)
                  (true-listp old) (true-listp reversed) (true-listp forward)
                  (fn-scc-octet-listp namespace) (equal (len namespace) 40)
                  (integerp watermark))
             (equal (fn-caac-prep-carry prep (fn-caam-preparation-annotation prep))
                    (fn-scs-summary prep))))
  :hints (("Goal"
           :use ((:instance fn-caam-prepared-root-carry-is-exact)
                 (:instance fn-scs-octets-establishes-canonical-size
                            (n 40) (xs namespace))
                 (:instance fn-caac-spine-keeps-canonical-size
                            (xs (fn-caa-preparation phase old reversed forward
                                  (fn-caa-root policy index credentials) namespace watermark))
                            (cs (list (fn-caac-atom :account-preparation)
                                      (fn-caac-atom phase)
                                      (fn-caac-list-carry (fn-caam-list-annotation old))
                                      (fn-caac-list-carry (fn-caam-list-annotation reversed))
                                      (fn-caac-list-carry (fn-caam-list-annotation forward))
                                      (fn-caac-root-carry (fn-caa-root policy index credentials)
                                        (fn-caam-preparation-annotation
                                          (fn-caa-preparation phase old reversed forward
                                            (fn-caa-root policy index credentials) namespace watermark)))
                                      (fn-scs-octets 40) (fn-caac-atom watermark)))))
           :in-theory
           (e/d (fn-caac-prep-carry fn-caam-preparation-annotation
                 fn-caa-root fn-caa-preparation fn-cp-nth fn-scs-correspondsp
                 fn-caac-atom)
                (fn-caac-spine fn-caac-root-carry fn-caac-list-carry
                 fn-caam-list-annotation fn-scs-summary fn-scs-atom
                 fn-scs-octets fn-cait-size fn-cait-carry fn-cait-annotation)))))

; Proof-only constructor domain. It names fixed shape/byte facts; the account
; representation relation separately supplies exact row/index authority.
(defun fn-caam-preparation-sizep (prep)
  (declare (xargs :guard t :verify-guards nil))
  (let ((root (fn-cp-nth 5 prep)))
    (and (equal prep (fn-caa-preparation (fn-cp-nth 1 prep)
                          (fn-cp-nth 2 prep) (fn-cp-nth 3 prep)
                          (fn-cp-nth 4 prep) root (fn-cp-nth 6 prep)
                          (fn-cp-nth 7 prep)))
         (equal root (fn-caa-root (fn-cp-nth 1 root)
                                  (fn-cp-nth 2 root) (fn-cp-nth 3 root)))
         (symbolp (fn-cp-nth 1 prep)) (integerp (fn-cp-nth 1 root))
         (true-listp (fn-cp-nth 2 root))
         (true-listp (fn-cp-nth 2 prep)) (true-listp (fn-cp-nth 3 prep))
         (true-listp (fn-cp-nth 4 prep))
         (fn-scc-octet-listp (fn-cp-nth 6 prep))
         (equal (len (fn-cp-nth 6 prep)) 40)
         (integerp (fn-cp-nth 7 prep)))))

(defthm fn-caam-shaped-preparation-carry-is-exact
  (implies (fn-caam-preparation-sizep prep)
           (equal (fn-caac-prep-carry prep (fn-caam-preparation-annotation prep))
                  (fn-scs-summary prep)))
  :hints (("Goal"
           :use ((:instance fn-caam-preparation-carry-is-exact
                            (phase (fn-cp-nth 1 prep)) (old (fn-cp-nth 2 prep))
                            (reversed (fn-cp-nth 3 prep)) (forward (fn-cp-nth 4 prep))
                            (policy (fn-cp-nth 1 (fn-cp-nth 5 prep)))
                            (index (fn-cp-nth 2 (fn-cp-nth 5 prep)))
                            (credentials (fn-cp-nth 3 (fn-cp-nth 5 prep)))
                            (namespace (fn-cp-nth 6 prep)) (watermark (fn-cp-nth 7 prep))))
           :in-theory (e/d (fn-caam-preparation-sizep)
                            (fn-caac-prep-carry fn-caam-preparation-annotation
                             fn-caa-root fn-caa-preparation fn-cp-nth
                             fn-scs-summary)))))

(defun fn-caam-pending-sizep (p)
  (declare (xargs :guard t :verify-guards nil))
  (or (null p)
      (and (equal p (fn-caa-pending (fn-cp-nth 1 p) (fn-cp-nth 2 p)
                                    (fn-cp-nth 3 p) (fn-cp-nth 4 p)
                                    (fn-cp-nth 5 p) (fn-cp-nth 6 p)
                                    (fn-cp-nth 7 p) (fn-cp-nth 8 p)))
           (fn-scc-octet-listp (fn-cp-nth 1 p))
           (integerp (fn-cp-nth 2 p)) (integerp (fn-cp-nth 3 p))
           (integerp (fn-cp-nth 4 p))
           (fn-caam-preparation-sizep (fn-cp-nth 5 p))
           (fn-scc-octet-listp (fn-cp-nth 6 p))
           (fn-scc-octet-listp (fn-cp-nth 7 p))
           (equal (len (fn-cp-nth 7 p)) 32)
           (booleanp (fn-cp-nth 8 p)))))

(defthm fn-caam-pending-constructor-carry-is-exact
  (let ((p (fn-caa-pending candidate base count watermark prep last digest ready)))
    (implies (and (fn-scc-octet-listp candidate) (integerp base) (integerp count)
                  (integerp watermark) (fn-caam-preparation-sizep prep)
                  (fn-scc-octet-listp last) (fn-scc-octet-listp digest)
                  (equal (len digest) 32) (booleanp ready))
             (equal (fn-caac-pending-carry p (fn-caam-preparation-annotation prep))
                    (fn-scs-summary p))))
  :hints (("Goal"
           :use ((:instance fn-scs-octets-establishes-canonical-size
                            (n (len candidate)) (xs candidate))
                 (:instance fn-scs-octets-establishes-canonical-size
                            (n (len last)) (xs last))
                 (:instance fn-scs-octets-establishes-canonical-size
                            (n 32) (xs digest))
                 (:instance fn-caam-shaped-preparation-carry-is-exact)
                 (:instance fn-caac-spine-keeps-canonical-size
                            (xs (fn-caa-pending candidate base count watermark prep last digest ready))
                            (cs (list (fn-caac-atom :adoption)
                                      (fn-scs-octets (len candidate))
                                      (fn-caac-atom base) (fn-caac-atom count)
                                      (fn-caac-atom watermark)
                                      (fn-caac-prep-carry prep (fn-caam-preparation-annotation prep))
                                      (fn-scs-octets (len last)) (fn-scs-octets 32)
                                      (fn-caac-atom ready)))))
           :in-theory
           (e/d (fn-caac-pending-carry fn-caa-pending fn-cp-nth
                 fn-scs-correspondsp fn-caac-atom booleanp)
                (fn-caac-spine fn-caac-prep-carry fn-caam-preparation-annotation
                 fn-caam-preparation-sizep fn-scs-summary fn-scs-octets
                 fn-cait-size fn-scs-atom)))))

(defthm fn-caam-pending-carry-is-exact
  (implies (fn-caam-pending-sizep p)
           (equal (fn-caac-pending-carry p
                    (and p (fn-caam-preparation-annotation (fn-cp-nth 5 p))))
                  (fn-scs-summary p)))
  :hints (("Goal"
           :use ((:instance fn-caam-pending-constructor-carry-is-exact
                            (candidate (fn-cp-nth 1 p)) (base (fn-cp-nth 2 p))
                            (count (fn-cp-nth 3 p)) (watermark (fn-cp-nth 4 p))
                            (prep (fn-cp-nth 5 p)) (last (fn-cp-nth 6 p))
                            (digest (fn-cp-nth 7 p)) (ready (fn-cp-nth 8 p))))
           :in-theory
           (e/d (fn-caam-pending-sizep)
                (fn-caac-pending-carry fn-caa-pending fn-cp-nth
                 fn-caam-preparation-annotation fn-scs-summary)))))

(defthm fn-caam-authority-constructor-carry-is-exact
  (let ((a (list :authority revision watermark namespace accounts pending)))
    (implies (and (integerp revision) (integerp watermark)
                  (or (null namespace)
                      (and (fn-scc-octet-listp namespace) (equal (len namespace) 40)))
                  (true-listp accounts) (fn-caam-pending-sizep pending))
             (equal (fn-caac-authority-carry a
                      (fn-caam-list-annotation accounts)
                      (and pending (fn-caam-preparation-annotation (fn-cp-nth 5 pending))))
                    (fn-scs-summary a))))
  :hints (("Goal"
           :use ((:instance fn-scs-octets-establishes-canonical-size
                            (n 40) (xs namespace))
                 (:instance fn-caam-pending-carry-is-exact (p pending))
                 (:instance fn-caac-spine-keeps-canonical-size
                            (xs (list :authority revision watermark namespace accounts pending))
                            (cs (list (fn-caac-atom :authority)
                                      (fn-caac-atom revision) (fn-caac-atom watermark)
                                      (if namespace (fn-scs-octets 40) (fn-caac-atom nil))
                                      (fn-caac-list-carry (fn-caam-list-annotation accounts))
                                      (fn-caac-pending-carry pending
                                        (and pending (fn-caam-preparation-annotation
                                                       (fn-cp-nth 5 pending))))))))
           :in-theory
           (e/d (fn-caac-authority-carry fn-cp-nth fn-scs-correspondsp fn-caac-atom)
                (fn-caac-spine fn-caac-pending-carry fn-caac-list-carry
                 fn-caam-list-annotation fn-caam-preparation-annotation
                 fn-caam-pending-sizep fn-caam-preparation-sizep
                 fn-scs-summary fn-scs-atom fn-scs-octets fn-cait-size)))))

(defun fn-caam-authority-sizep (a)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal a (list :authority (fn-cp-nth 1 a) (fn-cp-nth 2 a)
                           (fn-cp-nth 3 a) (fn-cp-nth 4 a) (fn-cp-nth 5 a)))
       (integerp (fn-cp-nth 1 a)) (integerp (fn-cp-nth 2 a))
       (or (null (fn-cp-nth 3 a))
           (and (fn-scc-octet-listp (fn-cp-nth 3 a))
                (equal (len (fn-cp-nth 3 a)) 40)))
       (true-listp (fn-cp-nth 4 a)) (fn-caam-pending-sizep (fn-cp-nth 5 a))))

(defthm fn-caam-authority-carry-is-exact
  (implies (fn-caam-authority-sizep a)
           (equal (fn-caac-authority-carry a
                    (fn-caam-list-annotation (fn-cp-nth 4 a))
                    (and (fn-cp-nth 5 a)
                         (fn-caam-preparation-annotation (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                  (fn-scs-summary a)))
  :hints (("Goal"
           :use ((:instance fn-caam-authority-constructor-carry-is-exact
                            (revision (fn-cp-nth 1 a)) (watermark (fn-cp-nth 2 a))
                            (namespace (fn-cp-nth 3 a)) (accounts (fn-cp-nth 4 a))
                            (pending (fn-cp-nth 5 a))))
           :in-theory
           (e/d (fn-caam-authority-sizep)
                (fn-caac-authority-carry fn-caam-list-annotation
                 fn-caam-preparation-annotation fn-cp-nth fn-scs-summary)))))

(defthm fn-caam-metadata-constructor-maintains-full-annotation
  (let* ((old (fn-cp-state-carry history incarnation old-frontier next-epoch entries old-authority))
         (next (fn-cp-state-carry history incarnation frontier next-epoch entries authority))
         (pending (fn-cp-nth 5 authority)))
    (implies (and (integerp frontier) (fn-caam-authority-sizep authority))
             (equal
               (fn-caac-metadata next (fn-caam-field-annotation old)
                 (fn-caam-list-annotation (fn-cp-nth 4 authority))
                 (and pending (fn-caam-preparation-annotation (fn-cp-nth 5 pending))))
               (fn-caam-annotation next))))
  :hints (("Goal"
           :use ((:instance fn-caam-authority-carry-is-exact (a authority)))
           :in-theory
           (e/d (fn-caac-metadata fn-cp-state-carry fn-caam-annotation
                 fn-caam-field-annotation fn-cp-nth fn-caac-atom)
                (fn-caac-authority-carry fn-caam-authority-sizep
                 fn-caam-list-annotation fn-caam-preparation-annotation
                 fn-scs-summary fn-scs-atom)))))

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
                 (integerp (fn-cp-nth 1 event)) (integerp (fn-cp-nth 2 event))
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

(in-theory (disable fn-caam-list-annotation fn-caam-field-annotation
                    fn-caam-preparation-annotation fn-caam-annotation
                    fn-caam-correspondsp))
