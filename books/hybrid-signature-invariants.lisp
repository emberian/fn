; Injectivity of the exact hybrid authored-source byte subject.
(in-package "ACL2")
(include-book "hybrid-signature")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-hybrid-signature-vocabulary)))
(local (in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes)))

(local
 (defthm fn-hsigi-take-len-append
   (implies (true-listp xs)
            (equal (take (len xs) (append xs rest)) xs))))

(local
 (defthm fn-hsigi-len-append
   (equal (len (append xs rest)) (+ (len xs) (len rest)))))

(local
 (defthm fn-hsigi-nthcdr-len-append
   (equal (nthcdr (len xs) (append xs rest)) rest)))

(local
 (defthm fn-hsigi-nthcdr-len-plus-append
   (equal (nthcdr (+ (len xs) (nfix k)) (append xs rest))
          (nthcdr (nfix k) rest))))

(local
 (defthm fn-hsigi-u16-length
   (equal (len (fn-cbor-u16-bytes n)) 2)
   :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes)))))

(local
 (defthm fn-hsigi-cons-extensional
   (implies (and (consp x) (consp y)
                 (equal (car x) (car y))
                 (equal (cdr x) (cdr y)))
            (equal x y))
   :rule-classes nil))

(local
 (defthm fn-hsigi-two-list-extensional
   (implies (and (true-listp x) (equal (len x) 2)
                 (true-listp y) (equal (len y) 2)
                 (equal (car x) (car y))
                 (equal (cadr x) (cadr y)))
            (equal x y))
   :rule-classes nil))

(defun fn-hsigi-principal (body)
  (declare (xargs :guard (true-listp body)))
  (take 32 (nthcdr 2 body)))

(defun fn-hsigi-ed-key (body)
  (declare (xargs :guard (true-listp body)))
  (take 32 (nthcdr 35 body)))

(defun fn-hsigi-ml-key (body)
  (declare (xargs :guard (true-listp body)))
  (take 1952 (nthcdr 68 body)))

(defun fn-hsigi-source (body)
  (declare (xargs :guard (true-listp body)))
  (nthcdr 2022 body))

(defthm fn-hsigi-principal-of-subject-body
  (implies (fn-hsig-subject-p principal keys source)
           (equal (fn-hsigi-principal
                   (fn-hsig-subject-body principal keys source))
                  principal))
  :hints (("Goal"
           :use ((:instance fn-hsigi-take-len-append
                            (xs principal)
                            (rest
                             (append
                              (list *fn-hsig-ed25519-algorithm*)
                              (cdr (car keys))
                              (list *fn-hsig-ml-dsa-65-algorithm*)
                              (cdr (cadr keys))
                              (fn-cbor-u16-bytes (len source)) source))))
           :in-theory (enable fn-hsigi-principal))))

(defthm fn-hsigi-ed-key-of-subject-body
  (implies (fn-hsig-subject-p principal keys source)
           (equal (fn-hsigi-ed-key
                   (fn-hsig-subject-body principal keys source))
                  (cdr (car keys))))
  :hints (("Goal"
           :use ((:instance fn-hsigi-nthcdr-len-plus-append
                            (xs principal) (k 1)
                            (rest
                             (append
                              (list *fn-hsig-ed25519-algorithm*)
                              (cdr (car keys))
                              (list *fn-hsig-ml-dsa-65-algorithm*)
                              (cdr (cadr keys))
                              (fn-cbor-u16-bytes (len source)) source)))
                 (:instance fn-hsigi-take-len-append
                            (xs (cdr (car keys)))
                            (rest
                             (append
                              (list *fn-hsig-ml-dsa-65-algorithm*)
                              (cdr (cadr keys))
                              (fn-cbor-u16-bytes (len source)) source))))
           :in-theory (enable fn-hsigi-ed-key))))

(defthm fn-hsigi-ml-key-of-subject-body
  (implies (fn-hsig-subject-p principal keys source)
           (equal (fn-hsigi-ml-key
                   (fn-hsig-subject-body principal keys source))
                  (cdr (cadr keys))))
  :hints (("Goal"
           :use ((:instance fn-hsigi-nthcdr-len-plus-append
                            (xs principal) (k 34)
                            (rest
                             (append (list *fn-hsig-ed25519-algorithm*)
                                     (cdr (car keys))
                                     (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u16-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-plus-append
                            (xs (cdr (car keys))) (k 1)
                            (rest
                             (append (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u16-bytes (len source)) source)))
                 (:instance fn-hsigi-take-len-append
                            (xs (cdr (cadr keys)))
                            (rest (append (fn-cbor-u16-bytes (len source))
                                          source))))
           :in-theory (enable fn-hsigi-ml-key))))

(defthm fn-hsigi-source-of-subject-body
  (implies (fn-hsig-subject-p principal keys source)
           (equal (fn-hsigi-source
                   (fn-hsig-subject-body principal keys source))
                  source))
  :hints (("Goal"
           :use ((:instance fn-hsigi-nthcdr-len-plus-append
                            (xs principal) (k 1988)
                            (rest
                             (append (list *fn-hsig-ed25519-algorithm*)
                                     (cdr (car keys))
                                     (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u16-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-plus-append
                            (xs (cdr (car keys))) (k 1955)
                            (rest
                             (append (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u16-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-plus-append
                            (xs (cdr (cadr keys))) (k 2)
                            (rest (append (fn-cbor-u16-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-append
                            (xs (fn-cbor-u16-bytes (len source)))
                            (rest source)))
           :in-theory (enable fn-hsigi-source))))

(defthm fn-hsigi-subject-body-length
  (implies (fn-hsig-subject-p principal keys source)
           (equal (len (fn-hsig-subject-body principal keys source))
                  (+ 2022 (len source))))
  :hints (("Goal" :in-theory (enable fn-hsig-subject-p
                                      fn-hsig-keyset-p
                                      fn-hsig-exact-octets-p
                                      fn-hsig-subject-body))))

(defthm fn-hsigi-keysets-equal-from-components
  (implies (and (fn-hsig-keyset-p keys-a)
                (fn-hsig-keyset-p keys-b)
                (equal (cdr (car keys-a)) (cdr (car keys-b)))
                (equal (cdr (cadr keys-a)) (cdr (cadr keys-b))))
           (equal keys-a keys-b))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hsigi-cons-extensional
                            (x (car keys-a)) (y (car keys-b)))
                 (:instance fn-hsigi-cons-extensional
                            (x (cadr keys-a)) (y (cadr keys-b)))
                 (:instance fn-hsigi-two-list-extensional
                            (x keys-a) (y keys-b)))
           :in-theory (enable fn-hsig-keyset-p))))

(defthm fn-hsig-subject-body-injective
  (implies (and (fn-hsig-subject-p principal-a keys-a source-a)
                (fn-hsig-subject-p principal-b keys-b source-b)
                (equal (fn-hsig-subject-body principal-a keys-a source-a)
                       (fn-hsig-subject-body principal-b keys-b source-b)))
           (and (equal principal-a principal-b)
                (equal keys-a keys-b)
                (equal source-a source-b)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hsigi-principal-of-subject-body
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-principal-of-subject-body
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-ed-key-of-subject-body
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-ed-key-of-subject-body
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-ml-key-of-subject-body
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-ml-key-of-subject-body
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-source-of-subject-body
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-source-of-subject-body
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-keysets-equal-from-components))
           :in-theory (e/d (fn-hsig-subject-p)
                           (fn-hsig-subject-body fn-hsigi-principal
                            fn-hsigi-ed-key fn-hsigi-ml-key fn-hsigi-source)))))

;; A tagged preimage is the tag's CBOR item followed by the body.  The item
;; is a ground constant here, so equal tags cancel on the left and different
;; tags of one width differ inside the prefix.  Neither step needs the
;; one-item decoder or its input cap, so the argument holds for every source
;; a length field can carry.
(local
 (defthm fn-hsigi-append-left-cancel
   (equal (equal (append x y) (append x z))
          (equal y z))))

(local
 (defthm fn-hsigi-nth-append-prefix
   (implies (< (nfix n) (len x))
            (equal (nth n (append x y)) (nth n x)))))

(defthm fn-hsig-signed-preimage-injective
  (implies (and (fn-hsig-subject-p principal-a keys-a source-a)
                (fn-hsig-subject-p principal-b keys-b source-b)
                (equal (fn-hsig-signed-preimage principal-a keys-a source-a)
                       (fn-hsig-signed-preimage principal-b keys-b source-b)))
           (and (equal principal-a principal-b)
                (equal keys-a keys-b)
                (equal source-a source-b)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hsig-subject-body-injective))
           :in-theory (e/d (fn-hsig-signed-preimage fn-digest-tagged-preimage)
                           (fn-hsig-subject-p fn-hsig-subject-body)))))

;; ---------------------------------------------------------------- carrier v2
;; The v2 body has the v1 layout with a four-octet length, so the source
;; starts two octets later.

(local
 (defthm fn-hsigi-u32-length
   (equal (len (fn-cbor-u32-bytes n)) 4)
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

(defun fn-hsigi-source-v2 (body)
  (declare (xargs :guard (true-listp body)))
  (nthcdr 2024 body))

(defthm fn-hsigi-principal-of-subject-body-v2
  (implies (fn-hsig-subject-v2-p principal keys source)
           (equal (fn-hsigi-principal
                   (fn-hsig-subject-body-v2 principal keys source))
                  principal))
  :hints (("Goal"
           :use ((:instance fn-hsigi-take-len-append
                            (xs principal)
                            (rest
                             (append
                              (list *fn-hsig-ed25519-algorithm*)
                              (cdr (car keys))
                              (list *fn-hsig-ml-dsa-65-algorithm*)
                              (cdr (cadr keys))
                              (fn-cbor-u32-bytes (len source)) source))))
           :in-theory (enable fn-hsigi-principal))))

(defthm fn-hsigi-ed-key-of-subject-body-v2
  (implies (fn-hsig-subject-v2-p principal keys source)
           (equal (fn-hsigi-ed-key
                   (fn-hsig-subject-body-v2 principal keys source))
                  (cdr (car keys))))
  :hints (("Goal"
           :use ((:instance fn-hsigi-nthcdr-len-plus-append
                            (xs principal) (k 1)
                            (rest
                             (append
                              (list *fn-hsig-ed25519-algorithm*)
                              (cdr (car keys))
                              (list *fn-hsig-ml-dsa-65-algorithm*)
                              (cdr (cadr keys))
                              (fn-cbor-u32-bytes (len source)) source)))
                 (:instance fn-hsigi-take-len-append
                            (xs (cdr (car keys)))
                            (rest
                             (append
                              (list *fn-hsig-ml-dsa-65-algorithm*)
                              (cdr (cadr keys))
                              (fn-cbor-u32-bytes (len source)) source))))
           :in-theory (enable fn-hsigi-ed-key))))

(defthm fn-hsigi-ml-key-of-subject-body-v2
  (implies (fn-hsig-subject-v2-p principal keys source)
           (equal (fn-hsigi-ml-key
                   (fn-hsig-subject-body-v2 principal keys source))
                  (cdr (cadr keys))))
  :hints (("Goal"
           :use ((:instance fn-hsigi-nthcdr-len-plus-append
                            (xs principal) (k 34)
                            (rest
                             (append (list *fn-hsig-ed25519-algorithm*)
                                     (cdr (car keys))
                                     (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u32-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-plus-append
                            (xs (cdr (car keys))) (k 1)
                            (rest
                             (append (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u32-bytes (len source)) source)))
                 (:instance fn-hsigi-take-len-append
                            (xs (cdr (cadr keys)))
                            (rest (append (fn-cbor-u32-bytes (len source))
                                          source))))
           :in-theory (enable fn-hsigi-ml-key))))

(defthm fn-hsigi-source-of-subject-body-v2
  (implies (fn-hsig-subject-v2-p principal keys source)
           (equal (fn-hsigi-source-v2
                   (fn-hsig-subject-body-v2 principal keys source))
                  source))
  :hints (("Goal"
           :use ((:instance fn-hsigi-nthcdr-len-plus-append
                            (xs principal) (k 1990)
                            (rest
                             (append (list *fn-hsig-ed25519-algorithm*)
                                     (cdr (car keys))
                                     (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u32-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-plus-append
                            (xs (cdr (car keys))) (k 1957)
                            (rest
                             (append (list *fn-hsig-ml-dsa-65-algorithm*)
                                     (cdr (cadr keys))
                                     (fn-cbor-u32-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-plus-append
                            (xs (cdr (cadr keys))) (k 4)
                            (rest (append (fn-cbor-u32-bytes (len source)) source)))
                 (:instance fn-hsigi-nthcdr-len-append
                            (xs (fn-cbor-u32-bytes (len source)))
                            (rest source)))
           :in-theory (enable fn-hsigi-source-v2))))

(defthm fn-hsig-subject-body-v2-injective
  (implies (and (fn-hsig-subject-v2-p principal-a keys-a source-a)
                (fn-hsig-subject-v2-p principal-b keys-b source-b)
                (equal (fn-hsig-subject-body-v2 principal-a keys-a source-a)
                       (fn-hsig-subject-body-v2 principal-b keys-b source-b)))
           (and (equal principal-a principal-b)
                (equal keys-a keys-b)
                (equal source-a source-b)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hsigi-principal-of-subject-body-v2
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-principal-of-subject-body-v2
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-ed-key-of-subject-body-v2
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-ed-key-of-subject-body-v2
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-ml-key-of-subject-body-v2
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-ml-key-of-subject-body-v2
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-source-of-subject-body-v2
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-source-of-subject-body-v2
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-keysets-equal-from-components))
           :in-theory (e/d (fn-hsig-subject-v2-p)
                           (fn-hsig-subject-body-v2 fn-hsigi-principal
                            fn-hsigi-ed-key fn-hsigi-ml-key
                            fn-hsigi-source-v2)))))

(defthm fn-hsig-signed-preimage-v2-injective
  (implies (and (fn-hsig-subject-v2-p principal-a keys-a source-a)
                (fn-hsig-subject-v2-p principal-b keys-b source-b)
                (equal (fn-hsig-signed-preimage-v2 principal-a keys-a source-a)
                       (fn-hsig-signed-preimage-v2 principal-b keys-b source-b)))
           (and (equal principal-a principal-b)
                (equal keys-a keys-b)
                (equal source-a source-b)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hsig-subject-body-v2-injective))
           :in-theory (e/d (fn-hsig-signed-preimage-v2 fn-digest-tagged-preimage)
                           (fn-hsig-subject-v2-p fn-hsig-subject-body-v2)))))

;; Domain separation between the versions: the two tags are 28 octets each
;; and differ in their last octet, so every v1 preimage differs from every
;; v2 preimage at octet 29 whatever the bodies are.  No v1 signature is a
;; signature over any v2 preimage, and the reverse.
(defthm fn-hsig-v1-v2-preimages-disjoint
  (not (equal (fn-hsig-signed-preimage principal-a keys-a source-a)
              (fn-hsig-signed-preimage-v2 principal-b keys-b source-b)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hsigi-nth-append-prefix
                            (n 29)
                            (x (fn-cbor-encode (cons :bytes *fn-hsig-domain-tag*)))
                            (y (fn-hsig-subject-body principal-a keys-a source-a)))
                 (:instance fn-hsigi-nth-append-prefix
                            (n 29)
                            (x (fn-cbor-encode (cons :bytes *fn-hsig-v2-domain-tag*)))
                            (y (fn-hsig-subject-body-v2 principal-b keys-b source-b))))
           :in-theory (e/d (fn-hsig-signed-preimage fn-hsig-signed-preimage-v2
                            fn-digest-tagged-preimage)
                           (fn-hsigi-nth-append-prefix fn-hsig-subject-body
                            fn-hsig-subject-body-v2 fn-cbor-encode)))))

;; One source length, one version: a subject admitted at VERSION is the
;; subject `fn-hsig-source-version' assigns, so the carrier's version item
;; can only name the version the signer used.
(defthm fn-hsig-subject-at-p-names-the-source-version
  (implies (fn-hsig-subject-at-p version principal keys source)
           (equal version (fn-hsig-source-version source)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hsig-subject-at-p fn-hsig-subject-p
                                     fn-hsig-subject-v2-p
                                     fn-hsig-source-version))))

;; Keystone for carrier v2: across both versions, equal signed preimages
;; mean the same version, principal, key set and exact source.
(defthm fn-hsig-signed-preimage-at-injective
  (implies (and (fn-hsig-subject-at-p version-a principal-a keys-a source-a)
                (fn-hsig-subject-at-p version-b principal-b keys-b source-b)
                (equal (fn-hsig-signed-preimage-at version-a principal-a keys-a source-a)
                       (fn-hsig-signed-preimage-at version-b principal-b keys-b source-b)))
           (and (equal version-a version-b)
                (equal principal-a principal-b)
                (equal keys-a keys-b)
                (equal source-a source-b)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hsig-signed-preimage-injective)
                 (:instance fn-hsig-signed-preimage-v2-injective)
                 (:instance fn-hsig-v1-v2-preimages-disjoint)
                 (:instance fn-hsig-v1-v2-preimages-disjoint
                            (principal-a principal-b) (keys-a keys-b)
                            (source-a source-b)
                            (principal-b principal-a) (keys-b keys-a)
                            (source-b source-a)))
           :in-theory (e/d (fn-hsig-subject-at-p fn-hsig-signed-preimage-at)
                           (fn-hsig-subject-p fn-hsig-subject-v2-p
                            fn-hsig-signed-preimage
                            fn-hsig-signed-preimage-v2)))))

;; Existing v1 records: at the version a v1-sized source is assigned, the
;; preimage and the authorization are the v1 functions, whose definitions
;; carrier v2 did not change.  Nothing is re-signed or re-verified.
(defthm fn-hsig-preimage-at-v1-source-is-v1-preimage-by-definition
  (implies (<= (len source) *fn-hsig-v1-max-source*)
           (equal (fn-hsig-signed-preimage-at (fn-hsig-source-version source)
                                              principal keys source)
                  (fn-hsig-signed-preimage principal keys source)))
  :hints (("Goal" :in-theory (enable fn-hsig-signed-preimage-at
                                     fn-hsig-source-version))))

(defthm fn-hsig-authorize-at-v1-source-is-authorize-by-definition
  (implies (<= (len source) *fn-hsig-v1-max-source*)
           (equal (fn-hsig-authorize-at (fn-hsig-source-version source)
                                        principal keys source signatures
                                        observed ed ml)
                  (fn-hsig-authorize principal keys source signatures
                                     observed ed ml)))
  :hints (("Goal" :in-theory (enable fn-hsig-authorize-at fn-hsig-authorize
                                     fn-hsig-subject-at-p
                                     fn-hsig-source-version))))
