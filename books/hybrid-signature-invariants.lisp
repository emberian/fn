; Injectivity of the exact hybrid authored-source byte subject.
(in-package "ACL2")
(include-book "hybrid-signature")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-hybrid-signature-vocabulary)))

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
           :in-theory (enable fn-hsig-subject-p))))

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
           :use ((:instance fn-digest-tagged-preimage-injective
                            (tag1 *fn-hsig-domain-tag*)
                            (m1 (fn-hsig-subject-body principal-a keys-a source-a))
                            (tag2 *fn-hsig-domain-tag*)
                            (m2 (fn-hsig-subject-body principal-b keys-b source-b)))
                 (:instance fn-hsig-subject-body-is-octets
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsig-subject-body-is-octets
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsigi-subject-body-length
                            (principal principal-a) (keys keys-a) (source source-a))
                 (:instance fn-hsigi-subject-body-length
                            (principal principal-b) (keys keys-b) (source source-b))
                 (:instance fn-hsig-subject-body-injective))
           :in-theory (enable fn-hsig-signed-preimage
                              fn-hsig-subject-p fn-hsig-subject-body
                              fn-hsig-exact-octets-p))))
