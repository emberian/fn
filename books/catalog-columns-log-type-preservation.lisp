; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-octet-types")

(local (defthm fn-lbr13-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(len binary-append))))))

(local (defthm fn-lbr13-true-list-append
 (implies (true-listp b) (true-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(true-listp binary-append len))))))

(local (defthm fn-lbr13-take-append-bounded
 (implies (and (natp n) (<= n (len a)))
 (equal (take n (append a b)) (take n a)))
 :hints (("Goal" :induct (take n a) :in-theory (union-theories (theory 'ground-zero) '(take len binary-append))))))

(local (defthm fn-lbr13-nthcdr-append-bounded
 (implies (and (natp n) (<= n (len a)))
 (equal (nthcdr n (append a b)) (append (nthcdr n a) b)))
 :hints (("Goal" :induct (nthcdr n a) :in-theory (union-theories (theory 'ground-zero) '(nthcdr len binary-append))))))

(local (defthm fn-lbr13-len-nthcdr-bounded
 (implies (and (natp n) (<= n (len a)))
 (equal (len (nthcdr n a)) (- (len a) n)))
 :hints (("Goal" :induct (nthcdr n a) :in-theory (union-theories (theory 'ground-zero) '(nthcdr len))))))

(local (defthm fn-lbr13-slice-append-bounded
 (implies (and (natp off) (natp n) (<= (+ off n) (len a)))
 (equal (take n (nthcdr off (append a b))) (take n (nthcdr off a))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr13-nthcdr-append-bounded fn-lbr13-len-nthcdr-bounded fn-lbr13-take-append-bounded))))))

(local (defthm fn-lbr13-entry-payload-of-byte-append
 (implies (and (fn-lb-log-model-entry-payloadp entry bytes) (true-listp tail))
 (fn-lb-log-model-entry-payloadp entry (append bytes tail)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-entry-payloadp fn-lbr13-slice-append-bounded fn-lbr13-take-append-bounded fn-lbr13-len-append
 fn-lbr13-true-list-append (:type-prescription nfix)))))))

(local (defthm fn-lbr13-entries-payload-of-byte-append
 (implies (and (fn-lb-log-model-entries-payloadp entries bytes) (true-listp tail))
 (fn-lb-log-model-entries-payloadp entries (append bytes tail)))
 :hints (("Goal" :induct (fn-lb-log-model-entries-payloadp entries bytes)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-entries-payloadp fn-lbr13-entry-payload-of-byte-append))))))

(local (defthm fn-lbr13-entries-payload-implies-true-listp
 (implies (fn-lb-log-model-entries-payloadp entries bytes) (true-listp entries))
 :hints (("Goal" :induct (fn-lb-log-model-entries-payloadp entries bytes)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-entries-payloadp true-listp))))))

(local (defthm fn-lbr13-entries-payload-append
 (implies (true-listp a) (equal (fn-lb-log-model-entries-payloadp (append a b) bytes)
 (and (fn-lb-log-model-entries-payloadp a bytes) (fn-lb-log-model-entries-payloadp b bytes))))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-entries-payloadp binary-append len true-listp))))))

(local (defthm fn-lbr13-next-entry-proper
 (true-listp (fn-lb-log-model-next-entry row payload segment))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-next-entry true-listp))))))

(local (defthm fn-lbr13-next-entry-payload-binding
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload))
 (fn-lb-log-model-entry-payloadp
   (fn-lb-log-model-next-entry row payload segment)
   (cadr (fn-lb-log-model-append-to-segment row payload segment))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-appended-range-byte-slice))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-entry-payloadp fn-lbr13-next-entry-proper
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-append-to-segment-bytes-by-definition fn-lb-log-model-next-range
 fn-lbr13-len-append fn-lbr13-true-list-append fn-lb-log-next-prefix-length
 fn-lb-log-next-prefix-true-listp fn-cbor-octet-listp-implies-true-listp
 fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp fn-blake3-stobj-satisfies-fn-frame-digest-length
 nfix natp))))))

(local (defthm fn-lbr13-appended-segment-payload-binding
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload)
 (fn-lb-log-model-entries-payloadp (caddr segment) (cadr segment)))
 (fn-lb-log-model-entries-payloadp
  (caddr (fn-lb-log-model-append-to-segment row payload segment))
  (cadr (fn-lb-log-model-append-to-segment row payload segment))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr13-next-entry-payload-binding))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-append-to-segment-directory-by-definition
 fn-lb-log-append-to-segment-bytes-by-definition
 fn-lbr13-entries-payload-append fn-lbr13-entries-payload-implies-true-listp fn-lbr13-entries-payload-of-byte-append
 fn-lbr13-next-entry-payload-binding fn-lb-log-model-entries-payloadp
 fn-lbr13-true-list-append fn-lb-log-next-prefix-true-listp
 fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp
 fn-cbor-octet-listp-implies-true-listp))))))

(local (defthm fn-lbltp-octets-append
 (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
 (fn-cbor-octet-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append fn-cbor-octet-listp)))))

(local (defthm fn-lbltp-entries-append
 (implies (and (fn-lb-log-model-entriesp entries) (fn-lb-log-model-entryp e))
 (fn-lb-log-model-entriesp (append entries (list e))))
 :hints (("Goal" :induct (len entries) :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-entriesp binary-append)))) ))

(local (defthm fn-lbltp-appended-segment-shape
 (and (true-listp (fn-lb-log-model-append-to-segment row payload segment))
      (equal (len (fn-lb-log-model-append-to-segment row payload segment)) 3)
      (equal (car (fn-lb-log-model-append-to-segment row payload segment)) (car segment)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-append-to-segment true-listp len car-cons cdr-cons (:executable-counterpart binary-+)))))))

(defthm fn-lb-log-append-to-segment-preserves-type
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload)
               (fn-lb-log-model-segsp (list segment)))
 (fn-lb-log-model-segsp (list (fn-lb-log-model-append-to-segment row payload segment))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr13-appended-segment-payload-binding)
       (:instance fn-lbltp-appended-segment-shape)
       (:instance fn-lb-log-next-entry-well-typed))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-segsp fn-lb-log-append-to-segment-directory-by-definition
 fn-lb-log-append-to-segment-bytes-by-definition fn-lbltp-entries-append
 fn-lbltp-octets-append fn-lb-log-model-next-prefix-is-octets
 fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp)))))

(local (defthm fn-lbltp-single-segment-type
 (implies (fn-lb-log-model-segsp (cons segment rest)) (fn-lb-log-model-segsp (list segment)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-segsp))))))

(local (defthm fn-lbltp-empty-segment-type
 (implies (unsigned-byte-p 64 target) (fn-lb-log-model-segsp (list (list target nil nil))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-segsp fn-lb-log-model-entriesp fn-lb-log-model-entries-payloadp fn-cbor-octet-listp))))))

(defthm fn-lb-log-append-preserves-type
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload)
 (unsigned-byte-p 64 target) (fn-lb-log-model-segsp log))
 (fn-lb-log-model-segsp (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lb-log-model-segsp fn-lbltp-single-segment-type fn-lbltp-empty-segment-type)))
 ("Subgoal *1/1" :use ((:instance fn-lb-log-append-to-segment-preserves-type (segment (car log)))))
 ("Subgoal *1/3" :use ((:instance fn-lb-log-append-to-segment-preserves-type (segment (list target nil nil)))))))

(defthm fn-lb-log-recycle-preserves-type
 (implies (fn-lb-log-model-segsp log)
 (fn-lb-log-model-segsp (fn-lb-log-model-recycle target log)))
 :hints (("Goal" :induct (fn-lb-log-model-recycle target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-segsp fn-lb-log-model-recycle)))))
