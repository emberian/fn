; Proof work log, not a certified book.  The prefix/source/stamp/fragment
; inversions below were admitted by local ACL2; the final round-trip theorem
; at the end is still open.  See 100da28f and the persvati manifest named in
; the handoff for the certified codec and exact wire vectors.
(in-package "ACL2")
(include-book "../../books/bp-status-report")
(include-book "../../books/bp-primary-invariants")

(defthm fn-bpn-report-read-source-of-encode
  (implies (and (fn-bpp-eidp source)
                (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp
                 (append (fn-bpc-enc :item (fn-bpp-eid-value source)) rest)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-read-source
                   (append (fn-bpc-enc :item (fn-bpp-eid-value source)) rest))
                  (fn-cbor-ok source rest)))
  :hints (("Goal" :use ((:instance fn-bpc-decode-of-encode
                                  (flg :item)
                                  (x (fn-bpp-eid-value source))
                                  (budget *fn-bpc-max-items*)))
           :in-theory (disable fn-bpc-dec fn-bpc-enc
                               fn-bpc-decode-of-encode
                               fn-bpp-eid-value fn-bpp-value-eid))))

(defthm fn-bpn-report-read-stamp-of-encode
  (implies (and (fn-bpn-report-uintp time)
                (fn-bpn-report-uintp sequence)
                (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp
                 (append (list 130)
                         (fn-bpn-report-uint-octets time)
                         (fn-bpn-report-uint-octets sequence)
                         rest)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-read-stamp
                   (append (list 130)
                           (fn-bpn-report-uint-octets time)
                           (fn-bpn-report-uint-octets sequence)
                           rest))
                  (fn-cbor-ok (list time sequence) rest)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-uint-of-encode
                            (n time)
                            (rest (append
                                   (fn-bpn-report-uint-octets sequence)
                                   rest)))
                 (:instance fn-bpn-report-read-uint-of-encode
                            (n sequence) (rest rest))
                 (:instance fn-bpn-report-bounded-append-suffix
                            (a (list 130))
                            (b (append
                                (fn-bpn-report-uint-octets time)
                                (fn-bpn-report-uint-octets sequence)
                                rest))
                            (bound *fn-bpc-max-input*))
                 (:instance fn-bpn-report-bounded-append-suffix
                            (a (fn-bpn-report-uint-octets time))
                            (b (append
                                (fn-bpn-report-uint-octets sequence)
                                rest))
                            (bound *fn-bpc-max-input*)))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-report-read-uint
                            fn-bpn-report-uint-octets
                            fn-cbor-at-mostp
                            fn-bpn-report-at-most-is-length
                            fn-bpn-report-read-uint-of-encode
                            fn-bpn-report-bounded-append-suffix)))))

(defthm fn-bpn-report-read-fragment-of-encode
  (implies (and (fn-bpn-report-uintp offset)
                (fn-bpn-report-uintp length)
                (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-uint-octets offset)
                         (fn-bpn-report-uint-octets length)
                         rest)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-read-fragment
                   t (append (fn-bpn-report-uint-octets offset)
                             (fn-bpn-report-uint-octets length)
                             rest))
                  (fn-cbor-ok (cons offset length) rest)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-uint-of-encode
                            (n offset)
                            (rest (append
                                   (fn-bpn-report-uint-octets length)
                                   rest)))
                 (:instance fn-bpn-report-read-uint-of-encode
                            (n length) (rest rest))
                 (:instance fn-bpn-report-bounded-append-suffix
                            (a (fn-bpn-report-uint-octets offset))
                            (b (append
                                (fn-bpn-report-uint-octets length)
                                rest))
                            (bound *fn-bpc-max-input*)))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-report-read-uint
                            fn-bpn-report-uint-octets
                            fn-cbor-at-mostp
                            fn-bpn-report-at-most-is-length
                            fn-bpn-report-read-uint-of-encode
                            fn-bpn-report-bounded-append-suffix)))))

(defthm fn-bpn-report-read-status-of-encode-aux
  (implies (and (fn-bpn-report-assertion-listp status)
                (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-status-octets status) rest)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-read-status
                   (len status)
                   (append (fn-bpn-report-status-octets status) rest))
                  (fn-cbor-ok status rest)))
  :hints (("Goal" :induct (fn-bpn-report-status-octets status)
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-report-read-assertion
                            fn-bpn-report-assertion-octets
                            fn-cbor-at-mostp
                            fn-bpn-report-at-most-is-length)))
          ("Subgoal *1/1"
           :use ((:instance fn-bpn-report-read-assertion-of-encode
                            (assertion (car status))
                            (rest (append
                                   (fn-bpn-report-status-octets (cdr status))
                                   rest)))
                 (:instance fn-bpn-report-bounded-append-suffix
                            (a (fn-bpn-report-assertion-octets (car status)))
                            (b (append
                                (fn-bpn-report-status-octets (cdr status))
                                rest))
                            (bound *fn-bpc-max-input*)))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-report-read-assertion
                            fn-bpn-report-assertion-octets
                            fn-cbor-at-mostp
                            fn-bpn-report-at-most-is-length
                            fn-bpn-report-read-assertion-of-encode
                            fn-bpn-report-bounded-append-suffix)))))

(defthm fn-bpn-report-four-list-shape
  (implies (and (true-listp x) (equal (len x) 4))
           (equal x (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpn-report-two-list-shape
                                  (x (cddr x))))
           :in-theory (enable len true-listp nth))))

(defthm fn-bpn-report-statusp-implies-listp
  (implies (fn-bpn-report-statusp status)
           (fn-bpn-report-assertion-listp status))
  :hints (("Goal" :use ((:instance fn-bpn-report-four-list-shape
                                  (x status)))
           :in-theory (enable fn-bpn-report-statusp
                              fn-bpn-report-assertion-listp))))

(defthm fn-bpn-report-read-status-of-encode
  (implies (and (fn-bpn-report-statusp status)
                (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-status-octets status) rest)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-read-status
                   4 (append (fn-bpn-report-status-octets status) rest))
                  (fn-cbor-ok status rest)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-status-of-encode-aux))
           :in-theory (disable fn-bpn-report-read-status
                               fn-bpn-report-status-octets))))

(defthm fn-bpn-reportp-components
  (implies (fn-bpn-reportp report)
           (and (fn-bpn-report-statusp (nth 1 report))
                (fn-bpn-report-uintp (nth 2 report))
                (fn-bpp-eidp (nth 3 report))
                (fn-bpn-report-uintp (car (nth 4 report)))
                (fn-bpn-report-uintp (cadr (nth 4 report)))
                (implies (nth 5 report)
                         (and (fn-bpn-report-uintp (car (nth 5 report)))
                              (fn-bpn-report-uintp (cdr (nth 5 report)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bpn-reportp
                                      fn-bpn-report-uintp))))

(defthm fn-bpn-reportp-stamp-shape
  (implies (fn-bpn-reportp report)
           (equal (nth 4 report)
                  (list (car (nth 4 report)) (cadr (nth 4 report)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpn-report-two-list-shape
                                  (x (nth 4 report))))
           :in-theory (enable fn-bpn-reportp))))

(defun fn-bpn-report-after-stamp-octets (report)
  (declare (xargs :guard t :verify-guards nil))
  (if (nth 5 report)
      (append (fn-bpn-report-uint-octets (car (nth 5 report)))
              (fn-bpn-report-uint-octets (cdr (nth 5 report))))
    nil))

(defun fn-bpn-report-after-source-octets (report)
  (declare (xargs :guard t :verify-guards nil))
  (append (list 130)
          (fn-bpn-report-uint-octets (car (nth 4 report)))
          (fn-bpn-report-uint-octets (cadr (nth 4 report)))
          (fn-bpn-report-after-stamp-octets report)))

(defun fn-bpn-report-after-reason-octets (report)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bpc-enc :item (fn-bpp-eid-value (nth 3 report)))
          (fn-bpn-report-after-source-octets report)))

(defun fn-bpn-report-tail-octets (report)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bpn-report-uint-octets (nth 2 report))
          (fn-bpn-report-after-reason-octets report)))

(defthm fn-bpn-report-encode-structure
  (implies (fn-bpn-reportp report)
           (equal (fn-bpn-report-encode report)
                  (append '(130 1)
                          (list (if (nth 5 report) 134 132) 132)
                          (fn-bpn-report-status-octets (nth 1 report))
                          (fn-bpn-report-tail-octets report))))
  :hints (("Goal" :in-theory (e/d (fn-bpn-report-encode
                                    fn-bpn-report-tail-octets
                                    fn-bpn-report-after-reason-octets
                                    fn-bpn-report-after-source-octets
                                    fn-bpn-report-after-stamp-octets
                                    fn-bpc-append-associativity)
                                   (fn-bpn-reportp fn-bpc-enc
                                    fn-bpp-eid-value
                                    fn-bpn-report-uint-octets
                                    fn-bpn-report-status-octets)))))

(defthm fn-bpn-report-after-reason-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-after-reason-octets report))
  :hints (("Goal"
           :use ((:instance fn-bpc-enc-are-octets
                            (flg :item)
                            (x (fn-bpp-eid-value (nth 3 report)))))
           :in-theory (disable fn-bpc-enc fn-bpp-eid-value
                               fn-bpn-report-uint-octets))))

(defthm fn-bpn-report-tail-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-tail-octets report))
  :hints (("Goal"
           :use ((:instance fn-bpc-enc-are-octets
                            (flg :item)
                            (x (fn-bpp-eid-value (nth 3 report)))))
           :in-theory (disable fn-bpc-enc fn-bpp-eid-value
                               fn-bpn-report-uint-octets))))

(defthm fn-bpn-report-round-trip
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp (fn-bpn-report-encode report)
                                  *fn-bpn-report-max-input*))
           (equal (fn-bpn-report-decode (fn-bpn-report-encode report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal" :use ((:instance fn-bpn-report-encode-octets)
                        (:instance fn-bpn-reportp-components)
                        (:instance fn-bpn-reportp-stamp-shape)
                        (:instance fn-bpn-report-read-uint-of-encode
                                   (n (nth 2 report))
                                   (rest (fn-bpn-report-after-reason-octets
                                          report)))
                        (:instance fn-bpn-report-bounded-append-suffix
                                   (a (fn-bpn-report-status-octets
                                       (nth 1 report)))
                                   (b (fn-bpn-report-tail-octets report))
                                   (bound 4096))
                        (:instance fn-bpn-report-at-most-monotone
                                   (xs (fn-bpn-report-tail-octets report))
                                   (small 4096) (large 65536))
                        (:instance fn-bpn-report-bounded-append-suffix
                                   (a (list 130 1
                                            (if (nth 5 report) 134 132)
                                            132))
                                   (b (append
                                       (fn-bpn-report-status-octets
                                        (nth 1 report))
                                       (fn-bpn-report-tail-octets report)))
                                   (bound 4096))
                        (:instance fn-bpn-report-read-status-of-encode
                                   (status (nth 1 report))
                                   (rest (fn-bpn-report-tail-octets report)))
                        (:instance fn-bpn-report-at-most-monotone
                                   (xs (append
                                        (fn-bpn-report-status-octets
                                         (nth 1 report))
                                        (fn-bpn-report-tail-octets report)))
                                   (small 4096) (large 65536)))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-report-encode-octets
                            fn-bpn-reportp
                            fn-bpn-report-read-status
                            fn-bpn-report-status-octets
                            fn-bpn-report-tail-octets
                            fn-bpn-report-after-reason-octets
                            fn-bpn-report-read-uint
                            fn-cbor-at-mostp
                            fn-bpn-report-at-most-is-length
                            fn-bpn-report-read-status-of-encode)))))
