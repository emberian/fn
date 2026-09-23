; Certified inversion and bounded composition facts for the RFC 9171 status-report codec.
; The decoder accepts remote observations; these theorems grant no release authority.
(in-package "ACL2")
(include-book "bp-status-report")
(include-book "bp-primary-invariants")

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

(defthm fn-bpn-reportp-reason-uintp
  (implies (fn-bpn-reportp report)
           (fn-bpn-report-uintp (nth 2 report)))
  :hints (("Goal" :in-theory (e/d (fn-bpn-reportp fn-bpn-report-uintp)
                                  (fn-bpn-report-statusp fn-bpp-eidp
                                   fn-bpn-report-assertionp)))))
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
  :hints (("Goal" :use ((:instance fn-bpn-reportp-reason-uintp))
           :in-theory (e/d (fn-bpn-reportp)
                           (fn-bpn-report-statusp fn-bpp-eidp
                            fn-bpn-report-uintp fn-bpn-report-assertionp)))))

(defthm fn-bpn-reportp-stamp-shape
  (implies (fn-bpn-reportp report)
           (equal (nth 4 report)
                  (list (car (nth 4 report)) (cadr (nth 4 report)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpn-report-two-list-shape
                                  (x (nth 4 report))))
           :in-theory (enable fn-bpn-reportp))))

(defthm fn-bpn-report-six-list-shape
  (implies (and (true-listp x) (equal (len x) 6))
           (equal x (list (nth 0 x) (nth 1 x) (nth 2 x)
                          (nth 3 x) (nth 4 x) (nth 5 x))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpn-report-two-list-shape
                                  (x (cddddr x))))
           :in-theory (enable len true-listp nth))))

(defthm fn-bpn-reportp-list-shape
  (implies (fn-bpn-reportp report)
           (equal report
                  (list :report (nth 1 report) (nth 2 report)
                        (nth 3 report) (nth 4 report) (nth 5 report))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpn-report-six-list-shape
                                  (x report)))
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

(defthm fn-bpn-report-after-stamp-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-after-stamp-octets report))
  :hints (("Goal" :in-theory (disable fn-bpn-report-uint-octets))))

(defthm fn-bpn-report-uint-pair-append-nil
  (equal (append (fn-bpn-report-uint-octets a)
                 (fn-bpn-report-uint-octets b) nil)
         (append (fn-bpn-report-uint-octets a)
                 (fn-bpn-report-uint-octets b)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-uint-octets-are-octets (x b))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-uint-octets b))))
           :in-theory (disable fn-bpn-report-uint-octets))))

(defthm fn-bpn-report-parse-fragment-whole
  (equal (fn-bpn-report-parse-fragment
          status reason source stamp nil rest)
         (fn-cbor-ok (list :report status reason source stamp nil) rest)))

(defthm fn-bpn-report-parse-fragment-of-encode
  (implies (and (fn-bpn-report-uintp offset)
                (fn-bpn-report-uintp length)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-uint-octets offset)
                         (fn-bpn-report-uint-octets length))
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse-fragment
                   status reason source stamp t
                   (append (fn-bpn-report-uint-octets offset)
                           (fn-bpn-report-uint-octets length)))
                  (fn-cbor-ok
                   (list :report status reason source stamp
                         (cons offset length)) nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-fragment-of-encode
                            (offset offset) (length length) (rest nil)))
           :in-theory (disable fn-bpn-report-read-fragment
                               fn-bpn-report-uint-octets
                               fn-bpn-report-at-most-is-length
                               fn-bpn-report-read-fragment-of-encode))))

(defthm fn-bpn-report-parse-stamp-compose
  (implies (and (fn-bpn-report-uintp time)
                (fn-bpn-report-uintp sequence)
                (fn-cbor-octet-listp fragment-octets)
                (fn-cbor-at-mostp
                 (append (list 130)
                         (fn-bpn-report-uint-octets time)
                         (fn-bpn-report-uint-octets sequence)
                         fragment-octets)
                 *fn-bpc-max-input*)
                (equal (fn-bpn-report-parse-fragment
                        status reason source (list time sequence)
                        fragmentp fragment-octets)
                       answer))
           (equal (fn-bpn-report-parse-stamp
                   status reason source fragmentp
                   (append (list 130)
                           (fn-bpn-report-uint-octets time)
                           (fn-bpn-report-uint-octets sequence)
                           fragment-octets))
                  answer))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-stamp-of-encode
                            (time time) (sequence sequence)
                            (rest fragment-octets)))
           :in-theory (disable fn-bpn-report-read-stamp
                               fn-bpn-report-parse-fragment
                               fn-bpn-report-uint-octets
                               fn-bpn-report-read-stamp-of-encode))))

(defthm fn-bpn-report-parse-source-compose
  (implies (and (fn-bpp-eidp source)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-bpc-enc :item (fn-bpp-eid-value source)) tail)
                 *fn-bpc-max-input*)
                (equal (fn-bpn-report-parse-stamp
                        status reason source fragmentp tail)
                       answer))
           (equal (fn-bpn-report-parse-source
                   status reason fragmentp
                   (append (fn-bpc-enc :item (fn-bpp-eid-value source))
                           tail))
                  answer))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-source-of-encode
                            (source source) (rest tail)))
           :in-theory (disable fn-bpn-report-read-source
                               fn-bpn-report-parse-stamp
                               fn-bpp-eid-value fn-bpc-enc
                               fn-bpn-report-read-source-of-encode))))

(defthm fn-bpn-report-parse-reason-compose
  (implies (and (fn-bpn-report-uintp reason)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-uint-octets reason) tail)
                 *fn-bpc-max-input*)
                (equal (fn-bpn-report-parse-source
                        status reason fragmentp tail)
                       answer))
           (equal (fn-bpn-report-parse-reason
                   status fragmentp
                   (append (fn-bpn-report-uint-octets reason) tail))
                  answer))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-uint-of-encode
                            (n reason) (rest tail)))
           :in-theory (disable fn-bpn-report-read-uint
                               fn-bpn-report-parse-source
                               fn-bpn-report-uint-octets
                               fn-bpn-report-read-uint-of-encode))))

(defthm fn-bpn-report-parse-after-header-compose
  (implies (and (fn-bpn-report-statusp status)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-status-octets status) tail)
                 *fn-bpc-max-input*)
                (equal (fn-bpn-report-parse-reason
                        status fragmentp tail)
                       answer))
           (equal (fn-bpn-report-parse-after-header
                   fragmentp
                   (append (fn-bpn-report-status-octets status) tail))
                  answer))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-status-of-encode
                            (status status) (rest tail)))
           :in-theory (disable fn-bpn-report-read-status
                               fn-bpn-report-parse-reason
                               fn-bpn-report-status-octets
                               fn-cbor-at-mostp
                               fn-bpn-report-at-most-is-length
                               fn-bpn-report-read-status-of-encode))))

(defthm fn-bpn-report-parse-header-compose
  (implies (or (equal fragmentp t) (null fragmentp))
           (equal (fn-bpn-report-parse
                   (append (list 130 1 (if fragmentp 134 132) 132) tail))
                  (fn-bpn-report-parse-after-header fragmentp tail)))
  :hints (("Goal" :in-theory (disable fn-bpn-report-parse-after-header))))

(defthm fn-bpn-report-parse-fragment-of-whole-report
  (implies (and (fn-bpn-reportp report)
                (null (nth 5 report)))
           (equal (fn-bpn-report-parse-fragment
                   (nth 1 report) (nth 2 report) (nth 3 report)
                   (nth 4 report) nil
                   (fn-bpn-report-after-stamp-octets report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal" :use ((:instance fn-bpn-reportp-list-shape))
           :in-theory (disable fn-bpn-reportp))))

(defthm fn-bpn-report-parse-fragment-of-fragment-report
  (implies (and (fn-bpn-reportp report)
                (nth 5 report)
                (fn-cbor-at-mostp
                 (fn-bpn-report-after-stamp-octets report)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse-fragment
                   (nth 1 report) (nth 2 report) (nth 3 report)
                   (nth 4 report) t
                   (fn-bpn-report-after-stamp-octets report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-parse-fragment-of-encode
                            (status (nth 1 report))
                            (reason (nth 2 report))
                            (source (nth 3 report))
                            (stamp (nth 4 report))
                            (offset (car (nth 5 report)))
                            (length (cdr (nth 5 report))))
                 (:instance fn-bpn-reportp-components)
                 (:instance fn-bpn-reportp-list-shape))
           :in-theory (disable fn-bpn-reportp
                               fn-bpn-report-parse-fragment
                               fn-bpn-report-uint-octets
                               fn-bpn-report-uintp
                               fn-bpn-report-statusp
                               fn-bpp-eidp
                               fn-bpn-report-at-most-is-length
                               fn-bpn-report-parse-fragment-of-encode))))

(defthm fn-bpn-report-parse-fragment-of-report
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp
                 (fn-bpn-report-after-stamp-octets report)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse-fragment
                   (nth 1 report) (nth 2 report) (nth 3 report)
                   (nth 4 report) (if (nth 5 report) t nil)
                   (fn-bpn-report-after-stamp-octets report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal" :use ((:instance fn-bpn-report-parse-fragment-of-whole-report)
                         (:instance fn-bpn-report-parse-fragment-of-fragment-report))
           :in-theory (disable fn-bpn-reportp fn-bpn-report-parse-fragment
                               fn-bpn-report-parse-fragment-of-whole-report
                               fn-bpn-report-parse-fragment-of-fragment-report))))

(defthm fn-bpn-report-after-stamp-bounded-from-source
  (implies (fn-cbor-at-mostp
            (fn-bpn-report-after-source-octets report)
            *fn-bpc-max-input*)
           (fn-cbor-at-mostp
            (fn-bpn-report-after-stamp-octets report)
            *fn-bpc-max-input*))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-bounded-append-suffix
                            (a (append (list 130)
                                       (fn-bpn-report-uint-octets
                                        (car (nth 4 report)))
                                       (fn-bpn-report-uint-octets
                                        (cadr (nth 4 report)))))
                            (b (fn-bpn-report-after-stamp-octets report))
                            (bound *fn-bpc-max-input*))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-after-stamp-octets report))))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-cbor-at-mostp fn-bpn-report-uint-octets
                            fn-bpn-report-at-most-is-length
                            fn-bpn-report-bounded-append-suffix)))))

(defthm fn-bpn-report-parse-stamp-of-report
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp
                 (fn-bpn-report-after-source-octets report)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse-stamp
                   (nth 1 report) (nth 2 report) (nth 3 report)
                   (if (nth 5 report) t nil)
                   (fn-bpn-report-after-source-octets report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-parse-stamp-compose
                            (time (car (nth 4 report)))
                            (sequence (cadr (nth 4 report)))
                            (fragment-octets
                             (fn-bpn-report-after-stamp-octets report))
                            (status (nth 1 report)) (reason (nth 2 report))
                            (source (nth 3 report))
                            (fragmentp (if (nth 5 report) t nil))
                            (answer (fn-cbor-ok report nil)))
                 (:instance fn-bpn-report-parse-fragment-of-report)
                 (:instance fn-bpn-report-after-stamp-bounded-from-source)
                 (:instance fn-bpn-reportp-stamp-shape)
                 (:instance fn-bpn-reportp-components))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-reportp fn-bpn-report-uintp
                               fn-bpn-report-statusp fn-bpp-eidp
                               fn-bpn-report-parse-stamp
                               fn-bpn-report-parse-fragment
                               fn-bpn-report-read-fragment
                               fn-bpn-report-read-uint fn-bpc-decode
                               fn-bpn-report-parse-stamp-compose
                               fn-bpn-report-parse-fragment-of-report
                               fn-bpn-report-after-stamp-bounded-from-source
                               fn-cbor-at-mostp
                               fn-bpn-report-at-most-is-length
                               fn-bpn-report-uint-octets
                               fn-bpn-report-after-stamp-octets-are-octets)))))

(defthm fn-bpn-report-after-source-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-after-source-octets report))
  :hints (("Goal" :in-theory (disable fn-bpn-report-uint-octets))))

(defthm fn-bpn-report-after-source-bounded-from-reason
  (implies (fn-cbor-at-mostp
            (fn-bpn-report-after-reason-octets report)
            *fn-bpc-max-input*)
           (fn-cbor-at-mostp
            (fn-bpn-report-after-source-octets report)
            *fn-bpc-max-input*))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-bounded-append-suffix
                            (a (fn-bpc-enc :item
                                           (fn-bpp-eid-value (nth 3 report))))
                            (b (fn-bpn-report-after-source-octets report))
                            (bound *fn-bpc-max-input*))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-after-source-octets report)))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpc-enc :item
                                               (fn-bpp-eid-value
                                                (nth 3 report))))))
           :in-theory (disable fn-cbor-at-mostp fn-bpn-report-at-most-is-length
                               fn-bpc-enc fn-bpp-eid-value
                               fn-bpn-report-bounded-append-suffix))))

(defthm fn-bpn-report-parse-source-of-report
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp
                 (fn-bpn-report-after-reason-octets report)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse-source
                   (nth 1 report) (nth 2 report)
                   (if (nth 5 report) t nil)
                   (fn-bpn-report-after-reason-octets report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-parse-source-compose
                            (source (nth 3 report))
                            (tail (fn-bpn-report-after-source-octets report))
                            (status (nth 1 report)) (reason (nth 2 report))
                            (fragmentp (if (nth 5 report) t nil))
                            (answer (fn-cbor-ok report nil)))
                 (:instance fn-bpn-report-parse-stamp-of-report)
                 (:instance fn-bpn-report-after-source-bounded-from-reason)
                 (:instance fn-bpn-reportp-components))
           :in-theory (disable fn-bpn-reportp fn-bpn-report-uintp
                               fn-bpn-report-statusp fn-bpp-eidp
                               fn-bpn-report-parse-source
                               fn-bpn-report-parse-stamp
                               fn-bpn-report-parse-source-compose
                               fn-bpn-report-parse-stamp-of-report
                               fn-bpn-report-after-source-bounded-from-reason
                               fn-cbor-at-mostp
                               fn-bpn-report-at-most-is-length
                               fn-bpc-enc fn-bpp-eid-value))))

(defthm fn-bpn-report-after-reason-bounded-from-tail
  (implies (fn-cbor-at-mostp
            (fn-bpn-report-tail-octets report)
            *fn-bpc-max-input*)
           (fn-cbor-at-mostp
            (fn-bpn-report-after-reason-octets report)
            *fn-bpc-max-input*))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-bounded-append-suffix
                            (a (fn-bpn-report-uint-octets (nth 2 report)))
                            (b (fn-bpn-report-after-reason-octets report))
                            (bound *fn-bpc-max-input*))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-after-reason-octets report)))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-uint-octets (nth 2 report)))))
           :in-theory (disable fn-cbor-at-mostp fn-bpn-report-at-most-is-length
                               fn-bpn-report-uint-octets
                               fn-bpn-report-bounded-append-suffix))))

(defthm fn-bpn-report-parse-reason-of-report
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp
                 (fn-bpn-report-tail-octets report)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse-reason
                   (nth 1 report) (if (nth 5 report) t nil)
                   (fn-bpn-report-tail-octets report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-parse-reason-compose
                            (reason (nth 2 report))
                            (tail (fn-bpn-report-after-reason-octets report))
                            (status (nth 1 report))
                            (fragmentp (if (nth 5 report) t nil))
                            (answer (fn-cbor-ok report nil)))
                 (:instance fn-bpn-report-parse-source-of-report)
                 (:instance fn-bpn-report-after-reason-bounded-from-tail)
                 (:instance fn-bpn-reportp-components))
           :in-theory (disable fn-bpn-reportp fn-bpn-report-uintp
                               fn-bpn-report-statusp fn-bpp-eidp
                               fn-bpn-report-parse-reason
                               fn-bpn-report-parse-source
                               fn-bpn-report-parse-reason-compose
                               fn-bpn-report-parse-source-of-report
                               fn-bpn-report-after-reason-bounded-from-tail
                               fn-cbor-at-mostp
                               fn-bpn-report-at-most-is-length
                               fn-bpn-report-uint-octets
                               fn-bpn-report-after-reason-octets
                               fn-bpn-report-after-source-octets
                               fn-bpn-report-after-stamp-octets
                               fn-bpc-enc fn-bpp-eid-value))))

(defun fn-bpn-report-after-header-octets (report)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bpn-report-status-octets (nth 1 report))
          (fn-bpn-report-tail-octets report)))

(defthm fn-bpn-report-tail-bounded-from-after-header
  (implies (fn-cbor-at-mostp
            (fn-bpn-report-after-header-octets report)
            *fn-bpc-max-input*)
           (fn-cbor-at-mostp
            (fn-bpn-report-tail-octets report)
            *fn-bpc-max-input*))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-bounded-append-suffix
                            (a (fn-bpn-report-status-octets (nth 1 report)))
                            (b (fn-bpn-report-tail-octets report))
                            (bound *fn-bpc-max-input*))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-status-octets
                                 (nth 1 report))))
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-tail-octets report))))
           :in-theory (disable fn-cbor-at-mostp fn-bpn-report-at-most-is-length
                               fn-bpn-report-status-octets
                               fn-bpn-report-tail-octets
                               fn-bpn-report-after-reason-octets
                               fn-bpn-report-after-source-octets
                               fn-bpn-report-after-stamp-octets
                               fn-bpc-enc fn-bpp-eid-value
                               fn-bpn-report-bounded-append-suffix))))

(defthm fn-bpn-report-parse-after-header-of-report
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp
                 (fn-bpn-report-after-header-octets report)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse-after-header
                   (if (nth 5 report) t nil)
                   (fn-bpn-report-after-header-octets report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-parse-after-header-compose
                            (status (nth 1 report))
                            (tail (fn-bpn-report-tail-octets report))
                            (fragmentp (if (nth 5 report) t nil))
                            (answer (fn-cbor-ok report nil)))
                 (:instance fn-bpn-report-parse-reason-of-report)
                 (:instance fn-bpn-report-tail-bounded-from-after-header)
                 (:instance fn-bpn-reportp-components))
           :in-theory (disable fn-bpn-reportp fn-bpn-report-uintp
                               fn-bpn-report-statusp fn-bpp-eidp
                               fn-bpn-report-parse-after-header
                               fn-bpn-report-parse-reason
                               fn-bpn-report-parse-after-header-compose
                               fn-bpn-report-parse-reason-of-report
                               fn-bpn-report-tail-bounded-from-after-header
                               fn-cbor-at-mostp
                               fn-bpn-report-at-most-is-length
                               fn-bpn-report-status-octets
                               fn-bpn-report-tail-octets))))

(defthm fn-bpn-report-after-header-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-after-header-octets report))
  :hints (("Goal" :in-theory (disable fn-bpn-report-status-octets
                                      fn-bpn-report-tail-octets))))

(defthm fn-bpn-report-after-header-bounded-from-encode
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp (fn-bpn-report-encode report)
                                  *fn-bpc-max-input*))
           (fn-cbor-at-mostp
            (fn-bpn-report-after-header-octets report)
            *fn-bpc-max-input*))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-bounded-append-suffix
                            (a (append '(130 1)
                                       (list (if (nth 5 report) 134 132)
                                             132)))
                            (b (fn-bpn-report-after-header-octets report))
                            (bound *fn-bpc-max-input*))
                 (:instance fn-bpn-report-encode-structure)
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-after-header-octets report))))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-reportp fn-bpn-report-encode
                            fn-bpn-report-encode-structure
                            fn-cbor-at-mostp fn-bpn-report-at-most-is-length
                            fn-bpn-report-status-octets
                            fn-bpn-report-tail-octets
                            fn-bpn-report-bounded-append-suffix)))))

(defthm fn-bpn-report-parse-of-encode
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp (fn-bpn-report-encode report)
                                  *fn-bpc-max-input*))
           (equal (fn-bpn-report-parse (fn-bpn-report-encode report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-parse-header-compose
                            (fragmentp (if (nth 5 report) t nil))
                            (tail (fn-bpn-report-after-header-octets report)))
                 (:instance fn-bpn-report-parse-after-header-of-report)
                 (:instance fn-bpn-report-after-header-bounded-from-encode)
                 (:instance fn-bpn-report-encode-structure))
           :in-theory (e/d (fn-bpc-append-associativity)
                           (fn-bpn-reportp fn-bpn-report-encode
                            fn-bpn-report-parse
                            fn-bpn-report-parse-after-header
                            fn-bpn-report-parse-header-compose
                            fn-bpn-report-parse-after-header-of-report
                            fn-bpn-report-after-header-bounded-from-encode
                            fn-bpn-report-encode-structure
                            fn-bpn-report-status-octets
                            fn-bpn-report-tail-octets
                            fn-cbor-at-mostp)))))

(defthm fn-bpn-report-decode-of-encode-when-bounded
  (implies (and (fn-bpn-reportp report)
                (fn-cbor-at-mostp (fn-bpn-report-encode report)
                                  *fn-bpn-report-max-input*))
           (equal (fn-bpn-report-decode
                   (fn-bpn-report-encode report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-parse-of-encode)
                 (:instance fn-bpn-report-encode-octets)
                 (:instance fn-bpn-report-at-most-monotone
                            (xs (fn-bpn-report-encode report))
                            (small *fn-bpn-report-max-input*)
                            (large *fn-bpc-max-input*)))
           :in-theory (disable fn-bpn-reportp fn-bpn-report-encode
                               fn-bpn-report-encode-structure
                               fn-bpn-report-tail-octets
                               fn-bpn-report-after-reason-octets
                               fn-bpn-report-after-source-octets
                               fn-bpn-report-after-stamp-octets
                               fn-bpn-report-status-octets
                               fn-bpn-report-uint-octets
                               fn-bpc-enc fn-bpp-eid-value
                               fn-bpn-report-parse
                               fn-bpn-report-parse-of-encode
                               fn-bpn-report-encode-octets
                               fn-bpn-report-at-most-is-length
                               fn-cbor-at-mostp))))

; Every valid report is smaller than the decoder preflight.  Its broad
; 1194-octet estimate counts maximal CBOR heads and the 1024-octet EID.
(defthm fn-bpn-report-uint-octets-length-bound
  (<= (len (fn-bpn-report-uint-octets n)) 9)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpc-argument-length-bound
                                   (major 0) (n n)))
           :in-theory (e/d (fn-bpn-report-uint-octets fn-bpc-enc)
                           (fn-bpc-argument fn-bpc-argument-length-bound)))))

(defthm fn-bpn-report-assertion-octets-length-bound
  (<= (len (fn-bpn-report-assertion-octets assertion)) 11)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpn-report-uint-octets-length-bound
                                   (n (cadr assertion))))
           :in-theory (disable fn-bpn-report-uint-octets))))

(defthm fn-bpn-report-status-octets-length-by-count
  (<= (len (fn-bpn-report-status-octets status))
      (* 11 (len status)))
  :hints (("Goal" :induct (fn-bpn-report-status-octets status)
           :in-theory (disable fn-bpn-report-assertion-octets
                               fn-bpn-report-uint-octets))
          ("Subgoal *1/1"
           :use ((:instance fn-bpn-report-assertion-octets-length-bound
                            (assertion (car status))))
           :in-theory (e/d (fn-bpc-len-of-append)
                           (fn-bpn-report-assertion-octets
                            fn-bpn-report-uint-octets))))
  :rule-classes :linear)

(defthm fn-bpn-report-status-octets-length-bound
  (implies (fn-bpn-report-statusp status)
           (<= (len (fn-bpn-report-status-octets status)) 44))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-bpn-report-status-octets
                                      fn-bpn-report-assertion-octets
                                      fn-bpn-report-uint-octets))))

(defthm fn-bpn-report-eid-octets-length-bound
  (implies (fn-bpp-eidp eid)
           (<= (len (fn-bpc-enc :item (fn-bpp-eid-value eid))) 1100))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance fn-bpc-argument-length-bound
                            (major 4) (n 2))
                 (:instance fn-bpc-argument-length-bound
                            (major 0) (n 1))
                 (:instance fn-bpc-argument-length-bound
                            (major 0) (n 2))
                 (:instance fn-bpc-argument-length-bound
                            (major 3) (n (len (cdr eid))))
                 (:instance fn-bpc-argument-length-bound
                            (major 0) (n (nth 1 eid)))
                 (:instance fn-bpc-argument-length-bound
                            (major 0) (n (nth 2 eid))))
           :in-theory (e/d (fn-bpp-eid-value fn-bpc-enc
                             fn-bpp-eidp fn-bpp-dtn-sspp
                             fn-bpc-len-of-append)
                           (fn-bpc-argument fn-bpc-argument-length-bound
                            fn-bpp-vchar-listp fn-bpp-name-delim-at)))))

(defthm fn-bpn-report-after-stamp-length-bound
  (<= (len (fn-bpn-report-after-stamp-octets report)) 18)
  :hints (("Goal" :in-theory (e/d (fn-bpc-len-of-append)
                                  (fn-bpn-report-uint-octets))))
  :rule-classes :linear)

(defthm fn-bpn-report-after-source-length-bound
  (<= (len (fn-bpn-report-after-source-octets report)) 37)
  :hints (("Goal" :in-theory (e/d (fn-bpc-len-of-append)
                                  (fn-bpn-report-uint-octets
                                   fn-bpn-report-after-stamp-octets))))
  :rule-classes :linear)

(defthm fn-bpn-report-after-reason-length-bound
  (implies (fn-bpn-reportp report)
           (<= (len (fn-bpn-report-after-reason-octets report)) 1137))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-eid-octets-length-bound
                            (eid (nth 3 report)))
                 (:instance fn-bpn-reportp-components))
           :in-theory (e/d (fn-bpc-len-of-append)
                           (fn-bpn-reportp fn-bpp-eidp
                            fn-bpn-report-statusp fn-bpn-report-uintp
                            fn-bpn-report-assertionp
                            fn-bpn-report-after-source-octets
                            fn-bpc-enc fn-bpp-eid-value))))
  :rule-classes :linear)

(defthm fn-bpn-report-tail-length-bound
  (implies (fn-bpn-reportp report)
           (<= (len (fn-bpn-report-tail-octets report)) 1146))
  :hints (("Goal" :in-theory (e/d (fn-bpc-len-of-append)
                                  (fn-bpn-reportp fn-bpn-report-statusp
                                   fn-bpn-report-uintp fn-bpp-eidp
                                   fn-bpn-report-uint-octets
                                   fn-bpn-report-after-reason-octets))))
  :rule-classes :linear)

(defthm fn-bpn-report-after-header-length-bound
  (implies (fn-bpn-reportp report)
           (<= (len (fn-bpn-report-after-header-octets report)) 1190))
  :hints (("Goal"
           :use ((:instance fn-bpn-reportp-components)
                 (:instance fn-bpn-report-status-octets-length-bound
                            (status (nth 1 report))))
           :in-theory (e/d (fn-bpc-len-of-append)
                           (fn-bpn-reportp fn-bpn-report-statusp
                            fn-bpn-report-uintp fn-bpp-eidp
                            fn-bpn-report-tail-octets
                            fn-bpn-report-status-octets))))
  :rule-classes :linear)

(defthm fn-bpn-report-encode-length-bound
  (implies (fn-bpn-reportp report)
           (<= (len (fn-bpn-report-encode report)) 1194))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-encode-structure)
                 (:instance fn-bpn-report-after-header-length-bound))
           :in-theory (e/d (fn-bpc-len-of-append
                             fn-bpn-report-after-header-octets)
                           (fn-bpn-reportp fn-bpn-report-encode
                            fn-bpn-report-encode-structure
                            fn-bpn-report-status-octets
                            fn-bpn-report-tail-octets))))
  :rule-classes :linear)

(defthm fn-bpn-report-encode-fits-public-bound
  (implies (fn-bpn-reportp report)
           (fn-cbor-at-mostp (fn-bpn-report-encode report)
                             *fn-bpn-report-max-input*))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-encode-length-bound)
                 (:instance fn-bpn-report-encode-octets)
                 (:instance fn-cbor-octet-listp-implies-true-listp
                            (xs (fn-bpn-report-encode report)))
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-bpn-report-encode report))
                            (bound *fn-bpn-report-max-input*)))
           :in-theory (disable fn-bpn-reportp fn-bpn-report-encode
                               fn-bpn-report-encode-length-bound
                               fn-bpn-report-encode-octets
                               fn-bpn-report-encode-structure
                               fn-bpn-report-tail-octets
                               fn-bpn-report-after-reason-octets
                               fn-bpn-report-after-source-octets
                               fn-bpn-report-after-stamp-octets
                               fn-bpn-report-status-octets
                               fn-bpn-report-uint-octets
                               fn-bpc-enc fn-bpp-eid-value
                               fn-bpn-report-at-most-is-length
                               fn-cbor-at-mostp-from-length
                               fn-cbor-at-mostp))))

(defthm fn-bpn-report-decode-of-encode
  (implies (fn-bpn-reportp report)
           (equal (fn-bpn-report-decode (fn-bpn-report-encode report))
                  (fn-cbor-ok report nil)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-decode-of-encode-when-bounded)
                 (:instance fn-bpn-report-encode-fits-public-bound))
           :in-theory (disable fn-bpn-reportp fn-bpn-report-encode
                               fn-bpn-report-decode
                               fn-bpn-report-decode-of-encode-when-bounded
                               fn-bpn-report-encode-fits-public-bound))))
