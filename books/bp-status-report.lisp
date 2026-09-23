; RFC 9171 section 6.1.1 administrative status-report payloads.
; A decoded report is a remote observation.  This book grants no retention,
; receipt, retry, or release authority to any assertion.
(in-package "ACL2")
(include-book "bp-primary")
(set-verify-guards-eagerness 0)

(defconst *fn-bpn-report-max-input* 4096)

(defun fn-bpn-report-uintp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *fn-bpc-max-uint*)))

(defun fn-bpn-report-assertionp (x)
  (declare (xargs :guard t))
  (or (equal x '(nil)) (equal x '(t))
      (and (true-listp x) (equal (len x) 2)
           (eq (car x) t) (fn-bpn-report-uintp (cadr x)))))

(defthm fn-bpn-report-two-list-shape
  (implies (and (true-listp x) (equal (len x) 2))
           (equal x (list (car x) (cadr x))))
  :rule-classes nil)

(defun fn-bpn-report-statusp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (fn-bpn-report-assertionp (nth 0 x))
       (fn-bpn-report-assertionp (nth 1 x))
       (fn-bpn-report-assertionp (nth 2 x))
       (fn-bpn-report-assertionp (nth 3 x))))

; The subject bundle is not part of the report payload.  Its processing flag
; is therefore an explicit generation input, never inferred from this record.
(defun fn-bpn-report-assertion-time-consistentp (x requested)
  (declare (xargs :guard t))
  (if (eq (fn-cbor-ag-car x) t)
      (equal (len x) (if requested 2 1))
    (equal x '(nil))))

(defun fn-bpn-report-status-time-consistentp (xs requested)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (and (fn-bpn-report-assertion-time-consistentp (car xs) requested)
           (fn-bpn-report-status-time-consistentp (cdr xs) requested))
    (null xs)))

(defun fn-bpn-reportp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6) (eq (car x) :report)
       (fn-bpn-report-statusp (nth 1 x))
       (natp (nth 2 x)) (<= (nth 2 x) 11)
       (fn-bpp-eidp (nth 3 x))
       (true-listp (nth 4 x)) (equal (len (nth 4 x)) 2)
       (fn-bpn-report-uintp (nth 0 (nth 4 x)))
       (fn-bpn-report-uintp (nth 1 (nth 4 x)))
       (or (null (nth 5 x))
           (and (consp (nth 5 x))
                (fn-bpn-report-uintp (car (nth 5 x)))
                (fn-bpn-report-uintp (cdr (nth 5 x)))))))

(defun fn-bpn-report-uint-octets (x)
  (declare (xargs :guard t))
  (fn-bpc-enc :item (cons :uint x)))

(defun fn-bpn-report-assertion-octets (x)
  (declare (xargs :guard t))
  (cond ((equal x '(nil)) '(129 244))
        ((equal x '(t)) '(129 245))
        (t (append '(130 245)
                   (fn-bpn-report-uint-octets
                    (fn-cbor-ag-car (fn-cbor-ag-cdr x)))))))

(defun fn-bpn-report-status-octets (xs)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (append (fn-bpn-report-assertion-octets (car xs))
              (fn-bpn-report-status-octets (cdr xs)))
    nil))

(defthm fn-bpn-report-uint-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-uint-octets x))
  :hints (("Goal" :in-theory (disable fn-bpc-enc-are-octets)
           :use ((:instance fn-bpc-enc-are-octets
                            (flg :item) (x (cons :uint x)))))))

(defthm fn-bpn-report-assertion-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-assertion-octets x))
  :hints (("Goal" :in-theory (disable fn-bpn-report-uint-octets
                                      fn-bpc-enc))))

(defthm fn-bpn-report-octets-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b)))
  :hints (("Goal" :induct (append a b)
           :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-bpn-report-status-octets-are-octets
  (fn-cbor-octet-listp (fn-bpn-report-status-octets xs))
  :hints (("Goal" :induct (fn-bpn-report-status-octets xs)
           :in-theory (disable fn-bpn-report-uint-octets fn-bpc-enc))))

(defun fn-bpn-report-encode (report)
  (declare (xargs :guard t))
  (if (not (fn-bpn-reportp report))
      :bad
    (let ((fragment (nth 5 report)) (stamp (nth 4 report)))
      (append '(130 1)
              (list (if fragment 134 132) 132)
              (fn-bpn-report-status-octets (nth 1 report))
              (fn-bpn-report-uint-octets (nth 2 report))
              (fn-bpc-enc :item (fn-bpp-eid-value (nth 3 report)))
              (list 130)
              (fn-bpn-report-uint-octets (car stamp))
              (fn-bpn-report-uint-octets (cadr stamp))
              (if fragment
                  (append (fn-bpn-report-uint-octets (car fragment))
                          (fn-bpn-report-uint-octets (cdr fragment)))
                nil)))))

(defun fn-bpn-report-encode-for-subject (report time-requested)
  (declare (xargs :guard t))
  (if (and (fn-bpn-reportp report)
           (fn-bpn-report-status-time-consistentp (nth 1 report)
                                                   time-requested))
      (fn-bpn-report-encode report)
    :bad))

; The primitive parser already enforces definite arrays, minimal integer
; heads, item/work limits, and the BP uint bound.  Boolean heads are read only
; at the four assertion positions; the public decoder checks exact reencoding.
(defun fn-bpn-report-read-uint (xs)
  (declare (xargs :guard t))
  (let ((r (fn-bpc-decode xs)))
    (if (and (fn-cbor-result-okp r)
             (consp (fn-cbor-result-value r))
             (eq (car (fn-cbor-result-value r)) :uint))
        (fn-cbor-ok (cdr (fn-cbor-result-value r))
                    (fn-cbor-result-rest r))
      (fn-cbor-error :malformed))))

(defthm fn-bpn-report-read-uint-of-encode
  (implies (and (fn-bpn-report-uintp n)
                (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-uint-octets n) rest)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-read-uint
                   (append (fn-bpn-report-uint-octets n) rest))
                  (fn-cbor-ok n rest)))
  :hints (("Goal"
           :use ((:instance fn-bpc-decode-of-encode
                            (flg :item) (x (cons :uint n))
                            (budget *fn-bpc-max-items*)))
           :in-theory (disable fn-bpc-dec fn-bpc-enc
                               fn-bpc-decode-of-encode))))

(defun fn-bpn-report-at-most-induction (xs small large)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (fn-bpn-report-at-most-induction (cdr xs) (1- small) (1- large))
    (list small large)))

(defthm fn-bpn-report-at-most-monotone
  (implies (and (natp small) (natp large) (<= small large)
                (fn-cbor-at-mostp xs small))
           (fn-cbor-at-mostp xs large))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpn-report-at-most-induction xs small large)
           :in-theory (enable fn-cbor-at-mostp))))

(defthm fn-bpn-report-at-most-is-length
  (implies (and (true-listp xs) (natp bound))
           (equal (fn-cbor-at-mostp xs bound)
                  (<= (len xs) bound)))
  :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
           :in-theory (enable fn-cbor-at-mostp))))

(defthm fn-bpn-report-bounded-append-suffix
  (implies (and (true-listp a) (true-listp b)
                (natp bound)
                (fn-cbor-at-mostp (append a b) bound))
           (fn-cbor-at-mostp b bound))
  :hints (("Goal" :in-theory (disable fn-cbor-at-mostp))))

(defun fn-bpn-report-read-assertion (xs)
  (declare (xargs :guard t))
  (cond ((and (consp xs) (equal (car xs) 129)
              (consp (cdr xs)) (equal (cadr xs) 244))
         (fn-cbor-ok '(nil) (cddr xs)))
        ((and (consp xs) (equal (car xs) 129)
              (consp (cdr xs)) (equal (cadr xs) 245))
         (fn-cbor-ok '(t) (cddr xs)))
        ((and (consp xs) (equal (car xs) 130)
              (consp (cdr xs)) (equal (cadr xs) 245))
         (let ((r (fn-bpn-report-read-uint (cddr xs))))
           (if (fn-cbor-result-okp r)
               (fn-cbor-ok (list t (fn-cbor-result-value r))
                           (fn-cbor-result-rest r))
             r)))
        (t (fn-cbor-error :malformed))))

(defthm fn-bpn-report-read-assertion-of-encode
  (implies (and (fn-bpn-report-assertionp assertion)
                (fn-cbor-octet-listp rest)
                (fn-cbor-at-mostp
                 (append (fn-bpn-report-assertion-octets assertion) rest)
                 *fn-bpc-max-input*))
           (equal (fn-bpn-report-read-assertion
                   (append (fn-bpn-report-assertion-octets assertion) rest))
                  (fn-cbor-ok assertion rest)))
  :hints (("Goal"
           :use ((:instance fn-bpn-report-read-uint-of-encode
                            (n (cadr assertion)) (rest rest))
                 (:instance fn-bpn-report-two-list-shape
                            (x assertion))
                 (:instance fn-bpn-report-at-most-monotone
                            (xs (append
                                 (fn-bpn-report-uint-octets (cadr assertion))
                                 rest))
                            (small 65534) (large 65536)))
           :in-theory (e/d (fn-cbor-at-mostp)
                           (fn-bpn-report-read-uint
                            fn-bpn-report-uint-octets
                            fn-bpn-report-read-uint-of-encode)))))

(defun fn-bpn-report-read-status (n xs)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      (fn-cbor-ok nil xs)
    (let ((a (fn-bpn-report-read-assertion xs)))
      (if (not (fn-cbor-result-okp a)) a
        (let ((tail (fn-bpn-report-read-status
                     (- n 1) (fn-cbor-result-rest a))))
          (if (fn-cbor-result-okp tail)
              (fn-cbor-ok (cons (fn-cbor-result-value a)
                                (fn-cbor-result-value tail))
                          (fn-cbor-result-rest tail))
            tail))))))

(defun fn-bpn-report-assertion-listp (xs)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (consp xs)
      (and (fn-bpn-report-assertionp (car xs))
           (fn-bpn-report-assertion-listp (cdr xs)))
    (null xs)))


(defun fn-bpn-report-read-source (xs)
  (declare (xargs :guard t))
  (let* ((r (fn-bpc-decode xs))
         (eid (and (fn-cbor-result-okp r)
                   (fn-bpp-value-eid (fn-cbor-result-value r)))))
    (if (and eid (fn-bpp-eidp eid))
        (fn-cbor-ok eid (fn-cbor-result-rest r))
      (fn-cbor-error :malformed))))

(defun fn-bpn-report-read-stamp (xs)
  (declare (xargs :guard t))
  (if (not (and (consp xs) (equal (car xs) 130)))
      (fn-cbor-error :malformed)
    (let ((a (fn-bpn-report-read-uint (cdr xs))))
      (if (not (fn-cbor-result-okp a)) a
        (let ((b (fn-bpn-report-read-uint (fn-cbor-result-rest a))))
          (if (fn-cbor-result-okp b)
              (fn-cbor-ok (list (fn-cbor-result-value a)
                                (fn-cbor-result-value b))
                          (fn-cbor-result-rest b))
            b))))))

(defun fn-bpn-report-read-fragment (fragmentp xs)
  (declare (xargs :guard t))
  (if (not fragmentp) (fn-cbor-ok nil xs)
    (let ((a (fn-bpn-report-read-uint xs)))
      (if (not (fn-cbor-result-okp a)) a
        (let ((b (fn-bpn-report-read-uint (fn-cbor-result-rest a))))
          (if (fn-cbor-result-okp b)
              (fn-cbor-ok (cons (fn-cbor-result-value a)
                                (fn-cbor-result-value b))
                          (fn-cbor-result-rest b))
            b))))))

(defun fn-bpn-report-parse (xs)
  (declare (xargs :guard t))
  (if (not (and (consp xs) (equal (car xs) 130)
                (consp (cdr xs)) (equal (cadr xs) 1)
                (consp (cddr xs))
                (or (equal (caddr xs) 132) (equal (caddr xs) 134))
                (consp (cdddr xs)) (equal (cadddr xs) 132)))
      (fn-cbor-error :malformed)
    (let* ((fragmentp (equal (caddr xs) 134))
           (status (fn-bpn-report-read-status 4 (cddddr xs))))
      (if (not (fn-cbor-result-okp status)) status
        (let ((reason (fn-bpn-report-read-uint (fn-cbor-result-rest status))))
          (if (not (fn-cbor-result-okp reason)) reason
            (let ((source (fn-bpn-report-read-source
                           (fn-cbor-result-rest reason))))
              (if (not (fn-cbor-result-okp source)) source
                (let ((stamp (fn-bpn-report-read-stamp
                              (fn-cbor-result-rest source))))
                  (if (not (fn-cbor-result-okp stamp)) stamp
                    (let ((fragment (fn-bpn-report-read-fragment
                                     fragmentp (fn-cbor-result-rest stamp))))
                      (if (not (fn-cbor-result-okp fragment)) fragment
                        (fn-cbor-ok
                         (list :report (fn-cbor-result-value status)
                               (fn-cbor-result-value reason)
                               (fn-cbor-result-value source)
                               (fn-cbor-result-value stamp)
                               (fn-cbor-result-value fragment))
                         (fn-cbor-result-rest fragment))))))))))))))

(defun fn-bpn-report-decode (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-bpn-report-max-input*))
      (fn-cbor-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-cbor-error :malformed)
      (let* ((r (fn-bpn-report-parse octets))
             (report (and (fn-cbor-result-okp r)
                          (fn-cbor-result-value r))))
        (if (and (fn-cbor-result-okp r)
                 (null (fn-cbor-result-rest r))
                 (fn-bpn-reportp report)
                 (equal (fn-bpn-report-encode report) octets))
            (fn-cbor-ok report nil)
          (fn-cbor-error :malformed))))))

(defthm fn-bpn-report-encode-octets
  (implies (fn-bpn-reportp report)
           (fn-cbor-octet-listp (fn-bpn-report-encode report)))
  :hints (("Goal"
           :use ((:instance fn-bpc-enc-are-octets
                            (flg :item)
                            (x (fn-bpp-eid-value (nth 3 report))))
                 (:instance fn-bpn-report-status-octets-are-octets
                            (xs (nth 1 report)))
                 (:instance fn-bpn-report-uint-octets-are-octets
                            (x (nth 2 report)))
                 (:instance fn-bpn-report-uint-octets-are-octets
                            (x (car (nth 4 report))))
                 (:instance fn-bpn-report-uint-octets-are-octets
                            (x (cadr (nth 4 report)))))
           :in-theory (e/d (fn-cbor-octet-listp)
                           (fn-bpc-enc fn-bpn-report-uint-octets
                            fn-bpn-report-status-octets fn-bpp-eid-value)))))

(defthm fn-bpn-report-accepted-input-is-canonical
  (implies (fn-cbor-result-okp (fn-bpn-report-decode octets))
           (equal (fn-bpn-report-encode
                   (fn-cbor-result-value (fn-bpn-report-decode octets)))
                  octets))
  :hints (("Goal" :in-theory (disable fn-bpn-report-parse
                                      fn-bpn-report-encode
                                      fn-bpn-reportp))))

(verify-guards fn-bpn-report-uintp)
(verify-guards fn-bpn-report-assertionp)
(verify-guards fn-bpn-report-statusp)
(verify-guards fn-bpn-report-assertion-time-consistentp)
(verify-guards fn-bpn-report-status-time-consistentp)
(verify-guards fn-bpn-reportp)
(verify-guards fn-bpn-report-uint-octets)
(verify-guards fn-bpn-report-assertion-octets)
(verify-guards fn-bpn-report-status-octets)
(verify-guards fn-bpn-report-encode)
(verify-guards fn-bpn-report-encode-for-subject)
(verify-guards fn-bpn-report-read-uint)
(verify-guards fn-bpn-report-read-assertion)
(verify-guards fn-bpn-report-read-status)
(verify-guards fn-bpn-report-assertion-listp)
(verify-guards fn-bpn-report-read-source)
(verify-guards fn-bpn-report-read-stamp)
(verify-guards fn-bpn-report-read-fragment)
(verify-guards fn-bpn-report-parse)
(verify-guards fn-bpn-report-decode)
(deftheory fn-bpn-report-codec-vocabulary nil)
