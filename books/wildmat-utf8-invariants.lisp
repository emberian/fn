; Safety and progress properties for the bounded UTF-8 wildmat front end.
;
; RFC 3977 section 9 incorporates the RFC 3629 UTF-8 productions.  The base
; wildmat book implements those productions; this book proves that every
; successful decoder step returns one Unicode scalar and advances by one to
; four octets.  It then lifts those facts to the public decoder.
;
; These are properties of the executable parser's results for arbitrary ACL2
; objects.  They do not assume that a caller prevalidates the output record.

(in-package "ACL2")

(include-book "wildmat")
(local (include-book "arithmetic/top" :dir :system))

; A Unicode scalar value excludes the surrogate interval even though the
; parser's historical `fn-wildmat-codepointp` recognizer only records the
; numeric code-point range.
(defun fn-wildmat-unicode-scalarp (x)
  (and (natp x)
       (<= x *fn-wildmat-max-codepoint*)
       (or (<= x 55295) (<= 57344 x))))

(defthm fn-wildmat-unicode-scalarp-implies-codepointp
  (implies (fn-wildmat-unicode-scalarp x)
           (fn-wildmat-codepointp x))
  :hints (("Goal" :in-theory (enable fn-wildmat-unicode-scalarp
                                      fn-wildmat-codepointp))))

; The disjunction is deliberately stated in terms of the executable suffixes:
; a successful step leaves exactly the input after one, two, three, or four
; octets, rather than an unrelated list with merely a smaller length.
(defthm fn-wildmat-utf8-next-success-suffix
  (implies (fn-wildmat-result-okp (fn-wildmat-utf8-next octets))
           (or (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets))
                      (cdr octets))
               (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets))
                      (cdr (cdr octets)))
               (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets))
                      (cdr (cdr (cdr octets))))
               (equal (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets))
                      (cdr (cdr (cdr (cdr octets)))))))
  :hints (("Goal" :in-theory (enable fn-wildmat-utf8-next
                                      fn-wildmat-result-okp
                                      fn-wildmat-utf8-rest
                                      fn-wildmat-utf8-ok
                                      fn-wildmat-error))))

(defthm fn-wildmat-utf8-next-success-strict-progress
  (implies (fn-wildmat-result-okp (fn-wildmat-utf8-next octets))
           (< (acl2-count (fn-wildmat-utf8-rest
                           (fn-wildmat-utf8-next octets)))
              (acl2-count octets)))
  :hints (("Goal"
           :use fn-wildmat-utf8-next-success-suffix
           :in-theory (enable fn-wildmat-utf8-next
                               fn-wildmat-result-okp
                               fn-wildmat-utf8-rest
                               fn-wildmat-utf8-ok
                               fn-wildmat-error))))

(defthm fn-wildmat-utf8-next-success-scalar
  (implies (fn-wildmat-result-okp (fn-wildmat-utf8-next octets))
           (fn-wildmat-unicode-scalarp
            (fn-wildmat-result-value (fn-wildmat-utf8-next octets))))
  :hints (("Goal"
           :in-theory (enable fn-wildmat-utf8-next
                               fn-wildmat-result-okp
                               fn-wildmat-result-value
                               fn-wildmat-utf8-ok
                               fn-wildmat-error
                               fn-wildmat-utf8-2p
                               fn-wildmat-utf8-3-tailsp
                               fn-wildmat-utf8-4-tailsp
                               fn-wildmat-utf8-tailp
                               fn-wildmat-utf8-2-value
                               fn-wildmat-utf8-3-value
                               fn-wildmat-utf8-4-value
                               fn-wildmat-octetp
                               fn-cbor-octetp
                               fn-wildmat-unicode-scalarp)
           :nonlinearp t)))

(defthm fn-wildmat-utf8-next-success-codepointp
  (implies (fn-wildmat-result-okp (fn-wildmat-utf8-next octets))
           (fn-wildmat-codepointp
            (fn-wildmat-result-value (fn-wildmat-utf8-next octets))))
  :hints (("Goal" :use fn-wildmat-utf8-next-success-scalar)))

(defthm fn-wildmat-octet-listp-implies-true-listp
  (implies (fn-wildmat-octet-listp octets)
           (true-listp octets))
  :hints (("Goal" :in-theory (enable fn-wildmat-octet-listp
                                      fn-cbor-octet-listp))))

(defthm fn-wildmat-codepoint-listp-revappend
  (implies (and (fn-wildmat-codepoint-listp xs)
                (fn-wildmat-codepoint-listp ys))
           (fn-wildmat-codepoint-listp (revappend xs ys)))
  :hints (("Goal" :induct (revappend xs ys)
           :in-theory (enable fn-wildmat-codepoint-listp revappend))))

(defthm fn-wildmat-codepoint-listp-reverse
  (implies (fn-wildmat-codepoint-listp xs)
           (fn-wildmat-codepoint-listp (reverse xs)))
  :hints (("Goal"
           :use ((:instance fn-wildmat-codepoint-listp-revappend (ys nil)))
           :in-theory (enable fn-wildmat-codepoint-listp reverse))))

(defthm fn-wildmat-len-revappend
  (equal (len (revappend xs ys))
         (+ (len xs) (len ys)))
  :hints (("Goal" :induct (revappend xs ys)
           :in-theory (enable revappend))))

(defthm fn-wildmat-len-reverse
  (equal (len (reverse xs)) (len xs))
  :hints (("Goal"
           :use ((:instance fn-wildmat-len-revappend (ys nil)))
           :in-theory (enable reverse))))

(defthm fn-wildmat-items-p-revappend
  (implies (and (fn-wildmat-items-p xs)
                (fn-wildmat-items-p ys))
           (fn-wildmat-items-p (revappend xs ys)))
  :hints (("Goal" :induct (revappend xs ys)
           :in-theory (enable fn-wildmat-items-p revappend))))

(defthm fn-wildmat-items-p-reverse
  (implies (fn-wildmat-items-p xs)
           (fn-wildmat-items-p (reverse xs)))
  :hints (("Goal"
           :use ((:instance fn-wildmat-items-p-revappend (ys nil)))
           :in-theory (enable fn-wildmat-items-p reverse))))

(defthm fn-wildmat-utf8-next-success-rest-true-listp
  (implies (and (true-listp octets)
                (fn-wildmat-result-okp (fn-wildmat-utf8-next octets)))
           (true-listp (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets))))
  :hints (("Goal" :use fn-wildmat-utf8-next-success-suffix
           :in-theory (enable fn-wildmat-utf8-next
                               fn-wildmat-result-okp
                               fn-wildmat-utf8-rest
                               fn-wildmat-utf8-ok
                               fn-wildmat-error))))

(defthm fn-wildmat-utf8-next-success-rest-shorter
  (implies (and (true-listp octets)
                (fn-wildmat-result-okp (fn-wildmat-utf8-next octets)))
           (< (len (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets)))
              (len octets)))
  :hints (("Goal" :use fn-wildmat-utf8-next-success-suffix
           :in-theory (enable fn-wildmat-utf8-next
                               fn-wildmat-result-okp
                               fn-wildmat-utf8-rest
                               fn-wildmat-utf8-ok
                               fn-wildmat-error))))

(defthm fn-wildmat-utf8-next-success-rest-octet-listp
  (implies (and (fn-wildmat-octet-listp octets)
                (fn-wildmat-result-okp (fn-wildmat-utf8-next octets)))
           (fn-wildmat-octet-listp
            (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets))))
  :hints (("Goal" :use fn-wildmat-utf8-next-success-suffix
           :in-theory (enable fn-wildmat-octet-listp
                               fn-cbor-octet-listp))))

(defthm fn-wildmat-decode-aux-success-codepoint-listp
  (implies (and (fn-wildmat-octet-listp octets)
                (fn-wildmat-codepoint-listp codepoints-rev)
                (fn-wildmat-result-okp
                 (fn-wildmat-decode-aux octets codepoints-rev)))
           (fn-wildmat-codepoint-listp
            (fn-wildmat-result-value
             (fn-wildmat-decode-aux octets codepoints-rev))))
  :hints (("Goal"
           :induct (fn-wildmat-decode-aux octets codepoints-rev)
           :in-theory (enable fn-wildmat-decode-aux
                               fn-wildmat-result-okp
                               fn-wildmat-result-value
                               fn-wildmat-codepoint-listp))))

(defthm fn-wildmat-decode-aux-success-length-bound
  (implies (and (fn-wildmat-octet-listp octets)
                (true-listp codepoints-rev)
                (fn-wildmat-result-okp
                 (fn-wildmat-decode-aux octets codepoints-rev)))
           (<= (len (fn-wildmat-result-value
                     (fn-wildmat-decode-aux octets codepoints-rev)))
               (+ (len octets) (len codepoints-rev))))
  :hints (("Goal"
           :induct (fn-wildmat-decode-aux octets codepoints-rev)
           :in-theory (enable fn-wildmat-decode-aux
                               fn-wildmat-result-okp
                               fn-wildmat-result-value))))

(defthm fn-wildmat-successful-decode-codepoint-listp
  (implies (fn-wildmat-result-okp (fn-wildmat-decode octets))
           (fn-wildmat-codepoint-listp
            (fn-wildmat-result-value (fn-wildmat-decode octets))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-decode-aux-success-codepoint-listp
                            (codepoints-rev nil)))
           :in-theory (e/d (fn-wildmat-decode
                             fn-wildmat-octet-listp
                             fn-wildmat-result-okp
                             fn-wildmat-result-value)
                           (fn-wildmat-decode-aux)))))

(defthm fn-wildmat-successful-decode-length-bounded-by-input
  (implies (fn-wildmat-result-okp (fn-wildmat-decode octets))
           (<= (len (fn-wildmat-result-value (fn-wildmat-decode octets)))
               (len octets)))
  :hints (("Goal"
           :use ((:instance fn-wildmat-decode-aux-success-length-bound
                            (codepoints-rev nil)))
           :in-theory (e/d (fn-wildmat-decode
                             fn-wildmat-octet-listp
                             fn-wildmat-result-okp
                             fn-wildmat-result-value)
                           (fn-wildmat-decode-aux)))))

(defthm fn-wildmat-scan-end-success-items
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-scan-endp
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (and (consp (fn-wildmat-scan-items
                        (fn-wildmat-scan-pattern codepoints items-rev)))
                (fn-wildmat-items-p
                 (fn-wildmat-scan-items
                  (fn-wildmat-scan-pattern codepoints items-rev)))))
  :hints (("Goal"
           :induct (fn-wildmat-scan-pattern codepoints items-rev)
           :in-theory (enable fn-wildmat-scan-pattern
                               fn-wildmat-scan-endp
                               fn-wildmat-scan-items
                               fn-wildmat-items-p))))

(defthm fn-wildmat-scan-more-success-items
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-scan-morep
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (and (consp (fn-wildmat-scan-items
                        (fn-wildmat-scan-pattern codepoints items-rev)))
                (fn-wildmat-items-p
                 (fn-wildmat-scan-items
                  (fn-wildmat-scan-pattern codepoints items-rev)))))
  :hints (("Goal"
           :induct (fn-wildmat-scan-pattern codepoints items-rev)
           :in-theory (enable fn-wildmat-scan-pattern
                               fn-wildmat-scan-morep
                               fn-wildmat-scan-items
                               fn-wildmat-items-p))))

(defthm fn-wildmat-scan-end-success-items-consp
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-scan-endp
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (consp (fn-wildmat-scan-items
                   (fn-wildmat-scan-pattern codepoints items-rev))))
  :hints (("Goal" :use fn-wildmat-scan-end-success-items)))

(defthm fn-wildmat-scan-end-success-items-valid
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-scan-endp
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints items-rev))))
  :hints (("Goal" :use fn-wildmat-scan-end-success-items)))

(defthm fn-wildmat-scan-more-success-items-consp
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-scan-morep
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (consp (fn-wildmat-scan-items
                   (fn-wildmat-scan-pattern codepoints items-rev))))
  :hints (("Goal" :use fn-wildmat-scan-more-success-items)))

(defthm fn-wildmat-scan-more-success-items-valid
  (implies (and (fn-wildmat-items-p items-rev)
                (fn-wildmat-scan-morep
                 (fn-wildmat-scan-pattern codepoints items-rev)))
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints items-rev))))
  :hints (("Goal" :use fn-wildmat-scan-more-success-items)))

(defthm fn-wildmat-scan-nil-end-items-consp
  (implies (equal (car (fn-wildmat-scan-pattern codepoints nil)) :end)
           (consp (fn-wildmat-scan-items
                   (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-end-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-endp fn-wildmat-items-p)))
  :rule-classes :forward-chaining)

(defthm fn-wildmat-scan-nil-end-items-valid
  (implies (equal (car (fn-wildmat-scan-pattern codepoints nil)) :end)
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-end-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-endp fn-wildmat-items-p)))
  :rule-classes :forward-chaining)

(defthm fn-wildmat-scan-nil-more-items-consp
  (implies (equal (car (fn-wildmat-scan-pattern codepoints nil)) :more)
           (consp (fn-wildmat-scan-items
                   (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-more-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-morep fn-wildmat-items-p)))
  :rule-classes :forward-chaining)

(defthm fn-wildmat-scan-nil-more-items-valid
  (implies (equal (car (fn-wildmat-scan-pattern codepoints nil)) :more)
           (fn-wildmat-items-p
            (fn-wildmat-scan-items
             (fn-wildmat-scan-pattern codepoints nil))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-scan-more-success-items
                            (items-rev nil)))
           :in-theory (enable fn-wildmat-scan-morep fn-wildmat-items-p)))
  :rule-classes :forward-chaining)
