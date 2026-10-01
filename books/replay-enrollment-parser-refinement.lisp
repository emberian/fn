; Ghost denotation of the actual retained parser fields. No served validation.
(in-package "ACL2")
(include-book "replay-enrollment-producer")
(include-book "statement-items-cursor-spans")

(defthm fn-rse-span-model-is-parser-borrowed-prefix
 (equal (fn-rse-span-model n tail) (take (nfix n) tail))
 :hints (("Goal" :induct (fn-rse-span-model n tail)
          :in-theory (enable fn-rse-span-model take))))

(local (defthm fn-rse-parser-at-is-nth
 (implies (natp n) (equal (fn-sic-at n x) (nth n x)))
 :hints (("Goal" :induct (fn-sic-at n x)
          :in-theory (enable fn-sic-at nth fn-cbor-ag-car fn-cbor-ag-cdr)))))
(local (defthm fn-rse-selector-at-is-nth
 (implies (natp n) (equal (fn-rsc-at n x) (nth n x)))
 :hints (("Goal" :induct (fn-rsc-at n x)
          :in-theory (enable fn-rsc-at nth)))))
(local (defthm fn-rse-nth-of-parser-item-abstraction
 (implies (natp n)
  (equal (nth n (fn-sic-items-abstract items))
         (fn-sic-item-abstract (nth n items))))
 :hints (("Goal" :induct (nth n items)
  :in-theory (enable nth fn-sic-items-abstract fn-sic-item-abstract
                     fn-cbor-ag-car fn-sic-at)))))

; This is the complete selected principal/key value, not a length tariff.
(defthm fn-rse-selected-spans-denote-the-same-parsed-fields
 (implies (fn-rse-result-spans result)
  (let* ((items (fn-rsc-at 1 result))
         (abstract (fn-sic-items-abstract items)))
   (equal (fn-rse-enrollment-model (fn-rse-result-spans result))
    (list (cdr (nth 0 abstract))
     (list (cons :ed25519 (cdr (nth 2 abstract)))
           (cons :ml-dsa-65 (cdr (nth 4 abstract))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (enable fn-rse-result-spans fn-rse-enrollment-model
          fn-rse-span-length fn-rse-span-tail fn-rse-span-shapep
          fn-sic-item-abstract
          fn-rsc-at fn-sic-at fn-rsc-widthp
          fn-cbor-ag-car fn-cbor-ag-cdr))))

; The parser's fixed4 source-span contract is a required producer premise.
; It is proved by the actual parser, never obtained from host readiness.
(local (defthm fn-rse-parser-span-list-selected-item
 (implies (and (fn-sic-span-item-listp items source)
               (natp n) (< n (len items)))
  (fn-sic-span-itemp (nth n items) source))
 :hints (("Goal" :induct (nth n items)
  :in-theory (enable fn-sic-span-item-listp nth len)))))
(local (defthm fn-rse-parser-source-suffix-has-octets
 (implies (fn-cbor-octet-listp source)
  (fn-cbor-octet-listp (nthcdr n source)))
 :hints (("Goal" :induct (nthcdr n source)
  :in-theory (enable nthcdr fn-cbor-octet-listp)))))
(local (defthm fn-rse-parser-source-suffix-length
 (equal (len (nthcdr n source)) (nfix (- (len source) (nfix n))))
 :hints (("Goal" :induct (nthcdr n source)
  :in-theory (enable nthcdr len nfix)))))
(local (defthm fn-rse-bounded-prefix-has-octets
 (implies (and (natp n) (fn-cbor-octet-listp tail) (<= n (len tail)))
  (fn-cbor-octet-listp (take n tail)))
 :hints (("Goal" :induct (fn-rse-span-model n tail)
  :in-theory (enable take fn-cbor-octet-listp len)))))
(local (defthm fn-rse-length-of-borrowed-prefix
 (equal (len (take (nfix n) tail)) (nfix n))
 :hints (("Goal" :induct (fn-rse-span-model n tail)
  :in-theory (enable take len)))))
(defthm fn-rse-parser-byte-span-denotes-exact-octets
 (implies (and (fn-sic-span-itemp span source)
               (equal (car span) :bytes)
               (fn-cbor-octet-listp source))
  (and (fn-cbor-octet-listp
         (fn-rse-span-model (fn-rse-span-length span) (fn-rse-span-tail span)))
       (equal (len (fn-rse-span-model (fn-rse-span-length span)
                                     (fn-rse-span-tail span)))
              (fn-rse-span-length span))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rse-parser-source-suffix-has-octets (n (nth 1 span)))
        (:instance fn-rse-parser-source-suffix-length (n (nth 1 span)))
        (:instance fn-rse-bounded-prefix-has-octets
          (n (nth 2 span)) (tail (nth 3 span)))
        (:instance fn-rse-length-of-borrowed-prefix
          (n (nth 2 span)) (tail (nth 3 span))))
  :in-theory (e/d
   (fn-sic-span-itemp fn-rse-span-length fn-rse-span-tail
    fn-rsc-at fn-sic-at fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-cbor-octet-listp nthcdr take len)))))
(local (defthm fn-rse-width-has-exact-length
 (implies (fn-rsc-widthp n x) (equal (len x) (nfix n)))
 :hints (("Goal" :induct (fn-rsc-widthp n x)
  :in-theory (enable fn-rsc-widthp len)))))
(defthm fn-rse-selected-spans-retain-the-original-source
 (implies (and (fn-sic-span-item-listp (fn-rsc-at 1 result) source)
               (fn-rse-result-spans result))
  (let ((spans (fn-rse-result-spans result)))
   (and (fn-sic-span-itemp (fn-rsc-at 0 spans) source)
        (fn-sic-span-itemp (fn-rsc-at 1 spans) source)
        (fn-sic-span-itemp (fn-rsc-at 2 spans) source))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (enable fn-rse-result-spans fn-sic-span-item-listp
          fn-rsc-at fn-rsc-widthp))))

(defthm fn-rse-selected-span-layout-and-widths-by-definition
 (implies (fn-rse-result-spans result)
  (let ((spans (fn-rse-result-spans result)))
   (and (fn-rsc-widthp 3 spans)
        (equal (car (fn-rsc-at 0 spans)) :bytes)
        (equal (car (fn-rsc-at 1 spans)) :bytes)
        (equal (car (fn-rsc-at 2 spans)) :bytes)
        (equal (fn-rse-span-length (fn-rsc-at 0 spans)) 32)
        (equal (fn-rse-span-length (fn-rsc-at 1 spans)) 32)
        (equal (fn-rse-span-length (fn-rsc-at 2 spans)) 1952))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (enable fn-rse-result-spans fn-rse-span-length fn-rse-span-shapep
          fn-rsc-at fn-rsc-widthp))))

(defthm fn-rse-selected-parser-result-is-accepted-by-definition
 (implies (fn-rse-result-spans result)
  (and (fn-stmt-okp result)
       (equal (fn-stmt-value result) (fn-rsc-at 1 result))))
 :hints (("Goal" :in-theory
  (enable fn-rse-result-spans fn-stmt-okp fn-stmt-value
          fn-rsc-at fn-rsc-widthp))))

(local (defthm fn-rse-five-items-reconstruct-by-definition
 (implies (fn-rsc-widthp 5 items)
  (equal items (list (nth 0 items) (nth 1 items) (nth 2 items)
                    (nth 3 items) (nth 4 items))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :expand ((fn-rsc-widthp 5 items) (fn-rsc-widthp 4 (cdr items))
           (fn-rsc-widthp 3 (cddr items)) (fn-rsc-widthp 2 (cdddr items))
           (fn-rsc-widthp 1 (cddddr items))
           (fn-rsc-widthp 0 (cdr (cddddr items))))
  :in-theory (enable nth fn-rsc-widthp)))))
(local (defthm fn-rse-five-item-abstraction-unfolds
 (implies (fn-rsc-widthp 5 items)
  (equal (fn-sic-items-abstract items)
   (list (fn-sic-item-abstract (nth 0 items))
         (fn-sic-item-abstract (nth 1 items))
         (fn-sic-item-abstract (nth 2 items))
         (fn-sic-item-abstract (nth 3 items))
         (fn-sic-item-abstract (nth 4 items)))))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-rsc-widthp 5 items) (fn-rsc-widthp 4 (cdr items))
           (fn-rsc-widthp 3 (cddr items)) (fn-rsc-widthp 2 (cdddr items))
           (fn-rsc-widthp 1 (cddddr items))
           (fn-rsc-widthp 0 (cdr (cddddr items)))
           (fn-sic-items-abstract items) (fn-sic-items-abstract (cdr items))
           (fn-sic-items-abstract (cddr items))
           (fn-sic-items-abstract (cdddr items))
           (fn-sic-items-abstract (cddddr items)))
  :in-theory (enable nth fn-rsc-widthp fn-sic-items-abstract)))))
(defthm fn-rse-selected-parser-items-have-exact-five-field-denotation
 (implies (fn-rse-result-spans result)
  (let ((value (fn-rse-enrollment-model (fn-rse-result-spans result))))
   (equal (fn-sic-items-abstract (fn-rsc-at 1 result))
    (list (cons :bytes (car value))
          (cons :uint 1)
          (cons :bytes (cdr (car (cadr value))))
          (cons :uint 2)
          (cons :bytes (cdr (cadr (cadr value))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rse-five-items-reconstruct-by-definition
          (items (fn-rsc-at 1 result))))
  :in-theory
  (enable fn-rse-result-spans fn-rse-enrollment-model
          fn-rse-span-length fn-rse-span-tail fn-rse-span-shapep
          fn-rsc-at fn-rsc-widthp fn-sic-items-abstract fn-sic-item-abstract
          fn-sic-at fn-cbor-ag-car fn-cbor-ag-cdr))))
