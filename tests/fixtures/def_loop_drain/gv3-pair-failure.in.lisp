(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-cfg-parse-items-loop (count octets acc)
  (declare (xargs :guard t :measure (nfix count)))
  (if (not (posp count))
      (fn-record-parse-ok (fn-ag-rev-onto acc nil) octets)
    (if (not (fn-cbor-octet-listp octets))
        (fn-record-parse-error :octets)
      (let ((d (fn-cfg-item-decode octets)))
        (if (not (fn-cbor-result-okp d))
            (fn-record-parse-error :item)
          (if (not (fn-cfg-itemp (fn-cbor-result-value d)))
              (fn-record-parse-error :item-type)
            (fn-cfg-parse-items-loop (- count 1) (fn-cbor-result-rest d)
                                     (cons (fn-cbor-result-value d) acc))))))))

(defun fn-cfg-parse-items (count octets)
  (declare (xargs :guard t :measure (nfix count) :verify-guards nil))
  (mbe :logic
       (if (not (posp count))
           (fn-record-parse-ok nil octets)
         (if (not (fn-cbor-octet-listp octets))
             (fn-record-parse-error :octets)
           (let ((d (fn-cfg-item-decode octets)))
             (if (not (fn-cbor-result-okp d))
                 (fn-record-parse-error :item)
               (if (not (fn-cfg-itemp (fn-cbor-result-value d)))
                   (fn-record-parse-error :item-type)
                 (let ((tail (fn-cfg-parse-items (- count 1)
                                                 (fn-cbor-result-rest d))))
                   (if (not (fn-record-parse-okp tail))
                       tail
                     (fn-record-parse-ok
                      (cons (fn-cbor-result-value d) (fn-record-parse-value tail))
                      (fn-record-parse-rest tail)))))))))
       :exec (fn-cfg-parse-items-loop count octets nil)))

(defthm fn-cfg-parse-items-loop-is-rev-onto
  (equal (fn-cfg-parse-items-loop count octets acc)
         (let ((r (fn-cfg-parse-items count octets)))
           (if (fn-record-parse-okp r)
               (fn-record-parse-ok (fn-ag-rev-onto acc (fn-record-parse-value r))
                                   (fn-record-parse-rest r))
             r)))
  :hints (("Goal" :induct (fn-cfg-parse-items-loop count octets acc)
                  :expand ((fn-cfg-parse-items count octets))
                  :in-theory (disable (:definition fn-cfg-parse-items)
                                      fn-cfg-parse-items-ok-shape
                                      fn-cfg-item-decode fn-cfg-itemp fn-cbor-octet-listp))))

(defthm fn-cfg-parse-items-loop-nil
  (equal (fn-cfg-parse-items-loop count octets nil) (fn-cfg-parse-items count octets))
  :hints (("Goal" :use ((:instance fn-cfg-parse-items-ok-shape))
                  :in-theory (union-theories '(fn-cfg-parse-items-loop-is-rev-onto fn-ag-rev-onto)
                                             (theory 'minimal-theory)))))

(verify-guards fn-cfg-parse-items
  :hints (("Goal" :expand ((fn-cfg-parse-items count octets))
                  :in-theory (disable (:definition fn-cfg-parse-items)
                                      (:definition fn-cfg-parse-items-loop)
                                      fn-cfg-parse-items-loop-is-rev-onto
                                      fn-cfg-parse-items-ok-shape
                                      fn-cfg-item-decode fn-cfg-itemp fn-cbor-octet-listp))))
