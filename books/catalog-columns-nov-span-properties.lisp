; The actual encoded NOV spans stay inside their appended byte pool.
; Width conversion has its existing semantics; wide values are retained by
; the caller's escape decision, without a stored-data ceiling.
(in-package "ACL2")
(include-book "catalog-columns-storage-growth")

(defthm fn-lbc-u64-natural
  (natp (fn-lbc-u64 x)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-lbc-u64 unsigned-byte-p integer-range-p))))

(defthm fn-lbc-u64-unsigned-by-definition
 (unsigned-byte-p 64 (fn-lbc-u64 x))
 :hints (("Goal" :in-theory (enable fn-lbc-u64 unsigned-byte-p integer-range-p))))

(defthm fn-lbc-u64-at-most-nfix
  (<= (fn-lbc-u64 x) (nfix x))
  :hints (("Goal" :in-theory (enable fn-lbc-u64 unsigned-byte-p integer-range-p nfix))))

(defthm fn-lbc-clamped-span-in-pool
  (implies (<= (+ (nfix start) (nfix length)) (nfix limit))
   (fn-lb-column-span-in-poolp (fn-lbc-u64 start) (fn-lbc-u64 length) limit))
  :hints (("Goal"
   :use ((:instance fn-lbc-u64-at-most-nfix (x start))
         (:instance fn-lbc-u64-at-most-nfix (x length)))
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lb-column-span-in-poolp nfix (:type-prescription fn-lbc-u64-natural))))))

(defun-nx fn-lb-span-pairs-layoutp (spans limit)
  (if (consp spans)
   (and (consp (cdr spans))
        (fn-lb-column-span-in-poolp (car spans) (cadr spans) limit)
        (fn-lb-span-pairs-layoutp (cddr spans) limit))
   (null spans)))

(local (defthm fn-lbns-len-true-list-fix
  (equal (len (true-list-fix xs)) (len xs))
  :hints (("Goal" :induct (len xs) :in-theory (enable true-list-fix len)))))

(local (defthm fn-lbns-len-append
  (equal (len (append xs ys)) (+ (len xs) (len ys)))
  :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(defthm fn-lbc-nov-spans-are-in-pool
  (implies (natp offset)
   (fn-lb-span-pairs-layoutp (fn-lbc-nov-spans texts offset)
    (+ offset (len (fn-lbc-texts-octets-model texts)))))
  :hints (("Goal" :induct (fn-lbc-nov-spans texts offset)
   :in-theory (union-theories (theory 'ground-zero)
    '(fn-lbc-nov-spans fn-lbc-texts-octets-model fn-lb-span-pairs-layoutp
      fn-lbc-clamped-span-in-pool fn-lbns-len-append fn-lbns-len-true-list-fix
      nfix)))))
