; fn: the value of a compressed payload (lane compression-extents, PRF-326).
;
; `fn-lzr-lz-value dict c n' is what an arena handle over a compressed
; extent holds: the N octets C decodes to against DICT (books/payload-lz.lisp,
; the proved decoder), always N octets long.  The arena's compressed seal and
; reseat (books/payload-arena.lisp) are defined over it, and the host's
; realizer for a compressed extent (A-DURABLE-LZ, books/assumptions.lisp)
; answers it: the host reads C, runs this decoder, and REFUSES by name
; (:lz-decode) where the decode fails, so the zero fill below is never served.
; Every compressed extent the node makes is one whose C decodes to its N
; octets (books/payload-lz-record.lisp fn-lzr-extent-of, the commit's check),
; so the value is the payload (`fn-lzr-lz-value-of-decode').

(in-package "ACL2")
(include-book "payload-lz")

;; The decoder's answer: a pair, and an :ok answer is octets.
(defthm fn-lzr-decode-consp
  (and (consp (fn-lz-decode dict c n))
       (true-listp (fn-lz-decode dict c n)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-lz-decode-buf))))

(defthm fn-lzr-decode-octets
  (implies (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c)
                (equal (car (fn-lz-decode dict c n)) :ok))
           (fn-cbor-octet-listp (cadr (fn-lz-decode dict c n))))
  :hints (("Goal" :in-theory (disable fn-lz-run))))

(defthm fn-lzr-decode-true-listp
  (implies (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c)
                (equal (car (fn-lz-decode dict c n)) :ok))
           (true-listp (cadr (fn-lz-decode dict c n))))
  :hints (("Goal" :in-theory (disable fn-lz-decode fn-lzr-decode-octets)
           :use fn-lzr-decode-octets)))

(in-theory (disable fn-lz-decode))

(defun fn-lzr-zeros (n)
  (declare (xargs :guard (natp n)))
  (make-list n :initial-element 0))

(defun fn-lzr-lz-value (dict c n)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c) (natp n))))
  (let ((r (fn-lz-decode dict c n)))
    (if (and (eq (car r) :ok) (true-listp (cadr r)) (equal (len (cadr r)) (nfix n)))
        (cadr r)
      (fn-lzr-zeros (nfix n)))))

(local
 (defthm fn-lzr-octets-of-make-list-ac
   (implies (fn-cbor-octet-listp ac)
            (fn-cbor-octet-listp (make-list-ac n 0 ac)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-lzr-len-make-list-ac
   (equal (len (make-list-ac n x ac)) (+ (nfix n) (len ac)))))

(defthm fn-lzr-lz-value-len
  (equal (len (fn-lzr-lz-value dict c n)) (nfix n)))

(defthm fn-lzr-lz-value-octets
  (implies (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c))
           (fn-cbor-octet-listp (fn-lzr-lz-value dict c n)))
  :hints (("Goal" :in-theory (disable fn-lz-run))))

(defthm fn-lzr-lz-value-of-decode
  (implies (and (equal (fn-lz-decode dict c n) (list :ok payload))
                (true-listp payload)
                (equal (len payload) (nfix n)))
           (equal (fn-lzr-lz-value dict c n) payload)))

(in-theory (disable fn-lzr-lz-value))
