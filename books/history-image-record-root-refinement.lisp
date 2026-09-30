(in-package "ACL2")
(include-book "history-image-record-root")
(local (include-book "arithmetic/top" :dir :system))

; Local facts connect actual checksum bytes and concrete word writes.
; None is a replacement writer or an assumption about caller data.
(local (progn
(defthm fn-hpir-acc-step-bound
  (implies (and (rationalp octet) (<= 0 octet) (<= octet 255)
                (rationalp factor) (<= 0 factor) (rationalp acc) (<= 0 acc))
           (<= (+ factor (* octet factor) (* 256 acc factor))
               (* (+ 1 acc) 256 factor)))
  :hints (("Goal" :nonlinearp t)))
))

(local (progn
(defthm fn-hpir-octet-acc-bound
  (implies (and (fn-b3-octet-listp bytes) (natp acc))
           (and (natp (pgs-octets-be-nat-acc bytes acc))
                (< (pgs-octets-be-nat-acc bytes acc)
                   (* (+ 1 acc) (expt 256 (len bytes))))))
  :hints (("Goal" :induct (pgs-octets-be-nat-acc bytes acc) :nonlinearp t
           :in-theory (enable pgs-octets-be-nat-acc fn-b3-octet-listp expt))
          ("Subgoal *1/1'''" :use ((:instance fn-hpir-acc-step-bound
               (acc acc) (octet (car bytes)) (factor (expt 256 (len (cdr bytes))))))
            :in-theory (disable fn-hpir-acc-step-bound))))

(defthm fn-hpir-blake3-check-is-u256
  (unsigned-byte-p 256 (pgs-octets-be-nat (fn-blake3 bytes)))
  :hints (("Goal" :use ((:instance fn-hpir-octet-acc-bound
                                   (bytes (fn-blake3 bytes)) (acc 0)))
           :in-theory (e/d (pgs-octets-be-nat unsigned-byte-p)
                           (fn-blake3 pgs-octets-be-nat-acc fn-hpir-octet-acc-bound)))))
))

(local (progn
(defthm fn-hpir-zero-array
  (equal (nth *pgs-mi* (pgs-x-zero-words 1 0 20 pgs-mem))
         (append (pgs-zeros 20) (nthcdr 20 (nth *pgs-mi* pgs-mem))))
  :hints (("Goal"
           :expand ((:free (a k pgs-mem) (pgs-x-zero-words 1 a k pgs-mem))
                    (:free (k xs) (nthcdr k xs)))
           :in-theory (enable pgs-x-zero-words pgs-x-put update-pgs-mi
                              pgs-mi update-nth nthcdr pgs-zeros))))
))

; Complete root output, not only its checksum. The logical equality has
; no premises; executable reference calls still satisfy the stobj guards.
(defthm fn-hpir-root-agrees-with-current-record-writer
  (equal (fn-hpir-root txid address count digest)
         (mv-nth 0 (pgs-x-write-rec 0 txid address count digest
                                    pgs-mem fn-octets-pg)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-hpir-blake3-check-is-u256
              (bytes (pgs-words-le-octets
                        (fn-hpir-body-words txid address count digest)))))
           :in-theory (e/d (fn-hpir-root fn-hpir-body-words pgs-x-write-rec
                            pgs-x-put-dig4 pgs-x-dig4 pgs-x-words pgs-x-arr
                            pgs-x-put pgs-x-word pgs-x-len
                            update-pgs-mi pgs-mi update-nth nth take pgs-m-length unsigned-byte-p)
                           (fn-hpir-blake3-check-is-u256 pgs-x-zero-words fn-blake3 pgs-words-le-octets pgs-octets-be-nat
                            pgs-x-words-digest pgs-dlo pgs-dhi)))))
