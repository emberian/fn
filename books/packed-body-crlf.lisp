; fn: total body framing check over the original packed natural.
(in-package "ACL2")
(include-book "packed-octet-access")
(include-book "article")
(include-book "def-loop")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-pcr-step-okp (index count n)
 (declare (xargs :guard (and (natp index) (natp count))))
 (let ((byte (fn-poa-octet index n)))
  (if (equal byte 13)
   (and (< (+ 1 index) count) (equal (fn-poa-octet (+ 1 index) n) 10))
   (not (equal byte 10)))))

(local (in-theory (disable fn-poa-octet-is-indexed-octet
                          fn-poa-length-is-unpack-length fn-pcr-step-okp)))

; STEP with no emitted rows is a tail loop that returns only its final
; boolean. It never calls CONS on the executed path. The BODY 0 term and
; NEXT arm belong to the generator's unreachable EMIT branch.
(def-loop fn-pcr-scan (index count n)
 :shape :step :over index
 :guard (and (natp index) (natp count))
 :measure (nfix (- (nfix count) (nfix index)))
 :done (or (not (natp index)) (>= index (nfix count))
           (not (fn-pcr-step-okp index count n)))
 :tail (>= (nfix index) (nfix count))
 :emit nil :body 0
 :next (+ index 1)
 :skip-next (+ index (if (equal (fn-poa-octet index n) 13) 2 1)))

(local (defthm fn-pcr-consp-nthcdr
 (implies (natp index)
  (equal (consp (nthcdr index xs)) (< index (len xs))))
 :hints (("Goal" :induct (nthcdr index xs)))))

(local (defthm fn-pcr-car-nthcdr
 (equal (car (nthcdr index xs)) (nth index xs))
 :hints (("Goal" :induct (nthcdr index xs)))))

(local (defthm fn-pcr-cdr-nthcdr
 (implies (natp index)
  (equal (cdr (nthcdr index xs)) (nthcdr (+ 1 index) xs)))
 :hints (("Goal" :induct (nthcdr index xs)))))

(defthm fn-pcr-scan-refines
 (implies (and (natp index) (equal count (len (fn-bch-unpack n))))
  (equal (fn-pcr-scan index count n)
         (fn-article-body-crlfp (nthcdr index (fn-bch-unpack n)))))
 :hints (("Goal" :induct (fn-pcr-scan index count n)
          :in-theory (e/d (fn-pcr-scan fn-pcr-step-okp fn-poa-octet-is-indexed-octet)
                          (fn-bch-unpack nthcdr nth fn-poa-octet fn-poa-bits))
          :expand ((fn-article-body-crlfp (nthcdr index (fn-bch-unpack n)))))))

(defun fn-art-body-crlfp (body)
 (declare (xargs :guard t))
 (fn-pcr-scan 0 (fn-poa-length body) body))

(defthm fn-art-body-crlfp-refines
 (equal (fn-art-body-crlfp body)
        (fn-article-body-crlfp (fn-bch-unpack body)))
 :hints (("Goal" :in-theory (e/d (fn-art-body-crlfp fn-poa-length-is-unpack-length)
                          (fn-pcr-scan fn-poa-length fn-bch-unpack fn-article-body-crlfp)))))

(in-theory (disable fn-art-body-crlfp fn-pcr-scan fn-pcr-step-okp))
