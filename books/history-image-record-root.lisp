; Fixed record body extracted from pgs-x-write-rec. The abstract pgs-make-rec
; is a logical model and calls constrained pgs-digest; it is not executable.
(in-package "ACL2")
(include-book "pagestore-exec")
(include-book "pagestore-words-blake3")

(defun fn-hpir-body-words (txid address count digest)
  (declare (xargs :guard t))
  (list *pgs-magic* (pgs-dlo txid) (pgs-dlo address) (pgs-dlo count)
        *pgs-page-words* 0 0 0
        (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi digest))))
        (pgs-dlo (pgs-dhi (pgs-dhi digest)))
        (pgs-dlo (pgs-dhi digest)) (pgs-dlo digest) 0 0 0 0))

(defun fn-hpir-root (txid address count digest)
  (declare (xargs :guard t))
  (list :pgs-commit (pgs-dlo txid) (pgs-dlo address) (pgs-dlo count)
        (pgs-h64 (pgs-dlo digest)
          (pgs-h64 (pgs-dlo (pgs-dhi digest))
            (pgs-h64 (pgs-dlo (pgs-dhi (pgs-dhi digest)))
                     (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi digest)))))))
        (pgs-octets-be-nat
          (fn-blake3 (pgs-words-le-octets
                       (fn-hpir-body-words txid address count digest))))))

; The complete concrete record relation to pgs-x-write-rec remains an open
; PRF-1144 boundary obligation until its actual word writes are connected.
; The fixed16 words and fixed128 hash bytes are independent of stored data.
(defthm fn-hpir-body-width-by-definition
  (equal (len (fn-hpir-body-words txid address count digest)) 16))
