; Reachable witnesses and corruption teeth for P4 metadata frames.
(in-package "ACL2")
(include-book "../../books/byte-store-frame")
(include-book "../../books/codec-attach")

; The development profile and zero frontier are the actual bytes init writes.
(assert-event (fn-bs-config-okp (fn-bs-initial-config-octets)))
(assert-event (equal (fn-bs-config-decode (fn-bs-initial-config-octets))
                     *fn-bs-meta-development-values*))
(assert-event (equal (fn-bs-frontier-decode (fn-bs-initial-frontier-octets)) 0))
(assert-event (equal (fn-bs-frontier-decode
                      (fn-bs-frontier-encode 4294967295))
                     4294967295))
(assert-event (equal (fn-bs-frontier-next 4294967294) 4294967295))
(assert-event (not (fn-bs-frontier-next 4294967295)))

; New stores adopt format 7's 196,608-octet record ceiling.  Persisted format
; 6 profiles remain readable but refuse the same prospective record before
; publication, and both profiles refuse an aggregate overflow.
(assert-event
 (equal (fn-bs-profile-record-ceiling *fn-bs-meta-development-values*) 196608))
(assert-event
 (equal (fn-bs-profile-record-ceiling
         *fn-bs-meta-legacy-development-values*) 65538))
(assert-event
 (fn-bs-publication-admissiblep *fn-bs-meta-development-values* 0 196608))
(assert-event
 (not (fn-bs-publication-admissiblep
       *fn-bs-meta-legacy-development-values* 0 196608)))
(assert-event
 (not (fn-bs-publication-admissiblep
       *fn-bs-meta-development-values* 128 196608)))
(assert-event
 (fn-bs-profile-aggregate-covers-recordsp *fn-bs-meta-development-values*))
(assert-event
 (fn-bs-profile-aggregate-covers-recordsp
  *fn-bs-meta-legacy-development-values*))
(assert-event
 (equal (fn-bs-config-decode
         (fn-bs-config-encode *fn-bs-meta-legacy-development-values*))
        *fn-bs-meta-legacy-development-values*))

; A truncated authentic frame must not become a frontier.  The visible value
; is not merely a wrong integer: decoding reports no value at all.
(assert-event
 (let ((cut (take (1- (len (fn-bs-initial-frontier-octets)))
                  (fn-bs-initial-frontier-octets))))
   (and (not (fn-bs-frontier-decode cut))
        (not (fn-bs-config-okp cut)))))

; A frame with a valid trailer but the wrong metadata kind is also rejected.
(assert-event
 (let ((wrong (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                             *fn-bs-meta-config-kind*
                             (fn-cbor-encode (cons :uint 0)))))
   (not (fn-bs-frontier-decode wrong))))
