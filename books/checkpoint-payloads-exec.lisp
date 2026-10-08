; Concrete payload frame writer. The source is a range of the byte buffer;
; the frame is appended to that buffer using its existing concrete back-copy.
; No payload list is materialized by the executable writer.
(in-package "ACL2")
(include-book "checkpoint-payloads")
(include-book "frame-digest-buffer")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm cplx-len-append
         (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm cplx-append-assoc
         (equal (append (append a b) c) (append a b c))))
(local (defthm cplx-nth-after-prefix
         (equal (nth (len pre) (append pre xs)) (car xs))))

(local
 (defun cplx-copy-ind (pre xs post)
   (if (consp xs)
       (cplx-copy-ind (append pre (list (car xs))) (cdr xs)
                       (append post (list (car xs))))
     (list pre post))))

(local
 (defthm cplx-back-copy-parts
   (implies (and (true-listp pre) (true-listp xs) (true-listp post))
            (equal (fn-oct-back-copy (+ (len xs) (len post)) (len xs)
                                     (append pre xs post))
                   (append pre xs post xs)))
   :hints (("Goal" :induct (cplx-copy-ind pre xs post)
            :in-theory (enable fn-oct-back-copy fn-oct-snoc-is-append
                               fn-oct-nth-is-nth)))))

(local (defthm cplx-len-take
         (implies (natp n) (equal (len (take n x)) n))))
(local (defthm cplx-len-nthcdr
         (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
         :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))
(local (defthm cplx-split
         (implies (and (true-listp x) (natp n) (<= n (len x)))
                  (equal (append (take n x) (nthcdr n x)) x))))
(local (defthm cplx-split-tail
         (implies (and (true-listp x) (natp n) (<= n (len x)))
                  (equal (append (take n x) (nthcdr n x) tail) (append x tail)))
         :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))
(local
 (defthm cplx-back-copy-range
   (implies (and (true-listp x) (natp a) (natp n) (<= (+ a n) (len x)))
            (equal (fn-oct-back-copy (- (len x) a) n x)
                   (append x (take n (nthcdr a x)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-oct-back-copy cplx-back-copy-parts)
            :use ((:instance cplx-back-copy-parts
                             (pre (take a x)) (xs (take n (nthcdr a x)))
                             (post (nthcdr n (nthcdr a x)))))))))

(defun fn-cpl-x-write-frame (a n base fn-octets)
  ; Append the frame after the original buffer. A and N name that buffer's
  ; source range. BASE is the committed payload-file boundary, never EOF.
  ; The host drains only the appended frame; REF names its payload on disk.
  (declare (xargs :stobjs fn-octets :verify-guards nil
                  :guard (and (natp a) (natp n) (natp base)
                              (<= (+ a n) (fn-octets-len fn-octets))
                              (< (+ 1 n) 18446744073709551616))))
  (let* ((start (fn-octets-len fn-octets))
         (fn-octets (fn-sccb-append-list (fn-scc-header 0 1 n 0) fn-octets))
         (fn-octets (fn-octets-append-back (- (fn-octets-len fn-octets) a) n fn-octets))
         (trailer (fn-blake3-of-prefixed-range nil start (+ 37 n) fn-octets))
         (fn-octets (fn-sccb-append-list trailer fn-octets)))
    (mv (list (+ base 37) n) trailer fn-octets)))

(local (defthm cplx-nthcdr-append
         (implies (and (natp n) (<= n (len x)))
                  (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))
         :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))
(local (defthm cplx-take-append
         (implies (and (natp n) (<= n (len x)))
                  (equal (take n (append x y)) (take n x)))))
(local
 (defthm cplx-copy-after-header
   (implies (and (true-listp x) (natp a) (natp n) (<= (+ a n) (len x)))
            (equal (fn-octets-append-back
                    (- (len (append x (fn-scc-header 0 1 n 0))) a) n
                    (append x (fn-scc-header 0 1 n 0)))
                   (append x (fn-scc-header 0 1 n 0) (take n (nthcdr a x)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-oct-append-back-is-back-copy)
                            (fn-oct-back-copy cplx-back-copy-range fn-scc-header))
            :use ((:instance cplx-back-copy-range (x (append x (fn-scc-header 0 1 n 0)))))))))

(local (defthm cplx-nthcdr-len
         (implies (true-listp x) (equal (nthcdr (len x) x) nil))))
(local (defthm cplx-take-len
         (implies (true-listp x) (equal (take (len x) x) x))))
(local (defthm cplx-cbor-scc
         (implies (fn-cbor-octet-listp x) (fn-scc-octet-listp x))
         :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-cbor-octet-listp
                                           fn-sccb-scc-octetp-is-cbor-octetp)))))
(local (defthm cplx-octets-nthcdr
         (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (nthcdr a x)))
         :hints (("Goal" :induct (nthcdr a x) :in-theory (enable nthcdr fn-cbor-octet-listp)))))
(local (defthm cplx-octets-take
         (implies (and (fn-cbor-octet-listp x) (natp n) (<= n (len x)))
                  (fn-cbor-octet-listp (take n x)))
         :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm cplx-payloadp-range
         (implies (and (fn-octets-p x) (natp a) (natp n) (<= (+ a n) (len x))
                       (< (+ 1 n) 18446744073709551616))
                  (fn-cpl-payloadp (fn-shr-win a n x)))
         :hints (("Goal" :in-theory (enable fn-cpl-payloadp fn-shr-win
                                           fn-oct-octets-p-is-octet-listp)))))

(local (defthm cplx-take-full
         (implies (and (true-listp x) (equal n (len x)))
                  (equal (take n x) x))))

(defthm fn-cpl-x-write-frame-is-the-frame
  (implies (and (fn-octets-p fn-octets) (natp a) (natp n) (natp base)
                (<= (+ a n) (fn-octets-len fn-octets))
                (< (+ 1 n) 18446744073709551616))
           (let ((p (fn-shr-win a n fn-octets))
                 (r (fn-cpl-x-write-frame a n base fn-octets)))
             (and (equal (mv-nth 0 r) (list (+ base 37) (len p)))
                  (equal (mv-nth 1 r) (fn-cpl-trailer p))
                  (equal (mv-nth 2 r) (fn-cpl-write-frame p fn-octets)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-x-write-frame fn-shr-win fn-cpl-prefix fn-frame-digest)
                           (fn-blake3 fn-blake3-of-prefixed-range fn-cpl-trailer
                            fn-cpl-write-frame fn-cpl-frame fn-scc-header fn-octets-append-back
                            fn-oct-back-copy))
           :use ((:instance cplx-payloadp-range (x fn-octets))
                 (:instance cplx-copy-after-header (x fn-octets))
                 (:instance fn-cpl-trailer-is-the-frame-digest (p (fn-shr-win a n fn-octets)))
                 (:instance fn-cpl-write-frame-is-the-frame (p (fn-shr-win a n fn-octets)))
                 (:instance fn-cpl-frame-layout (p (fn-shr-win a n fn-octets)))
                 (:instance fn-blake3-of-prefixed-range-is-blake3
                            (prefix nil) (a (len fn-octets)) (wn (+ 37 n))
                            (fn-octets (append fn-octets (fn-scc-header 0 1 n 0)
                                                (take n (nthcdr a fn-octets)))))))))

(local (defthm cplx-u64-octets (fn-scc-octet-listp (fn-scc-u64 n k))
         :hints (("Goal" :in-theory (enable fn-scc-u64 fn-scc-octetp fn-scc-octet-listp)))))
(local (defthm cplx-scc-append
         (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
                  (fn-scc-octet-listp (append a b)))
         :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))
(local (defthm cplx-header-octets
         (fn-scc-octet-listp (fn-scc-header 0 1 n 0))
         :hints (("Goal" :in-theory (enable fn-scc-header fn-scc-octetp fn-scc-octet-listp)))))
(verify-guards fn-cpl-x-write-frame
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scc-header fn-octets-append-back fn-oct-back-copy)
           :use ((:instance cplx-copy-after-header (x fn-octets))))))

; The four packed trailer words consumed by row staging are precisely those
; of the frame just appended, not a second host digest calculation.
(defthm fn-cpl-x-write-frame-trailer-is-the-staging-trailer
  (implies (and (fn-octets-p fn-octets) (natp a) (natp n) (natp base)
                (<= (+ a n) (fn-octets-len fn-octets))
                (< (+ 1 n) 18446744073709551616))
           (equal (fn-cpl-pack-words
                   (mv-nth 1 (fn-cpl-x-write-frame a n base fn-octets)) 4)
                  (fn-cpl-trailer-words-impl (fn-shr-win a n fn-octets))))
  :hints (("Goal" :use fn-cpl-x-write-frame-is-the-frame
           :in-theory (e/d (fn-cpl-trailer-words-impl)
                           (fn-cpl-x-write-frame fn-cpl-trailer fn-cpl-pack-words)))))
