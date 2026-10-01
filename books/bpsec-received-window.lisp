; Refinement at the actual concrete received-byte leaf reader. The whole
; segment abstraction is ghost only; served FN-BPRX-SEGMENT-WINDOW stays <=64.
; This does not issue a backing reference or establish registered lifetime.
(in-package "ACL2")
(include-book "bp-received-byte-storage")
(include-book "bpsec-model")

(defun fn-bps-received-segment-alpha-from (at count fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment :measure (nfix count)
  :guard (and (natp at) (natp count) (<= (+ at count) 256))))
 (if (zp count) nil
  (cons (fn-bprx-bytesi at fn-bprx-segment)
        (fn-bps-received-segment-alpha-from (1+ at) (1- count) fn-bprx-segment))))

(defun fn-bps-received-segment-alpha (fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment :guard t))
 (fn-bps-received-segment-alpha-from 0 (fn-bprx-used fn-bprx-segment) fn-bprx-segment))

(local
 (defthm fn-bps-received-window-loop-by-definition
  (implies (and (natp at) (natp count))
   (equal (fn-bprx-segment-window-bytes at count fn-bprx-segment)
          (fn-bps-received-segment-alpha-from at count fn-bprx-segment)))
  :hints (("Goal" :induct (fn-bprx-segment-window-bytes at count fn-bprx-segment)
                  :in-theory (disable fn-bprx-bytesi)))))

(local
 (defun fn-bps-received-drop-induct (drop at count)
  (declare (xargs :guard t :measure (nfix drop)))
  (if (zp (nfix drop)) (list at count)
    (fn-bps-received-drop-induct (1- (nfix drop)) (1+ (nfix at)) (1- (nfix count))))))

(local
 (defthm fn-bps-received-alpha-drop-by-definition
  (implies (and (natp at) (natp count) (natp drop) (<= drop count))
   (equal (nthcdr drop (fn-bps-received-segment-alpha-from at count fn-bprx-segment))
          (fn-bps-received-segment-alpha-from (+ at drop) (- count drop) fn-bprx-segment)))
  :hints (("Goal" :induct (fn-bps-received-drop-induct drop at count)
                  :in-theory (disable fn-bprx-bytesi)))))

(local
 (defthm fn-bps-received-alpha-take-by-definition
  (implies (and (natp at) (natp count) (natp width) (<= width count))
   (equal (take width (fn-bps-received-segment-alpha-from at count fn-bprx-segment))
          (fn-bps-received-segment-alpha-from at width fn-bprx-segment)))
  :hints (("Goal" :induct (fn-bps-received-drop-induct width at count)
                  :in-theory (disable fn-bprx-bytesi)))))

(local
 (defthm fn-bps-received-used-domain-by-definition
  (implies (fn-bprx-segmentp fn-bprx-segment)
           (and (natp (fn-bprx-used fn-bprx-segment))
                (<= (fn-bprx-used fn-bprx-segment) 256)))
  :hints (("Goal" :in-theory (enable fn-bprx-segmentp fn-bprx-used)))))

(local
 (defthm fn-bps-received-alpha-length-by-definition
  (implies (natp count)
           (equal (len (fn-bps-received-segment-alpha-from at count fn-bprx-segment)) count))
  :hints (("Goal" :induct (fn-bps-received-segment-alpha-from at count fn-bprx-segment)
                  :in-theory (disable fn-bprx-bytesi)))))


(local
 (defthm fn-bps-received-array-nth-octet-by-definition
  (implies (and (fn-bprx-bytesp xs) (natp at) (< at (len xs)))
           (fn-cbor-octetp (nth at xs)))
  :hints (("Goal" :induct (nth at xs)
                  :in-theory (enable fn-cbor-octetp fn-bprx-bytesp)))))

(local
 (defthm fn-bps-received-getter-octet-by-definition
  (implies (and (fn-bprx-segmentp fn-bprx-segment) (natp at) (< at 256))
           (fn-cbor-octetp (fn-bprx-bytesi at fn-bprx-segment)))
  :hints (("Goal" :in-theory (enable fn-bprx-segmentp fn-bprx-bytesi)))))

(local
 (defthm fn-bps-received-alpha-octets-by-definition
  (implies (and (fn-bprx-segmentp fn-bprx-segment) (natp at) (natp count) (<= (+ at count) 256))
           (fn-cbor-octet-listp (fn-bps-received-segment-alpha-from at count fn-bprx-segment)))
  :hints (("Goal" :induct (fn-bps-received-segment-alpha-from at count fn-bprx-segment)
                  :in-theory (e/d (fn-cbor-octet-listp)
                                  (fn-bprx-segmentp fn-bprx-bytesi fn-cbor-octetp))))))

; The alias is a logical segment backing, not a source-issued runtime grant.
; Absolute original-wire/block binding and lifetime are caller obligations.
(local
 (defthm fn-bps-received-window-parser-shape-by-definition
 (implies (and (fn-bprx-segmentp fn-bprx-segment) (natp at) (natp count) (<= count 64)
               (equal nonce (fn-bprx-nonce fn-bprx-segment))
               (equal ordinal (fn-bprx-ordinal fn-bprx-segment))
               (eq (fn-bprx-phase fn-bprx-segment) :frozen)
               (<= (+ at count) (fn-bprx-used fn-bprx-segment)))
  (fn-bps-windowp (fn-bps-window-make backing-id at
    (mv-nth 1 (fn-bprx-segment-window nonce ordinal at count fn-bprx-segment)))))
 :hints (("Goal" :use ((:instance fn-bps-received-used-domain-by-definition))
                  :in-theory (e/d (fn-bprx-segment-window fn-bps-windowp fn-bps-window-make
                                    fn-bps-uintp fn-bps-field)
                                   (fn-bprx-segmentp fn-bprx-used fn-bprx-nonce fn-bprx-ordinal fn-bprx-phase
                                    fn-bprx-segment-window-bytes fn-bps-received-segment-alpha-from
                                    fn-cbor-octet-listp fn-bps-received-used-domain-by-definition))))))

(defthm fn-bps-received-window-is-exact-concrete-slice
 (implies (and (fn-bprx-segmentp fn-bprx-segment) (natp at) (natp count) (<= count 64)
               (equal nonce (fn-bprx-nonce fn-bprx-segment))
               (equal ordinal (fn-bprx-ordinal fn-bprx-segment))
               (eq (fn-bprx-phase fn-bprx-segment) :frozen)
               (<= (+ at count) (fn-bprx-used fn-bprx-segment)))
  (and (equal (mv-nth 0 (fn-bprx-segment-window nonce ordinal at count fn-bprx-segment)) :source-window)
       (equal (mv-nth 1 (fn-bprx-segment-window nonce ordinal at count fn-bprx-segment))
              (take count (nthcdr at (fn-bps-received-segment-alpha fn-bprx-segment))))
       (equal (len (mv-nth 1 (fn-bprx-segment-window nonce ordinal at count fn-bprx-segment))) count)
       (<= (len (mv-nth 1 (fn-bprx-segment-window nonce ordinal at count fn-bprx-segment))) 64)
       (fn-bps-windowp (fn-bps-window-make backing-id at
          (mv-nth 1 (fn-bprx-segment-window nonce ordinal at count fn-bprx-segment))))))
 :hints (("Goal" :use ((:instance fn-bps-received-window-parser-shape-by-definition)
                       (:instance fn-bps-received-used-domain-by-definition)
                       (:instance fn-bps-received-alpha-drop-by-definition
                                  (drop at) (at 0) (count (fn-bprx-used fn-bprx-segment)))
                       (:instance fn-bps-received-alpha-take-by-definition
                                  (at at) (count (- (fn-bprx-used fn-bprx-segment) at)) (width count)))
                  :in-theory (e/d (fn-bprx-segment-window fn-bps-received-segment-alpha)
                                (fn-bprx-segmentp fn-bprx-used fn-bprx-phase fn-bprx-nonce fn-bprx-ordinal
                                 fn-bprx-segment-window-bytes fn-bps-received-segment-alpha-from
                                 fn-bps-received-alpha-drop-by-definition fn-bps-received-alpha-take-by-definition
                                 fn-bps-received-used-domain-by-definition fn-bps-windowp
                                 fn-bps-received-window-parser-shape-by-definition)))))

