; PRF-1132 / SCN-1039. Actual input helper to selected arithmetic object path.
(in-package "ACL2")
(include-book "payload-window-width")
(include-book "assumptions-selected-runtime-pull")

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-paw-actual-shift-in-fixnum-domain
  (implies (fn-srp-pull-object-domain-p bits nbits octet)
           (and (natp (expt 2 nbits)) (<= (expt 2 nbits) (expt 2 31))
                (natp (* octet (expt 2 nbits)))
                (< (* octet (expt 2 nbits)) (expt 2 39))
                (natp (fn-zin-shift-in bits nbits octet))
                (< (fn-zin-shift-in bits nbits octet) (expt 2 39))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-srp-pull-object-domain-p fn-zin-shift-in)
                  :nonlinearp t))))

(defthm fn-paw-actual-pull-helper-domain
 (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
               (< (fn-zin-nbits fn-zin-st) 32)
               (fn-cbor-octetp (fn-octets-get ip fn-octets)))
          (fn-srp-pull-object-domain-p
           (fn-zin-bits fn-zin-st) (fn-zin-nbits fn-zin-st)
           (fn-octets-get ip fn-octets)))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-pzw-state-bits-widthp fn-pzw-bits-widthp
                  fn-srp-pull-object-domain-p fn-cbor-octetp))))

(defthm fn-paw-actual-needed-pull-helper-domain
 (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
               (< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
               (fn-cbor-octetp (fn-octets-get ip fn-octets)))
          (fn-srp-pull-object-domain-p
           (fn-zin-bits fn-zin-st) (fn-zin-nbits fn-zin-st)
           (fn-octets-get ip fn-octets)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-paw-actual-pull-helper-domain)
                       (:instance fn-zin-need-bound)))))

(defthm fn-paw-actual-pull-helper-object-workspace-by-definition
 (implies (and (fn-srp-pull-coordinate-p coordinate body)
               (fn-pzw-state-bits-widthp fn-zin-st)
               (< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
               (fn-cbor-octetp (fn-octets-get ip fn-octets)))
          (equal (fn-assume-srp-pull-object-octets
                   (fn-zin-bits fn-zin-st) (fn-zin-nbits fn-zin-st)
                   (fn-octets-get ip fn-octets) coordinate body) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-srp-pull-object-domain-p)
          :use ((:instance fn-paw-actual-needed-pull-helper-domain)
                (:instance fn-assume-srp-pull-object-path-bound
                 (bits (fn-zin-bits fn-zin-st))
                 (nbits (fn-zin-nbits fn-zin-st))
                 (octet (fn-octets-get ip fn-octets)))))))
