; Genuine weakening to the existing generic16-bit pending-register carry.
; No conditional mode12 length-code invariant or new data policy is invented.
(in-package "ACL2")
(include-book "payload-action-runtime-workspace")
(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-paw-match-header16-arithmetic-domain
  (implies (and (< (fn-zin-tin fn-zin-st) 18446744073709551616)
                (<= (+ (fn-zin-tout fn-zin-st) (nfix room))
                    4722366482869645213696)
                (< (fn-zin-n fn-zin-st) 65536))
           (fn-ppr-arithmetic-domain
            (cdr (fn-pat-zin-match room fn-zin-st fn-zin-win fn-zin-out))
            18889465931478580854784))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-paw-match-copied-span)
                 (:instance fn-paw-copy-arithmetic-domain
                   (k (fn-pat-match-count room fn-zin-st))
                   (w (fn-zin-wpos fn-zin-st)) (d (fn-zin-dist fn-zin-st))
                   (tout (fn-zin-tout fn-zin-st)) (h (fn-zin-preset fn-zin-st))))
           :in-theory
           (e/d (fn-pat-zin-match fn-pat-match-count fn-pzt-zin-bomb-limit
                 fn-ppr-arithmetic-domain fn-srp-operand-domain-p
                 fn-srp-integer-inputs-fit fn-srp-positive-operand-domain-p
                 fn-srp-positive-factorp fn-ppr-scale-factor fn-ppr-scale-value)
                (fn-zin-fld fn-zin-set fn-pzc-copy fn-zin-copy binary-append)))))
)

(defthm fn-paw-actual-match-header16-arithmetic-workspace
 (implies (and (fn-srp-coordinate-p coordinate)
               (< (fn-zin-tin fn-zin-st) 18446744073709551616)
               (<= (+ (fn-zin-tout fn-zin-st) (nfix room))
                   4722366482869645213696)
               (< (fn-zin-n fn-zin-st) 65536))
          (<= (fn-ppr-arithmetic-octets
               (cdr (fn-pat-zin-match room fn-zin-st fn-zin-win fn-zin-out)) coordinate)
              (if (zp (fn-pat-match-count room fn-zin-st)) 128
                (+ 224 (* 96 (nfix (fn-pat-match-count room fn-zin-st)))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-paw-match-header16-arithmetic-domain)
        (:instance fn-pat-match-arithmetic-counts)
        (:instance fn-ppr-arithmetic-family-primitive-bound
          (limit 18889465931478580854784)
          (trace (cdr (fn-pat-zin-match room fn-zin-st fn-zin-win fn-zin-out)))))
  :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                 (fn-pat-zin-match fn-ppr-arithmetic-domain
                  fn-ppr-arithmetic-octets fn-srp-coordinate-p)))))
